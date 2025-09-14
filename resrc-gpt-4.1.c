/* resrc.c -- read and write Windows rc files.
   Copyright (C) 1997-2025 Free Software Foundation, Inc.
   Written by Ian Lance Taylor, Cygnus Support.
   Rewritten by Kai Tietz, Onevision.

   This file is part of GNU Binutils.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 51 Franklin Street - Fifth Floor, Boston, MA
   02110-1301, USA.  */

/* This file contains functions that read and write Windows rc files.
   These are text files that represent resources.  */

#include "sysdep.h"
#include "bfd.h"
#include "bucomm.h"
#include "libiberty.h"
#include "safe-ctype.h"
#include "windres.h"

#include <assert.h>

#ifdef HAVE_SYS_WAIT_H
#include <sys/wait.h>
#else /* ! HAVE_SYS_WAIT_H */
#if ! defined (_WIN32) || defined (__CYGWIN__)
#ifndef WIFEXITED
#define WIFEXITED(w)	(((w)&0377) == 0)
#endif
#ifndef WIFSIGNALED
#define WIFSIGNALED(w)	(((w)&0377) != 0177 && ((w)&~0377) == 0)
#endif
#ifndef WTERMSIG
#define WTERMSIG(w)	((w) & 0177)
#endif
#ifndef WEXITSTATUS
#define WEXITSTATUS(w)	(((w) >> 8) & 0377)
#endif
#else /* defined (_WIN32) && ! defined (__CYGWIN__) */
#ifndef WIFEXITED
#define WIFEXITED(w)	(((w) & 0xff) == 0)
#endif
#ifndef WIFSIGNALED
#define WIFSIGNALED(w)	(((w) & 0xff) != 0 && ((w) & 0xff) != 0x7f)
#endif
#ifndef WTERMSIG
#define WTERMSIG(w)	((w) & 0x7f)
#endif
#ifndef WEXITSTATUS
#define WEXITSTATUS(w)	(((w) & 0xff00) >> 8)
#endif
#endif /* defined (_WIN32) && ! defined (__CYGWIN__) */
#endif /* ! HAVE_SYS_WAIT_H */

#ifndef STDOUT_FILENO
#define STDOUT_FILENO 1
#endif

#if defined (_WIN32) && ! defined (__CYGWIN__)
#define popen _popen
#define pclose _pclose
#endif

/* The default preprocessor.  */

#define DEFAULT_PREPROCESSOR_CMD "gcc"
#define DEFAULT_PREPROCESSOR_ARGS "-E -xc -DRC_INVOKED"

/* We read the directory entries in a cursor or icon file into
   instances of this structure.  */

struct icondir
{
  /* Width of image.  */
  bfd_byte width;
  /* Height of image.  */
  bfd_byte height;
  /* Number of colors in image.  */
  bfd_byte colorcount;
  union
  {
    struct
    {
      /* Color planes.  */
      unsigned short planes;
      /* Bits per pixel.  */
      unsigned short bits;
    } icon;
    struct
    {
      /* X coordinate of hotspot.  */
      unsigned short xhotspot;
      /* Y coordinate of hotspot.  */
      unsigned short yhotspot;
    } cursor;
  } u;
  /* Bytes in image.  */
  unsigned long bytes;
  /* File offset of image.  */
  unsigned long offset;
};

/* The name of the rc file we are reading.  */

char *rc_filename;

/* The line number in the rc file.  */

int rc_lineno;

/* The pipe we are reading from, so that we can close it if we exit.  */

FILE *cpp_pipe;

/* The temporary file used if we're not using popen, so we can delete it
   if we exit.  */

static char *cpp_temp_file;

/* Input stream is either a file or a pipe.  */

static enum {ISTREAM_PIPE, ISTREAM_FILE} istream_type;

/* As we read the rc file, we attach information to this structure.  */

static rc_res_directory *resources;

/* The number of cursor resources we have written out.  */

static int cursors;

/* The number of font resources we have written out.  */

static int fonts;

/* Font directory information.  */

rc_fontdir *fontdirs;

/* Resource info to use for fontdirs.  */

rc_res_res_info fontdirs_resinfo;

/* The number of icon resources we have written out.  */

static int icons;

/* The windres target bfd .  */

static windres_bfd wrtarget =
{
  (bfd *) NULL, (asection *) NULL, WR_KIND_TARGET
};

/* Local functions for rcdata based resource definitions.  */

static void define_font_rcdata (rc_res_id, const rc_res_res_info *,
				rc_rcdata_item *);
static void define_icon_rcdata (rc_res_id, const rc_res_res_info *,
				rc_rcdata_item *);
static void define_bitmap_rcdata (rc_res_id, const rc_res_res_info *,
				  rc_rcdata_item *);
static void define_cursor_rcdata (rc_res_id, const rc_res_res_info *,
				  rc_rcdata_item *);
static void define_fontdir_rcdata (rc_res_id, const rc_res_res_info *,
				   rc_rcdata_item *);
static void define_messagetable_rcdata (rc_res_id, const rc_res_res_info *,
					rc_rcdata_item *);
static rc_uint_type rcdata_copy (const rc_rcdata_item *, bfd_byte *);
static bfd_byte *rcdata_render_as_buffer (const rc_rcdata_item *, rc_uint_type *);

static int run_cmd (char *, const char *);
static FILE *open_input_stream (char *);
static FILE *look_for_default
  (char *, const char *, int, const char *, const char *);
static void close_input_stream (void);
static void unexpected_eof (const char *);
static int get_word (FILE *, const char *);
static unsigned long get_long (FILE *, const char *);
static void get_data (FILE *, bfd_byte *, rc_uint_type, const char *);
static void define_fontdirs (void);

/* Run `cmd' and redirect the output to `redir'.  */

static int run_cmd(char *cmd, const char *redir) {
    if (!cmd || !redir) {
        fatal(_("invalid arguments to run_cmd"));
        return 1;
    }

    int i = 0, retcode = 0, redir_handle = -1, stdout_save = -1;
    char *s = cmd;
    char *errmsg_fmt = NULL, *errmsg_arg = NULL;
    char *temp_base = make_temp_file(NULL);
    int pid, wait_status;

    // Argument count
    int argc = 1;
    for (s = cmd; *s; s++) {
        if (*s == ' ') argc++;
    }

    const char **argv = xmalloc(sizeof(char *) * (argc + 2));
    if (!argv) {
        fatal(_("allocation failure"));
        return 1;
    }

    // Argument parsing
    i = 0;
    s = cmd;
    while (1) {
        while (*s == ' ' && *s != 0) s++;
        if (*s == 0) break;

        int in_quote = (*s == '\'' || *s == '"');
        char sep = (in_quote) ? *s++ : ' ';
        argv[i++] = s;

        while (*s != sep && *s != 0) s++;
        if (*s == 0) break;
        *s++ = 0;
        if (in_quote) s++;
    }
    argv[i] = NULL;

    fflush(stdout);
    fflush(stderr);

    redir_handle = open(redir, O_WRONLY | O_TRUNC | O_CREAT, 0666);
    if (redir_handle == -1) {
        free(argv);
        fatal(_("can't open temporary file `%s': %s"), redir, strerror(errno));
        return 1;
    }

    stdout_save = dup(STDOUT_FILENO);
    if (stdout_save == -1) {
        close(redir_handle);
        free(argv);
        fatal(_("can't redirect stdout: `%s': %s"), redir, strerror(errno));
        return 1;
    }

    if (dup2(redir_handle, STDOUT_FILENO) == -1) {
        close(stdout_save);
        close(redir_handle);
        free(argv);
        fatal(_("dup2 failed: %s"), strerror(errno));
        return 1;
    }

    pid = pexecute(argv[0], (char * const *)argv, program_name, temp_base,
                   &errmsg_fmt, &errmsg_arg, PEXECUTE_ONE | PEXECUTE_SEARCH);

    dup2(stdout_save, STDOUT_FILENO);
    close(stdout_save);
    close(redir_handle);
    free(argv);

    if (pid == -1) {
        fatal("%s %s: %s", errmsg_fmt ? errmsg_fmt : "", errmsg_arg ? errmsg_arg : "", strerror(errno));
        return 1;
    }

    if (pwait(pid, &wait_status, 0) == -1) {
        fatal(_("wait: %s"), strerror(errno));
        retcode = 1;
    } else if (WIFSIGNALED(wait_status)) {
        fatal(_("subprocess got fatal signal %d"), WTERMSIG(wait_status));
        retcode = 1;
    } else if (WIFEXITED(wait_status)) {
        if (WEXITSTATUS(wait_status) != 0) {
            fatal(_("%s exited with status %d"), cmd, WEXITSTATUS(wait_status));
            retcode = 1;
        }
    } else {
        retcode = 1;
    }

    return retcode;
}

static FILE *open_input_stream(char *cmd) {
    char *fileprefix = NULL;
    FILE *pipe = NULL;

    if (istream_type == ISTREAM_FILE) {
        fileprefix = make_temp_file(NULL);
        if (!fileprefix)
            fatal(_("failed to create temporary file prefix: %s"), strerror(errno));

        cpp_temp_file = (char *)xmalloc(strlen(fileprefix) + 5);
        if (!cpp_temp_file)
            fatal(_("memory allocation failed: %s"), strerror(errno));

        snprintf(cpp_temp_file, strlen(fileprefix) + 5, "%s.irc", fileprefix);
        free(fileprefix);

        if (run_cmd(cmd, cpp_temp_file) != 0)
            fatal(_("can't execute `%s': %s"), cmd, strerror(errno));

        pipe = fopen(cpp_temp_file, FOPEN_RT);
        if (!pipe)
            fatal(_("can't open temporary file `%s': %s"), cpp_temp_file, strerror(errno));

        if (verbose) {
            fprintf(stderr, _("Using temporary file `%s' to read preprocessor output\n"), cpp_temp_file);
        }
    } else {
        pipe = popen(cmd, FOPEN_RT);
        if (!pipe)
            fatal(_("can't popen `%s': %s"), cmd, strerror(errno));
        if (verbose) {
            fprintf(stderr, _("Using popen to read preprocessor output\n"));
        }
    }

    cpp_pipe = pipe;
    xatexit(close_input_stream);
    return pipe;
}

/* Determine if FILENAME contains special characters that
   can cause problems unless the entire filename is quoted.  */

static int filename_need_quotes(const char *filename) {
    if (!filename)
        return 0;

    if (filename[0] == '-' && filename[1] == '\0')
        return 0;

    for (; *filename; filename++) {
        if (*filename == '&' || *filename == ' ' || *filename == '<' ||
            *filename == '>' || *filename == '|' || *filename == '%')
            return 1;
    }
    return 0;
}

/* Look for the preprocessor program.  */

static FILE *
look_for_default(char *cmd, const char *prefix, int end_prefix,
                 const char *preprocargs, const char *filename)
{
    struct stat s;
    const char *fnquotes;
    char *out;
    int need_quotes_cmd = 0;

    if (!cmd || !prefix || !preprocargs || !filename)
        return NULL;

    fnquotes = filename_need_quotes(filename) ? "\"" : "";

    memcpy(cmd, prefix, end_prefix);
    out = stpcpy(cmd + end_prefix, DEFAULT_PREPROCESSOR_CMD);

#if defined(__DJGPP__) || defined(__CYGWIN__) || defined(_WIN32)
    if (strchr(cmd, '\\') || strchr(cmd, '/'))
#else
    if (strchr(cmd, '/'))
#endif
    {
        int found = 0;
        if (stat(cmd, &s) == 0)
            found = 1;
#ifdef HAVE_EXECUTABLE_SUFFIX
        else if (stat(strcat(cmd, EXECUTABLE_SUFFIX), &s) == 0)
            found = 1;
#endif

        if (!found) {
            if (verbose)
                fprintf(stderr, _("Tried `%s'\n"), cmd);
            return NULL;
        }
    }

    need_quotes_cmd = filename_need_quotes(cmd);
    if (need_quotes_cmd) {
        size_t cmd_len = strlen(cmd);
        memmove(cmd + 1, cmd, cmd_len + 1);
        cmd[0] = '"';
        out = cmd + cmd_len + 1;
        *out++ = '"';
    }

    if (snprintf(out, FILENAME_MAX - (out - cmd), " %s %s %s%s%s",
            DEFAULT_PREPROCESSOR_ARGS, preprocargs, fnquotes, filename, fnquotes) < 0) {
        return NULL;
    }

    if (verbose)
        fprintf(stderr, _("Using `%s'\n"), cmd);

    cpp_pipe = open_input_stream(cmd);
    return cpp_pipe;
}

/* Read an rc file.  */

rc_res_directory *
read_rc_file(const char *filename, const char *preprocessor, const char *preprocargs, int language, int use_temp_file)
{
    char *cmd = NULL;
    const char *fnquotes;
    char *edit = NULL, *dir = NULL;
    char *dash = NULL, *slash = NULL, *cp;
    int is_relative = 0;

    if (!filename)
        filename = "-";
    fnquotes = filename_need_quotes(filename) ? "\"" : "";

    if (strcmp(filename, "-") != 0 && (strchr(filename, '/') || strchr(filename, '\\'))) {
        dir = xmalloc(strlen(filename) + 3);
        edit = dir;
        if (filename[0] != '/' && filename[0] != '\\' && filename[1] != ':') {
            *edit++ = '.';
            *edit++ = '/';
            is_relative = 1;
        }
        strcpy(edit, filename);

        edit = dir + strlen(dir);
        while (edit > dir && (edit[-1] != '\\' && edit[-1] != '/'))
            --edit;
        if (edit > dir)
            *--edit = 0;

        cp = dir;
        while ((cp = strchr(cp, '\\')) != NULL)
            *cp = '/';

        windres_add_include_dir(dir);
        free(dir);
    }

    istream_type = use_temp_file ? ISTREAM_FILE : ISTREAM_PIPE;

    if (!preprocargs)
        preprocargs = "";

    if (preprocessor) {
        cmd = xmalloc(strlen(preprocessor) + strlen(preprocargs) + strlen(filename) + strlen(fnquotes) * 2 + 10);
        sprintf(cmd, "%s %s %s%s%s", preprocessor, preprocargs, fnquotes, filename, fnquotes);
        cpp_pipe = open_input_stream(cmd);
    } else {
        cmd = xmalloc(strlen(program_name) +
                      strlen(DEFAULT_PREPROCESSOR_CMD) +
                      strlen(DEFAULT_PREPROCESSOR_ARGS) +
                      strlen(preprocargs) +
                      strlen(filename) +
                      strlen(fnquotes) * 2
#ifdef HAVE_EXECUTABLE_SUFFIX
                      + strlen(EXECUTABLE_SUFFIX)
#endif
                      + 10);

        dash = slash = NULL;
        for (cp = (char *)program_name; *cp; cp++) {
            if (*cp == '-')
                dash = cp;
#if defined (__DJGPP__) || defined (__CYGWIN__) || defined(_WIN32)
            if (*cp == ':' || *cp == '\\' || *cp == '/')
#else
            if (*cp == '/')
#endif
            {
                slash = cp;
                dash = NULL;
            }
        }
        cpp_pipe = NULL;
        if (dash)
            cpp_pipe = look_for_default(cmd, program_name, (int)(dash - program_name + 1), preprocargs, filename);
        if (slash && !cpp_pipe)
            cpp_pipe = look_for_default(cmd, program_name, (int)(slash - program_name + 1), preprocargs, filename);
        if (!cpp_pipe)
            cpp_pipe = look_for_default(cmd, "", 0, preprocargs, filename);
    }

    free(cmd);

    rc_filename = xstrdup(filename);
    rc_lineno = 1;

    if (language != -1)
        rcparse_set_language(language);

    yyparse();
    rcparse_discard_strings();

    close_input_stream();

    if (fontdirs)
        define_fontdirs();

    free(rc_filename);
    rc_filename = NULL;

    return resources;
}

/* Close the input stream if it is open.  */

static void close_input_stream(void)
{
    int errno_save;

    if (istream_type == ISTREAM_FILE) {
        if (cpp_pipe) {
            fclose(cpp_pipe);
            cpp_pipe = NULL;
        }
        if (cpp_temp_file) {
            errno_save = errno;
            unlink(cpp_temp_file);
            errno = errno_save;
            free(cpp_temp_file);
            cpp_temp_file = NULL;
        }
    } else {
        if (cpp_pipe) {
            int err = pclose(cpp_pipe);
            cpp_pipe = NULL;
            if (err != 0 || errno == ECHILD) {
                cpp_temp_file = NULL;
                fatal(_("preprocessing failed."));
            }
        }
    }
    cpp_pipe = NULL;
    cpp_temp_file = NULL;
}

/* Report an error while reading an rc file.  */

void yyerror(const char *msg) {
    if (msg == NULL) {
        msg = "Unknown error";
    }
    if (rc_filename == NULL) {
        rc_filename = "unknown";
    }
    fatal("%s:%d: %s", rc_filename, rc_lineno, msg);
}

/* Issue a warning while reading an rc file.  */

void rcparse_warning(const char *msg) {
    if (!msg || !rc_filename) {
        fputs("Unknown error location or message.\n", stderr);
        return;
    }
    fprintf(stderr, "%s:%d: %s\n", rc_filename, rc_lineno, msg);
}

/* Die if we get an unexpected end of file.  */

static void unexpected_eof(const char *msg)
{
    if (msg == NULL) {
        fatal(_("unexpected EOF: <null message>"));
        return;
    }
    fatal(_("%s: unexpected EOF"), msg);
}

/* Read a 16 bit word from a file.  The data is assumed to be little
   endian.  */

static int get_word(FILE *e, const char *msg)
{
    int b1 = getc(e);
    if (b1 == EOF) {
        unexpected_eof(msg);
    }
    int b2 = getc(e);
    if (b2 == EOF) {
        unexpected_eof(msg);
    }
    return ((b2 & 0xFF) << 8) | (b1 & 0xFF);
}

/* Read a 32 bit word from a file.  The data is assumed to be little
   endian.  */

static unsigned long get_long(FILE *e, const char *msg)
{
    unsigned char bytes[4];
    size_t read_count = fread(bytes, 1, 4, e);
    if (read_count != 4) {
        unexpected_eof(msg);
        return 0;
    }
    return ((unsigned long)bytes[3] << 24) |
           ((unsigned long)bytes[2] << 16) |
           ((unsigned long)bytes[1] << 8)  |
           (unsigned long)bytes[0];
}

/* Read data from a file.  This is a wrapper to do error checking.  */

static void get_data(FILE *e, bfd_byte *p, rc_uint_type c, const char *msg) {
    rc_uint_type got = (rc_uint_type)fread(p, 1, c, e);
    if (got != c) {
        fatal(_("%s: read of %lu returned %lu"), msg, (unsigned long)c, (unsigned long)got);
    }
}

static rc_uint_type target_get_16(const void *p, size_t len)
{
    if (p == NULL || len < 2) {
        fatal(_("not enough data"));
    }
    return windres_get_16(&wrtarget, p);
}

static rc_uint_type target_get_32(const void *p, size_t len) {
    if (!p || len < 4) {
        fatal(_("not enough data"));
    }
    return windres_get_32(&wrtarget, p);
}

/* Define an accelerator resource.  */

void define_accelerator(rc_res_id id, const rc_res_res_info *resinfo, rc_accelerator *data)
{
    rc_res_resource *r = define_standard_resource(&resources, RT_ACCELERATOR, id, resinfo->language, 0);
    if (r == NULL || resinfo == NULL || data == NULL) {
        return;
    }
    r->type = RES_TYPE_ACCELERATOR;
    r->u.acc = data;
    r->res_info = *resinfo;
}

/* Define a bitmap resource.  Bitmap data is stored in a file.  The
   first 14 bytes of the file are a standard header, which is not
   included in the resource data.  */

#define BITMAP_SKIP (14)

void define_bitmap(rc_res_id id, const rc_res_res_info *resinfo, const char *filename) {
    FILE *file = NULL;
    char *real_filename = NULL;
    struct stat file_stat;
    bfd_byte *data = NULL;
    rc_uint_type i;
    rc_res_resource *resource = NULL;
    size_t data_length;

    file = open_file_search(filename, FOPEN_RB, "bitmap file", &real_filename);
    if (!file || !real_filename)
        fatal(_("could not open bitmap file `%s'"), filename);

    if (stat(real_filename, &file_stat) < 0) {
        if (file)
            fclose(file);
        free(real_filename);
        fatal(_("stat failed on bitmap file `%s': %s"), real_filename, strerror(errno));
    }

    if ((size_t)file_stat.st_size < BITMAP_SKIP) {
        fclose(file);
        free(real_filename);
        fatal(_("bitmap file `%s' too small"), real_filename);
    }

    data_length = file_stat.st_size - BITMAP_SKIP;
    data = (bfd_byte *)res_alloc(data_length);

    for (i = 0; i < BITMAP_SKIP; i++) {
        if (getc(file) == EOF) {
            fclose(file);
            free(real_filename);
            fatal(_("unexpected EOF while skipping header in bitmap file `%s'"), real_filename);
        }
    }

    get_data(file, data, data_length, real_filename);

    fclose(file);
    free(real_filename);

    resource = define_standard_resource(&resources, RT_BITMAP, id, resinfo->language, 0);
    if (!resource)
        fatal(_("failed to define standard resource for bitmap file `%s'"), filename);

    resource->type = RES_TYPE_BITMAP;
    resource->u.data.length = data_length;
    resource->u.data.data = data;
    resource->res_info = *resinfo;
}

/* Define a cursor resource.  A cursor file may contain a set of
   bitmaps, each representing the same cursor at various different
   resolutions.  They each get written out with a different ID.  The
   real cursor resource is then a group resource which can be used to
   select one of the actual cursors.  */

void define_cursor(rc_res_id id, const rc_res_res_info *resinfo, const char *filename)
{
    FILE *e = NULL;
    char *real_filename = NULL;
    int type, count, i;
    struct icondir *icondirs = NULL;
    int first_cursor;
    rc_res_resource *r;
    rc_group_cursor *first = NULL, **pp = NULL;

    e = open_file_search(filename, FOPEN_RB, "cursor file", &real_filename);
    if (!e)
        fatal(_("could not open cursor file `%s'"), filename);

    get_word(e, real_filename);
    type = get_word(e, real_filename);
    count = get_word(e, real_filename);

    if (type != 2) {
        fclose(e);
        free(real_filename);
        fatal(_("cursor file `%s' does not contain cursor data"), real_filename);
    }

    if (count <= 0) {
        fclose(e);
        free(real_filename);
        fatal(_("cursor file `%s' contains no cursor entries"), real_filename);
    }

    icondirs = (struct icondir *)xmalloc(count * sizeof(*icondirs));
    if (!icondirs) {
        fclose(e);
        free(real_filename);
        fatal(_("out of memory allocating cursor directory"));
    }

    for (i = 0; i < count; i++) {
        icondirs[i].width = getc(e);
        icondirs[i].height = getc(e);
        icondirs[i].colorcount = getc(e);
        getc(e);
        icondirs[i].u.cursor.xhotspot = get_word(e, real_filename);
        icondirs[i].u.cursor.yhotspot = get_word(e, real_filename);
        icondirs[i].bytes = get_long(e, real_filename);
        icondirs[i].offset = get_long(e, real_filename);

        if (feof(e)) {
            free(icondirs);
            fclose(e);
            free(real_filename);
            unexpected_eof(real_filename);
        }
    }

    first_cursor = cursors;

    for (i = 0; i < count; i++) {
        bfd_byte *data = NULL;
        rc_res_id name;
        rc_cursor *c = NULL;

        if (fseek(e, icondirs[i].offset, SEEK_SET) != 0) {
            free(icondirs);
            fclose(e);
            free(real_filename);
            fatal(_("%s: fseek to %lu failed: %s"), real_filename, icondirs[i].offset, strerror(errno));
        }

        data = (bfd_byte *)res_alloc(icondirs[i].bytes);
        if (!data) {
            free(icondirs);
            fclose(e);
            free(real_filename);
            fatal(_("out of memory allocating cursor data"));
        }

        get_data(e, data, icondirs[i].bytes, real_filename);

        c = (rc_cursor *)res_alloc(sizeof(rc_cursor));
        if (!c) {
            free(icondirs);
            fclose(e);
            free(real_filename);
            fatal(_("out of memory allocating rc_cursor"));
        }
        c->xhotspot = icondirs[i].u.cursor.xhotspot;
        c->yhotspot = icondirs[i].u.cursor.yhotspot;
        c->length = icondirs[i].bytes;
        c->data = data;

        ++cursors;

        name.named = 0;
        name.u.id = cursors;

        r = define_standard_resource(&resources, RT_CURSOR, name, resinfo->language, 0);
        r->type = RES_TYPE_CURSOR;
        r->u.cursor = c;
        r->res_info = *resinfo;
    }

    fclose(e);
    free(real_filename);

    first = NULL;
    pp = &first;
    for (i = 0; i < count; i++) {
        rc_group_cursor *cg = (rc_group_cursor *)res_alloc(sizeof(rc_group_cursor));
        if (!cg) {
            free(icondirs);
            fatal(_("out of memory allocating rc_group_cursor"));
        }
        cg->next = NULL;
        cg->width = icondirs[i].width;
        cg->height = 2 * icondirs[i].height;
        cg->planes = 1;
        cg->bits = 1;
        cg->bytes = icondirs[i].bytes + 4;
        cg->index = first_cursor + i + 1;

        *pp = cg;
        pp = &cg->next;
    }

    free(icondirs);

    r = define_standard_resource(&resources, RT_GROUP_CURSOR, id, resinfo->language, 0);
    r->type = RES_TYPE_GROUP_CURSOR;
    r->u.group_cursor = first;
    r->res_info = *resinfo;
}

/* Define a dialog resource.  */

void define_dialog(rc_res_id id, const rc_res_res_info *resinfo, const rc_dialog *dialog) {
    if (!resinfo || !dialog) {
        return;
    }

    rc_dialog *copy = (rc_dialog *)res_alloc(sizeof(rc_dialog));
    if (!copy) {
        return;
    }
    *copy = *dialog;

    rc_res_resource *r = define_standard_resource(&resources, RT_DIALOG, id, resinfo->language, 0);
    if (!r) {
        // resources allocated to copy, free if applicable
        // free(copy); // Uncomment if res_alloc uses malloc/can be freed
        return;
    }
    r->type = RES_TYPE_DIALOG;
    r->u.dialog = copy;
    r->res_info = *resinfo;
}

/* Define a dialog control.  This does not define a resource, but
   merely allocates and fills in a structure.  */

rc_dialog_control *
define_control(const rc_res_id iid, rc_uint_type id, rc_uint_type x,
               rc_uint_type y, rc_uint_type width, rc_uint_type height,
               const rc_res_id class, rc_uint_type style,
               rc_uint_type exstyle)
{
    rc_dialog_control *n = res_alloc(sizeof(rc_dialog_control));
    if (!n)
        return NULL;

    n->next = NULL;
    n->id = id;
    n->style = style;
    n->exstyle = exstyle;
    n->x = x;
    n->y = y;
    n->width = width;
    n->height = height;
    n->class = class;
    n->text = iid;
    n->data = NULL;
    n->help = 0;

    return n;
}

rc_dialog_control *define_icon_control(rc_res_id iid, rc_uint_type id, rc_uint_type x,
                                      rc_uint_type y, rc_uint_type style,
                                      rc_uint_type exstyle, rc_uint_type help,
                                      rc_rcdata_item *data, rc_dialog_ex *ex) {
    rc_dialog_control *n;
    rc_res_id tid = {0};
    rc_res_id cid = {0};

    if (style == 0)
        style = SS_ICON | WS_CHILD | WS_VISIBLE;

    res_string_to_id(&tid, "");

    cid.named = 0;
    cid.u.id = CTL_STATIC;

    n = define_control(tid, id, x, y, 0, 0, cid, style, exstyle);
    if (!n)
        return NULL;

    n->text = iid;

    if (help && !ex)
        rcparse_warning(_("help ID requires DIALOGEX"));
    if (data && !ex)
        rcparse_warning(_("control data requires DIALOGEX"));

    n->help = help;
    n->data = data;

    return n;
}

/* Define a font resource.  */

void define_font(rc_res_id id, const rc_res_res_info *resinfo, const char *filename) {
    FILE *e = NULL;
    char *real_filename = NULL;
    struct stat s;
    bfd_byte *data = NULL;
    rc_res_resource *r = NULL;
    long offset_device, offset_face;
    long fontdatalength;
    bfd_byte *fontdata = NULL;
    rc_fontdir *fd = NULL;
    const char *device = "";
    const char *face = "";
    rc_fontdir **pp = NULL;

    e = open_file_search(filename, FOPEN_RB, "font file", &real_filename);
    if (!e || !real_filename)
        fatal(_("Failed to open font file `%s'"), filename);

    if (stat(real_filename, &s) < 0) {
        fclose(e);
        free(real_filename);
        fatal(_("stat failed on font file `%s': %s"), real_filename, strerror(errno));
    }

    if (s.st_size < 0) {
        fclose(e);
        free(real_filename);
        fatal(_("Font file `%s' has invalid size"), real_filename);
    }

    data = (bfd_byte *)res_alloc((size_t)s.st_size);
    if (!data) {
        fclose(e);
        free(real_filename);
        fatal(_("Memory allocation failure for font file `%s'"), real_filename);
    }

    get_data(e, data, s.st_size, real_filename);
    fclose(e);
    free(real_filename);

    r = define_standard_resource(&resources, RT_FONT, id, resinfo->language, 0);
    r->type = RES_TYPE_FONT;
    r->u.data.length = s.st_size;
    r->u.data.data = data;
    r->res_info = *resinfo;

    if (s.st_size > 51) {
        offset_device = ((((((long)data[47] << 8 | data[46]) << 8 | data[45]) << 8) | data[44]));
        if (offset_device > 0 && offset_device < s.st_size)
            device = (const char *)data + offset_device;
        else
            device = "";

        offset_face = ((((((long)data[51] << 8 | data[50]) << 8 | data[49]) << 8) | data[48]));
        if (offset_face > 0 && offset_face < s.st_size)
            face = (const char *)data + offset_face;
        else
            face = "";
    }

    ++fonts;

    fontdatalength = 58 + (long)strlen(device) + (long)strlen(face);
    fontdata = (bfd_byte *)res_alloc((size_t)fontdatalength);
    if (!fontdata)
        fatal(_("Memory allocation failure for fontdata"));

    if (s.st_size >= 56)
        memcpy(fontdata, data, 56);
    else
        memset(fontdata, 0, 56);

    strcpy((char *)fontdata + 56, device);
    strcpy((char *)fontdata + 57 + strlen(device), face);

    fd = (rc_fontdir *)res_alloc(sizeof(rc_fontdir));
    if (!fd)
        fatal(_("Memory allocation failure for fontdir"));

    fd->next = NULL;
    fd->index = fonts;
    fd->length = fontdatalength;
    fd->data = fontdata;

    for (pp = &fontdirs; *pp != NULL; pp = &(*pp)->next)
        ;
    *pp = fd;

    fontdirs_resinfo = *resinfo;
}

static void define_font_rcdata(rc_res_id id, const rc_res_res_info *resinfo, rc_rcdata_item *data) {
    rc_res_resource *res;
    rc_uint_type data_len;
    bfd_byte *data_buf;

    if (!resinfo || !data) {
        return;
    }

    res = define_standard_resource(&resources, RT_FONT, id, resinfo->language, 0);
    if (!res) {
        return;
    }

    data_buf = rcdata_render_as_buffer(data, &data_len);
    if (!data_buf) {
        return;
    }

    res->type = RES_TYPE_FONT;
    res->u.data.length = data_len;
    res->u.data.data = data_buf;
    res->res_info = *resinfo;
}

/* Define the fontdirs resource.  This is called after the entire rc
   file has been parsed, if any font resources were seen.  */

static void define_fontdirs(void)
{
    rc_res_id id = { .named = 0, .u.id = 1 };
    rc_res_resource *r = define_standard_resource(&resources, RT_FONTDIR, id, 0x409, 0);
    if (!r)
        return;
    r->type = RES_TYPE_FONTDIR;
    r->u.fontdir = fontdirs;
    r->res_info = fontdirs_resinfo;
}

static bfd_byte *
rcdata_render_as_buffer(const rc_rcdata_item *data, rc_uint_type *plen)
{
    if (!data) {
        if (plen) *plen = 0;
        return NULL;
    }

    rc_uint_type len = 0;
    const rc_rcdata_item *d = data;

    while (d) {
        len += rcdata_copy(d, NULL);
        d = d->next;
    }

    bfd_byte *ret = NULL;
    if (len > 0) {
        ret = (bfd_byte *)res_alloc(len);
        if (!ret) {
            if (plen) *plen = 0;
            return NULL;
        }
        bfd_byte *pret = ret;
        for (d = data; d != NULL; d = d->next)
            pret += rcdata_copy(d, pret);
    }

    if (plen)
        *plen = len;
    return ret;
}

static void define_fontdir_rcdata(rc_res_id id, const rc_res_res_info *resinfo, rc_rcdata_item *data)
{
    rc_res_resource *r;
    rc_fontdir *fd_first = NULL, *fd_cur = NULL, *fd = NULL;
    rc_uint_type len_data;
    bfd_byte *pb_data;

    r = define_standard_resource(&resources, RT_FONTDIR, id, 0x409, 0);
    pb_data = rcdata_render_as_buffer(data, &len_data);

    if (pb_data != NULL && len_data >= 2) {
        rc_uint_type off = 2;
        rc_uint_type count = target_get_16(pb_data, len_data);
        for (rc_uint_type i = 0; i < count; i++) {
            rc_uint_type safe_pos = off;
            const struct bin_fontdir_item *bfi;
            size_t name_len, device_name_len;

            if (off + sizeof(struct bin_fontdir_item) > len_data)
                break;

            bfi = (const struct bin_fontdir_item *)(pb_data + off);
            fd = (rc_fontdir *)res_alloc(sizeof(rc_fontdir));
            if (!fd)
                break;

            fd->index = target_get_16(bfi->index, len_data - off);
            fd->data = pb_data + off;
            off += 56;

            if (off >= len_data)
                break;

            device_name_len = strlen((char *)(pb_data + off)) + 1;
            off += (rc_uint_type)device_name_len;

            if (off >= len_data)
                break;

            name_len = strlen((char *)(pb_data + off)) + 1;
            off += (rc_uint_type)name_len;

            fd->length = (off > safe_pos) ? (off - safe_pos) : 0;
            fd->next = NULL;

            if (fd_first == NULL)
                fd_first = fd;
            else
                fd_cur->next = fd;
            fd_cur = fd;
        }
    }
    r->type = RES_TYPE_FONTDIR;
    r->u.fontdir = fd_first;
    if (resinfo)
        r->res_info = *resinfo;
}

static void define_messagetable_rcdata(rc_res_id id, const rc_res_res_info *resinfo, rc_rcdata_item *data)
{
    rc_res_resource *resource;
    rc_uint_type data_length = 0;
    bfd_byte *buffer_data = NULL;

    if (!resinfo || !data)
        return;

    resource = define_standard_resource(&resources, RT_MESSAGETABLE, id, resinfo->language, 0);
    if (!resource)
        return;

    buffer_data = rcdata_render_as_buffer(data, &data_length);
    if (!buffer_data)
        return;

    resource->type = RES_TYPE_MESSAGETABLE;
    resource->u.data.length = data_length;
    resource->u.data.data = buffer_data;
    resource->res_info = *resinfo;
}

/* Define an icon resource.  An icon file may contain a set of
   bitmaps, each representing the same icon at various different
   resolutions.  They each get written out with a different ID.  The
   real icon resource is then a group resource which can be used to
   select one of the actual icon bitmaps.  */

void define_icon(rc_res_id id, const rc_res_res_info *resinfo, const char *filename)
{
    FILE *e = NULL;
    char *real_filename = NULL;
    int type, count, i;
    struct icondir *icondirs = NULL;
    int first_icon;
    rc_res_resource *r;
    rc_group_icon *first = NULL, **pp = NULL;

    e = open_file_search(filename, FOPEN_RB, "icon file", &real_filename);
    if (!e) {
        fatal(_("Failed to open icon file `%s'"), filename);
        return;
    }

    (void)get_word(e, real_filename);
    type = get_word(e, real_filename);
    count = get_word(e, real_filename);

    if (type != 1) {
        fclose(e);
        free(real_filename);
        fatal(_("icon file `%s' does not contain icon data"), real_filename);
        return;
    }

    if (count <= 0 || count > 4096) {
        fclose(e);
        free(real_filename);
        fatal(_("icon file `%s' contains an invalid icon count (%d)"), real_filename, count);
        return;
    }

    icondirs = (struct icondir *)xmalloc(count * sizeof(*icondirs));
    if (!icondirs) {
        fclose(e);
        free(real_filename);
        fatal(_("memory allocation failed for %d icon directory entries"), count);
        return;
    }

    for (i = 0; i < count; i++) {
        icondirs[i].width = getc(e);
        icondirs[i].height = getc(e);
        icondirs[i].colorcount = getc(e);
        (void)getc(e);
        icondirs[i].u.icon.planes = get_word(e, real_filename);
        icondirs[i].u.icon.bits = get_word(e, real_filename);
        icondirs[i].bytes = get_long(e, real_filename);
        icondirs[i].offset = get_long(e, real_filename);

        if (feof(e)) {
            free(icondirs);
            fclose(e);
            free(real_filename);
            unexpected_eof(real_filename);
            return;
        }
    }

    first_icon = icons;

    for (i = 0; i < count; i++) {
        bfd_byte *data;
        rc_res_id name;
        if (fseek(e, icondirs[i].offset, SEEK_SET) != 0) {
            free(icondirs);
            fclose(e);
            free(real_filename);
            fatal(_("%s: fseek to %lu failed: %s"), real_filename,
                  icondirs[i].offset, strerror(errno));
            return;
        }

        data = (bfd_byte *)res_alloc(icondirs[i].bytes);
        if (!data) {
            free(icondirs);
            fclose(e);
            free(real_filename);
            fatal(_("memory allocation failed for icon data (%lu bytes)"), icondirs[i].bytes);
            return;
        }
        get_data(e, data, icondirs[i].bytes, real_filename);

        ++icons;
        name.named = 0;
        name.u.id = icons;

        r = define_standard_resource(&resources, RT_ICON, name,
                                    resinfo->language, 0);
        if (r) {
            r->type = RES_TYPE_ICON;
            r->u.data.length = icondirs[i].bytes;
            r->u.data.data = data;
            r->res_info = *resinfo;
        }
    }

    fclose(e);
    free(real_filename);

    first = NULL;
    pp = &first;
    for (i = 0; i < count; i++) {
        rc_group_icon *cg;

        cg = (rc_group_icon *)res_alloc(sizeof(rc_group_icon));
        if (!cg) {
            free(icondirs);
            // Memory leak of previously allocated group_icons handled by app exit
            fatal(_("memory allocation failed for group icon"));
            return;
        }
        cg->next = NULL;
        cg->width = icondirs[i].width;
        cg->height = icondirs[i].height;
        cg->colors = icondirs[i].colorcount;

        cg->planes = icondirs[i].u.icon.planes ? icondirs[i].u.icon.planes : 1;

        if (icondirs[i].u.icon.bits)
            cg->bits = icondirs[i].u.icon.bits;
        else {
            cg->bits = 0;
            while ((1L << cg->bits) < cg->colors) ++cg->bits;
        }
        cg->bytes = icondirs[i].bytes;
        cg->index = first_icon + i + 1;

        *pp = cg;
        pp = &cg->next;
    }

    free(icondirs);

    r = define_standard_resource(&resources, RT_GROUP_ICON, id,
                                resinfo->language, 0);
    if (r) {
        r->type = RES_TYPE_GROUP_ICON;
        r->u.group_icon = first;
        r->res_info = *resinfo;
    }
}

static void define_group_icon_rcdata(rc_res_id id, const rc_res_res_info *resinfo, rc_rcdata_item *data)
{
    rc_res_resource *r;
    rc_group_icon *first = NULL, *cur = NULL, *cg = NULL;
    rc_uint_type len_data;
    bfd_byte *pb_data = rcdata_render_as_buffer(data, &len_data);
    rc_uint_type offset = 0;

    if (!pb_data)
        fatal(_("failed to render rcdata"));

    while (len_data - offset >= 6) {
        if (len_data - offset < 6)
            fatal(_("insufficient group icon header size"));

        unsigned short type = target_get_16(pb_data + offset + 2, len_data - offset - 2);
        if (type != 1)
            fatal(_("unexpected group icon type %d"), type);

        int count = target_get_16(pb_data + offset + 4, len_data - offset - 4);
        offset += 6;

        for (int i = 0; i < count; i++) {
            if (len_data - offset < 14)
                fatal(_("too small group icon rcdata"));

            cg = (rc_group_icon *)res_alloc(sizeof(rc_group_icon));
            if (!cg)
                fatal(_("memory allocation failed for rc_group_icon"));
            cg->next = NULL;
            cg->width = pb_data[offset + 0];
            cg->height = pb_data[offset + 1];
            cg->colors = pb_data[offset + 2];
            cg->planes = target_get_16(pb_data + offset + 4, len_data - offset - 4);
            cg->bits = target_get_16(pb_data + offset + 6, len_data - offset - 6);
            cg->bytes = target_get_32(pb_data + offset + 8, len_data - offset - 8);
            cg->index = target_get_16(pb_data + offset + 12, len_data - offset - 12);

            if (!first)
                first = cg;
            else
                cur->next = cg;
            cur = cg;

            offset += 14;
        }
    }

    r = define_standard_resource(&resources, RT_GROUP_ICON, id, resinfo->language, 0);
    if (!r)
        fatal(_("failed to define standard resource"));
    r->type = RES_TYPE_GROUP_ICON;
    r->u.group_icon = first;
    r->res_info = *resinfo;
}

static void define_group_cursor_rcdata(rc_res_id id, const rc_res_res_info *resinfo, rc_rcdata_item *data) {
    rc_res_resource *r;
    rc_group_cursor *first = NULL, *cur = NULL, *cg = NULL;
    rc_uint_type len_data = 0;
    bfd_byte *pb_data = rcdata_render_as_buffer(data, &len_data);
    bfd_byte *data_end = pb_data + len_data;

    if (!pb_data)
        fatal(_("rcdata_render_as_buffer returned NULL"));

    while (pb_data + 6 <= data_end) {
        unsigned short type = target_get_16(pb_data + 2, (rc_uint_type)(data_end - (pb_data + 2)));
        if (type != 2)
            fatal(_("unexpected group cursor type %d"), type);
        int c = target_get_16(pb_data + 4, (rc_uint_type)(data_end - (pb_data + 4)));
        pb_data += 6;

        for (int i = 0; i < c; i++) {
            if (pb_data + 14 > data_end)
                fatal(_("too small group icon rcdata"));
            cg = (rc_group_cursor *)res_alloc(sizeof(rc_group_cursor));
            if (!cg)
                fatal(_("res_alloc failed for group cursor"));
            cg->next = NULL;
            cg->width  = target_get_16(pb_data, (rc_uint_type)(data_end - pb_data));
            cg->height = target_get_16(pb_data + 2, (rc_uint_type)(data_end - (pb_data + 2)));
            cg->planes = target_get_16(pb_data + 4, (rc_uint_type)(data_end - (pb_data + 4)));
            cg->bits   = target_get_16(pb_data + 6, (rc_uint_type)(data_end - (pb_data + 6)));
            cg->bytes  = target_get_32(pb_data + 8, (rc_uint_type)(data_end - (pb_data + 8)));
            cg->index  = target_get_16(pb_data + 12, (rc_uint_type)(data_end - (pb_data + 12)));
            if (!first)
                first = cg;
            else
                cur->next = cg;
            cur = cg;
            pb_data += 14;
        }
    }

    r = define_standard_resource(&resources, RT_GROUP_ICON, id, resinfo->language, 0);
    if (!r)
        fatal(_("define_standard_resource returned NULL"));
    r->type = RES_TYPE_GROUP_CURSOR;
    r->u.group_cursor = first;
    r->res_info = *resinfo;
}

static void define_cursor_rcdata(rc_res_id id, const rc_res_res_info *resinfo, rc_rcdata_item *data) {
    rc_cursor *c;
    rc_res_resource *r;
    rc_uint_type len_data;
    bfd_byte *pb_data;

    if (!resinfo || !data) {
        return;
    }

    pb_data = rcdata_render_as_buffer(data, &len_data);
    if (!pb_data || len_data < BIN_CURSOR_SIZE) {
        return;
    }

    c = (rc_cursor *)res_alloc(sizeof(rc_cursor));
    if (!c) {
        return;
    }

    c->xhotspot = target_get_16(pb_data, len_data);
    c->yhotspot = target_get_16(pb_data + 2, len_data - 2);
    c->length = len_data - BIN_CURSOR_SIZE;
    c->data = pb_data + BIN_CURSOR_SIZE;

    r = define_standard_resource(&resources, RT_CURSOR, id, resinfo->language, 0);
    if (!r) {
        free(c);
        return;
    }

    r->type = RES_TYPE_CURSOR;
    r->u.cursor = c;
    r->res_info = *resinfo;
}

static void define_bitmap_rcdata(rc_res_id id, const rc_res_res_info *resinfo, rc_rcdata_item *data) {
    rc_res_resource *r;
    rc_uint_type len_data = 0;
    bfd_byte *pb_data = rcdata_render_as_buffer(data, &len_data);

    if (!pb_data) {
        return;
    }

    r = define_standard_resource(&resources, RT_BITMAP, id, resinfo->language, 0);
    if (!r) {
        free(pb_data);
        return;
    }

    r->type = RES_TYPE_BITMAP;
    r->u.data.length = len_data;
    r->u.data.data = pb_data;
    r->res_info = *resinfo;
}

static void define_icon_rcdata(rc_res_id id, const rc_res_res_info *resinfo, rc_rcdata_item *data)
{
    rc_res_resource *r;
    rc_uint_type len_data = 0;
    bfd_byte *pb_data = rcdata_render_as_buffer(data, &len_data);

    if (!pb_data) {
        return;
    }

    r = define_standard_resource(&resources, RT_ICON, id, resinfo->language, 0);
    if (!r) {
        free(pb_data);
        return;
    }

    r->type = RES_TYPE_ICON;
    r->u.data.length = len_data;
    r->u.data.data = pb_data;
    r->res_info = *resinfo;
}

/* Define a menu resource.  */

void define_menu(rc_res_id id, const rc_res_res_info *resinfo, rc_menuitem *menuitems) {
    if (!resinfo || !menuitems)
        return;

    rc_menu *m = (rc_menu *)res_alloc(sizeof(rc_menu));
    if (!m)
        return;

    m->items = menuitems;
    m->help = NULL;

    rc_res_resource *r = define_standard_resource(&resources, RT_MENU, id, resinfo->language, 0);
    if (!r) {
        /* Free the allocated menu if resource creation fails */
        free(m);
        return;
    }
    r->type = RES_TYPE_MENU;
    r->u.menu = m;
    r->res_info = *resinfo;
}

/* Define a menu item.  This does not define a resource, but merely
   allocates and fills in a structure.  */

rc_menuitem *define_menuitem(const unichar *text, rc_uint_type menuid, rc_uint_type type,
                             rc_uint_type state, rc_uint_type help, rc_menuitem *menuitems)
{
    rc_menuitem *mi = res_alloc(sizeof(rc_menuitem));
    if (!mi)
        return NULL;

    mi->next = NULL;
    mi->type = type;
    mi->state = state;
    mi->id = menuid;
    mi->text = unichar_dup(text);
    if (text && !mi->text) {
        res_free(mi);
        return NULL;
    }
    mi->help = help;
    mi->popup = menuitems;
    return mi;
}


/* Define a messagetable resource.  */

void define_messagetable(rc_res_id id, const rc_res_res_info *resinfo, const char *filename) {
    FILE *e = NULL;
    char *real_filename = NULL;
    struct stat s;
    bfd_byte *data = NULL;
    rc_res_resource *r = NULL;

    e = open_file_search(filename, FOPEN_RB, "messagetable file", &real_filename);
    if (!e || !real_filename) {
        fatal(_("Failed to open messagetable file `%s'"), filename);
        return;
    }

    if (stat(real_filename, &s) != 0) {
        fclose(e);
        free(real_filename);
        fatal(_("stat failed on bitmap file `%s': %s"), real_filename, strerror(errno));
        return;
    }

    if (s.st_size <= 0) {
        fclose(e);
        free(real_filename);
        fatal(_("Invalid file size for messagetable file `%s'"), real_filename);
        return;
    }

    data = (bfd_byte *)res_alloc(s.st_size);
    if (!data) {
        fclose(e);
        free(real_filename);
        fatal(_("Memory allocation failed for messagetable file `%s'"), real_filename);
        return;
    }

    get_data(e, data, s.st_size, real_filename);

    fclose(e);
    free(real_filename);

    r = define_standard_resource(&resources, RT_MESSAGETABLE, id, resinfo->language, 0);
    if (!r) {
        free(data);
        fatal(_("Failed to define resource for messagetable file"));
        return;
    }

    r->type = RES_TYPE_MESSAGETABLE;
    r->u.data.length = s.st_size;
    r->u.data.data = data;
    r->res_info = *resinfo;
}

/* Define an rcdata resource.  */

void define_rcdata(rc_res_id id, const rc_res_res_info *resinfo, rc_rcdata_item *data) {
    if (!resinfo) {
        return;
    }

    rc_res_resource *r = define_standard_resource(&resources, RT_RCDATA, id, resinfo->language, 0);
    if (!r) {
        return;
    }

    r->type = RES_TYPE_RCDATA;
    r->u.rcdata = data;
    r->res_info = *resinfo;
}

/* Create an rcdata item holding a string.  */

rc_rcdata_item *
define_rcdata_string(const char *string, rc_uint_type len)
{
  if (!string || len == 0) {
    return NULL;
  }

  rc_rcdata_item *ri = (rc_rcdata_item *) res_alloc(sizeof(rc_rcdata_item));
  if (!ri) {
    return NULL;
  }

  ri->next = NULL;
  ri->type = RCDATA_STRING;
  ri->u.string.length = len;

  char *s = (char *) res_alloc(len);
  if (!s) {
    return NULL;
  }

  memcpy(s, string, len);
  ri->u.string.s = s;

  return ri;
}

/* Create an rcdata item holding a unicode string.  */

rc_rcdata_item *
define_rcdata_unistring(const unichar *string, rc_uint_type len)
{
  if (!string || len == 0)
    return NULL;

  rc_rcdata_item *ri = res_alloc(sizeof(rc_rcdata_item));
  if (!ri)
    return NULL;

  ri->next = NULL;
  ri->type = RCDATA_WSTRING;
  ri->u.wstring.length = len;

  unichar *s = res_alloc(len * sizeof(unichar));
  if (!s) {
    // If memory allocation fails, free previously allocated memory (if necessary)
    // but per supplied contract, just return NULL
    return NULL;
  }

  memcpy(s, string, len * sizeof(unichar));
  ri->u.wstring.w = s;

  return ri;
}

/* Create an rcdata item holding a number.  */

rc_rcdata_item *
define_rcdata_number(rc_uint_type val, int dword)
{
  rc_rcdata_item *ri = res_alloc(sizeof(rc_rcdata_item));
  if (!ri)
    return NULL;

  ri->next = NULL;
  ri->type = dword ? RCDATA_DWORD : RCDATA_WORD;
  ri->u.word = val;

  return ri;
}

/* Define a stringtable resource.  This is called for each string
   which appears in a STRINGTABLE statement.  */

void define_stringtable(const rc_res_res_info *resinfo,
                        rc_uint_type stringid, const unichar *string, int len)
{
    if (!resinfo || (!string && len > 0) || len < 0) {
        return;
    }

    rc_res_id id;
    id.named = 0;
    id.u.id = (stringid >> 4) + 1;

    rc_res_resource *r = define_standard_resource(&resources, RT_STRING, id, resinfo->language, 1);
    if (!r) {
        return;
    }

    if (r->type == RES_TYPE_UNINITIALIZED) {
        r->type = RES_TYPE_STRINGTABLE;
        rc_stringtable *stringtable = (rc_stringtable *)res_alloc(sizeof(rc_stringtable));
        if (!stringtable) {
            return;
        }
        for (int i = 0; i < 16; i++) {
            stringtable->strings[i].length = 0;
            stringtable->strings[i].string = NULL;
        }
        r->u.stringtable = stringtable;
        r->res_info = *resinfo;
    }

    unichar *h = (unichar *)res_alloc(((size_t)len + 1) * sizeof(unichar));
    if (!h) {
        return;
    }

    if (len > 0) {
        memcpy(h, string, (size_t)len * sizeof(unichar));
    }
    h[len] = 0;

    int idx = (int)(stringid & 0xf);
    r->u.stringtable->strings[idx].length = (rc_uint_type)len;
    r->u.stringtable->strings[idx].string = h;
}

void define_toolbar(rc_res_id id, rc_res_res_info *resinfo, rc_uint_type width, rc_uint_type height, rc_toolbar_item *items) {
    if (!resinfo) return;

    rc_toolbar *t = res_alloc(sizeof(rc_toolbar));
    if (!t) return;

    t->button_width = width;
    t->button_height = height;
    t->items = items;

    rc_uint_type count = 0;
    rc_toolbar_item *curr = items;
    while (curr) {
        ++count;
        curr = curr->next;
    }
    t->nitems = count;

    rc_res_resource *r = define_standard_resource(&resources, RT_TOOLBAR, id, resinfo->language, 0);
    if (!r) {
        /* Optional: free(t); */
        return;
    }
    r->type = RES_TYPE_TOOLBAR;
    r->u.toolbar = t;
    r->res_info = *resinfo;
}

/* Define a user data resource where the data is in the rc file.  */

void define_user_data(rc_res_id id, rc_res_id type, const rc_res_res_info *resinfo, rc_rcdata_item *data) {
    rc_res_id ids[3];
    rc_res_resource *r;
    bfd_byte *pb_data;
    rc_uint_type len_data;

    if (type.named == 0) {
        switch (type.u.id) {
            case RT_FONTDIR:
                define_fontdir_rcdata(id, resinfo, data);
                return;
            case RT_FONT:
                define_font_rcdata(id, resinfo, data);
                return;
            case RT_ICON:
                define_icon_rcdata(id, resinfo, data);
                return;
            case RT_BITMAP:
                define_bitmap_rcdata(id, resinfo, data);
                return;
            case RT_CURSOR:
                define_cursor_rcdata(id, resinfo, data);
                return;
            case RT_GROUP_ICON:
                define_group_icon_rcdata(id, resinfo, data);
                return;
            case RT_GROUP_CURSOR:
                define_group_cursor_rcdata(id, resinfo, data);
                return;
            case RT_MESSAGETABLE:
                define_messagetable_rcdata(id, resinfo, data);
                return;
            default:
                break;
        }
    }

    ids[0] = type;
    ids[1] = id;
    ids[2].named = 0;
    ids[2].u.id = resinfo->language;

    r = define_resource(&resources, 3, ids, 0);
    if (r == NULL)
        return;
    r->type = RES_TYPE_USERDATA;
    r->u.userdata = (rc_rcdata_item *)res_alloc(sizeof(rc_rcdata_item));
    if (r->u.userdata == NULL)
        return;
    r->u.userdata->next = NULL;
    r->u.userdata->type = RCDATA_BUFFER;
    pb_data = rcdata_render_as_buffer(data, &len_data);
    if (pb_data == NULL) {
        r->u.userdata->u.buffer.length = 0;
        r->u.userdata->u.buffer.data = NULL;
    } else {
        r->u.userdata->u.buffer.length = len_data;
        r->u.userdata->u.buffer.data = pb_data;
    }
    r->res_info = *resinfo;
}

void define_rcdata_file(rc_res_id id, const rc_res_res_info *resinfo, const char *filename)
{
    rc_rcdata_item *ri = NULL;
    FILE *e = NULL;
    char *real_filename = NULL;
    struct stat s;
    bfd_byte *data = NULL;

    e = open_file_search(filename, FOPEN_RB, "file", &real_filename);
    if (e == NULL || real_filename == NULL) {
        fatal(_("Could not open file `%s'"), filename ? filename : "(null)");
        return;
    }

    if (stat(real_filename, &s) < 0) {
        fatal(_("stat failed on file `%s': %s"), real_filename, strerror(errno));
        fclose(e);
        free(real_filename);
        return;
    }

    if (s.st_size <= 0) {
        fatal(_("File `%s' is empty or inaccessible"), real_filename);
        fclose(e);
        free(real_filename);
        return;
    }

    data = (bfd_byte *)res_alloc(s.st_size);
    if (data == NULL) {
        fatal(_("Memory allocation failed for rcdata buffer of file `%s'"), real_filename);
        fclose(e);
        free(real_filename);
        return;
    }

    get_data(e, data, s.st_size, real_filename);

    fclose(e);
    free(real_filename);

    ri = (rc_rcdata_item *)res_alloc(sizeof(rc_rcdata_item));
    if (ri == NULL) {
        fatal(_("Memory allocation failed for rc_rcdata_item"));
        free(data);
        return;
    }

    ri->next = NULL;
    ri->type = RCDATA_BUFFER;
    ri->u.buffer.length = s.st_size;
    ri->u.buffer.data = data;

    define_rcdata(id, resinfo, ri);
}

/* Define a user data resource where the data is in a file.  */

void define_user_file(rc_res_id id, rc_res_id type, const rc_res_res_info *resinfo, const char *filename) {
    FILE *file = NULL;
    char *real_filename = NULL;
    struct stat file_stat;
    bfd_byte *data = NULL;
    rc_res_id ids[3];
    rc_res_resource *resource = NULL;

    file = open_file_search(filename, FOPEN_RB, "file", &real_filename);
    if (!file || !real_filename) {
        fatal(_("Failed to open file: %s"), filename);
        return;
    }

    if (stat(real_filename, &file_stat) < 0) {
        fatal(_("stat failed on file `%s': %s"), real_filename, strerror(errno));
        fclose(file);
        free(real_filename);
        return;
    }

    if (file_stat.st_size <= 0) {
        fatal(_("Invalid file size for file `%s'"), real_filename);
        fclose(file);
        free(real_filename);
        return;
    }

    data = (bfd_byte *)res_alloc(file_stat.st_size);
    if (!data) {
        fatal(_("Memory allocation failed for file: %s"), real_filename);
        fclose(file);
        free(real_filename);
        return;
    }

    get_data(file, data, file_stat.st_size, real_filename);

    fclose(file);
    free(real_filename);

    ids[0] = type;
    ids[1] = id;
    ids[2].named = 0;
    ids[2].u.id = resinfo->language;

    resource = define_resource(&resources, 3, ids, 0);
    if (!resource) {
        fatal(_("Failed to define resource"));
        free(data);
        return;
    }
    resource->type = RES_TYPE_USERDATA;
    resource->u.userdata = (rc_rcdata_item *)res_alloc(sizeof(rc_rcdata_item));
    if (!resource->u.userdata) {
        fatal(_("Memory allocation failed for resource userdata"));
        free(data);
        return;
    }
    resource->u.userdata->next = NULL;
    resource->u.userdata->type = RCDATA_BUFFER;
    resource->u.userdata->u.buffer.length = file_stat.st_size;
    resource->u.userdata->u.buffer.data = data;
    resource->res_info = *resinfo;
}

/* Define a versioninfo resource.  */

void define_versioninfo(rc_res_id id, rc_uint_type language, rc_fixed_versioninfo *fixedverinfo, rc_ver_info *verinfo) {
    rc_res_resource *r = define_standard_resource(&resources, RT_VERSION, id, language, 0);
    if (!r) {
        return;
    }
    r->type = RES_TYPE_VERSIONINFO;
    r->u.versioninfo = (rc_versioninfo *)res_alloc(sizeof(rc_versioninfo));
    if (!r->u.versioninfo) {
        return;
    }
    r->u.versioninfo->fixed = fixedverinfo;
    r->u.versioninfo->var = verinfo;
    r->res_info.language = language;
}

/* Add string version info to a list of version information.  */

rc_ver_info *
append_ver_stringfileinfo(rc_ver_info *verinfo, rc_ver_stringtable *stringtables)
{
    rc_ver_info *vi = (rc_ver_info *)res_alloc(sizeof(rc_ver_info));
    if (!vi)
        return verinfo;
    vi->next = NULL;
    vi->type = VERINFO_STRING;
    vi->u.string.stringtables = stringtables;

    if (!verinfo) {
        return vi;
    }

    rc_ver_info *curr = verinfo;
    while (curr->next) {
        curr = curr->next;
    }
    curr->next = vi;

    return verinfo;
}

rc_ver_stringtable *
append_ver_stringtable(rc_ver_stringtable *stringtable,
                       const char *language,
                       rc_ver_stringinfo *strings)
{
    rc_ver_stringtable *vst;

    vst = (rc_ver_stringtable *)res_alloc(sizeof(rc_ver_stringtable));
    if (!vst)
        return stringtable;

    vst->next = NULL;

    if (unicode_from_ascii(NULL, &vst->language, language) != 0) {
        /* Handle conversion failure if possible */
        /* Optionally free vst, depending on application logic */
        return stringtable;
    }

    vst->strings = strings;

    if (!stringtable)
        return vst;

    rc_ver_stringtable *last = stringtable;
    while (last->next)
        last = last->next;
    last->next = vst;

    return stringtable;
}

/* Add variable version info to a list of version information.  */

rc_ver_info *
append_ver_varfileinfo(rc_ver_info *verinfo, const unichar *key, rc_ver_varinfo *var)
{
    if (!key || !var) {
        return verinfo;
    }

    rc_ver_info *vi = (rc_ver_info *)res_alloc(sizeof(*vi));
    if (!vi) {
        return verinfo;
    }

    vi->next = NULL;
    vi->type = VERINFO_VAR;
    vi->u.var.key = unichar_dup(key);
    vi->u.var.var = var;

    if (!vi->u.var.key) {
        /* handle allocation failure */
        /* Memory for vi is leaked to avoid double-free, since original code did not handle this */
        return verinfo;
    }

    rc_ver_info **pp = &verinfo;
    while (*pp) {
        pp = &(*pp)->next;
    }
    *pp = vi;

    return verinfo;
}

/* Append version string information to a list.  */

rc_ver_stringinfo *
append_verval(rc_ver_stringinfo *strings, const unichar *key, const unichar *value)
{
    rc_ver_stringinfo *vs;
    rc_ver_stringinfo **pp = &strings;

    if (!key || !value)
        return strings;

    vs = (rc_ver_stringinfo *)res_alloc(sizeof(rc_ver_stringinfo));
    if (!vs)
        return strings;

    vs->key = unichar_dup(key);
    vs->value = unichar_dup(value);
    if (!vs->key || !vs->value) {
        /* Cleanup if needed, assuming res_free exists */
        if (vs->key)
            res_free(vs->key);
        if (vs->value)
            res_free(vs->value);
        res_free(vs);
        return strings;
    }
    vs->next = NULL;

    while (*pp)
        pp = &(*pp)->next;
    *pp = vs;

    return strings;
}

/* Append version variable information to a list.  */

rc_ver_varinfo *
append_vertrans(rc_ver_varinfo *var, rc_uint_type language, rc_uint_type charset)
{
    rc_ver_varinfo *new_node;
    rc_ver_varinfo *current;

    new_node = (rc_ver_varinfo *)res_alloc(sizeof(rc_ver_varinfo));
    if (!new_node)
        return var;

    new_node->next = NULL;
    new_node->language = language;
    new_node->charset = charset;

    if (var == NULL) {
        return new_node;
    }

    current = var;
    while (current->next != NULL) {
        current = current->next;
    }
    current->next = new_node;

    return var;
}

/* Local functions used to write out an rc file.  */

static void indent (FILE *, int);
static void write_rc_directory (FILE *, const rc_res_directory *, const rc_res_id *,
				const rc_res_id *, rc_uint_type *, int);
static void write_rc_subdir (FILE *, const rc_res_entry *, const rc_res_id *,
			     const rc_res_id *, rc_uint_type *, int);
static void write_rc_resource (FILE *, const rc_res_id *, const rc_res_id *,
			       const rc_res_resource *, rc_uint_type *);
static void write_rc_accelerators (FILE *, const rc_accelerator *);
static void write_rc_cursor (FILE *, const rc_cursor *);
static void write_rc_group_cursor (FILE *, const rc_group_cursor *);
static void write_rc_dialog (FILE *, const rc_dialog *);
static void write_rc_dialog_control (FILE *, const rc_dialog_control *);
static void write_rc_fontdir (FILE *, const rc_fontdir *);
static void write_rc_group_icon (FILE *, const rc_group_icon *);
static void write_rc_menu (FILE *, const rc_menu *, int);
static void write_rc_toolbar (FILE *, const rc_toolbar *);
static void write_rc_menuitems (FILE *, const rc_menuitem *, int, int);
static void write_rc_messagetable (FILE *, rc_uint_type , const bfd_byte *);

static void write_rc_datablock (FILE *, rc_uint_type , const bfd_byte *, int, int, int);
static void write_rc_rcdata (FILE *, const rc_rcdata_item *, int);
static void write_rc_stringtable (FILE *, const rc_res_id *, const rc_stringtable *);
static void write_rc_versioninfo (FILE *, const rc_versioninfo *);

/* Indent a given number of spaces.  */

static void indent(FILE *e, int c) {
    if (e == NULL || c <= 0) {
        return;
    }
    for (int i = 0; i < c; i++) {
        if (fputc(' ', e) == EOF) {
            break;
        }
    }
}

/* Dump the resources we have read in the format of an rc file.

   Reasoned by the fact, that some resources need to be stored into file and
   refer to that file, we use the user-data model for that to express it binary
   without the need to store it somewhere externally.  */

bool write_rc_file(const char *filename, const rc_res_directory *res_dir) {
    FILE *file = NULL;
    rc_uint_type language = (rc_uint_type)((bfd_signed_vma)-1);

    if (!res_dir) {
        non_fatal(_("resource directory is NULL"));
        return false;
    }

    if (filename == NULL) {
        file = stdout;
    } else {
        file = fopen(filename, FOPEN_WT);
        if (!file) {
            non_fatal(_("can't open `%s' for output: %s"), filename, strerror(errno));
            return false;
        }
    }

    write_rc_directory(file, res_dir, NULL, NULL, &language, 1);

    if (file && file != stdout) {
        if (fclose(file) != 0) {
            non_fatal(_("error closing file `%s': %s"), filename, strerror(errno));
            return false;
        }
    }

    return true;
}

/* Write out a directory.  E is the file to write to.  RD is the
   directory.  TYPE is a pointer to the level 1 ID which serves as the
   resource type.  NAME is a pointer to the level 2 ID which serves as
   an individual resource name.  LANGUAGE is a pointer to the current
   language.  LEVEL is the level in the tree.  */

static void write_rc_directory(FILE *e, const rc_res_directory *rd, const rc_res_id *type, const rc_res_id *name, rc_uint_type *language, int level) {
    const rc_res_entry *re;

    if (rd->time != 0 || rd->characteristics != 0 || rd->major != 0 || rd->minor != 0) {
        wr_printcomment(e, "COFF information not part of RC");
        if (rd->time != 0)
            wr_printcomment(e, "Time stamp: %u", rd->time);
        if (rd->characteristics != 0)
            wr_printcomment(e, "Characteristics: %u", rd->characteristics);
        if (rd->major != 0 || rd->minor != 0)
            wr_printcomment(e, "Version major:%d minor:%d", rd->major, rd->minor);
    }

    re = rd->entries;
    if (re == NULL) {
        wr_print_flush(e);
        return;
    }

    for (; re != NULL; re = re->next) {
        const rc_res_id *cur_type = type;
        const rc_res_id *cur_name = name;
        rc_uint_type *cur_language = language;

        switch (level) {
            case 1:
                cur_type = &re->id;
                break;
            case 2:
                cur_name = &re->id;
                break;
            case 3:
                if (!re->id.named &&
                    re->id.u.id != (unsigned long)(unsigned int)*language &&
                    (re->id.u.id & 0xffff) == re->id.u.id) {
                    wr_print(e, "LANGUAGE %u, %u\n",
                             re->id.u.id & ((1 << SUBLANG_SHIFT) - 1),
                             (re->id.u.id >> SUBLANG_SHIFT) & 0xff);
                    *language = re->id.u.id;
                }
                break;
            default:
                break;
        }

        if (re->subdir) {
            write_rc_subdir(e, re, cur_type, cur_name, cur_language, level);
        } else {
            if (level == 3) {
                write_rc_resource(e, cur_type, cur_name, re->u.res, cur_language);
            } else {
                wr_printcomment(e, "Resource at unexpected level %d", level);
                write_rc_resource(e, cur_type, NULL, re->u.res, cur_language);
            }
        }
    }
}


/* Write out a subdirectory entry.  E is the file to write to.  RE is
   the subdirectory entry.  TYPE and NAME are pointers to higher level
   IDs, or NULL.  LANGUAGE is a pointer to the current language.
   LEVEL is the level in the tree.  */

static void write_rc_subdir(FILE *e, const rc_res_entry *re,
                            const rc_res_id *type, const rc_res_id *name,
                            rc_uint_type *language, int level) {
    fprintf(e, "\n");
    switch (level) {
        case 1: {
            wr_printcomment(e, "Type: ");
            if (re->id.named) {
                res_id_print(e, re->id, 1);
            } else {
                static const struct {
                    int id;
                    const char *name;
                } type_names[] = {
                    {RT_CURSOR, "cursor"},
                    {RT_BITMAP, "bitmap"},
                    {RT_ICON, "icon"},
                    {RT_MENU, "menu"},
                    {RT_DIALOG, "dialog"},
                    {RT_STRING, "stringtable"},
                    {RT_FONTDIR, "fontdir"},
                    {RT_FONT, "font"},
                    {RT_ACCELERATOR, "accelerators"},
                    {RT_RCDATA, "rcdata"},
                    {RT_MESSAGETABLE, "messagetable"},
                    {RT_GROUP_CURSOR, "group cursor"},
                    {RT_GROUP_ICON, "group icon"},
                    {RT_VERSION, "version"},
                    {RT_DLGINCLUDE, "dlginclude"},
                    {RT_PLUGPLAY, "plugplay"},
                    {RT_VXD, "vxd"},
                    {RT_ANICURSOR, "anicursor"},
                    {RT_ANIICON, "aniicon"},
                    {RT_TOOLBAR, "toolbar"},
                    {RT_HTML, "html"}
                };
                const char *s = NULL;
                for (size_t i = 0; i < sizeof(type_names)/sizeof(type_names[0]); ++i) {
                    if (type_names[i].id == re->id.u.id) {
                        s = type_names[i].name;
                        break;
                    }
                }
                if (s) {
                    fprintf(e, "%s", s);
                } else {
                    res_id_print(e, re->id, 1);
                }
            }
            break;
        }
        case 2:
            wr_printcomment(e, "Name: ");
            res_id_print(e, re->id, 1);
            break;
        case 3:
            wr_printcomment(e, "Language: ");
            res_id_print(e, re->id, 1);
            break;
        default:
            wr_printcomment(e, "Level %d: ", level);
            res_id_print(e, re->id, 1);
            break;
    }
    if (re && re->u.dir) {
        write_rc_directory(e, re->u.dir, type, name, language, level + 1);
    }
}

/* Write out a single resource.  E is the file to write to.  TYPE is a
   pointer to the type of the resource.  NAME is a pointer to the name
   of the resource; it will be NULL if there is a level mismatch.  RES
   is the resource data.  LANGUAGE is a pointer to the current
   language.  */

static void write_rc_resource(FILE *e, const rc_res_id *type,
                             const rc_res_id *name, const rc_res_resource *res,
                             rc_uint_type *language)
{
    const char *s = NULL;
    int rt = 0;
    int menuex = 0;

    if (!e || !res || !language) {
        abort();
    }

    switch (res->type) {
        case RES_TYPE_ACCELERATOR:
            s = "ACCELERATORS";
            rt = RT_ACCELERATOR;
            break;
        case RES_TYPE_BITMAP:
            s = "2 /* RT_BITMAP */";
            rt = RT_BITMAP;
            break;
        case RES_TYPE_CURSOR:
            s = "1 /* RT_CURSOR */";
            rt = RT_CURSOR;
            break;
        case RES_TYPE_GROUP_CURSOR:
            s = "12 /* RT_GROUP_CURSOR */";
            rt = RT_GROUP_CURSOR;
            break;
        case RES_TYPE_DIALOG:
            s = extended_dialog(res->u.dialog) ? "DIALOGEX" : "DIALOG";
            rt = RT_DIALOG;
            break;
        case RES_TYPE_FONT:
            s = "8 /* RT_FONT */";
            rt = RT_FONT;
            break;
        case RES_TYPE_FONTDIR:
            s = "7 /* RT_FONTDIR */";
            rt = RT_FONTDIR;
            break;
        case RES_TYPE_ICON:
            s = "3 /* RT_ICON */";
            rt = RT_ICON;
            break;
        case RES_TYPE_GROUP_ICON:
            s = "14 /* RT_GROUP_ICON */";
            rt = RT_GROUP_ICON;
            break;
        case RES_TYPE_MENU:
            if (extended_menu(res->u.menu)) {
                s = "MENUEX";
                menuex = 1;
            } else {
                s = "MENU";
                menuex = 0;
            }
            rt = RT_MENU;
            break;
        case RES_TYPE_MESSAGETABLE:
            s = "11 /* RT_MESSAGETABLE */";
            rt = RT_MESSAGETABLE;
            break;
        case RES_TYPE_RCDATA:
            s = "RCDATA";
            rt = RT_RCDATA;
            break;
        case RES_TYPE_STRINGTABLE:
            s = "STRINGTABLE";
            rt = RT_STRING;
            break;
        case RES_TYPE_USERDATA:
            s = NULL;
            rt = 0;
            break;
        case RES_TYPE_VERSIONINFO:
            s = "VERSIONINFO";
            rt = RT_VERSION;
            break;
        case RES_TYPE_TOOLBAR:
            s = "TOOLBAR";
            rt = RT_TOOLBAR;
            break;
        default:
            abort();
    }

    if (rt != 0 && type && (type->named || type->u.id != (unsigned long)rt)) {
        wr_printcomment(e, "Unexpected resource type mismatch: ");
        res_id_print(e, *type, 1);
        fprintf(e, " != %d", rt);
    }

    if (res->coff_info.codepage)
        wr_printcomment(e, "Code page: %u", res->coff_info.codepage);

    if (res->coff_info.reserved)
        wr_printcomment(e, "COFF reserved value: %u", res->coff_info.reserved);

    wr_print(e, "\n");

    if (rt != RT_STRING) {
        if (name)
            res_id_print(e, *name, 1);
        else
            fprintf(e, "??Unknown-Name??");
        fprintf(e, " ");
    }

    if (s) {
        fprintf(e, "%s", s);
    } else if (type) {
        if (!type->named) {
            switch (type->u.id) {
                #define PRINT_RT_NAME(NAME) case NAME: \
                    fprintf(e, "%u /* %s */", (unsigned int)NAME, #NAME); break
                PRINT_RT_NAME(RT_MANIFEST);
                PRINT_RT_NAME(RT_ANICURSOR);
                PRINT_RT_NAME(RT_ANIICON);
                PRINT_RT_NAME(RT_RCDATA);
                PRINT_RT_NAME(RT_ICON);
                PRINT_RT_NAME(RT_CURSOR);
                PRINT_RT_NAME(RT_BITMAP);
                PRINT_RT_NAME(RT_PLUGPLAY);
                PRINT_RT_NAME(RT_VXD);
                PRINT_RT_NAME(RT_FONT);
                PRINT_RT_NAME(RT_FONTDIR);
                PRINT_RT_NAME(RT_HTML);
                PRINT_RT_NAME(RT_MESSAGETABLE);
                PRINT_RT_NAME(RT_DLGINCLUDE);
                PRINT_RT_NAME(RT_DLGINIT);
                default:
                    res_id_print(e, *type, 0);
                    break;
                #undef PRINT_RT_NAME
            }
        } else {
            res_id_print(e, *type, 1);
        }
    } else {
        fprintf(e, "??Unknown-Type??");
    }

    if (res->res_info.memflags) {
        if ((res->res_info.memflags & MEMFLAG_MOVEABLE))
            fprintf(e, " MOVEABLE");
        if ((res->res_info.memflags & MEMFLAG_PURE))
            fprintf(e, " PURE");
        if ((res->res_info.memflags & MEMFLAG_PRELOAD))
            fprintf(e, " PRELOAD");
        if ((res->res_info.memflags & MEMFLAG_DISCARDABLE))
            fprintf(e, " DISCARDABLE");
    }

    if (res->type == RES_TYPE_DIALOG) {
        fprintf(e, " %d, %d, %d, %d",
                (int)res->u.dialog->x, (int)res->u.dialog->y,
                (int)res->u.dialog->width, (int)res->u.dialog->height);
        if (res->u.dialog->ex && res->u.dialog->ex->help != 0)
            fprintf(e, ", %u", (unsigned int)res->u.dialog->ex->help);
    } else if (res->type == RES_TYPE_TOOLBAR) {
        fprintf(e, " %d, %d", (int)res->u.toolbar->button_width,
                (int)res->u.toolbar->button_height);
    }

    fprintf(e, "\n");

    if ((res->res_info.language && res->res_info.language != *language) ||
        res->res_info.characteristics ||
        res->res_info.version) {
        int modifiers = 0;
        switch (res->type) {
            case RES_TYPE_ACCELERATOR:
            case RES_TYPE_DIALOG:
            case RES_TYPE_MENU:
            case RES_TYPE_RCDATA:
            case RES_TYPE_STRINGTABLE:
                modifiers = 1;
                break;
            default:
                modifiers = 0;
                break;
        }

        if (res->res_info.language && res->res_info.language != *language)
            fprintf(e, "%sLANGUAGE %d, %d\n",
                modifiers ? "// " : "",
                (int)res->res_info.language & ((1 << SUBLANG_SHIFT) - 1),
                (int)(res->res_info.language >> SUBLANG_SHIFT) & 0xff);
        if (res->res_info.characteristics)
            fprintf(e, "%sCHARACTERISTICS %u\n",
                modifiers ? "// " : "",
                (unsigned int)res->res_info.characteristics);
        if (res->res_info.version)
            fprintf(e, "%sVERSION %u\n",
                modifiers ? "// " : "",
                (unsigned int)res->res_info.version);
    }

    switch (res->type) {
        case RES_TYPE_ACCELERATOR:
            write_rc_accelerators(e, res->u.acc);
            break;
        case RES_TYPE_CURSOR:
            write_rc_cursor(e, res->u.cursor);
            break;
        case RES_TYPE_GROUP_CURSOR:
            write_rc_group_cursor(e, res->u.group_cursor);
            break;
        case RES_TYPE_DIALOG:
            write_rc_dialog(e, res->u.dialog);
            break;
        case RES_TYPE_FONTDIR:
            write_rc_fontdir(e, res->u.fontdir);
            break;
        case RES_TYPE_GROUP_ICON:
            write_rc_group_icon(e, res->u.group_icon);
            break;
        case RES_TYPE_MENU:
            write_rc_menu(e, res->u.menu, menuex);
            break;
        case RES_TYPE_RCDATA:
            write_rc_rcdata(e, res->u.rcdata, 0);
            break;
        case RES_TYPE_STRINGTABLE:
            write_rc_stringtable(e, name, res->u.stringtable);
            break;
        case RES_TYPE_USERDATA:
            write_rc_rcdata(e, res->u.userdata, 0);
            break;
        case RES_TYPE_TOOLBAR:
            write_rc_toolbar(e, res->u.toolbar);
            break;
        case RES_TYPE_VERSIONINFO:
            write_rc_versioninfo(e, res->u.versioninfo);
            break;
        case RES_TYPE_BITMAP:
        case RES_TYPE_FONT:
        case RES_TYPE_ICON:
            write_rc_datablock(e, res->u.data.length, res->u.data.data, 0, 1, 0);
            break;
        case RES_TYPE_MESSAGETABLE:
            write_rc_messagetable(e, res->u.data.length, res->u.data.data);
            break;
        default:
            abort();
    }
}

/* Write out accelerator information.  */

static void write_rc_accelerators(FILE *e, const rc_accelerator *accelerators) {
    const rc_accelerator *acc = accelerators;

    if (e == NULL || acc == NULL)
        return;

    if (fprintf(e, "BEGIN\n") < 0)
        return;

    while (acc) {
        int printable = 0;
        int is_virtkey = (acc->flags & ACC_VIRTKEY) != 0;

        if (fprintf(e, "  ") < 0)
            return;

        if ((acc->key & 0x7f) == acc->key && ISPRINT(acc->key) && !is_virtkey) {
            if (fprintf(e, "\"%c\"", (char)acc->key) < 0)
                return;
            printable = 1;
        } else {
            if (fprintf(e, "%d", (int)acc->key) < 0)
                return;
        }

        if (fprintf(e, ", %d", (int)acc->id) < 0)
            return;

        if (!printable) {
            if (is_virtkey) {
                if (fprintf(e, ", VIRTKEY") < 0)
                    return;
            } else {
                if (fprintf(e, ", ASCII") < 0)
                    return;
            }
        }

        if ((acc->flags & ACC_SHIFT) && fprintf(e, ", SHIFT") < 0)
            return;
        if ((acc->flags & ACC_CONTROL) && fprintf(e, ", CONTROL") < 0)
            return;
        if ((acc->flags & ACC_ALT) && fprintf(e, ", ALT") < 0)
            return;

        if (fprintf(e, "\n") < 0)
            return;

        acc = acc->next;
    }

    fprintf(e, "END\n");
}

/* Write out cursor information.  This would normally be in a separate
   file, which the rc file would include.  */

static void write_rc_cursor(FILE *e, const rc_cursor *cursor)
{
    if (e == NULL || cursor == NULL) {
        return;
    }

    fprintf(e, "BEGIN\n");
    indent(e, 2);

    fprintf(
        e,
        " 0x%x, 0x%x,\t/* Hotspot x: %d, y: %d.  */\n",
        (unsigned int)cursor->xhotspot,
        (unsigned int)cursor->yhotspot,
        (int)cursor->xhotspot,
        (int)cursor->yhotspot
    );

    write_rc_datablock(
        e,
        (rc_uint_type)cursor->length,
        (const bfd_byte *)cursor->data,
        0, 0, 0
    );

    fprintf(e, "END\n");
}

/* Write out group cursor data.  This would normally be built from the
   cursor data.  */

static void write_rc_group_cursor(FILE *e, const rc_group_cursor *group_cursor)
{
    const rc_group_cursor *gc = group_cursor;
    int count = 0;
    if (e == NULL || group_cursor == NULL)
        return;

    while (gc) {
        ++count;
        gc = gc->next;
    }

    fprintf(e, "BEGIN\n");
    indent(e, 2);
    fprintf(e, "0, 2, %d%s\t /* Having %d items.  */\n", count, (count ? "," : ""), count);
    indent(e, 4);
    fprintf(e, "/* width, height, planes, bits, bytes, index.  */\n");

    gc = group_cursor;
    for (int i = 1; gc != NULL; gc = gc->next, ++i) {
        indent(e, 4);
        fprintf(e, "%d, %d, %d, %d, 0x%xL, %d%s /* Element %d. */\n",
            (int)gc->width, (int)gc->height, (int)gc->planes, (int)gc->bits,
            (unsigned int)gc->bytes, (int)gc->index, (gc->next ? "," : ""), i);
        fprintf(e, "/* width: %d; height %d; planes %d; bits %d.  */\n",
            (int)gc->width, (int)gc->height, (int)gc->planes, (int)gc->bits);
    }
    fprintf(e, "END\n");
}

/* Write dialog data.  */

static void write_rc_dialog(FILE *e, const rc_dialog *dialog)
{
    const rc_dialog_control *control;

    if (e == NULL || dialog == NULL) {
        return;
    }

    fprintf(e, "STYLE 0x%x\n", dialog->style);

    if (dialog->exstyle != 0) {
        fprintf(e, "EXSTYLE 0x%x\n", (unsigned int)dialog->exstyle);
    }

    if ((dialog->class.named && dialog->class.u.n.length > 0) || dialog->class.u.id != 0) {
        fprintf(e, "CLASS ");
        res_id_print(e, dialog->class, 1);
        fprintf(e, "\n");
    }

    if (dialog->caption) {
        fprintf(e, "CAPTION ");
        unicode_print_quoted(e, dialog->caption, -1);
        fprintf(e, "\n");
    }

    if ((dialog->menu.named && dialog->menu.u.n.length > 0) || dialog->menu.u.id != 0) {
        fprintf(e, "MENU ");
        res_id_print(e, dialog->menu, 0);
        fprintf(e, "\n");
    }

    if (dialog->font) {
        fprintf(e, "FONT %d, ", (int)dialog->pointsize);
        unicode_print_quoted(e, dialog->font, -1);

        if (dialog->ex &&
            (dialog->ex->weight != 0 ||
             dialog->ex->italic != 0 ||
             dialog->ex->charset != 1))
        {
            fprintf(e, ", %d, %d, %d",
                (int)dialog->ex->weight,
                (int)dialog->ex->italic,
                (int)dialog->ex->charset);
        }
        fprintf(e, "\n");
    }

    fprintf(e, "BEGIN\n");

    control = dialog->controls;
    while (control) {
        write_rc_dialog_control(e, control);
        control = control->next;
    }

    fprintf(e, "END\n");
}

/* For each predefined control keyword, this table provides the class
   and the style.  */

struct control_info
{
  const char *name;
  unsigned short class;
  unsigned long style;
};

static const struct control_info control_info[] =
{
  { "AUTO3STATE", CTL_BUTTON, BS_AUTO3STATE },
  { "AUTOCHECKBOX", CTL_BUTTON, BS_AUTOCHECKBOX },
  { "AUTORADIOBUTTON", CTL_BUTTON, BS_AUTORADIOBUTTON },
  { "CHECKBOX", CTL_BUTTON, BS_CHECKBOX },
  { "COMBOBOX", CTL_COMBOBOX, (unsigned long) -1 },
  { "CTEXT", CTL_STATIC, SS_CENTER },
  { "DEFPUSHBUTTON", CTL_BUTTON, BS_DEFPUSHBUTTON },
  { "EDITTEXT", CTL_EDIT, (unsigned long) -1 },
  { "GROUPBOX", CTL_BUTTON, BS_GROUPBOX },
  { "ICON", CTL_STATIC, SS_ICON },
  { "LISTBOX", CTL_LISTBOX, (unsigned long) -1 },
  { "LTEXT", CTL_STATIC, SS_LEFT },
  { "PUSHBOX", CTL_BUTTON, BS_PUSHBOX },
  { "PUSHBUTTON", CTL_BUTTON, BS_PUSHBUTTON },
  { "RADIOBUTTON", CTL_BUTTON, BS_RADIOBUTTON },
  { "RTEXT", CTL_STATIC, SS_RIGHT },
  { "SCROLLBAR", CTL_SCROLLBAR, (unsigned long) -1 },
  { "STATE3", CTL_BUTTON, BS_3STATE },
  /* It's important that USERBUTTON come after all the other button
     types, so that it won't be matched too early.  */
  { "USERBUTTON", CTL_BUTTON, (unsigned long) -1 },
  { NULL, 0, 0 }
};

/* Write a dialog control.  */

static void write_rc_dialog_control(FILE *e, const rc_dialog_control *control) {
    const struct control_info *ci = NULL;
    int print_text = 0;
    int should_print_dimensions = 0;

    fprintf(e, "  ");

    if (!control->class.named) {
        for (ci = control_info; ci->name != NULL; ++ci) {
            if (ci->class == control->class.u.id &&
                (ci->style == (unsigned long)-1 ||
                 ci->style == (control->style & 0xff)))
                break;
        }
        if (ci->name == NULL)
            ci = NULL;
    }

    if (ci == NULL || ci->name == NULL) {
        fprintf(e, "CONTROL");
        ci = NULL;
    } else {
        fprintf(e, "%s", ci->name);
    }

    if ((control->text.named || control->text.u.id != 0) &&
        (!ci ||
         (ci->class != CTL_EDIT &&
          ci->class != CTL_COMBOBOX &&
          ci->class != CTL_LISTBOX &&
          ci->class != CTL_SCROLLBAR))) {
        print_text = 1;
    }

    if (print_text) {
        fprintf(e, " ");
        res_id_print(e, control->text, 1);
        fprintf(e, ",");
    }

    fprintf(e, " %d, ", (int)control->id);

    if (ci == NULL) {
        if (control->class.named)
            fprintf(e, "\"");
        res_id_print(e, control->class, 0);
        if (control->class.named)
            fprintf(e, "\"");
        fprintf(e, ", 0x%x, ", (unsigned int)control->style);
    }

    fprintf(e, "%d, %d", (int)control->x, (int)control->y);

    should_print_dimensions =
        (control->style != SS_ICON || control->exstyle != 0 ||
         control->width != 0 || control->height != 0 || control->help != 0);

    if (should_print_dimensions) {
        fprintf(e, ", %d, %d", (int)control->width, (int)control->height);

        if (ci != NULL)
            fprintf(e, ", 0x%x", (unsigned int)control->style);

        if (control->exstyle != 0 || control->help != 0)
            fprintf(e, ", 0x%x, %u", (unsigned int)control->exstyle,
                    (unsigned int)control->help);
    }

    fprintf(e, "\n");

    if (control->data != NULL)
        write_rc_rcdata(e, control->data, 2);
}

/* Write out font directory data.  This would normally be built from
   the font data.  */

static void write_rc_fontdir(FILE *e, const rc_fontdir *fontdir)
{
    const rc_fontdir *fc = fontdir;
    int count = 0;

    while (fc != NULL) {
        count++;
        fc = fc->next;
    }

    if (fprintf(e, "BEGIN\n") < 0) {
        return;
    }
    indent(e, 2);
    if (fprintf(e, "%d%s\t /* Has %d elements.  */\n", count, (count != 0 ? "," : ""), count) < 0) {
        return;
    }

    int c = 1;
    for (fc = fontdir; fc != NULL; fc = fc->next, c++) {
        indent(e, 4);
        if (fprintf(e, "%d,\t/* Font no %d with index %d.  */\n",
                    (int)fc->index, c, (int)fc->index) < 0) {
            return;
        }
        write_rc_datablock(
            e,
            (rc_uint_type)(fc->length > 2 ? fc->length - 2 : 0),
            (const bfd_byte *)((const bfd_byte *)fc->data + 4),
            fc->next != NULL,
            0,
            0
        );
    }
    fprintf(e, "END\n");
}

/* Write out group icon data.  This would normally be built from the
   icon data.  */

static void write_rc_group_icon(FILE *e, const rc_group_icon *group_icon)
{
    if (e == NULL || group_icon == NULL)
        return;

    int count = 0;
    const rc_group_icon *gi = group_icon;

    while (gi) {
        count++;
        gi = gi->next;
    }

    if (fprintf(e, "BEGIN\n") < 0) return;
    indent(e, 2);
    if (fprintf(e, " 0, 1, %d%s\t /* Has %d elements.  */\n", count, (count ? "," : ""), count) < 0) return;

    indent(e, 4);
    if (fprintf(e, "/* \"width height colors pad\", planes, bits, bytes, index.  */\n") < 0) return;

    gi = group_icon;
    int element_no = 1;
    while (gi) {
        indent(e, 4);
        if (fprintf(e, "\"\\%03o\\%03o\\%03o\\%03o\", %d, %d, 0x%xL, %d%s\t/* Element no %d.  */\n",
                    gi->width, gi->height, gi->colors, 0, (int)gi->planes, (int)gi->bits,
                    (unsigned int)gi->bytes, (int)gi->index, (gi->next ? "," : ""), element_no) < 0)
            return;
        gi = gi->next;
        element_no++;
    }
    fprintf(e, "END\n");
}


/* Write out a menu resource.  */

static void write_rc_menu(FILE *e, const rc_menu *menu, int menuex) {
    if (!e || !menu) {
        return;
    }
    if (menu->help) {
        if (fprintf(e, "// Help ID: %u\n", (unsigned int)menu->help) < 0) {
            return;
        }
    }
    write_rc_menuitems(e, menu->items, menuex, 0);
}

static void write_rc_toolbar(FILE *e, const rc_toolbar *tb)
{
    if (!e || !tb)
        return;

    indent(e, 0);
    fprintf(e, "BEGIN\n");

    for (rc_toolbar_item *it = tb->items; it; it = it->next) {
        indent(e, 2);
        if (it->id.u.id == 0)
            fprintf(e, "SEPARATOR\n");
        else
            fprintf(e, "BUTTON %d\n", (int)it->id.u.id);
    }

    indent(e, 0);
    fprintf(e, "END\n");
}

/* Write out menuitems.  */

static void write_rc_menuitems(FILE *e, const rc_menuitem *menuitems, int menuex, int ind) {
    const rc_menuitem *mi;

    if (!e || !menuitems) return;

    indent(e, ind);
    fprintf(e, "BEGIN\n");

    for (mi = menuitems; mi != NULL; mi = mi->next) {
        indent(e, ind + 2);

        if (mi->popup == NULL)
            fprintf(e, "MENUITEM");
        else
            fprintf(e, "POPUP");

        if (!menuex && mi->popup == NULL && mi->text == NULL && mi->type == 0 && mi->id == 0) {
            fprintf(e, " SEPARATOR\n");
            continue;
        }

        fprintf(e, " ");
        if (mi->text == NULL)
            fprintf(e, "\"\"");
        else
            unicode_print_quoted(e, mi->text, -1);

        if (!menuex) {
            if (mi->popup == NULL)
                fprintf(e, ", %d", (int)mi->id);

            unsigned int type = mi->type;
            if (type & MENUITEM_CHECKED)    fprintf(e, ", CHECKED");
            if (type & MENUITEM_GRAYED)     fprintf(e, ", GRAYED");
            if (type & MENUITEM_HELP)       fprintf(e, ", HELP");
            if (type & MENUITEM_INACTIVE)   fprintf(e, ", INACTIVE");
            if (type & MENUITEM_MENUBARBREAK) fprintf(e, ", MENUBARBREAK");
            if (type & MENUITEM_MENUBREAK)    fprintf(e, ", MENUBREAK");
            if (type & MENUITEM_OWNERDRAW)    fprintf(e, ", OWNERDRAW");
            if (type & MENUITEM_BITMAP)       fprintf(e, ", BITMAP");
        } else {
            int needs_id = mi->id != 0 || mi->type != 0 || mi->state != 0 || mi->help != 0;
            if (needs_id) {
                fprintf(e, ", %d", (int)mi->id);
                if (mi->type != 0 || mi->state != 0 || mi->help != 0) {
                    fprintf(e, ", %u", (unsigned int)mi->type);
                    if (mi->state != 0 || mi->help != 0) {
                        fprintf(e, ", %u", (unsigned int)mi->state);
                        if (mi->help != 0)
                            fprintf(e, ", %u", (unsigned int)mi->help);
                    }
                }
            }
        }

        fprintf(e, "\n");

        if (mi->popup != NULL)
            write_rc_menuitems(e, mi->popup, menuex, ind + 2);
    }

    indent(e, ind);
    fprintf(e, "END\n");
}

static int test_rc_datablock_unicode(rc_uint_type length, const bfd_byte *data) {
    rc_uint_type i;
    if (!data || (length & 1) != 0)
        return 0;

    for (i = 0; i + 1 < length; i += 2) {
        if (((data[i] == 0 && data[i + 1] == 0) && (i + 2) < length) ||
            (data[i] == 0xff && data[i + 1] == 0xff))
            return 0;
    }
    return 1;
}

static int test_rc_datablock_text(rc_uint_type length, const bfd_byte *data) {
    if (!data || length <= 1)
        return 0;

    int newlines = 0;
    rc_uint_type nonprint = 0;

    for (rc_uint_type i = 0; i < length; i++) {
        bfd_byte ch = data[i];

        if (ISPRINT(ch) || ch == '\t' ||
            (ch == 0 && (i + 1) != length)) {
            // printable
        } else if (ch == '\n') {
            newlines++;
        } else if (ch == '\r' && (i + 1) < length && data[i + 1] == '\n') {
            // allow CR if followed by LF
        } else {
            if (ch <= 7)
                return 0;
            nonprint++;
        }
    }
    if (length > 80 && newlines == 0)
        return 0;

    rc_uint_type ratio = (nonprint * 10000 + (length / 100) - 1) / length;
    if (ratio >= 150)
        return 0;

    return 1;
}

static void write_rc_messagetable(FILE *e, rc_uint_type length, const bfd_byte *data) {
    int has_error = 0;
    const struct bin_messagetable *mt;

    fprintf(e, "BEGIN\n");
    write_rc_datablock(e, length, data, 0, 0, 0);
    fprintf(e, "\n");

    wr_printcomment(e, "MC syntax dump");

    if (length < BIN_MESSAGETABLE_SIZE) {
        has_error = 1;
    } else {
        rc_uint_type m, i;

        mt = (const struct bin_messagetable *)data;
        m = target_get_32(mt->cblocks, length);

        if (length < (BIN_MESSAGETABLE_SIZE + m * BIN_MESSAGETABLE_BLOCK_SIZE)) {
            has_error = 1;
        } else {
            for (i = 0; i < m && !has_error; i++) {
                rc_uint_type low, high, offset;
                const struct bin_messagetable_item *mti;

                low = windres_get_32(&wrtarget, mt->items[i].lowid);
                high = windres_get_32(&wrtarget, mt->items[i].highid);
                offset = windres_get_32(&wrtarget, mt->items[i].offset);

                while (low <= high) {
                    rc_uint_type elen, flags;
                    if ((offset + BIN_MESSAGETABLE_ITEM_SIZE) > length) {
                        has_error = 1;
                        break;
                    }
                    mti = (const struct bin_messagetable_item *)&data[offset];
                    elen = windres_get_16(&wrtarget, mti->length);
                    flags = windres_get_16(&wrtarget, mti->flags);
                    if ((offset + elen) > length) {
                        has_error = 1;
                        break;
                    }

                    wr_printcomment(e, "MessageId = 0x%x", low);
                    wr_printcomment(e, "");

                    if ((flags & MESSAGE_RESOURCE_UNICODE) == MESSAGE_RESOURCE_UNICODE) {
                        if (elen > BIN_MESSAGETABLE_ITEM_SIZE * 2)
                            unicode_print(e, (const unichar *)mti->data,
                                (elen - BIN_MESSAGETABLE_ITEM_SIZE) / 2);
                    } else {
                        if (elen > BIN_MESSAGETABLE_ITEM_SIZE)
                            ascii_print(e, (const char *)mti->data,
                                (elen - BIN_MESSAGETABLE_ITEM_SIZE));
                    }

                    wr_printcomment(e, "");
                    ++low;
                    offset += elen;
                }
            }
        }
    }

    if (has_error)
        wr_printcomment(e, "Illegal data");
    wr_print_flush(e);
    fprintf(e, "END\n");
}

static void write_rc_datablock(FILE *e, rc_uint_type length, const bfd_byte *data,
                              int has_next, int hasblock, int show_comment) {
    int plen;
    if (!e || (!data && length)) return;

    if (hasblock)
        fprintf(e, "BEGIN\n");

    if (show_comment == -1) {
        if (test_rc_datablock_text(length, data)) {
            rc_uint_type i = 0;
            while (i < length) {
                rc_uint_type c = 0, j;
                indent(e, 2);
                fprintf(e, "\"");

                for (j = i; j < length && c < 160 && data[j] != '\n'; ++c, ++j)
                    ;
                if (j < length && data[j] == '\n')
                    ++j, ++c;

                ascii_print(e, (const char *)&data[i], c);
                fprintf(e, "\"");
                i = j;
                if (i < length)
                    fprintf(e, "\n");
            }
            if (length == 0) {
                indent(e, 2);
                fprintf(e, "\"\"");
            }
            if (has_next)
                fprintf(e, ",");
            fprintf(e, "\n");
            if (hasblock)
                fprintf(e, "END\n");
            return;
        }

        if (test_rc_datablock_unicode(length, data)) {
            rc_uint_type i = 0;
            while (i < length) {
                rc_uint_type c = 0, j = i / 2;
                const unichar *u = (const unichar *)&data[i];

                indent(e, 2);
                fprintf(e, "L\"");

                while ((i + c*2) < length && c < 160 && u[c] != '\n')
                    ++c;
                if ((i + c*2) < length && u[c] == '\n') {
                    ++c;
                }

                unicode_print(e, u, c);
                fprintf(e, "\"");
                i += c * 2;
                if (i < length)
                    fprintf(e, "\n");
            }
            if (length == 0) {
                indent(e, 2);
                fprintf(e, "L\"\"");
            }
            if (has_next)
                fprintf(e, ",");
            fprintf(e, "\n");
            if (hasblock)
                fprintf(e, "END\n");
            return;
        }

        show_comment = 0;
    }

    if (length) {
        rc_uint_type i = 0;
        int first = 1;
        rc_uint_type max_row = show_comment ? 4 : 8;

        while (i + 3 < length) {
            rc_uint_type comment_start = i, k;
            if (!first)
                indent(e, 2);

            for (k = 0; k < max_row && i + 3 < length; ++k, i += 4) {
                unsigned long val = (unsigned long)target_get_32(data + i, length - i);
                if (k == 0)
                    plen = fprintf(e, "0x%lxL", val);
                else
                    plen = fprintf(e, " 0x%lxL", val) - 1;
                if (has_next || (i + 4) < length) {
                    if (plen > 0 && plen < 11)
                        indent(e, 11 - plen);
                    fprintf(e, ",");
                }
            }
            if (show_comment) {
                fprintf(e, "\t/* ");
                ascii_print(e, (const char *)&data[comment_start], i - comment_start);
                fprintf(e, ".  */");
            }
            fprintf(e, "\n");
            first = 0;
        }

        if (i + 1 < length) {
            if (!first)
                indent(e, 2);
            plen = fprintf(e, "0x%x", (int)target_get_16(data + i, length - i));
            if (has_next || i + 2 < length) {
                if (plen > 0 && plen < 11)
                    indent(e, 11 - plen);
                fprintf(e, ",");
            }
            if (show_comment) {
                fprintf(e, "\t/* ");
                ascii_print(e, (const char *)&data[i], 2);
                fprintf(e, ".  */");
            }
            fprintf(e, "\n");
            i += 2;
            first = 0;
        }

        if (i < length) {
            if (!first)
                indent(e, 2);
            fprintf(e, "\"");
            ascii_print(e, (const char *)&data[i], 1);
            fprintf(e, "\"");
            if (has_next)
                fprintf(e, ",");
            fprintf(e, "\n");
        }
    }

    if (hasblock)
        fprintf(e, "END\n");
}

/* Write out an rcdata resource.  This is also used for other types of
   resources that need to print arbitrary data.  */

static void write_rc_rcdata(FILE *e, const rc_rcdata_item *rcdata, int ind) {
    const rc_rcdata_item *ri;

    if (e == NULL) {
        return;
    }

    indent(e, ind);
    fprintf(e, "BEGIN\n");

    for (ri = rcdata; ri != NULL; ri = ri->next) {
        if (ri->type == RCDATA_BUFFER && ri->u.buffer.length == 0) {
            continue;
        }

        switch (ri->type) {
            case RCDATA_WORD:
                indent(e, ind + 2);
                fprintf(e, "%ld", (long)(ri->u.word & 0xffff));
                break;

            case RCDATA_DWORD:
                indent(e, ind + 2);
                fprintf(e, "%luL", (unsigned long)ri->u.dword);
                break;

            case RCDATA_STRING:
                indent(e, ind + 2);
                fprintf(e, "\"");
                ascii_print(e, ri->u.string.s, ri->u.string.length);
                fprintf(e, "\"");
                break;

            case RCDATA_WSTRING:
                indent(e, ind + 2);
                fprintf(e, "L\"");
                unicode_print(e, ri->u.wstring.w, ri->u.wstring.length);
                fprintf(e, "\"");
                break;

            case RCDATA_BUFFER:
                write_rc_datablock(e,
                                   (rc_uint_type)ri->u.buffer.length,
                                   (const bfd_byte *)ri->u.buffer.data,
                                   ri->next != NULL,
                                   0,
                                   -1);
                break;

            default:
                abort();
                break;
        }

        if (ri->type != RCDATA_BUFFER) {
            if (ri->next != NULL) {
                fprintf(e, ",");
            }
            fprintf(e, "\n");
        }
    }

    indent(e, ind);
    fprintf(e, "END\n");
}

/* Write out a stringtable resource.  */

static void write_rc_stringtable(FILE *e, const rc_res_id *name, const rc_stringtable *stringtable) {
    rc_uint_type offset = 0;
    int i;

    if (name != NULL && !name->named) {
        offset = (name->u.id - 1) << 4;
    } else {
        fprintf(e, "/* %s string table name.  */\n", (name == NULL ? "Missing" : "Invalid"));
    }

    fprintf(e, "BEGIN\n");

    for (i = 0; i < 16; i++) {
        if (stringtable->strings[i].length == 0)
            continue;
        fprintf(e, "  %lu, ", (unsigned long)offset + i);
        unicode_print_quoted(e, stringtable->strings[i].string, stringtable->strings[i].length);
        fprintf(e, "\n");
    }

    fprintf(e, "END\n");
}

/* Write out a versioninfo resource.  */

static void write_rc_versioninfo(FILE *e, const rc_versioninfo *versioninfo) {
    if (!e || !versioninfo || !versioninfo->fixed)
        return;

    const rc_fixed_versioninfo *f = versioninfo->fixed;

    if (f->file_version_ms || f->file_version_ls) {
        fprintf(e, " FILEVERSION %u, %u, %u, %u\n",
                (unsigned)((f->file_version_ms >> 16) & 0xFFFF),
                (unsigned)(f->file_version_ms & 0xFFFF),
                (unsigned)((f->file_version_ls >> 16) & 0xFFFF),
                (unsigned)(f->file_version_ls & 0xFFFF));
    }
    if (f->product_version_ms || f->product_version_ls) {
        fprintf(e, " PRODUCTVERSION %u, %u, %u, %u\n",
                (unsigned)((f->product_version_ms >> 16) & 0xFFFF),
                (unsigned)(f->product_version_ms & 0xFFFF),
                (unsigned)((f->product_version_ls >> 16) & 0xFFFF),
                (unsigned)(f->product_version_ls & 0xFFFF));
    }
    if (f->file_flags_mask)
        fprintf(e, " FILEFLAGSMASK 0x%x\n", (unsigned)f->file_flags_mask);
    if (f->file_flags)
        fprintf(e, " FILEFLAGS 0x%x\n", (unsigned)f->file_flags);
    if (f->file_os)
        fprintf(e, " FILEOS 0x%x\n", (unsigned)f->file_os);
    if (f->file_type)
        fprintf(e, " FILETYPE 0x%x\n", (unsigned)f->file_type);
    if (f->file_subtype)
        fprintf(e, " FILESUBTYPE 0x%x\n", (unsigned)f->file_subtype);
    if (f->file_date_ms || f->file_date_ls) {
        fprintf(e, "/* Date: %u, %u.  */\n", (unsigned)f->file_date_ms, (unsigned)f->file_date_ls);
    }

    fprintf(e, "BEGIN\n");

    for (const rc_ver_info *vi = versioninfo->var; vi; vi = vi->next) {
        if (vi->type == VERINFO_STRING) {
            fprintf(e, "  BLOCK \"StringFileInfo\"\n  BEGIN\n");
            for (const rc_ver_stringtable *vst = vi->u.string.stringtables; vst; vst = vst->next) {
                fprintf(e, "    BLOCK ");
                unicode_print_quoted(e, vst->language, -1);
                fprintf(e, "\n    BEGIN\n");
                for (const rc_ver_stringinfo *vs = vst->strings; vs; vs = vs->next) {
                    fprintf(e, "      VALUE ");
                    unicode_print_quoted(e, vs->key, -1);
                    fprintf(e, ", ");
                    unicode_print_quoted(e, vs->value, -1);
                    fprintf(e, "\n");
                }
                fprintf(e, "    END\n");
            }
            fprintf(e, "  END\n");
        } else if (vi->type == VERINFO_VAR) {
            fprintf(e, "  BLOCK \"VarFileInfo\"\n  BEGIN\n    VALUE ");
            unicode_print_quoted(e, vi->u.var.key, -1);
            for (const rc_ver_varinfo *vv = vi->u.var.var; vv; vv = vv->next) {
                fprintf(e, ", 0x%x, %d", (unsigned)vv->language, (int)vv->charset);
            }
            fprintf(e, "\n  END\n");
        }
    }

    fprintf(e, "END\n");
}

static rc_uint_type rcdata_copy(const rc_rcdata_item *src, bfd_byte *dst)
{
    if (src == NULL)
        return 0;

    switch (src->type) {
        case RCDATA_WORD:
            if (dst) {
                windres_put_16(&wrtarget, dst, (rc_uint_type)src->u.word);
            }
            return 2;
        case RCDATA_DWORD:
            if (dst) {
                windres_put_32(&wrtarget, dst, (rc_uint_type)src->u.dword);
            }
            return 4;
        case RCDATA_STRING:
            if (src->u.string.length > 0 && dst != NULL) {
                memcpy(dst, src->u.string.s, src->u.string.length);
            }
            return (rc_uint_type)src->u.string.length;
        case RCDATA_WSTRING:
            if (src->u.wstring.length > 0 && dst != NULL) {
                memcpy(dst, src->u.wstring.w, src->u.wstring.length * sizeof(unichar));
            }
            return (rc_uint_type)(src->u.wstring.length * sizeof(unichar));
        case RCDATA_BUFFER:
            if (src->u.buffer.length > 0 && dst != NULL) {
                memcpy(dst, src->u.buffer.data, src->u.buffer.length);
            }
            return (rc_uint_type)src->u.buffer.length;
        default:
            return 0;
    }
}
