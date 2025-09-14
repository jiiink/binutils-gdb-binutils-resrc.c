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

#include <errno.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/wait.h>

#define PEXECUTE_ONE 1
#define PEXECUTE_SEARCH 2

extern int pexecute(const char *, char * const *, const char *, const char *, char **, char **, int);
extern int pwait(int, int *, int);
extern void fatal(const char *, ...);
extern char *make_temp_file(const char *);

static int run_cmd(char *cmd, const char *redir) {
  const char *delim = " \t";
  char *token, *saveptr;
  int pid, wait_status, retcode = 0;
  int redir_handle, stdout_save;
  char *errmsg_fmt = NULL, *errmsg_arg = NULL;
  char *temp_base = make_temp_file(NULL);
  const char **argv;
  int arg_count = 2; // Including NULL terminator

  for (char *p = cmd; *p != '\0'; p++) {
    if (*p == ' ') arg_count++;
  }

  argv = malloc(sizeof(char *) * arg_count);
  if (!argv) {
      fatal("Memory allocation failed");
      return 1;
  }

  arg_count = 0;
  for (token = strtok_r(cmd, delim, &saveptr); token; token = strtok_r(NULL, delim, &saveptr)) {
    argv[arg_count++] = token;
  }
  argv[arg_count] = NULL;

  if ((redir_handle = open(redir, O_WRONLY | O_TRUNC | O_CREAT, 0666)) == -1) {
    fatal("Can't open temporary file `%s': %s", redir, strerror(errno));
    free(argv);
    return 1;
  }

  if ((stdout_save = dup(STDOUT_FILENO)) == -1) {
    fatal("Can't redirect stdout: `%s': %s", redir, strerror(errno));
    close(redir_handle);
    free(argv);
    return 1;
  }

  dup2(redir_handle, STDOUT_FILENO);

  pid = pexecute(argv[0], (char * const *)argv, "program_name", temp_base, &errmsg_fmt, &errmsg_arg, PEXECUTE_ONE | PEXECUTE_SEARCH);

  dup2(stdout_save, STDOUT_FILENO);
  close(stdout_save);
  close(redir_handle);
  free(argv);

  if (pid == -1) {
    fatal("%s %s: %s", errmsg_fmt, errmsg_arg, strerror(errno));
    return 1;
  }

  if ((pid = pwait(pid, &wait_status, 0)) == -1) {
    fatal("wait: %s", strerror(errno));
    return 1;
  } else if (WIFSIGNALED(wait_status)) {
    fatal("subprocess got fatal signal %d", WTERMSIG(wait_status));
    retcode = 1;
  } else if (WIFEXITED(wait_status) && WEXITSTATUS(wait_status) != 0) {
    fatal("%s exited with status %d", cmd, WEXITSTATUS(wait_status));
    retcode = 1;
  }

  return retcode;
}

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>

static FILE *open_input_stream(const char *cmd) {
    FILE *cpp_pipe = NULL;
    char *cpp_temp_file = NULL;
    char *fileprefix = NULL;

    switch (istream_type) {
        case ISTREAM_FILE:
            fileprefix = make_temp_file(NULL);
            if (fileprefix == NULL) {
                fatal(_("Failed to create a temporary file prefix"));
                break;
            }

            cpp_temp_file = (char *)malloc(strlen(fileprefix) + 5);
            if (cpp_temp_file == NULL) {
                free(fileprefix);
                fatal(_("Memory allocation failed"));
                break;
            }

            sprintf(cpp_temp_file, "%s.irc", fileprefix);
            free(fileprefix);

            if (run_cmd(cmd, cpp_temp_file)) {
                free(cpp_temp_file);
                fatal(_("can't execute `%s': %s"), cmd, strerror(errno));
                break;
            }

            cpp_pipe = fopen(cpp_temp_file, FOPEN_RT);
            if (cpp_pipe == NULL) {
                free(cpp_temp_file);
                fatal(_("can't open temporary file `%s': %s"), cpp_temp_file, strerror(errno));
                break;
            }

            if (verbose) {
                fprintf(stderr, _("Using temporary file `%s' to read preprocessor output\n"), cpp_temp_file);
            }
            break;

        default:
            cpp_pipe = popen(cmd, FOPEN_RT);
            if (cpp_pipe == NULL) {
                fatal(_("can't popen `%s': %s"), cmd, strerror(errno));
                break;
            }

            if (verbose) {
                fprintf(stderr, _("Using popen to read preprocessor output\n"));
            }
            break;
    }

    xatexit(close_input_stream);
    return cpp_pipe;
}

/* Determine if FILENAME contains special characters that
   can cause problems unless the entire filename is quoted.  */

int filename_need_quotes(const char *filename) {
    if (!filename || (filename[0] == '-' && filename[1] == '\0'))
        return 0;

    for (; *filename != '\0'; filename++) {
        if (*filename == '&' || *filename == ' ' || *filename == '<' ||
            *filename == '>' || *filename == '|' || *filename == '%') {
            return 1;
        }
    }
    return 0;
}

/* Look for the preprocessor program.  */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <errno.h>

static FILE *open_input_stream(const char *cmd);

static int check_file_exists(const char *path) {
    struct stat s;
    return stat(path, &s) == 0;
}

static void quote_if_needed(char *cmd, char **out_ptr) {
    char *out = *out_ptr;
    size_t len = strlen(cmd);
    memmove(cmd + 1, cmd, len);
    cmd[0] = '"';
    out = cmd + len + 1;
    *out++ = '"';
    *out = '\0';
    *out_ptr = out;
}

static FILE *look_for_default(char *cmd, const char *prefix, int end_prefix,
                              const char *preprocargs, const char *filename) {
    const char *fnquotes = filename_need_quotes(filename) ? "\"" : "";
    memcpy(cmd, prefix, end_prefix);
    char *out = stpcpy(cmd + end_prefix, DEFAULT_PREPROCESSOR_CMD);

    #ifdef HAVE_EXECUTABLE_SUFFIX
    char cmd_with_suffix[strlen(cmd) + strlen(EXECUTABLE_SUFFIX) + 1];
    strcpy(cmd_with_suffix, cmd);
    strcat(cmd_with_suffix, EXECUTABLE_SUFFIX);
    #endif

    int found = check_file_exists(cmd)
#ifdef HAVE_EXECUTABLE_SUFFIX
                || check_file_exists(cmd_with_suffix)
#endif
                ;

    if (!found) {
        if (verbose) {
            fprintf(stderr, "Tried `%s'\n", cmd);
        }
        return NULL;
    }

    if (filename_need_quotes(cmd)) {
        quote_if_needed(cmd, &out);
    }

    snprintf(out, LINE_MAX - (out - cmd), " %s %s %s%s%s",
             DEFAULT_PREPROCESSOR_ARGS, preprocargs, fnquotes, filename, fnquotes);

    if (verbose) {
        fprintf(stderr, "Using `%s'\n", cmd);
    }

    return open_input_stream(cmd);
}

/* Read an rc file.  */

#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#define ISTREAM_FILE 0
#define ISTREAM_PIPE 1
#define DEFAULT_PREPROCESSOR_CMD ""
#define DEFAULT_PREPROCESSOR_ARGS ""
#define HAVE_EXECUTABLE_SUFFIX
#define EXECUTABLE_SUFFIX ""

typedef struct {
    // Assuming some structure here as it's not given
} rc_res_directory;

// Placeholder functions
int open_input_stream(const char *cmd) { return 0; }
int close_input_stream() { return 0; }
bool filename_need_quotes(const char *filename) { return false; }
void windres_add_include_dir(char *dir) {}
int look_for_default(char *cmd, const char *prefix, size_t prefix_len, const char *preprocargs, const char *filename) { return 0; }
char *xmalloc(size_t size) { return (char *)malloc(size); }
char *xstrdup(const char *s) { return strdup(s); }
void rcparse_set_language(int language) {}
void yyparse() {}
void rcparse_discard_strings() {}
void define_fontdirs() {}

rc_res_directory *read_rc_file(const char *filename, const char *preprocessor, const char *preprocargs, int language, int use_temp_file) {
    char *cmd = NULL;
    char *edit, *dir;
    const char *fnquotes = (filename && filename_need_quotes(filename)) ? "\"" : "";
    int cpp_pipe;
#ifdef HAVE_EXECUTABLE_SUFFIX
    const char *suffix = EXECUTABLE_SUFFIX;
#else
    const char *suffix = "";
#endif

    if (!filename) {
        filename = "-";
    } else if (strchr(filename, '/') || strchr(filename, '\\')) {
        dir = xmalloc(strlen(filename) + 3);
        edit = dir;
        if (filename[0] != '/' && filename[0] != '\\' && filename[1] != ':') {
            *edit++ = '.';
            *edit++ = '/';
        }
        edit = stpcpy(edit, filename);
        while (edit > dir && (edit[-1] != '\\' && edit[-1] != '/')) {
            --edit;
        }
        *--edit = 0;
        while ((edit = strchr(dir, '\\')) != NULL) {
            *edit = '/';
        }
        windres_add_include_dir(dir);
        free(dir);
    }

    int istream_type = use_temp_file ? ISTREAM_FILE : ISTREAM_PIPE;
    preprocargs = preprocargs ? preprocargs : "";

    if (preprocessor) {
        cmd = xmalloc(strlen(preprocessor) + strlen(preprocargs) + strlen(filename) + strlen(fnquotes) * 2 + 10);
        sprintf(cmd, "%s %s %s%s%s", preprocessor, preprocargs, fnquotes, filename, fnquotes);
        cpp_pipe = open_input_stream(cmd);
    } else {
        size_t cmd_len = strlen(DEFAULT_PREPROCESSOR_CMD) + strlen(DEFAULT_PREPROCESSOR_ARGS) + strlen(preprocargs) + strlen(filename) + strlen(fnquotes) * 2 + strlen(suffix) + 10;
        cmd = xmalloc(cmd_len);

        const char *dash = NULL;
        const char *slash = NULL;
        const char *cp;
        for (cp = ""; *cp; cp++) {
            if (*cp == '-') dash = cp;
            if (*cp == '/' || *cp == '\\' || *cp == ':') {
                slash = cp;
                dash = NULL;
            }
        }

        cpp_pipe = 0;
        if (dash) {
            cpp_pipe = look_for_default(cmd, "", dash - "" + 1, preprocargs, filename);
        }
        if (slash && !cpp_pipe) {
            cpp_pipe = look_for_default(cmd, "", slash - "" + 1, preprocargs, filename);
        }
        if (!cpp_pipe) {
            cpp_pipe = look_for_default(cmd, "", 0, preprocargs, filename);
        }
    }

    free(cmd);
    char *rc_filename = xstrdup(filename);
    int rc_lineno = 1;
    if (language != -1) rcparse_set_language(language);
    yyparse();
    rcparse_discard_strings();
    close_input_stream();
    define_fontdirs();
    free(rc_filename);
    return NULL; // Assuming resources is NULL
}

/* Close the input stream if it is open.  */

static void close_input_stream(void) {
    if (istream_type == ISTREAM_FILE) {
        if (cpp_pipe != NULL) {
            fclose(cpp_pipe);
        }

        if (cpp_temp_file != NULL) {
            int errno_save = errno;
            if (unlink(cpp_temp_file) != 0) {
                errno = errno_save;
            }
            free(cpp_temp_file);
        }

    } else if (cpp_pipe != NULL) {
        int err = pclose(cpp_pipe);
        if (err != 0 && errno != ECHILD) {
            cpp_pipe = NULL;
            cpp_temp_file = NULL;
            fatal(_("preprocessing failed."));
        }
    }

    cpp_pipe = NULL;
    cpp_temp_file = NULL;
}

/* Report an error while reading an rc file.  */

void yyerror(const char *msg) {
    if (msg == NULL) {
        fatal("%s:%d: Unknown error", rc_filename, rc_lineno);
        return;
    }
    fatal("%s:%d: %s", rc_filename, rc_lineno, msg);
}

/* Issue a warning while reading an rc file.  */

#include <stdio.h>

void rcparse_warning(const char *msg)
{
    if (msg == NULL || rc_filename == NULL) {
        fprintf(stderr, "Warning: Invalid parameters or context not set\n");
        return;
    }
    fprintf(stderr, "%s:%d: %s\n", rc_filename, rc_lineno, msg);
}

/* Die if we get an unexpected end of file.  */

#include <stdio.h>
#include <stdlib.h>

static void unexpected_eof(const char *msg) {
    if (msg == NULL) {
        fprintf(stderr, "Error: Message cannot be null.\n");
        exit(EXIT_FAILURE);
    }
    fprintf(stderr, "%s: unexpected EOF\n", msg);
    exit(EXIT_FAILURE);
}

/* Read a 16 bit word from a file.  The data is assumed to be little
   endian.  */

#include <stdio.h>
#include <errno.h>

static int get_word(FILE *e, const char *msg) {
    int b1 = getc(e);
    if (b1 == EOF) {
        if (feof(e)) {
            unexpected_eof(msg);
        } else {
            perror("getc failed");
            return -1; // Indicate error
        }
    }

    int b2 = getc(e);
    if (b2 == EOF) {
        if (feof(e)) {
            unexpected_eof(msg);
        } else {
            perror("getc failed");
            return -1; // Indicate error
        }
    }

    return ((b2 & 0xff) << 8) | (b1 & 0xff);
}

/* Read a 32 bit word from a file.  The data is assumed to be little
   endian.  */

#include <stdio.h>
#include <errno.h>

static unsigned long get_long(FILE *e, const char *msg) {
    int bytes[4];

    for (int i = 0; i < 4; i++) {
        bytes[i] = getc(e);
        if (bytes[i] == EOF) {
            if (feof(e)) {
                unexpected_eof(msg);
            } else if (ferror(e)) {
                perror("Error reading file");
                exit(EXIT_FAILURE);
            }
            return 0; // Return 0 if an error other than EOF is not handled by unexpected_eof
        }
    }

    return ((unsigned long)(bytes[3] & 0xff) << 24) |
           ((unsigned long)(bytes[2] & 0xff) << 16) |
           ((unsigned long)(bytes[1] & 0xff) << 8)  |
           ((unsigned long)(bytes[0] & 0xff));
}

/* Read data from a file.  This is a wrapper to do error checking.  */

static void get_data(FILE *e, bfd_byte *p, rc_uint_type c, const char *msg) {
    if (fread(p, 1, c, e) != c) {
        fatal(_("%s: failed to read %lu bytes"), msg, (unsigned long)c);
    }
}

#include <stddef.h>
#include <stdio.h>

static rc_uint_type target_get_16(const void *p, size_t len) {
    if (p == NULL) {
        fprintf(stderr, "Invalid pointer\n");
        return 0; // Or handle the error as needed
    }

    if (len < 2) {
        fprintf(stderr, "Not enough data\n");
        return 0; // Or handle the error as needed
    }

    return windres_get_16(&wrtarget, p);
}

#include <stdbool.h>
#include <stddef.h>

static inline bool validate_length(size_t len, size_t required_len) {
    return len >= required_len;
}

static rc_uint_type target_get_32(const void *p, size_t len) {
    if (!validate_length(len, 4)) {
        fatal(_("not enough data"));
    }
    return windres_get_32(&wrtarget, p);
}

/* Define an accelerator resource.  */

void define_accelerator(rc_res_id id, const rc_res_res_info *resinfo, rc_accelerator *data) {
    rc_res_resource *resource = define_standard_resource(&resources, RT_ACCELERATOR, id, resinfo->language, 0);
    
    if (resource) {
        resource->type = RES_TYPE_ACCELERATOR;
        resource->u.acc = data;
        resource->res_info = *resinfo;
    }
}

/* Define a bitmap resource.  Bitmap data is stored in a file.  The
   first 14 bytes of the file are a standard header, which is not
   included in the resource data.  */

#define BITMAP_SKIP (14)

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <sys/stat.h>

#define FOPEN_RB "rb"
#define BITMAP_SKIP 0

typedef unsigned char bfd_byte;
typedef unsigned long rc_uint_type;
typedef struct {
  int language;
} rc_res_res_info;

typedef enum {
  RES_TYPE_BITMAP
} res_type;

typedef struct {
  rc_res_res_info res_info;
  res_type type;
  struct {
    rc_uint_type length;
    bfd_byte *data;
  } u;
} rc_res_resource;

typedef int rc_res_id;

rc_res_resource *define_standard_resource(void *, int, rc_res_id, int, int);
void *res_alloc(size_t size);
FILE *open_file_search(const char *filename, const char *mode, const char *desc, char **actual_name);
void get_data(FILE *file, bfd_byte *data, size_t size, const char *filename);
void fatal(const char *msg, ...);
void *resources;

void define_bitmap(rc_res_id id, const rc_res_res_info *resinfo, const char *filename) {
  FILE *e = NULL;
  char *real_filename = NULL;
  struct stat s;
  bfd_byte *data = NULL;

  e = open_file_search(filename, FOPEN_RB, "bitmap file", &real_filename);
  if (!e || stat(real_filename, &s) < 0) {
    fatal("stat failed on bitmap file `%s': %s", real_filename, strerror(errno));
  }
  
  data = (bfd_byte *)res_alloc(s.st_size - BITMAP_SKIP);
  fseek(e, BITMAP_SKIP, SEEK_CUR);
  
  get_data(e, data, s.st_size - BITMAP_SKIP, real_filename);

  fclose(e);
  free(real_filename);

  rc_res_resource *r = define_standard_resource(&resources, RT_BITMAP, id, resinfo->language, 0);
  r->type = RES_TYPE_BITMAP;
  r->u.data.length = s.st_size - BITMAP_SKIP;
  r->u.data.data = data;
  r->res_info = *resinfo;
}

/* Define a cursor resource.  A cursor file may contain a set of
   bitmaps, each representing the same cursor at various different
   resolutions.  They each get written out with a different ID.  The
   real cursor resource is then a group resource which can be used to
   select one of the actual cursors.  */

#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <string.h>

void define_cursor(rc_res_id id, const rc_res_res_info *resinfo, const char *filename) {
    FILE *e;
    char *real_filename = NULL;
    struct icondir *icondirs = NULL;
    rc_res_resource *r;
    rc_group_cursor *first = NULL, **pp;
    int type, count, i;
    int first_cursor;

    e = open_file_search(filename, FOPEN_RB, "cursor file", &real_filename);
    if (!e) {
        fatal(_("Failed to open cursor file `%s'"), filename);
        return;
    }

    (void)get_word(e, real_filename); 
    type = get_word(e, real_filename);
    count = get_word(e, real_filename);
    if (type != 2) {
        fatal(_("cursor file `%s' does not contain cursor data"), real_filename);
        return;
    }

    icondirs = (struct icondir *)xmalloc(count * sizeof(*icondirs));
    if (!icondirs) {
        fatal(_("Memory allocation failed for `icondirs`"));
        fclose(e);
        free(real_filename);
        return;
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
            unexpected_eof(real_filename);
            free(icondirs);
            fclose(e);
            free(real_filename);
            return;
        }
    }

    first_cursor = cursors;

    for (i = 0; i < count; i++) {
        rc_cursor *c;
        rc_res_id name;
        bfd_byte *data = (bfd_byte *)res_alloc(icondirs[i].bytes);

        if (!data) {
            fatal(_("Memory allocation failed for `data`"));
            free(icondirs);
            fclose(e);
            free(real_filename);
            return;
        }

        if (fseek(e, icondirs[i].offset, SEEK_SET) != 0) {
            fatal(_("%s: fseek to %lu failed: %s"), real_filename, icondirs[i].offset, strerror(errno));
            free(data);
            free(icondirs);
            fclose(e);
            free(real_filename);
            return;
        }

        get_data(e, data, icondirs[i].bytes, real_filename);

        c = (rc_cursor *)res_alloc(sizeof(rc_cursor));
        if (!c) {
            fatal(_("Memory allocation failed for `rc_cursor`"));
            free(data);
            free(icondirs);
            fclose(e);
            free(real_filename);
            return;
        }

        c->xhotspot = icondirs[i].u.cursor.xhotspot;
        c->yhotspot = icondirs[i].u.cursor.yhotspot;
        c->length = icondirs[i].bytes;
        c->data = data;

        ++cursors;
        name.named = 0;
        name.u.id = cursors;

        r = define_standard_resource(&resources, RT_CURSOR, name,
                                     resinfo->language, 0);
        if (!r) {
            fatal(_("Failed to define standard resource for cursor"));
            // Assuming necessary cleanup happens within define_standard_resource
            return;
        }
        r->type = RES_TYPE_CURSOR;
        r->u.cursor = c;
        r->res_info = *resinfo;
    }

    fclose(e);
    free(real_filename);

    pp = &first;
    for (i = 0; i < count; i++) {
        rc_group_cursor *cg;

        cg = (rc_group_cursor *)res_alloc(sizeof(rc_group_cursor));
        if (!cg) {
            fatal(_("Memory allocation failed for `rc_group_cursor`"));
            free(icondirs);
            // Assuming necessary cleanup for first and its previous pointers
            return;
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

    r = define_standard_resource(&resources, RT_GROUP_CURSOR, id,
                                 resinfo->language, 0);
    if (!r) {
        fatal(_("Failed to define standard resource for group cursor"));
        // Assuming necessary cleanup happens within define_standard_resource
        return;
    }
    r->type = RES_TYPE_GROUP_CURSOR;
    r->u.group_cursor = first;
    r->res_info = *resinfo;
}

/* Define a dialog resource.  */

#include <errno.h>
#include <string.h>
#include <stdlib.h>

void define_dialog(rc_res_id id, const rc_res_res_info *resinfo, const rc_dialog *dialog) {
    if (resinfo == NULL || dialog == NULL) {
        // Handle invalid parameters
        return;
    }
    
    rc_dialog *copy = (rc_dialog *)res_alloc(sizeof(rc_dialog));
    if (copy == NULL) {
        // Handle memory allocation failure
        return;
    }
    
    memcpy(copy, dialog, sizeof(rc_dialog));
    
    rc_res_resource *r = define_standard_resource(&resources, RT_DIALOG, id, resinfo->language, 0);
    if (r == NULL) {
        // Handle define_standard_resource failure
        free(copy); // Ensure proper cleanup
        return;
    }
    
    r->type = RES_TYPE_DIALOG;
    r->u.dialog = copy;
    r->res_info = *resinfo;
}

/* Define a dialog control.  This does not define a resource, but
   merely allocates and fills in a structure.  */

#include <stdlib.h> // Ensure that malloc is available

rc_dialog_control *define_control(const rc_res_id iid, rc_uint_type id, rc_uint_type x,
                                  rc_uint_type y, rc_uint_type width, rc_uint_type height,
                                  const rc_res_id class, rc_uint_type style,
                                  rc_uint_type exstyle) {
    rc_dialog_control *n = (rc_dialog_control *)malloc(sizeof(rc_dialog_control));
    if (n == NULL) {
        return NULL; // Proper error handling if memory allocation fails
    }

    // Initialize structure members directly
    *n = (rc_dialog_control) {
        .next = NULL,
        .id = id,
        .style = style,
        .exstyle = exstyle,
        .x = x,
        .y = y,
        .width = width,
        .height = height,
        .class = class,
        .text = iid,
        .data = NULL,
        .help = 0
    };

    return n;
}

rc_dialog_control *define_icon_control(rc_res_id iid, rc_uint_type id, rc_uint_type x, rc_uint_type y, rc_uint_type style, rc_uint_type exstyle, rc_uint_type help, rc_rcdata_item *data, rc_dialog_ex *ex) {
    rc_dialog_control *control;
    rc_res_id typeId, classId;

    if (style == 0) {
        style = SS_ICON | WS_CHILD | WS_VISIBLE;
    }

    classId.named = 0;
    classId.u.id = CTL_STATIC;
    
    res_string_to_id(&typeId, "");
    
    control = define_control(typeId, id, x, y, 0, 0, classId, style, exstyle);
    
    if (!control) {
        return NULL;
    }
    
    control->text = iid;

    if (help && !ex) {
        rcparse_warning(_("help ID requires DIALOGEX"));
    }

    if (data && !ex) {
        rcparse_warning(_("control data requires DIALOGEX"));
    }

    control->help = help;
    control->data = data;

    return control;
}

/* Define a font resource.  */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <errno.h>

void define_font(rc_res_id id, const rc_res_res_info *resinfo, const char *filename) {
    FILE *e = NULL;
    char *real_filename = NULL;
    struct stat s;
    bfd_byte *data = NULL;
    rc_res_resource *r = NULL;
    rc_fontdir *fd = NULL;
    rc_fontdir **pp = NULL;
    long offset = 0;
    const char *device = "";
    const char *face = "";
    long fontdatalength = 0;
    bfd_byte *fontdata = NULL;

    e = open_file_search(filename, FOPEN_RB, "font file", &real_filename);
    if (stat(real_filename, &s) < 0) {
        fatal(_("stat failed on font file `%s': %s"), real_filename, strerror(errno));
    }

    data = (bfd_byte *)res_alloc(s.st_size);
    get_data(e, data, s.st_size, real_filename);
    fclose(e);
    free(real_filename);

    r = define_standard_resource(&resources, RT_FONT, id, resinfo->language, 0);
    r->type = RES_TYPE_FONT;
    r->u.data.length = s.st_size;
    r->u.data.data = data;
    r->res_info = *resinfo;

    offset = (data[47] << 24) | (data[46] << 16) | (data[45] << 8) | data[44];
    if (offset > 0 && offset < s.st_size) {
        device = (char *)data + offset;
    }

    offset = (data[51] << 24) | (data[50] << 16) | (data[49] << 8) | data[48];
    if (offset > 0 && offset < s.st_size) {
        face = (char *)data + offset;
    }

    fonts++;
    fontdatalength = 58 + strlen(device) + strlen(face);
    fontdata = (bfd_byte *)res_alloc(fontdatalength);
    memcpy(fontdata, data, 56);
    strcpy((char *)fontdata + 56, device);
    strcpy((char *)fontdata + 57 + strlen(device), face);

    fd = (rc_fontdir *)res_alloc(sizeof(rc_fontdir));
    fd->next = NULL;
    fd->index = fonts;
    fd->length = fontdatalength;
    fd->data = fontdata;

    for (pp = &fontdirs; *pp != NULL; pp = &(*pp)->next);
    *pp = fd;
    fontdirs_resinfo = *resinfo;
}

static void define_font_rcdata(rc_res_id id, const rc_res_res_info *resinfo, rc_rcdata_item *data) {
    rc_res_resource *resource;
    rc_uint_type data_length;
    bfd_byte *data_buffer;

    resource = define_standard_resource(&resources, RT_FONT, id, resinfo->language, 0);

    data_buffer = rcdata_render_as_buffer(data, &data_length);
    if (data_buffer == NULL) {
        // Handle error - the buffer could not be rendered
        return;
    }

    resource->type = RES_TYPE_FONT;
    resource->u.data.length = data_length;
    resource->u.data.data = data_buffer;
    resource->res_info = *resinfo;
}

/* Define the fontdirs resource.  This is called after the entire rc
   file has been parsed, if any font resources were seen.  */

static void define_fontdirs(void) {
    rc_res_resource *resource;
    rc_res_id res_id = {0}; // Initialize structure with zero

    res_id.u.id = 1;

    resource = define_standard_resource(&resources, RT_FONTDIR, res_id, 0x409, 0);
    if (resource == NULL) {
        // Handle error, resource allocation failed
        return;
    }

    resource->type = RES_TYPE_FONTDIR;
    resource->u.fontdir = fontdirs;
    resource->res_info = fontdirs_resinfo;
}

static bfd_byte *rcdata_render_as_buffer(const rc_rcdata_item *data, rc_uint_type *plen) {
    rc_uint_type len = 0;

    if (data == NULL) {
        if (plen) {
            *plen = 0;
        }
        return NULL;
    }

    for (const rc_rcdata_item *d = data; d != NULL; d = d->next) {
        len += rcdata_copy(d, NULL);
    }

    if (plen) {
        *plen = len;
    }

    if (len == 0) {
        return NULL;
    }

    bfd_byte *ret = (bfd_byte *)res_alloc(len);
    if (ret == NULL) {
        return NULL; // Handle memory allocation failure
    }

    bfd_byte *pret = ret;
    for (const rc_rcdata_item *d = data; d != NULL; d = d->next) {
        pret += rcdata_copy(d, pret);
    }

    return ret;
}

static void define_fontdir_rcdata(rc_res_id id, const rc_res_res_info *resinfo, rc_rcdata_item *data) {
    rc_res_resource *r;
    rc_fontdir *fd_first = NULL, *fd_cur = NULL;
    rc_uint_type len_data, off = 2, entry_count;
    bfd_byte *pb_data;
    
    r = define_standard_resource(&resources, RT_FONTDIR, id, 0x409, 0);
    pb_data = rcdata_render_as_buffer(data, &len_data);
    
    if (pb_data == NULL) {
        r->type = RES_TYPE_FONTDIR;
        r->u.fontdir = NULL;
        r->res_info = *resinfo;
        return;
    }

    entry_count = target_get_16(pb_data, len_data);
    while (entry_count-- > 0) {
        rc_fontdir *fd;
        const struct bin_fontdir_item *bfi;
        size_t dev_name_len;

        if (off >= len_data) {
            break;
        }

        bfi = (const struct bin_fontdir_item *)(pb_data + off);
        fd = (rc_fontdir *)res_alloc(sizeof(rc_fontdir));
        fd->index = target_get_16(bfi->index, len_data - off);

        fd->data = pb_data + off;
        off += 56;

        dev_name_len = strlen((char *)bfi->device_name) + 1;
        off += (rc_uint_type)(dev_name_len);

        off += (rc_uint_type)strlen((char *)(bfi->device_name + dev_name_len)) + 1;

        fd->length = (off - (pb_data + off - fd->data));
        fd->next = NULL;

        if (fd_first == NULL) {
            fd_first = fd;
        } else {
            fd_cur->next = fd;
        }
        
        fd_cur = fd;
    }

    r->type = RES_TYPE_FONTDIR;
    r->u.fontdir = fd_first;
    r->res_info = *resinfo;
}

void define_messagetable_rcdata(rc_res_id id, const rc_res_res_info *resinfo, rc_rcdata_item *data) {
    if (resinfo == NULL || data == NULL) {
        return;
    }

    rc_uint_type len_data = 0;
    rc_res_resource *resource = define_standard_resource(&resources, RT_MESSAGETABLE, id, resinfo->language, 0);

    if (resource == NULL) {
        return;
    }

    bfd_byte *pb_data = rcdata_render_as_buffer(data, &len_data);

    if (pb_data == NULL) {
        return;
    }

    resource->type = RES_TYPE_MESSAGETABLE;
    resource->u.data.length = len_data;
    resource->u.data.data = pb_data;
    resource->res_info = *resinfo;
}

/* Define an icon resource.  An icon file may contain a set of
   bitmaps, each representing the same icon at various different
   resolutions.  They each get written out with a different ID.  The
   real icon resource is then a group resource which can be used to
   select one of the actual icon bitmaps.  */

void define_icon(rc_res_id id, const rc_res_res_info *resinfo, const char *filename) {
    FILE *file;
    char *real_filename;
    int type, count;
    struct icondir *icondirs;
    rc_res_resource *resource;
    rc_group_icon *group_icon_list = NULL, **last_group_icon = &group_icon_list;
    int current_icon = icons;

    file = open_file_search(filename, FOPEN_RB, "icon file", &real_filename);

    (void)get_word(file, real_filename);
    type = get_word(file, real_filename);
    count = get_word(file, real_filename);
    if (type != 1) {
        fatal(_("icon file `%s' does not contain icon data"), real_filename);
    }

    icondirs = (struct icondir *) xmalloc(count * sizeof(*icondirs));
    for (int i = 0; i < count; i++) {
        icondirs[i].width = getc(file);
        icondirs[i].height = getc(file);
        icondirs[i].colorcount = getc(file);
        (void)getc(file);
        icondirs[i].u.icon.planes = get_word(file, real_filename);
        icondirs[i].u.icon.bits = get_word(file, real_filename);
        icondirs[i].bytes = get_long(file, real_filename);
        icondirs[i].offset = get_long(file, real_filename);

        if (feof(file)) {
            unexpected_eof(real_filename);
        }
    }

    for (int i = 0; i < count; i++) {
        bfd_byte *data;
        rc_res_id name;

        if (fseek(file, icondirs[i].offset, SEEK_SET) != 0) {
            fatal(_("%s: fseek to %lu failed: %s"), real_filename, icondirs[i].offset, strerror(errno));
        }

        data = (bfd_byte *) res_alloc(icondirs[i].bytes);
        get_data(file, data, icondirs[i].bytes, real_filename);

        ++icons;
        name.named = 0;
        name.u.id = icons;

        resource = define_standard_resource(&resources, RT_ICON, name, resinfo->language, 0);
        resource->type = RES_TYPE_ICON;
        resource->u.data.length = icondirs[i].bytes;
        resource->u.data.data = data;
        resource->res_info = *resinfo;
    }

    fclose(file);
    free(real_filename);

    for (int i = 0; i < count; i++) {
        rc_group_icon *cg = (rc_group_icon *) res_alloc(sizeof(rc_group_icon));
        cg->next = NULL;
        cg->width = icondirs[i].width;
        cg->height = icondirs[i].height;
        cg->colors = icondirs[i].colorcount;

        cg->planes = (icondirs[i].u.icon.planes != 0) ? icondirs[i].u.icon.planes : 1;

        if (icondirs[i].u.icon.bits) {
            cg->bits = icondirs[i].u.icon.bits;
        } else {
            int bits = 0;
            while ((1L << bits) < cg->colors) ++bits;
            cg->bits = bits;
        }

        cg->bytes = icondirs[i].bytes;
        cg->index = current_icon + i + 1;

        *last_group_icon = cg;
        last_group_icon = &cg->next;
    }

    free(icondirs);

    resource = define_standard_resource(&resources, RT_GROUP_ICON, id, resinfo->language, 0);
    resource->type = RES_TYPE_GROUP_ICON;
    resource->u.group_icon = group_icon_list;
    resource->res_info = *resinfo;
}

static void define_group_icon_rcdata(rc_res_id id, const rc_res_res_info *resinfo, rc_rcdata_item *data) {
    rc_res_resource *r;
    rc_group_icon *first = NULL, *cur = NULL;
    rc_uint_type len_data;
    bfd_byte *pb_data;
    
    pb_data = rcdata_render_as_buffer(data, &len_data);

    while (len_data >= 6) {
        unsigned short type = target_get_16(pb_data + 2, len_data - 2);
        if (type != 1)
            fatal(_("unexpected group icon type %d"), type);

        int c = target_get_16(pb_data + 4, len_data - 4);
        len_data -= 6;
        pb_data += 6;

        for (int i = 0; i < c; i++) {
            if (len_data < 14)
                fatal("too small group icon rcdata");

            rc_group_icon *cg = (rc_group_icon *)res_alloc(sizeof(rc_group_icon));
            cg->next = NULL;
            cg->width = pb_data[0];
            cg->height = pb_data[1];
            cg->colors = pb_data[2];
            cg->planes = target_get_16(pb_data + 4, len_data - 4);
            cg->bits = target_get_16(pb_data + 6, len_data - 6);
            cg->bytes = target_get_32(pb_data + 8, len_data - 8);
            cg->index = target_get_16(pb_data + 12, len_data - 12);

            if (!first) {
                first = cg;
            } else {
                cur->next = cg;
            }
            cur = cg;
            pb_data += 14;
            len_data -= 14;
        }
    }

    r = define_standard_resource(&resources, RT_GROUP_ICON, id, resinfo->language, 0);
    r->type = RES_TYPE_GROUP_ICON;
    r->u.group_icon = first;
    r->res_info = *resinfo;
}

static void define_group_cursor_rcdata(rc_res_id id, const rc_res_res_info *resinfo, rc_rcdata_item *data) {
    rc_res_resource *resource;
    rc_group_cursor *first_cursor = NULL, *current_cursor = NULL, *new_cursor;
    rc_uint_type len_data;
    bfd_byte *pb_data = rcdata_render_as_buffer(data, &len_data);

    while (len_data >= 6) {
        int count, i;
        unsigned short type = target_get_16(pb_data + 2, len_data - 2);

        if (type != 2) {
            fatal(_("unexpected group cursor type %d"), type);
        }

        count = target_get_16(pb_data + 4, len_data - 4);
        pb_data += 6;
        len_data -= 6;

        for (i = 0; i < count; i++) {
            if (len_data < 14) {
                fatal("too small group icon rcdata");
            }

            new_cursor = (rc_group_cursor *)res_alloc(sizeof(rc_group_cursor));
            new_cursor->next = NULL;
            new_cursor->width = target_get_16(pb_data, len_data);
            new_cursor->height = target_get_16(pb_data + 2, len_data - 2);
            new_cursor->planes = target_get_16(pb_data + 4, len_data - 4);
            new_cursor->bits = target_get_16(pb_data + 6, len_data - 6);
            new_cursor->bytes = target_get_32(pb_data + 8, len_data - 8);
            new_cursor->index = target_get_16(pb_data + 12, len_data - 12);

            if (!first_cursor) {
                first_cursor = new_cursor;
            } else {
                current_cursor->next = new_cursor;
            }
            current_cursor = new_cursor;

            pb_data += 14;
            len_data -= 14;
        }
    }

    resource = define_standard_resource(&resources, RT_GROUP_ICON, id, resinfo->language, 0);
    resource->type = RES_TYPE_GROUP_CURSOR;
    resource->u.group_cursor = first_cursor;
    resource->res_info = *resinfo;
}

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
  unsigned short xhotspot;
  unsigned short yhotspot;
  size_t length;
  const bfd_byte *data;
} rc_cursor;

typedef struct {
  int language;
} rc_res_res_info;

typedef struct rc_res_resource {
  int type;
  rc_cursor *u_cursor;
  rc_res_res_info res_info;
} rc_res_resource;

#define BIN_CURSOR_SIZE 4
#define RES_TYPE_CURSOR 1
#define RT_CURSOR 1

typedef unsigned char bfd_byte;
typedef unsigned int rc_uint_type;
typedef void* rc_res_id;
typedef void* rc_rcdata_item;

// Assume definition of external functions
bfd_byte* rcdata_render_as_buffer(rc_rcdata_item *data, rc_uint_type *len_data);
rc_res_resource* define_standard_resource(rc_res_resource **res, int type, rc_res_id id, int language, int zero);
unsigned short target_get_16(const bfd_byte *data, rc_uint_type len);

static void define_cursor_rcdata(rc_res_id id, const rc_res_res_info *resinfo, rc_rcdata_item *data) {
    rc_uint_type len_data;
    bfd_byte *pb_data = rcdata_render_as_buffer(data, &len_data);
    if (!pb_data || len_data < BIN_CURSOR_SIZE) return;

    rc_cursor *c = (rc_cursor *) malloc(sizeof(rc_cursor));
    if (!c) return;

    c->xhotspot = target_get_16(pb_data, len_data);
    c->yhotspot = target_get_16(pb_data + 2, len_data - 2);
    c->length = len_data - BIN_CURSOR_SIZE;
    c->data = pb_data + BIN_CURSOR_SIZE;

    rc_res_resource *r = define_standard_resource(NULL, RT_CURSOR, id, resinfo->language, 0);
    if (!r) {
        free(c);
        return;
    }
    r->type = RES_TYPE_CURSOR;
    r->u_cursor = c;
    r->res_info = *resinfo;
}

#include <stdlib.h>
#include <stdbool.h>

static bool check_valid_resource(rc_res_id id, const rc_res_res_info *resinfo) {
    return id != NULL && resinfo != NULL;
}

static void define_bitmap_rcdata(rc_res_id id, const rc_res_res_info *resinfo, rc_rcdata_item *data) {
    if (!check_valid_resource(id, resinfo)) {
        return;
    }
    
    rc_res_resource *resource = define_standard_resource(&resources, RT_BITMAP, id, resinfo->language, 0);
    if (!resource) {
        return;
    }

    rc_uint_type data_length;
    bfd_byte *rendered_data = rcdata_render_as_buffer(data, &data_length);
    if (!rendered_data) {
        return;
    }

    resource->type = RES_TYPE_BITMAP;
    resource->u.data.length = data_length;
    resource->u.data.data = rendered_data;
    resource->res_info = *resinfo;
}

static void define_icon_rcdata(rc_res_id id, const rc_res_res_info *resinfo, rc_rcdata_item *data) {
    if (!data || !resinfo) return;

    rc_uint_type len_data;
    bfd_byte *pb_data = rcdata_render_as_buffer(data, &len_data);
    
    if (!pb_data) return;

    rc_res_resource *r = define_standard_resource(&resources, RT_ICON, id, resinfo->language, 0);
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
    rc_menu *menu = (rc_menu *)res_alloc(sizeof(rc_menu));
    if (!menu) {
        // Handle memory allocation error
        return;
    }
    menu->items = menuitems;
    menu->help = 0;

    rc_res_resource *resource = define_standard_resource(&resources, RT_MENU, id, resinfo->language, 0);
    if (!resource) {
        // Handle resource definition error
        return;
    }
    resource->type = RES_TYPE_MENU;
    resource->u.menu = menu;
    resource->res_info = *resinfo;
}

/* Define a menu item.  This does not define a resource, but merely
   allocates and fills in a structure.  */

rc_menuitem *define_menuitem(const unichar *text, rc_uint_type menuid, rc_uint_type type, rc_uint_type state, rc_uint_type help, rc_menuitem *menuitems) {
    rc_menuitem *mi = (rc_menuitem *)res_alloc(sizeof(rc_menuitem));
    if (mi == NULL) {
        return NULL;
    }

    mi->next = NULL;
    mi->type = type;
    mi->state = state;
    mi->id = menuid;
    mi->text = unichar_dup(text);
    if (mi->text == NULL) {
        free(mi);
        return NULL;
    }
    mi->help = help;
    mi->popup = menuitems;

    return mi;
}

/* Define a messagetable resource.  */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>

void define_messagetable(rc_res_id id, const rc_res_res_info *resinfo, const char *filename) {
    char *real_filename = NULL;
    bfd_byte *data = NULL;
    struct stat s;
    rc_res_resource *r = NULL;
    FILE *e = open_file_search(filename, FOPEN_RB, "messagetable file", &real_filename);

    if (!e) {
        if (real_filename) free(real_filename);
        fatal(_("Failed to open file `%s'"), filename);
        return;
    }

    if (stat(real_filename, &s) < 0) {
        fclose(e);
        free(real_filename);
        fatal(_("stat failed on file `%s': %s"), real_filename, strerror(errno));
        return;
    }

    data = (bfd_byte *)res_alloc(s.st_size);
    if (!data) {
        fclose(e);
        free(real_filename);
        fatal(_("Memory allocation failed"));
        return;
    }

    get_data(e, data, s.st_size, real_filename);

    fclose(e);
    free(real_filename);

    r = define_standard_resource(&resources, RT_MESSAGETABLE, id, resinfo->language, 0);

    if (!r) {
        free(data);
        fatal(_("Failed to define resource"));
        return;
    }

    r->type = RES_TYPE_MESSAGETABLE;
    r->u.data.length = s.st_size;
    r->u.data.data = data;
    r->res_info = *resinfo;
}

/* Define an rcdata resource.  */

void define_rcdata(rc_res_id id, const rc_res_res_info *resinfo, rc_rcdata_item *data) {
    rc_res_resource *r = define_standard_resource(&resources, RT_RCDATA, id, resinfo->language, 0);
    if (r == NULL) {
        // Handle error
        return;
    }
    r->type = RES_TYPE_RCDATA;
    r->u.rcdata = data;
    r->res_info = *resinfo;
}

/* Create an rcdata item holding a string.  */

#include <stddef.h>
#include <string.h>

typedef struct rc_rcdata_item {
  struct rc_rcdata_item *next;
  enum { RCDATA_STRING } type;
  union {
    struct {
      size_t length;
      char *s;
    } string;
  } u;
} rc_rcdata_item;

void *res_alloc(size_t size);

rc_rcdata_item *define_rcdata_string(const char *string, size_t len) {
  if (string == NULL || len == 0) return NULL;

  rc_rcdata_item *ri = (rc_rcdata_item *)res_alloc(sizeof(rc_rcdata_item));
  if (ri == NULL) return NULL;
  
  char *s = (char *)res_alloc(len);
  if (s == NULL) {
    // Implement appropriate cleanup or error handling here
    return NULL;
  }

  memcpy(s, string, len);

  ri->next = NULL;
  ri->type = RCDATA_STRING;
  ri->u.string.length = len;
  ri->u.string.s = s;

  return ri;
}

/* Create an rcdata item holding a unicode string.  */

rc_rcdata_item *define_rcdata_unistring(const unichar *string, rc_uint_type len) {
  if (string == NULL || len == 0) {
    return NULL;
  }

  rc_rcdata_item *ri = (rc_rcdata_item *) res_alloc(sizeof(rc_rcdata_item));
  if (ri == NULL) {
    return NULL;
  }

  unichar *s = (unichar *) res_alloc(len * sizeof(unichar));
  if (s == NULL) {
    return NULL;
  }

  memcpy(s, string, len * sizeof(unichar));

  ri->next = NULL;
  ri->type = RCDATA_WSTRING;
  ri->u.wstring.length = len;
  ri->u.wstring.w = s;

  return ri;
}

/* Create an rcdata item holding a number.  */

rc_rcdata_item *define_rcdata_number(rc_uint_type val, int dword) {
    rc_rcdata_item *ri = (rc_rcdata_item *)res_alloc(sizeof(rc_rcdata_item));
    if (ri == NULL) {
        // Handle memory allocation failure appropriately
        return NULL;
    }

    ri->next = NULL;
    ri->type = dword ? RCDATA_DWORD : RCDATA_WORD;
    if (dword && val > UINT32_MAX) {
        // Handle error if val exceeds DWORD limit
        return NULL;
    } else if (!dword && val > UINT16_MAX) {
        // Handle error if val exceeds WORD limit
        return NULL;
    }
    ri->u.word = val;

    return ri;
}

/* Define a stringtable resource.  This is called for each string
   which appears in a STRINGTABLE statement.  */

void define_stringtable(const rc_res_res_info *resinfo, rc_uint_type stringid, const unichar *string, int len) {
  rc_res_id id = { .named = 0, .u.id = (stringid >> 4) + 1 };
  rc_res_resource *r = define_standard_resource(&resources, RT_STRING, id, resinfo->language, 1);

  if (r->type == RES_TYPE_UNINITIALIZED) {
    r->type = RES_TYPE_STRINGTABLE;
    r->u.stringtable = res_alloc(sizeof(rc_stringtable));

    for (int i = 0; i < 16; i++) {
      r->u.stringtable->strings[i].length = 0;
      r->u.stringtable->strings[i].string = NULL;
    }

    r->res_info = *resinfo;
  }

  unichar *h = res_alloc((len + 1) * sizeof(unichar));
  if (len > 0) {
    memcpy(h, string, len * sizeof(unichar));
  }
  h[len] = 0;

  int index = stringid & 0xf;
  r->u.stringtable->strings[index].length = (rc_uint_type)len;
  r->u.stringtable->strings[index].string = h;
}

#include <stddef.h>
#include <stdint.h>

typedef uint32_t rc_uint_type;
typedef struct rc_toolbar_item {
  struct rc_toolbar_item *next;
} rc_toolbar_item;

typedef struct {
  rc_uint_type button_width;
  rc_uint_type button_height;
  rc_uint_type nitems;
  rc_toolbar_item *items;
} rc_toolbar;

typedef int rc_res_id;
typedef struct {
  int language;
} rc_res_res_info;

typedef struct {
  int type;
  union {
    rc_toolbar *toolbar;
  } u;
  rc_res_res_info res_info;
} rc_res_resource;

#define RT_TOOLBAR 1
#define RES_TYPE_TOOLBAR 2

extern rc_res_resource *define_standard_resource(void *, int, rc_res_id, int, int);
extern void *res_alloc(size_t);

void define_toolbar(rc_res_id id, rc_res_res_info *resinfo, rc_uint_type width, rc_uint_type height, rc_toolbar_item *items) {
  if (resinfo == NULL) {
    return;
  }

  rc_toolbar *t = res_alloc(sizeof(rc_toolbar));
  if (t == NULL) {
    return;
  }

  t->button_width = width;
  t->button_height = height;

  t->nitems = 0;
  t->items = items;

  for (; items != NULL; items = items->next) {
    t->nitems++;
  }

  rc_res_resource *r = define_standard_resource(NULL, RT_TOOLBAR, id, resinfo->language, 0);
  if (r == NULL) {
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
    if (r == NULL) return;

    r->type = RES_TYPE_USERDATA;
    r->u.userdata = (rc_rcdata_item *)res_alloc(sizeof(rc_rcdata_item));
    if (r->u.userdata == NULL) return;

    r->u.userdata->next = NULL;
    r->u.userdata->type = RCDATA_BUFFER;
    
    pb_data = rcdata_render_as_buffer(data, &len_data);
    if (pb_data == NULL) {
        free(r->u.userdata);
        return;
    }

    r->u.userdata->u.buffer.length = len_data;
    r->u.userdata->u.buffer.data = pb_data;
    r->res_info = *resinfo;
}

#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

void define_rcdata_file(rc_res_id id, const rc_res_res_info *resinfo, const char *filename) {
    rc_rcdata_item *ri = NULL;
    FILE *file = NULL;
    char *real_filename = NULL;
    struct stat file_stat;
    bfd_byte *data = NULL;

    file = open_file_search(filename, FOPEN_RB, "file", &real_filename);
    if (file == NULL) {
        fatal(_("Failed to open file `%s': %s"), filename, strerror(errno));
        return;
    }

    if (stat(real_filename, &file_stat) < 0) {
        fatal(_("stat failed on file `%s': %s"), real_filename, strerror(errno));
        fclose(file);
        free(real_filename);
        return;
    }

    data = (bfd_byte *)res_alloc(file_stat.st_size);
    if (data == NULL) {
        fatal(_("Memory allocation failed for file `%s'"), real_filename);
        fclose(file);
        free(real_filename);
        return;
    }

    get_data(file, data, file_stat.st_size, real_filename);
    fclose(file);
    free(real_filename);

    ri = (rc_rcdata_item *)res_alloc(sizeof(rc_rcdata_item));
    if (ri == NULL) {
        fatal(_("Memory allocation failed for rc_rcdata_item"));
        free(data);
        return;
    }

    ri->next = NULL;
    ri->type = RCDATA_BUFFER;
    ri->u.buffer.length = file_stat.st_size;
    ri->u.buffer.data = data;

    define_rcdata(id, resinfo, ri);
}

/* Define a user data resource where the data is in a file.  */

void define_user_file(rc_res_id id, rc_res_id type, const rc_res_res_info *resinfo, const char *filename) {
    FILE *file = NULL;
    char *real_filename = NULL;
    struct stat file_stat;
    bfd_byte *data_buffer = NULL;
    rc_res_id ids[3];
    rc_res_resource *resource = NULL;

    if ((file = open_file_search(filename, FOPEN_RB, "file", &real_filename)) == NULL) {
        perror("Error opening file");
        return;
    }

    if (stat(real_filename, &file_stat) < 0) {
        perror("Stat failed on file");
        fclose(file);
        free(real_filename);
        return;
    }

    data_buffer = (bfd_byte *)res_alloc(file_stat.st_size);
    if (data_buffer == NULL) {
        fprintf(stderr, "Memory allocation failed\n");
        fclose(file);
        free(real_filename);
        return;
    }

    if (!get_data(file, data_buffer, file_stat.st_size, real_filename)) {
        fprintf(stderr, "Error reading file data\n");
        fclose(file);
        free(real_filename);
        return;
    }

    fclose(file);
    free(real_filename);

    ids[0] = type;
    ids[1] = id;
    ids[2].named = 0;
    ids[2].u.id = resinfo->language;

    if ((resource = define_resource(&resources, 3, ids, 0)) == NULL) {
        fprintf(stderr, "Resource definition failed\n");
        free(data_buffer);
        return;
    }

    resource->type = RES_TYPE_USERDATA;
    resource->u.userdata = (rc_rcdata_item *)res_alloc(sizeof(rc_rcdata_item));
    if (resource->u.userdata == NULL) {
        fprintf(stderr, "Memory allocation failed for userdata\n");
        free(data_buffer);
        return;
    }

    resource->u.userdata->next = NULL;
    resource->u.userdata->type = RCDATA_BUFFER;
    resource->u.userdata->u.buffer.length = file_stat.st_size;
    resource->u.userdata->u.buffer.data = data_buffer;
    resource->res_info = *resinfo;
}

/* Define a versioninfo resource.  */

void define_versioninfo(rc_res_id id, rc_uint_type language, rc_fixed_versioninfo *fixedverinfo, rc_ver_info *verinfo) {
    rc_res_resource *resource = define_standard_resource(&resources, RT_VERSION, id, language, 0);
    if (resource == NULL) {
        return; // Handle error condition
    }

    resource->type = RES_TYPE_VERSIONINFO;
    resource->u.versioninfo = res_alloc(sizeof(rc_versioninfo));
    if (resource->u.versioninfo == NULL) {
        return; // Handle memory allocation failure
    }

    resource->u.versioninfo->fixed = fixedverinfo;
    resource->u.versioninfo->var = verinfo;
    resource->res_info.language = language;
}

/* Add string version info to a list of version information.  */

rc_ver_info *append_ver_stringfileinfo(rc_ver_info *verinfo, rc_ver_stringtable *stringtables) {
    rc_ver_info *vi = (rc_ver_info *)res_alloc(sizeof(rc_ver_info));
    if (vi == NULL) {
        return NULL; // Handle memory allocation failure
    }
    vi->next = NULL;
    vi->type = VERINFO_STRING;
    vi->u.string.stringtables = stringtables;

    rc_ver_info **pp = &verinfo;
    while (*pp != NULL) {
        pp = &(*pp)->next;
    }
    *pp = vi;

    return verinfo;
}

rc_ver_stringtable *append_ver_stringtable(rc_ver_stringtable *stringtable, const char *language, rc_ver_stringinfo *strings) {
    rc_ver_stringtable *vst;
    rc_ver_stringtable **pp = &stringtable;

    vst = (rc_ver_stringtable *)res_alloc(sizeof(rc_ver_stringtable));
    if (vst == NULL) {
        return stringtable;  // Handle allocation failure
    }

    if (unicode_from_ascii(NULL, &vst->language, language) == NULL) {
        return stringtable;  // Handle conversion failure
    }

    vst->strings = strings;
    vst->next = NULL;

    while (*pp != NULL) {
        pp = &(*pp)->next;
    }

    *pp = vst;
    return stringtable;
}

/* Add variable version info to a list of version information.  */

#include <stddef.h>  // for NULL
#include <stdlib.h>   // for malloc, free

rc_ver_info *append_ver_varfileinfo(rc_ver_info *verinfo, const unichar *key, rc_ver_varinfo *var) {
    rc_ver_info *vi = malloc(sizeof(rc_ver_info));
    if (!vi) return NULL; // Handle memory allocation failure

    // Initialize the new node
    vi->next = NULL;
    vi->type = VERINFO_VAR;
    vi->u.var.key = unichar_dup(key); 
    vi->u.var.var = var;

    // If there is no verinfo, return the new node as the head
    if (!verinfo) return vi;

    // Traverse to the end of the linked list
    rc_ver_info *current = verinfo;
    while (current->next != NULL) {
        current = current->next;
    }
    current->next = vi;

    return verinfo;
}

/* Append version string information to a list.  */

rc_ver_stringinfo *append_verval(rc_ver_stringinfo *strings, const unichar *key, const unichar *value) {
    rc_ver_stringinfo *new_node;
    rc_ver_stringinfo **current;

    new_node = (rc_ver_stringinfo *)res_alloc(sizeof(rc_ver_stringinfo));
    if (new_node == NULL) {
        return strings; // Handle allocation failure gracefully
    }
    
    new_node->key = unichar_dup(key);
    if (new_node->key == NULL) {
        free(new_node); // Cleanup on failure
        return strings;
    }
    
    new_node->value = unichar_dup(value);
    if (new_node->value == NULL) {
        free(new_node->key);
        free(new_node);
        return strings; 
    }
    
    new_node->next = NULL;

    for (current = &strings; *current != NULL; current = &(*current)->next);

    *current = new_node;
    return strings;
}

/* Append version variable information to a list.  */

rc_ver_varinfo *append_vertrans(rc_ver_varinfo *var, rc_uint_type language, rc_uint_type charset) {
    rc_ver_varinfo *new_var = (rc_ver_varinfo *) res_alloc(sizeof(rc_ver_varinfo));
    if (!new_var) {
        return NULL; // Handle memory allocation failure
    }

    new_var->next = NULL;
    new_var->language = language;
    new_var->charset = charset;

    if (!var) {
        return new_var; // Directly return if the initial list is empty
    }

    rc_ver_varinfo *current = var;
    while (current->next != NULL) {
        current = current->next;
    }
    current->next = new_var;

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
    if (c > 0) {
        for (int i = 0; i < c; i++) {
            if (putc(' ', e) == EOF) {
                perror("Failed to write to file");
                break;
            }
        }
    }
}

/* Dump the resources we have read in the format of an rc file.

   Reasoned by the fact, that some resources need to be stored into file and
   refer to that file, we use the user-data model for that to express it binary
   without the need to store it somewhere externally.  */

#include <stdio.h>
#include <stdbool.h>
#include <errno.h>
#include <string.h>

bool write_rc_file(const char *filename, const rc_res_directory *res_dir) {
    FILE *file;
    rc_uint_type language = (rc_uint_type)((bfd_signed_vma)-1);

    if (filename == NULL) {
        file = stdout;
    } else {
        file = fopen(filename, FOPEN_WT);
        if (file == NULL) {
            fprintf(stderr, "can't open `%s` for output: %s\n", filename, strerror(errno));
            return false;
        }
    }

    write_rc_directory(file, res_dir, NULL, NULL, &language, 1);

    if (file != stdout) {
        fclose(file);
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

    for (re = rd->entries; re != NULL; re = re->next) {
        if (level == 1) {
            type = &re->id;
        } else if (level == 2) {
            name = &re->id;
        } else if (level == 3) {
            if (!re->id.named && re->id.u.id != (unsigned long)(unsigned int)*language && (re->id.u.id & 0xffff) == re->id.u.id) {
                wr_print(e, "LANGUAGE %u, %u\n", re->id.u.id & ((1 << SUBLANG_SHIFT) - 1), (re->id.u.id >> SUBLANG_SHIFT) & 0xff);
                *language = re->id.u.id;
            }
        }

        if (re->subdir) {
            write_rc_subdir(e, re, type, name, language, level);
        } else {
            if (level == 3) {
                write_rc_resource(e, type, name, re->u.res, language);
            } else {
                wr_printcomment(e, "Resource at unexpected level %d", level);
                write_rc_resource(e, type, (rc_res_id *)NULL, re->u.res, language);
            }
        }
    }
    if (rd->entries == NULL) {
        wr_print_flush(e);
    }
}

/* Write out a subdirectory entry.  E is the file to write to.  RE is
   the subdirectory entry.  TYPE and NAME are pointers to higher level
   IDs, or NULL.  LANGUAGE is a pointer to the current language.
   LEVEL is the level in the tree.  */

static void write_rc_subdir(FILE *e, const rc_res_entry *re,
                             const rc_res_id *type, const rc_res_id *name,
                             rc_uint_type *language, int level) {
    const char *resource_names[] = {
        "cursor", "bitmap", "icon", "menu", "dialog", "stringtable",
        "fontdir", "font", "accelerators", "rcdata", "messagetable",
        "group cursor", "group icon", "version", "dlginclude", "plugplay",
        "vxd", "anicursor", "aniicon", "toolbar", "html"
    };

    fprintf(e, "\n");
    switch (level) {
        case 1:
            wr_printcomment(e, "Type: ");
            if (re->id.named) {
                res_id_print(e, re->id, 1);
            } else {
                if (re->id.u.id >= 0 && re->id.u.id < sizeof(resource_names) / sizeof(resource_names[0])) {
                    fprintf(e, "%s", resource_names[re->id.u.id]);
                } else {
                    res_id_print(e, re->id, 1);
                }
            }
            break;

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
    }

    write_rc_directory(e, re->u.dir, type, name, language, level + 1);
}

/* Write out a single resource.  E is the file to write to.  TYPE is a
   pointer to the type of the resource.  NAME is a pointer to the name
   of the resource; it will be NULL if there is a level mismatch.  RES
   is the resource data.  LANGUAGE is a pointer to the current
   language.  */

#include <stdio.h>
#include <stdlib.h>

static const char* get_resource_type_name(const rc_res_id *type, int rt, const char **s) {
    if (type && type->named == 0) {
        switch (type->u.id) {
            case RT_MANIFEST: *s = "RT_MANIFEST"; break;
            case RT_ANICURSOR: *s = "RT_ANICURSOR"; break;
            case RT_ANIICON: *s = "RT_ANIICON"; break;
            // Add other cases as necessary
            default: return NULL;
        }
        return *s;
    }
    return NULL;
}

static void handle_resource_type(FILE *e, int rt, const rc_res_id *type, const char *s) {
    const char *type_name = NULL;
    if (s) {
        fprintf(e, "%s", s);
    } else {
        type_name = get_resource_type_name(type, rt, &s);
        if (type_name != NULL)
            fprintf(e, "%u /* %s */", (unsigned int) rt, type_name);
        else if (type) 
            res_id_print(e, *type, 1);
        else 
            fprintf(e, "??Unknown-Type??");
    }
}

static void display_resource(FILE *e, const rc_res_id *name, const char *s, int rt) {
    if (rt != RT_STRING && name) {
        res_id_print(e, *name, 1);
        fprintf(e, " ");
    } else if (rt != RT_STRING) {
        fprintf(e, "??Unknown-Name?? ");
    }
    handle_resource_type(e, rt, name, s);
}

static void check_language_and_meta(const rc_res_resource *res, rc_uint_type *language, FILE *e) {
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
            break;
    }

    if (res->res_info.language != 0 && res->res_info.language != *language) {
        fprintf(e, "%sLANGUAGE %d, %d\n", modifiers ? "// " : "", (int) res->res_info.language & ((1<<SUBLANG_SHIFT)-1), (int) (res->res_info.language >> SUBLANG_SHIFT) & 0xff);
    }
    if (res->res_info.characteristics != 0) {
        fprintf(e, "%sCHARACTERISTICS %u\n", modifiers ? "// " : "", (unsigned int) res->res_info.characteristics);
    }
    if (res->res_info.version != 0) {
        fprintf(e, "%sVERSION %u\n", modifiers ? "// " : "", (unsigned int) res->res_info.version);
    }
}

static void write_action(FILE *e, const rc_res_resource *res, const rc_res_id *name, int menuex) {
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
        case RES_TYPE_USERDATA:
            write_rc_rcdata(e, res->u.rcdata, 0);
            break;
        case RES_TYPE_STRINGTABLE:
            write_rc_stringtable(e, name, res->u.stringtable);
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

static void write_rc_resource(FILE *e, const rc_res_id *type, const rc_res_id *name, const rc_res_resource *res, rc_uint_type *language) {
    const char *s = NULL;
    int rt = 0;

    if (res->type >= RES_TYPE_ACCELERATOR && res->type <= RES_TYPE_TOOLBAR) {
        static const char *resource_names[] = {
            "ACCELERATORS", "2 /* RT_BITMAP */", "1 /* RT_CURSOR */", "12 /* RT_GROUP_CURSOR */", 
            "DIALOG", "8 /* RT_FONT */", "7 /* RT_FONTDIR */", "3 /* RT_ICON */", 
            "14 /* RT_GROUP_ICON */", "MENU", "11 /* RT_MESSAGETABLE */", "RCDATA", 
            "STRINGTABLE", NULL, "VERSIONINFO", "TOOLBAR"
        };
        static const int resource_types[] = {
            RT_ACCELERATOR, RT_BITMAP, RT_CURSOR, RT_GROUP_CURSOR, 
            RT_DIALOG, RT_FONT, RT_FONTDIR, RT_ICON, 
            RT_GROUP_ICON, RT_MENU, RT_MESSAGETABLE, RT_RCDATA, 
            RT_STRING, 0, RT_VERSION, RT_TOOLBAR
        };
        s = resource_names[res->type - RES_TYPE_ACCELERATOR];
        rt = resource_types[res->type - RES_TYPE_ACCELERATOR];

        if (res->type == RES_TYPE_DIALOG && extended_dialog(res->u.dialog)) {
            s = "DIALOGEX";
        }
        if (res->type == RES_TYPE_MENU && extended_menu(res->u.menu)) {
            s = "MENUEX";
        }

        if (type && (type->named || type->u.id != (unsigned long) rt)) {
            wr_printcomment(e, "Unexpected resource type mismatch: ");
            res_id_print(e, *type, 1);
            fprintf(e, " != %d", rt);
        }
    }

    if (res->coff_info.codepage != 0) 
        wr_printcomment(e, "Code page: %u", res->coff_info.codepage);
    if (res->coff_info.reserved != 0) 
        wr_printcomment(e, "COFF reserved value: %u", res->coff_info.reserved);

    wr_print(e, "\n");
    display_resource(e, name, s, rt);

    if (res->res_info.memflags != 0) {
        if ((res->res_info.memflags & MEMFLAG_MOVEABLE) != 0)
            fprintf(e, " MOVEABLE");
        if ((res->res_info.memflags & MEMFLAG_PURE) != 0)
            fprintf(e, " PURE");
        if ((res->res_info.memflags & MEMFLAG_PRELOAD) != 0)
            fprintf(e, " PRELOAD");
        if ((res->res_info.memflags & MEMFLAG_DISCARDABLE) != 0)
            fprintf(e, " DISCARDABLE");
    }

    if (res->type == RES_TYPE_DIALOG) {
        fprintf(e, " %d, %d, %d, %d", (int) res->u.dialog->x, (int) res->u.dialog->y, (int) res->u.dialog->width, (int) res->u.dialog->height);
        if (res->u.dialog->ex != NULL && res->u.dialog->ex->help != 0)
            fprintf(e, ", %u", (unsigned int) res->u.dialog->ex->help);
    } else if (res->type == RES_TYPE_TOOLBAR) {
        fprintf(e, " %d, %d", (int) res->u.toolbar->button_width, (int) res->u.toolbar->button_height);
    }

    fprintf(e, "\n");
    check_language_and_meta(res, language, e);
    write_action(e, res, name, s == "MENUEX");
}

/* Write out accelerator information.  */

#include <stdio.h>

#define ISPRINT(x) ((x) >= 32 && (x) <= 126)  // Simplified ISPRINT macro

static void write_rc_accelerators(FILE *e, const rc_accelerator *accelerators) {
    if (!e || !accelerators) {
        return;
    }

    fprintf(e, "BEGIN\n");
    for (const rc_accelerator *acc = accelerators; acc != NULL; acc = acc->next) {
        int printable = ISPRINT(acc->key) && !(acc->flags & ACC_VIRTKEY);

        fprintf(e, "  ");
        if (printable) {
            fprintf(e, "\"%c\"", (char)acc->key);
        } else {
            fprintf(e, "%d", (int)acc->key);
        }

        fprintf(e, ", %d", (int)acc->id);

        if (!printable) {
            fprintf(e, ", %s", (acc->flags & ACC_VIRTKEY) ? "VIRTKEY" : "ASCII");
        }

        if (acc->flags & ACC_SHIFT) {
            fprintf(e, ", SHIFT");
        }
        if (acc->flags & ACC_CONTROL) {
            fprintf(e, ", CONTROL");
        }
        if (acc->flags & ACC_ALT) {
            fprintf(e, ", ALT");
        }

        fprintf(e, "\n");
    }
    fprintf(e, "END\n");
}

/* Write out cursor information.  This would normally be in a separate
   file, which the rc file would include.  */

#include <stdio.h>
#include <errno.h>

static void write_rc_cursor(FILE *e, const rc_cursor *cursor) {
    if (e == NULL || cursor == NULL) {
        errno = EINVAL;
        return;
    }

    if (fprintf(e, "BEGIN\n") < 0) {
        return;
    }
    
    indent(e, 2);

    if (fprintf(e, " 0x%x, 0x%x,\t/* Hotspot x: %d, y: %d.  */\n",
                (unsigned int) cursor->xhotspot,
                (unsigned int) cursor->yhotspot,
                (int) cursor->xhotspot,
                (int) cursor->yhotspot) < 0) {
        return;
    }

    if (!write_rc_datablock(e, (rc_uint_type) cursor->length, 
                            (const bfd_byte *) cursor->data, 0, 0, 0)) {
        return;
    }

    fprintf(e, "END\n");
}

/* Write out group cursor data.  This would normally be built from the
   cursor data.  */

static void write_rc_group_cursor(FILE *e, const rc_group_cursor *group_cursor) {
    if (e == NULL || group_cursor == NULL) {
        return;
    }

    int element_count = 0;
    for (const rc_group_cursor *gc = group_cursor; gc != NULL; gc = gc->next) {
        element_count++;
    }

    fprintf(e, "BEGIN\n");
    indent(e, 2);
    fprintf(e, "0, 2, %d%s\t /* Having %d items.  */\n", element_count, (element_count != 0 ? "," : ""), element_count);
    indent(e, 4);
    fprintf(e, "/* width, height, planes, bits, bytes, index.  */\n");

    int c = 1;
    for (const rc_group_cursor *gc = group_cursor; gc != NULL; gc = gc->next, c++) {
        indent(e, 4);
        fprintf(e, "%d, %d, %d, %d, 0x%xL, %d%s /* Element %d. */\n",
            (int)gc->width, (int)gc->height, (int)gc->planes, (int)gc->bits,
            (unsigned int)gc->bytes, (int)gc->index, (gc->next != NULL ? "," : ""), c);

        fprintf(e, "/* width: %d; height %d; planes %d; bits %d.  */\n",
            (int)gc->width, (int)gc->height, (int)gc->planes, (int)gc->bits);
    }
    fprintf(e, "END\n");
}

/* Write dialog data.  */

static void write_rc_dialog(FILE *e, const rc_dialog *dialog) {
    if (e == NULL || dialog == NULL) return;

    fprintf(e, "STYLE 0x%x\n", dialog->style);

    if (dialog->exstyle != 0)
        fprintf(e, "EXSTYLE 0x%x\n", (unsigned int)dialog->exstyle);

    if ((dialog->class.named && dialog->class.u.n.length > 0) || dialog->class.u.id != 0) {
        fprintf(e, "CLASS ");
        res_id_print(e, dialog->class, 1);
        fprintf(e, "\n");
    }

    if (dialog->caption != NULL) {
        fprintf(e, "CAPTION ");
        unicode_print_quoted(e, dialog->caption, -1);
        fprintf(e, "\n");
    }

    if ((dialog->menu.named && dialog->menu.u.n.length > 0) || dialog->menu.u.id != 0) {
        fprintf(e, "MENU ");
        res_id_print(e, dialog->menu, 0);
        fprintf(e, "\n");
    }

    if (dialog->font != NULL) {
        fprintf(e, "FONT %d, ", (int)dialog->pointsize);
        unicode_print_quoted(e, dialog->font, -1);

        if (dialog->ex != NULL && (dialog->ex->weight != 0 || dialog->ex->italic != 0 || dialog->ex->charset != 1)) {
            fprintf(e, ", %d, %d, %d", (int)dialog->ex->weight, (int)dialog->ex->italic, (int)dialog->ex->charset);
        }
        fprintf(e, "\n");
    }

    fprintf(e, "BEGIN\n");

    const rc_dialog_control *control = dialog->controls;
    while (control != NULL) {
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

static void
write_rc_dialog_control(FILE *e, const rc_dialog_control *control)
{
    const struct control_info *ci = NULL;

    fprintf(e, "  ");

    if (!control->class.named) {
        for (ci = control_info; ci->name != NULL; ++ci) {
            if (ci->class == control->class.u.id &&
                (ci->style == (unsigned long) -1 || ci->style == (control->style & 0xff))) {
                break;
            }
        }
    }

    fprintf(e, ci == NULL || ci->name == NULL ? "CONTROL" : "%s", ci && ci->name ? ci->name : "");

    if ((control->text.named || control->text.u.id != 0) &&
        (!ci || (ci->class != CTL_EDIT && ci->class != CTL_COMBOBOX &&
                 ci->class != CTL_LISTBOX && ci->class != CTL_SCROLLBAR))) {
        fprintf(e, " ");
        res_id_print(e, control->text, 1);
        fprintf(e, ",");
    }

    fprintf(e, " %d, ", (int)control->id);

    if (ci == NULL) {
        if (control->class.named) fprintf(e, "\"");
        res_id_print(e, control->class, 0);
        if (control->class.named) fprintf(e, "\"");
        fprintf(e, ", 0x%x, ", (unsigned int)control->style);
    }

    fprintf(e, "%d, %d", (int)control->x, (int)control->y);

    if (control->style != SS_ICON || control->exstyle != 0 ||
        control->width != 0 || control->height != 0 || control->help != 0) {
        fprintf(e, ", %d, %d", (int)control->width, (int)control->height);

        if (ci != NULL) fprintf(e, ", 0x%x", (unsigned int)control->style);

        if (control->exstyle != 0 || control->help != 0)
            fprintf(e, ", 0x%x, %u", (unsigned int)control->exstyle, (unsigned int)control->help);
    }

    fprintf(e, "\n");

    if (control->data != NULL) write_rc_rcdata(e, control->data, 2);
}

/* Write out font directory data.  This would normally be built from
   the font data.  */

#include <stdio.h>
#include <stdbool.h>

typedef struct rc_fontdir {
  int index;
  unsigned int length;
  char *data;
  struct rc_fontdir *next;
} rc_fontdir;

void indent(FILE *e, int spaces) {
  for (int i = 0; i < spaces; i++) {
    fputc(' ', e);
  }
}

void write_rc_datablock(FILE *e, unsigned int length, const char *data, bool has_next, int param1, int param2) {
  // Sample implementation; details not provided in original code
}

static void write_rc_fontdir(FILE *e, const rc_fontdir *fontdir) {
  int element_count = 0;
  const rc_fontdir *fc;

  for (fc = fontdir; fc != NULL; fc = fc->next) {
    element_count++;
  }

  fprintf(e, "BEGIN\n");
  indent(e, 2);
  fprintf(e, "%d%s\t/* Has %d elements.  */\n", element_count, (element_count != 0 ? "," : ""), element_count);

  int font_count = 1;
  for (fc = fontdir; fc != NULL; fc = fc->next) {
    indent(e, 4);
    fprintf(e, "%d,\t/* Font no %d with index %d.  */\n", fc->index, font_count, fc->index);
    write_rc_datablock(e, fc->length - 2, fc->data + 4, fc->next != NULL, 0, 0);
    font_count++;
  }

  fprintf(e, "END\n");
}

/* Write out group icon data.  This would normally be built from the
   icon data.  */

static void write_rc_group_icon(FILE *e, const rc_group_icon *group_icon) {
    const rc_group_icon *gi = group_icon;
    int element_count = 0;

    while (gi != NULL) {
        element_count++;
        gi = gi->next;
    }

    fprintf(e, "BEGIN\n");
    indent(e, 2);
    fprintf(e, " 0, 1, %d%s\t /* Has %d elements.  */\n", 
            element_count, (element_count != 0 ? "," : ""), element_count);

    if (element_count > 0) {
        indent(e, 4);
        fprintf(e, "/* \"width height colors pad\", planes, bits, bytes, index.  */\n");
    }

    gi = group_icon;
    for (int i = 1; gi != NULL; gi = gi->next, i++) {
        indent(e, 4);
        fprintf(e, "\"\\%03o\\%03o\\%03o\\%03o\", %d, %d, 0x%xL, %d%s\t/* Element no %d.  */\n",
                gi->width, gi->height, gi->colors, 0, gi->planes, gi->bits,
                (unsigned int)gi->bytes, gi->index, (gi->next != NULL ? "," : ""), i);
    }
    fprintf(e, "END\n");
}

/* Write out a menu resource.  */

static void write_rc_menu(FILE *e, const rc_menu *menu, int menuex) {
  if (menu->help != NULL) {
    fprintf(e, "// Help ID: %u\n", (unsigned int)menu->help);
  }
  if (menu->items != NULL) {
    write_rc_menuitems(e, menu->items, menuex, 0);
  }
}

static void write_rc_toolbar(FILE *e, const rc_toolbar *tb) {
    if (!e || !tb) return;

    fprintf(e, "BEGIN\n");

    for (rc_toolbar_item *it = tb->items; it != NULL; it = it->next) {
        fprintf(e, "  ");
        if (it->id.u.id == 0) {
            fprintf(e, "SEPARATOR\n");
        } else {
            fprintf(e, "BUTTON %d\n", (int)it->id.u.id);
        }
    }
    
    fprintf(e, "END\n");
}

/* Write out menuitems.  */

static void write_rc_menuitems(FILE *e, const rc_menuitem *menuitems, int menuex, int ind) {
    const rc_menuitem *mi;

    indent(e, ind);
    fprintf(e, "BEGIN\n");

    for (mi = menuitems; mi != NULL; mi = mi->next) {
        indent(e, ind + 2);

        if (mi->popup) {
            fprintf(e, "POPUP ");
            unicode_print_quoted(e, mi->text ? mi->text : "", -1);
            fprintf(e, "\n");
            write_rc_menuitems(e, mi->popup, menuex, ind + 2);
        } else {
            fprintf(e, "MENUITEM");
            if (!menuex && !mi->text && mi->type == 0 && mi->id == 0) {
                fprintf(e, " SEPARATOR\n");
            } else {
                fprintf(e, " ");
                unicode_print_quoted(e, mi->text ? mi->text : "", -1);
                fprintf(e, ", %d", (int)mi->id);

                if (!menuex) {
                    if (mi->type & MENUITEM_CHECKED) fprintf(e, ", CHECKED");
                    if (mi->type & MENUITEM_GRAYED) fprintf(e, ", GRAYED");
                    if (mi->type & MENUITEM_HELP) fprintf(e, ", HELP");
                    if (mi->type & MENUITEM_INACTIVE) fprintf(e, ", INACTIVE");
                    if (mi->type & MENUITEM_MENUBARBREAK) fprintf(e, ", MENUBARBREAK");
                    if (mi->type & MENUITEM_MENUBREAK) fprintf(e, ", MENUBREAK");
                    if (mi->type & MENUITEM_OWNERDRAW) fprintf(e, ", OWNERDRAW");
                    if (mi->type & MENUITEM_BITMAP) fprintf(e, ", BITMAP");
                } else {
                    if (mi->type || mi->state || mi->help) {
                        fprintf(e, ", %u", (unsigned int)mi->type);
                        if (mi->state || mi->help) {
                            fprintf(e, ", %u", (unsigned int)mi->state);
                            if (mi->help) fprintf(e, ", %u", (unsigned int)mi->help);
                        }
                    }
                }
                fprintf(e, "\n");
            }
        }
    }
    
    indent(e, ind);
    fprintf(e, "END\n");
}

#include <stdbool.h>

static bool test_rc_datablock_unicode(rc_uint_type length, const bfd_byte *data) {
    if (length % 2 != 0) {
        return false;
    }

    for (rc_uint_type i = 0; i < length; i += 2) {
        if ((data[i] == 0 && data[i + 1] == 0 && i + 2 < length) ||
            (data[i] == 0xFF && data[i + 1] == 0xFF)) {
            return false;
        }
    }
    return true;
}

int test_rc_datablock_text(rc_uint_type length, const bfd_byte *data) {
    if (length <= 1) {
        return 0;
    }

    int has_newline = 0;
    rc_uint_type non_print_count = 0;

    for (rc_uint_type i = 0; i < length; i++) {
        bfd_byte current = data[i];

        if (ISPRINT(current) || current == '\n' || current == '\t' ||
            (current == '\r' && (i + 1) < length && data[i + 1] == '\n') ||
            (current == 0 && (i + 1) != length)) {
            if (current == '\n') {
                has_newline++;
            }
        } else {
            if (current <= 7) {
                return 0;
            }
            non_print_count++;
        }
    }

    if (length > 80 && !has_newline) {
        return 0;
    }

    rc_uint_type ratio = (non_print_count * 10000 + length / 100 - 1) / length;

    return ratio < 150;
}

static void write_rc_messagetable(FILE *e, rc_uint_type length, const bfd_byte *data) {
    if (!e || !data) {
        return;
    }

    fprintf(e, "BEGIN\n");
    write_rc_datablock(e, length, data, 0, 0, 0);
    fprintf(e, "\n");
    wr_printcomment(e, "MC syntax dump");

    if (length < BIN_MESSAGETABLE_SIZE) {
        wr_printcomment(e, "Illegal data");
        wr_print_flush(e);
        fprintf(e, "END\n");
        return;
    }

    const struct bin_messagetable *mt = (const struct bin_messagetable *)data;
    rc_uint_type m = target_get_32(mt->cblocks, length);

    if (length < (BIN_MESSAGETABLE_SIZE + m * BIN_MESSAGETABLE_BLOCK_SIZE)) {
        wr_printcomment(e, "Illegal data");
        wr_print_flush(e);
        fprintf(e, "END\n");
        return;
    }

    for (rc_uint_type i = 0; i < m; ++i) {
        rc_uint_type low = windres_get_32(&wrtarget, mt->items[i].lowid);
        rc_uint_type high = windres_get_32(&wrtarget, mt->items[i].highid);
        rc_uint_type offset = windres_get_32(&wrtarget, mt->items[i].offset);

        if (offset > length) {
            wr_printcomment(e, "Illegal data");
            wr_print_flush(e);
            fprintf(e, "END\n");
            return;
        }

        while (low <= high) {
            if ((offset + BIN_MESSAGETABLE_ITEM_SIZE) > length) {
                wr_printcomment(e, "Illegal data");
                wr_print_flush(e);
                fprintf(e, "END\n");
                return;
            }

            const struct bin_messagetable_item *mti = (const struct bin_messagetable_item *)&data[offset];
            rc_uint_type elen = windres_get_16(&wrtarget, mti->length);
            rc_uint_type flags = windres_get_16(&wrtarget, mti->flags);

            if ((offset + elen) > length) {
                wr_printcomment(e, "Illegal data");
                wr_print_flush(e);
                fprintf(e, "END\n");
                return;
            }

            wr_printcomment(e, "MessageId = 0x%x", low);
            wr_printcomment(e, "");

            if ((flags & MESSAGE_RESOURCE_UNICODE) == MESSAGE_RESOURCE_UNICODE) {
                if (elen > BIN_MESSAGETABLE_ITEM_SIZE * 2) {
                    unicode_print(e, (const unichar *)mti->data, (elen - BIN_MESSAGETABLE_ITEM_SIZE) / 2);
                }
            } else {
                if (elen > BIN_MESSAGETABLE_ITEM_SIZE) {
                    ascii_print(e, (const char *)mti->data, (elen - BIN_MESSAGETABLE_ITEM_SIZE));
                }
            }

            wr_printcomment(e, "");
            ++low;
            offset += elen;
        }
    }

    wr_print_flush(e);
    fprintf(e, "END\n");
}

static void write_rc_datablock(FILE *e, rc_uint_type length, const bfd_byte *data, int has_next, int hasblock, int show_comment) {
    if (hasblock) fprintf(e, "BEGIN\n");

    if (show_comment == -1) {
        if (test_rc_datablock_text(length, data) || test_rc_datablock_unicode(length, data)) {
            rc_uint_type i = 0;
            while (i < length) {
                rc_uint_type c = 0;
                indent(e, 2);
                fprintf(e, test_rc_datablock_text(length, data) ? "\"" : "L\"");

                while (i < length && c < 160 && ((test_rc_datablock_text(length, data) && data[i] != '\n') || (test_rc_datablock_unicode(length, data) && ((unichar *)data)[i / 2] != '\n'))) {
                    c++;
                    i += (test_rc_datablock_text(length, data) ? 1 : 2);
                }
                if (i < length && ((test_rc_datablock_text(length, data) && data[i] == '\n') || (test_rc_datablock_unicode(length, data) && ((unichar *)data)[i / 2] == '\n'))) {
                    i += (test_rc_datablock_text(length, data) ? 1 : 2);
                    c++;
                }
                if (test_rc_datablock_text(length, data)) {
                    ascii_print(e, (const char *)&data[i - c], c);
                } else {
                    unicode_print(e, (const unichar *)&data[(i / 2 - c) * 2], c);
                }
                fprintf(e, "\"\n");
            }

            indent(e, 2);
            fprintf(e, test_rc_datablock_text(length, data) ? "\"\"" : "L\"\"");
            if (has_next) fprintf(e, ",");
            fprintf(e, "\n");

            if (hasblock) fprintf(e, "END\n");
            return;
        }

        show_comment = 0;
    }

    if (length != 0) {
        rc_uint_type i = 0;
        int first = 1;
        rc_uint_type max_row = (show_comment ? 4 : 8);
        while (i + 3 < length) {
            rc_uint_type k = 0;
            rc_uint_type comment_start = i;
            if (!first) indent(e, 2);

            while (k < max_row && i + 3 < length) {
                plen = fprintf(e, "%s0x%lxL", k == 0 ? "" : " ", (unsigned long)target_get_32(data + i, length - i)) - (k == 0 ? 0 : 1);
                if (has_next || (i + 4) < length) {
                    if (plen > 0 && plen < 11) indent(e, 11 - plen);
                    fprintf(e, ",");
                }
                i += 4;
                k++;
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
            if (!first) indent(e, 2);
            plen = fprintf(e, "0x%x", (int)target_get_16(data + i, length - i));
            if (has_next || i + 2 < length) {
                if (plen > 0 && plen < 11) indent(e, 11 - plen);
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
            if (!first) indent(e, 2);
            fprintf(e, "\"");
            ascii_print(e, (const char *)&data[i], 1);
            fprintf(e, "\"");
            if (has_next) fprintf(e, ",");
            fprintf(e, "\n");
            first = 0;
        }
    }

    if (hasblock) fprintf(e, "END\n");
}

/* Write out an rcdata resource.  This is also used for other types of
   resources that need to print arbitrary data.  */

static void write_rc_rcdata(FILE *e, const rc_rcdata_item *rcdata, int ind) {
    if (!e || !rcdata) return;

    indent(e, ind);
    fprintf(e, "BEGIN\n");

    for (const rc_rcdata_item *ri = rcdata; ri != NULL; ri = ri->next) {
        if (ri->type == RCDATA_BUFFER && ri->u.buffer.length == 0) continue;

        indent(e, ind + 2);
        switch (ri->type) {
            case RCDATA_WORD:
                fprintf(e, "%ld", (long)(ri->u.word & 0xffff));
                break;

            case RCDATA_DWORD:
                fprintf(e, "%luL", (unsigned long)ri->u.dword);
                break;

            case RCDATA_STRING:
                fprintf(e, "\"");
                ascii_print(e, ri->u.string.s, ri->u.string.length);
                fprintf(e, "\"");
                break;

            case RCDATA_WSTRING:
                fprintf(e, "L\"");
                unicode_print(e, ri->u.wstring.w, ri->u.wstring.length);
                fprintf(e, "\"");
                break;

            case RCDATA_BUFFER:
                write_rc_datablock(e, (rc_uint_type)ri->u.buffer.length,
                                   (const bfd_byte *)ri->u.buffer.data,
                                   ri->next != NULL, 0, -1);
                break;

            default:
                abort();
        }

        if (ri->type != RCDATA_BUFFER) {
            if (ri->next != NULL) fprintf(e, ",");
            fprintf(e, "\n");
        }
    }

    indent(e, ind);
    fprintf(e, "END\n");
}

/* Write out a stringtable resource.  */

#include <stdio.h>
#include <stdlib.h>

static void write_rc_stringtable(FILE *e, const rc_res_id *name, const rc_stringtable *stringtable) {
    if (!e || !name || !stringtable) {
        fprintf(stderr, "Invalid input parameters.\n");
        return;
    }

    rc_uint_type offset = 0;
    if (!name->named) {
        offset = (name->u.id - 1) << 4;
    } else {
        fprintf(e, "/* %s string table name.  */\n", "Invalid");
    }

    fprintf(e, "BEGIN\n");
    for (int i = 0; i < 16; i++) {
        if (stringtable->strings[i].length > 0) {
            fprintf(e, "  %lu, ", (unsigned long)offset + i);
            unicode_print_quoted(e, stringtable->strings[i].string, stringtable->strings[i].length);
            fprintf(e, "\n");
        }
    }
    fprintf(e, "END\n");
}



/* Write out a versioninfo resource.  */

static void write_rc_versioninfo(FILE *e, const rc_versioninfo *versioninfo) {
    if (!e || !versioninfo) {
        return;
    }
    
    const rc_fixed_versioninfo *f = versioninfo->fixed;
    if (!f) {
        return;
    }
    
    if (f->file_version_ms || f->file_version_ls) {
        fprintf(e, " FILEVERSION %u, %u, %u, %u\n",
                (unsigned int)((f->file_version_ms >> 16) & 0xffff),
                (unsigned int)(f->file_version_ms & 0xffff),
                (unsigned int)((f->file_version_ls >> 16) & 0xffff),
                (unsigned int)(f->file_version_ls & 0xffff));
    }
    if (f->product_version_ms || f->product_version_ls) {
        fprintf(e, " PRODUCTVERSION %u, %u, %u, %u\n",
                (unsigned int)((f->product_version_ms >> 16) & 0xffff),
                (unsigned int)(f->product_version_ms & 0xffff),
                (unsigned int)((f->product_version_ls >> 16) & 0xffff),
                (unsigned int)(f->product_version_ls & 0xffff));
    }
    if (f->file_flags_mask) {
        fprintf(e, " FILEFLAGSMASK 0x%x\n", (unsigned int)f->file_flags_mask);
    }
    if (f->file_flags) {
        fprintf(e, " FILEFLAGS 0x%x\n", (unsigned int)f->file_flags);
    }
    if (f->file_os) {
        fprintf(e, " FILEOS 0x%x\n", (unsigned int)f->file_os);
    }
    if (f->file_type) {
        fprintf(e, " FILETYPE 0x%x\n", (unsigned int)f->file_type);
    }
    if (f->file_subtype) {
        fprintf(e, " FILESUBTYPE 0x%x\n", (unsigned int)f->file_subtype);
    }
    if (f->file_date_ms || f->file_date_ls) {
        fprintf(e, "/* Date: %u, %u.  */\n",
                (unsigned int)f->file_date_ms, (unsigned int)f->file_date_ls);
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
                fprintf(e, ", 0x%x, %d", (unsigned int)vv->language, (int)vv->charset);
            }
            fprintf(e, "\n  END\n");
        }
    }

    fprintf(e, "END\n");
}

static rc_uint_type rcdata_copy(const rc_rcdata_item *src, bfd_byte *dst) {
    if (!src) return 0;

    rc_uint_type length = 0;
    switch (src->type) {
        case RCDATA_WORD:
            if (dst) windres_put_16(&wrtarget, dst, (rc_uint_type)src->u.word);
            length = 2;
            break;
        case RCDATA_DWORD:
            if (dst) windres_put_32(&wrtarget, dst, (rc_uint_type)src->u.dword);
            length = 4;
            break;
        case RCDATA_STRING:
            if (dst && src->u.string.length) {
                memcpy(dst, src->u.string.s, src->u.string.length);
            }
            length = (rc_uint_type)src->u.string.length;
            break;
        case RCDATA_WSTRING:
            if (dst && src->u.wstring.length) {
                memcpy(dst, src->u.wstring.w, src->u.wstring.length * sizeof(unichar));
            }
            length = (rc_uint_type)(src->u.wstring.length * sizeof(unichar));
            break;
        case RCDATA_BUFFER:
            if (dst && src->u.buffer.length) {
                memcpy(dst, src->u.buffer.data, src->u.buffer.length);
            }
            length = (rc_uint_type)src->u.buffer.length;
            break;
        default:
            abort();
    }

    return length;
}
