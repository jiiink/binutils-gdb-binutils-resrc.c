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

static int count_args(const char *cmd)
{
    int count = 0;
    const char *s = cmd;
    
    while (*s) {
        if (*s == ' ')
            count++;
        s++;
    }
    
    return count + 1;
}

static void skip_spaces(char **s)
{
    while (**s == ' ' && **s != 0)
        (*s)++;
}

static char get_separator(char **s, int *in_quote)
{
    *in_quote = (**s == '\'' || **s == '"');
    if (*in_quote)
        return *(*s)++;
    return ' ';
}

static void extract_token(char **s, char sep)
{
    while (**s != sep && **s != 0)
        (*s)++;
}

static void parse_command_args(char *cmd, const char **argv)
{
    char *s = cmd;
    int i = 0;
    int in_quote;
    char sep;
    
    while (1) {
        skip_spaces(&s);
        
        if (*s == 0)
            break;
        
        sep = get_separator(&s, &in_quote);
        argv[i++] = s;
        
        extract_token(&s, sep);
        
        if (*s == 0)
            break;
        
        *s++ = 0;
        
        if (in_quote)
            s++;
    }
    
    argv[i] = NULL;
}

static int setup_output_redirection(const char *redir)
{
    int redir_handle = open(redir, O_WRONLY | O_TRUNC | O_CREAT, 0666);
    if (redir_handle == -1)
        fatal(_("can't open temporary file `%s': %s"), redir, strerror(errno));
    
    return redir_handle;
}

static int save_stdout(void)
{
    int stdout_save = dup(STDOUT_FILENO);
    if (stdout_save == -1)
        fatal(_("can't redirect stdout: `%s': %s"), "stdout", strerror(errno));
    
    return stdout_save;
}

static void redirect_stdout_to_file(int redir_handle)
{
    dup2(redir_handle, STDOUT_FILENO);
}

static void restore_stdout(int stdout_save)
{
    dup2(stdout_save, STDOUT_FILENO);
}

static int execute_command(const char **argv, char *temp_base, char **errmsg_fmt, char **errmsg_arg)
{
    return pexecute(argv[0], (char * const *) argv, program_name, temp_base,
                    errmsg_fmt, errmsg_arg, PEXECUTE_ONE | PEXECUTE_SEARCH);
}

static int check_execution_status(int pid, char *cmd)
{
    int wait_status;
    int retcode = 0;
    
    pid = pwait(pid, &wait_status, 0);
    
    if (pid == -1) {
        fatal(_("wait: %s"), strerror(errno));
        return 1;
    }
    
    if (WIFSIGNALED(wait_status)) {
        fatal(_("subprocess got fatal signal %d"), WTERMSIG(wait_status));
        return 1;
    }
    
    if (WIFEXITED(wait_status) && WEXITSTATUS(wait_status) != 0) {
        fatal(_("%s exited with status %d"), cmd, WEXITSTATUS(wait_status));
        return 1;
    }
    
    if (!WIFEXITED(wait_status))
        return 1;
    
    return retcode;
}

static int run_cmd(char *cmd, const char *redir)
{
    int arg_count = count_args(cmd);
    const char **argv = xmalloc(sizeof(char *) * (arg_count + 3));
    
    parse_command_args(cmd, argv);
    
    fflush(stdout);
    fflush(stderr);
    
    int redir_handle = setup_output_redirection(redir);
    int stdout_save = save_stdout();
    
    redirect_stdout_to_file(redir_handle);
    
    char *errmsg_fmt = NULL;
    char *errmsg_arg = NULL;
    char *temp_base = make_temp_file(NULL);
    
    int pid = execute_command(argv, temp_base, &errmsg_fmt, &errmsg_arg);
    free(argv);
    
    restore_stdout(stdout_save);
    close(redir_handle);
    
    if (pid == -1) {
        fatal("%s %s: %s", errmsg_fmt, errmsg_arg, strerror(errno));
        return 1;
    }
    
    return check_execution_status(pid, cmd);
}

static FILE *open_temp_file(const char *filename)
{
    FILE *file = fopen(filename, FOPEN_RT);
    if (file == NULL)
        fatal(_("can't open temporary file `%s': %s"), filename, strerror(errno));
    return file;
}

static FILE *open_pipe(const char *cmd)
{
    FILE *pipe = popen(cmd, FOPEN_RT);
    if (pipe == NULL)
        fatal(_("can't popen `%s': %s"), cmd, strerror(errno));
    return pipe;
}

static void print_verbose_message(const char *message, const char *detail)
{
    if (verbose)
        fprintf(stderr, message, detail);
}

static char *create_temp_filename(void)
{
    const char *IRC_EXTENSION = ".irc";
    char *fileprefix = make_temp_file(NULL);
    cpp_temp_file = (char *)xmalloc(strlen(fileprefix) + 5);
    sprintf(cpp_temp_file, "%s%s", fileprefix, IRC_EXTENSION);
    free(fileprefix);
    return cpp_temp_file;
}

static FILE *open_file_stream(char *cmd)
{
    create_temp_filename();
    
    if (run_cmd(cmd, cpp_temp_file))
        fatal(_("can't execute `%s': %s"), cmd, strerror(errno));
    
    FILE *file = open_temp_file(cpp_temp_file);
    print_verbose_message(_("Using temporary file `%s' to read preprocessor output\n"), cpp_temp_file);
    return file;
}

static FILE *open_pipe_stream(char *cmd)
{
    FILE *pipe = open_pipe(cmd);
    print_verbose_message(_("Using popen to read preprocessor output\n"), NULL);
    return pipe;
}

static FILE *open_input_stream(char *cmd)
{
    if (istream_type == ISTREAM_FILE)
        cpp_pipe = open_file_stream(cmd);
    else
        cpp_pipe = open_pipe_stream(cmd);
    
    xatexit(close_input_stream);
    return cpp_pipe;
}

/* Determine if FILENAME contains special characters that
   can cause problems unless the entire filename is quoted.  */

static int is_special_character(char c)
{
    return c == '&' || c == ' ' || c == '<' || c == '>' || c == '|' || c == '%';
}

static int is_stdin_indicator(const char *filename)
{
    return filename[0] == '-' && filename[1] == 0;
}

static int
filename_need_quotes (const char *filename)
{
  if (filename == NULL || is_stdin_indicator(filename))
    return 0;

  while (*filename != 0)
    {
      if (is_special_character(*filename))
        return 1;
      ++filename;
    }
  return 0;
}

/* Look for the preprocessor program.  */

static int has_path_separator(const char *cmd) {
#if defined (__DJGPP__) || defined (__CYGWIN__) || defined (_WIN32)
    return strchr(cmd, '\\') || strchr(cmd, '/');
#else
    return strchr(cmd, '/');
#endif
}

static int file_exists(char *cmd) {
    struct stat s;
    if (stat(cmd, &s) == 0)
        return 1;
#ifdef HAVE_EXECUTABLE_SUFFIX
    strcat(cmd, EXECUTABLE_SUFFIX);
    return stat(cmd, &s) == 0;
#else
    return 0;
#endif
}

static void report_verbose(const char *format, const char *cmd) {
    if (verbose)
        fprintf(stderr, format, cmd);
}

static char* add_quotes_if_needed(char *cmd, char *out) {
    if (!filename_need_quotes(cmd))
        return out;
    
    memmove(cmd + 1, cmd, out - cmd);
    cmd[0] = '"';
    out++;
    *out++ = '"';
    return out;
}

static void build_command_line(char *out, const char *preprocargs, 
                               const char *filename, const char *fnquotes) {
    sprintf(out, " %s %s %s%s%s",
            DEFAULT_PREPROCESSOR_ARGS, preprocargs, 
            fnquotes, filename, fnquotes);
}

static FILE *look_for_default(char *cmd, const char *prefix, int end_prefix,
                              const char *preprocargs, const char *filename) {
    const char *fnquotes = (filename_need_quotes(filename) ? "\"" : "");
    
    memcpy(cmd, prefix, end_prefix);
    char *out = stpcpy(cmd + end_prefix, DEFAULT_PREPROCESSOR_CMD);
    
    if (has_path_separator(cmd)) {
        if (!file_exists(cmd)) {
            report_verbose(_("Tried `%s'\n"), cmd);
            return NULL;
        }
    }
    
    out = add_quotes_if_needed(cmd, out);
    build_command_line(out, preprocargs, filename, fnquotes);
    
    report_verbose(_("Using `%s'\n"), cmd);
    
    cpp_pipe = open_input_stream(cmd);
    return cpp_pipe;
}

/* Read an rc file.  */

static void add_include_dir_from_path(const char *filename) {
    char *edit, *dir;
    
    if (strchr(filename, '/') == NULL && strchr(filename, '\\') == NULL)
        return;
    
    edit = dir = xmalloc(strlen(filename) + 3);
    
    if (filename[0] != '/' && filename[0] != '\\' && filename[1] != ':') {
        *edit++ = '.';
        *edit++ = '/';
    }
    
    edit = stpcpy(edit, filename);
    
    while (edit > dir && (edit[-1] != '\\' && edit[-1] != '/'))
        --edit;
    
    *--edit = 0;
    
    while ((edit = strchr(dir, '\\')) != NULL)
        *edit = '/';
    
    windres_add_include_dir(dir);
}

static char *build_preprocessor_command(const char *preprocessor, const char *preprocargs, 
                                       const char *filename, const char *fnquotes) {
    char *cmd = xmalloc(strlen(preprocessor) + strlen(preprocargs) + 
                       strlen(filename) + strlen(fnquotes) * 2 + 10);
    sprintf(cmd, "%s %s %s%s%s", preprocessor, preprocargs, fnquotes, filename, fnquotes);
    return cmd;
}

static int find_last_separator_type(const char *program_name, char **dash, char **slash) {
    char *cp;
    *dash = *slash = 0;
    
    for (cp = (char *)program_name; *cp; cp++) {
        if (*cp == '-')
            *dash = cp;
        if (*cp == '/' ||
#if defined (__DJGPP__) || defined (__CYGWIN__) || defined(_WIN32)
            *cp == ':' || *cp == '\\' ||
#endif
            0) {
            *slash = cp;
            *dash = 0;
        }
    }
    return 0;
}

static FILE *try_open_preprocessor(char *cmd, const char *program_name, 
                                  const char *preprocargs, const char *filename) {
    char *dash, *slash;
    FILE *pipe = 0;
    
    find_last_separator_type(program_name, &dash, &slash);
    
    if (dash) {
        pipe = look_for_default(cmd, program_name, dash - program_name + 1,
                              preprocargs, filename);
    }
    
    if (!pipe && slash) {
        pipe = look_for_default(cmd, program_name, slash - program_name + 1,
                              preprocargs, filename);
    }
    
    if (!pipe) {
        pipe = look_for_default(cmd, "", 0, preprocargs, filename);
    }
    
    return pipe;
}

static char *allocate_default_command(const char *program_name, const char *preprocargs, 
                                     const char *filename, const char *fnquotes) {
    size_t cmd_size = strlen(program_name) + strlen(DEFAULT_PREPROCESSOR_CMD) +
                     strlen(DEFAULT_PREPROCESSOR_ARGS) + strlen(preprocargs) +
                     strlen(filename) + strlen(fnquotes) * 2 + 10;
#ifdef HAVE_EXECUTABLE_SUFFIX
    cmd_size += strlen(EXECUTABLE_SUFFIX);
#endif
    return xmalloc(cmd_size);
}

static FILE *open_preprocessor_pipe(const char *preprocessor, const char *preprocargs,
                                   const char *filename, const char *fnquotes,
                                   const char *program_name) {
    char *cmd;
    FILE *pipe;
    
    if (preprocessor) {
        cmd = build_preprocessor_command(preprocessor, preprocargs, filename, fnquotes);
        pipe = open_input_stream(cmd);
    } else {
        cmd = allocate_default_command(program_name, preprocargs, filename, fnquotes);
        pipe = try_open_preprocessor(cmd, program_name, preprocargs, filename);
    }
    
    free(cmd);
    return pipe;
}

static void parse_rc_content(const char *filename, int language) {
    rc_filename = xstrdup(filename);
    rc_lineno = 1;
    
    if (language != -1)
        rcparse_set_language(language);
    
    yyparse();
    rcparse_discard_strings();
    close_input_stream();
    
    if (fontdirs != NULL)
        define_fontdirs();
    
    free(rc_filename);
    rc_filename = NULL;
}

rc_res_directory *
read_rc_file(const char *filename, const char *preprocessor,
            const char *preprocargs, int language, int use_temp_file) {
    const char *fnquotes;
    
    if (filename == NULL) {
        filename = "-";
    } else {
        add_include_dir_from_path(filename);
    }
    
    fnquotes = (filename_need_quotes(filename) ? "\"" : "");
    istream_type = (use_temp_file) ? ISTREAM_FILE : ISTREAM_PIPE;
    
    if (preprocargs == NULL)
        preprocargs = "";
    
    cpp_pipe = open_preprocessor_pipe(preprocessor, preprocargs, filename, 
                                     fnquotes, program_name);
    
    parse_rc_content(filename, language);
    
    return resources;
}

/* Close the input stream if it is open.  */

static void close_file_stream(void)
{
    if (cpp_pipe != NULL)
        fclose(cpp_pipe);

    if (cpp_temp_file != NULL)
    {
        int errno_save = errno;
        unlink(cpp_temp_file);
        errno = errno_save;
        free(cpp_temp_file);
    }
}

static void close_pipe_stream(void)
{
    if (cpp_pipe == NULL)
        return;

    int err = pclose(cpp_pipe);
    if (err != 0 || errno == ECHILD)
    {
        reset_stream_pointers();
        fatal(_("preprocessing failed."));
    }
}

static void reset_stream_pointers(void)
{
    cpp_pipe = NULL;
    cpp_temp_file = NULL;
}

static void close_input_stream(void)
{
    if (istream_type == ISTREAM_FILE)
        close_file_stream();
    else
        close_pipe_stream();

    reset_stream_pointers();
}

/* Report an error while reading an rc file.  */

#define ERROR_MESSAGE_FORMAT "%s:%d: %s"

void
yyerror (const char *msg)
{
  fatal (ERROR_MESSAGE_FORMAT, rc_filename, rc_lineno, msg);
}

/* Issue a warning while reading an rc file.  */

void
rcparse_warning (const char *msg)
{
  fprintf (stderr, "%s:%d: %s\n", rc_filename, rc_lineno, msg);
}

/* Die if we get an unexpected end of file.  */

static void unexpected_eof(const char *msg)
{
    fatal(_("%s: unexpected EOF"), msg);
}

/* Read a 16 bit word from a file.  The data is assumed to be little
   endian.  */

static int
get_word (FILE *e, const char *msg)
{
  int b1, b2;

  b1 = getc (e);
  b2 = getc (e);
  if (feof (e))
    unexpected_eof (msg);
  return ((b2 & 0xff) << 8) | (b1 & 0xff);
}

/* Read a 32 bit word from a file.  The data is assumed to be little
   endian.  */

static unsigned long
get_long (FILE *e, const char *msg)
{
  int bytes[4];
  
  for (int i = 0; i < 4; i++)
  {
    bytes[i] = getc (e);
  }
  
  if (feof (e))
    unexpected_eof (msg);
    
  unsigned long result = 0;
  for (int i = 3; i >= 0; i--)
  {
    result = (result << 8) | (bytes[i] & 0xff);
  }
  
  return result;
}

/* Read data from a file.  This is a wrapper to do error checking.  */

static void
get_data (FILE *e, bfd_byte *p, rc_uint_type c, const char *msg)
{
  rc_uint_type got = (rc_uint_type) fread (p, 1, c, e);
  
  if (got != c)
    {
      fatal (_("%s: read of %lu returned %lu"),
             msg, (unsigned long) c, (unsigned long) got);
    }
}

static rc_uint_type
target_get_16 (const void *p, size_t len)
{
  const size_t REQUIRED_BYTES = 2;
  
  if (len < REQUIRED_BYTES)
    fatal (_("not enough data"));
  return windres_get_16 (&wrtarget, p);
}

static rc_uint_type
target_get_32 (const void *p, size_t len)
{
  const size_t REQUIRED_SIZE = 4;
  
  if (len < REQUIRED_SIZE)
    fatal (_("not enough data"));
  return windres_get_32 (&wrtarget, p);
}

/* Define an accelerator resource.  */

void
define_accelerator (rc_res_id id, const rc_res_res_info *resinfo,
		    rc_accelerator *data)
{
  rc_res_resource *r;

  r = define_standard_resource (&resources, RT_ACCELERATOR, id,
				resinfo->language, 0);
  r->type = RES_TYPE_ACCELERATOR;
  r->u.acc = data;
  r->res_info = *resinfo;
}

/* Define a bitmap resource.  Bitmap data is stored in a file.  The
   first 14 bytes of the file are a standard header, which is not
   included in the resource data.  */

#define BITMAP_SKIP (14)

#define BITMAP_SKIP 14

static FILE *open_bitmap_file(const char *filename, char **real_filename)
{
    return open_file_search(filename, FOPEN_RB, "bitmap file", real_filename);
}

static void validate_bitmap_file(const char *real_filename, struct stat *s)
{
    if (stat(real_filename, s) < 0)
        fatal(_("stat failed on bitmap file `%s': %s"), real_filename,
              strerror(errno));
}

static bfd_byte *read_bitmap_data(FILE *e, const char *real_filename, off_t file_size)
{
    rc_uint_type data_size = file_size - BITMAP_SKIP;
    bfd_byte *data = (bfd_byte *)res_alloc(data_size);
    
    for (rc_uint_type i = 0; i < BITMAP_SKIP; i++)
        getc(e);
    
    get_data(e, data, data_size, real_filename);
    return data;
}

static rc_res_resource *create_bitmap_resource(rc_res_id id, const rc_res_res_info *resinfo)
{
    return define_standard_resource(&resources, RT_BITMAP, id,
                                   resinfo->language, 0);
}

static void setup_bitmap_resource(rc_res_resource *r, bfd_byte *data, 
                                 off_t file_size, const rc_res_res_info *resinfo)
{
    r->type = RES_TYPE_BITMAP;
    r->u.data.length = file_size - BITMAP_SKIP;
    r->u.data.data = data;
    r->res_info = *resinfo;
}

void define_bitmap(rc_res_id id, const rc_res_res_info *resinfo,
                  const char *filename)
{
    char *real_filename;
    FILE *e = open_bitmap_file(filename, &real_filename);
    
    struct stat s;
    validate_bitmap_file(real_filename, &s);
    
    bfd_byte *data = read_bitmap_data(e, real_filename, s.st_size);
    
    fclose(e);
    free(real_filename);
    
    rc_res_resource *r = create_bitmap_resource(id, resinfo);
    setup_bitmap_resource(r, data, s.st_size, resinfo);
}

/* Define a cursor resource.  A cursor file may contain a set of
   bitmaps, each representing the same cursor at various different
   resolutions.  They each get written out with a different ID.  The
   real cursor resource is then a group resource which can be used to
   select one of the actual cursors.  */

void define_cursor(rc_res_id id, const rc_res_res_info *resinfo, const char *filename)
{
    FILE *e;
    char *real_filename;
    int count;
    struct icondir *icondirs;
    int first_cursor;
    rc_res_resource *r;

    e = open_file_search(filename, FOPEN_RB, "cursor file", &real_filename);
    
    count = read_cursor_header(e, real_filename);
    icondirs = read_icon_directories(e, real_filename, count);
    
    first_cursor = cursors;
    define_individual_cursors(e, real_filename, icondirs, count, resinfo);
    
    fclose(e);
    free(real_filename);
    
    rc_group_cursor *first = create_cursor_group(icondirs, count, first_cursor);
    free(icondirs);
    
    r = define_standard_resource(&resources, RT_GROUP_CURSOR, id, resinfo->language, 0);
    r->type = RES_TYPE_GROUP_CURSOR;
    r->u.group_cursor = first;
    r->res_info = *resinfo;
}

static int read_cursor_header(FILE *e, const char *real_filename)
{
    get_word(e, real_filename);
    int type = get_word(e, real_filename);
    int count = get_word(e, real_filename);
    
    if (type != 2)
        fatal(_("cursor file `%s' does not contain cursor data"), real_filename);
    
    return count;
}

static struct icondir *read_icon_directories(FILE *e, const char *real_filename, int count)
{
    struct icondir *icondirs = (struct icondir *)xmalloc(count * sizeof *icondirs);
    
    for (int i = 0; i < count; i++)
    {
        read_single_icon_directory(e, real_filename, &icondirs[i]);
    }
    
    return icondirs;
}

static void read_single_icon_directory(FILE *e, const char *real_filename, struct icondir *icondir)
{
    icondir->width = getc(e);
    icondir->height = getc(e);
    icondir->colorcount = getc(e);
    getc(e);
    icondir->u.cursor.xhotspot = get_word(e, real_filename);
    icondir->u.cursor.yhotspot = get_word(e, real_filename);
    icondir->bytes = get_long(e, real_filename);
    icondir->offset = get_long(e, real_filename);
    
    if (feof(e))
        unexpected_eof(real_filename);
}

static void define_individual_cursors(FILE *e, const char *real_filename, 
                                     struct icondir *icondirs, int count, 
                                     const rc_res_res_info *resinfo)
{
    for (int i = 0; i < count; i++)
    {
        define_single_cursor(e, real_filename, &icondirs[i], resinfo);
    }
}

static void define_single_cursor(FILE *e, const char *real_filename,
                                struct icondir *icondir, const rc_res_res_info *resinfo)
{
    if (fseek(e, icondir->offset, SEEK_SET) != 0)
        fatal(_("%s: fseek to %lu failed: %s"), real_filename,
              icondir->offset, strerror(errno));
    
    bfd_byte *data = (bfd_byte *)res_alloc(icondir->bytes);
    get_data(e, data, icondir->bytes, real_filename);
    
    rc_cursor *c = (rc_cursor *)res_alloc(sizeof(rc_cursor));
    c->xhotspot = icondir->u.cursor.xhotspot;
    c->yhotspot = icondir->u.cursor.yhotspot;
    c->length = icondir->bytes;
    c->data = data;
    
    ++cursors;
    
    rc_res_id name;
    name.named = 0;
    name.u.id = cursors;
    
    rc_res_resource *r = define_standard_resource(&resources, RT_CURSOR, name,
                                                  resinfo->language, 0);
    r->type = RES_TYPE_CURSOR;
    r->u.cursor = c;
    r->res_info = *resinfo;
}

static rc_group_cursor *create_cursor_group(struct icondir *icondirs, int count, int first_cursor)
{
    rc_group_cursor *first = NULL;
    rc_group_cursor **pp = &first;
    
    for (int i = 0; i < count; i++)
    {
        rc_group_cursor *cg = create_single_cursor_group_entry(&icondirs[i], first_cursor + i + 1);
        *pp = cg;
        pp = &(*pp)->next;
    }
    
    return first;
}

static rc_group_cursor *create_single_cursor_group_entry(struct icondir *icondir, int index)
{
    #define DEFAULT_PLANES 1
    #define DEFAULT_BITS 1
    #define CURSOR_HEIGHT_MULTIPLIER 2
    #define CURSOR_BYTES_OVERHEAD 4
    
    rc_group_cursor *cg = (rc_group_cursor *)res_alloc(sizeof(rc_group_cursor));
    cg->next = NULL;
    cg->width = icondir->width;
    cg->height = CURSOR_HEIGHT_MULTIPLIER * icondir->height;
    cg->planes = DEFAULT_PLANES;
    cg->bits = DEFAULT_BITS;
    cg->bytes = icondir->bytes + CURSOR_BYTES_OVERHEAD;
    cg->index = index;
    
    return cg;
}

/* Define a dialog resource.  */

void
define_dialog (rc_res_id id, const rc_res_res_info *resinfo,
	       const rc_dialog *dialog)
{
  rc_dialog *copy;
  rc_res_resource *r;

  copy = (rc_dialog *) res_alloc (sizeof *copy);
  *copy = *dialog;

  r = define_standard_resource (&resources, RT_DIALOG, id,
				resinfo->language, 0);
  r->type = RES_TYPE_DIALOG;
  r->u.dialog = copy;
  r->res_info = *resinfo;
}

/* Define a dialog control.  This does not define a resource, but
   merely allocates and fills in a structure.  */

rc_dialog_control *
define_control (const rc_res_id iid, rc_uint_type id, rc_uint_type x,
		rc_uint_type y, rc_uint_type width, rc_uint_type height,
		const rc_res_id class, rc_uint_type style,
		rc_uint_type exstyle)
{
  rc_dialog_control *n;

  n = (rc_dialog_control *) res_alloc (sizeof (rc_dialog_control));
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

rc_dialog_control *
define_icon_control (rc_res_id iid, rc_uint_type id, rc_uint_type x,
		     rc_uint_type y, rc_uint_type style,
		     rc_uint_type exstyle, rc_uint_type help,
		     rc_rcdata_item *data, rc_dialog_ex *ex)
{
  rc_dialog_control *n;
  rc_res_id tid;
  rc_res_id cid;

  if (style == 0)
    style = SS_ICON | WS_CHILD | WS_VISIBLE;
  res_string_to_id (&tid, "");
  cid.named = 0;
  cid.u.id = CTL_STATIC;
  n = define_control (tid, id, x, y, 0, 0, cid, style, exstyle);
  n->text = iid;
  if (help && ! ex)
    rcparse_warning (_("help ID requires DIALOGEX"));
  if (data && ! ex)
    rcparse_warning (_("control data requires DIALOGEX"));
  n->help = help;
  n->data = data;

  return n;
}

/* Define a font resource.  */

void
define_font (rc_res_id id, const rc_res_res_info *resinfo,
	     const char *filename)
{
  FILE *e;
  char *real_filename;
  struct stat s;
  bfd_byte *data;
  rc_res_resource *r;
  rc_fontdir *fd;
  const char *device, *face;
  rc_fontdir **pp;

  e = open_file_search (filename, FOPEN_RB, "font file", &real_filename);

  if (stat (real_filename, &s) < 0)
    fatal (_("stat failed on font file `%s': %s"), real_filename,
	   strerror (errno));

  data = (bfd_byte *) res_alloc (s.st_size);

  get_data (e, data, s.st_size, real_filename);

  fclose (e);
  free (real_filename);

  r = define_standard_resource (&resources, RT_FONT, id,
				resinfo->language, 0);

  r->type = RES_TYPE_FONT;
  r->u.data.length = s.st_size;
  r->u.data.data = data;
  r->res_info = *resinfo;

  device = extract_string_from_offset(data, 44, s.st_size);
  face = extract_string_from_offset(data, 48, s.st_size);

  ++fonts;

  fd = create_fontdir_entry(data, device, face);

  for (pp = &fontdirs; *pp != NULL; pp = &(*pp)->next)
    ;
  *pp = fd;

  fontdirs_resinfo = *resinfo;
}

static const char *
extract_string_from_offset(bfd_byte *data, int base_index, size_t data_size)
{
  long offset = read_long_from_bytes(data, base_index);
  
  if (offset > 0 && offset < data_size)
    return (char *) data + offset;
  
  return "";
}

static long
read_long_from_bytes(bfd_byte *data, int base_index)
{
  return ((((((data[base_index + 3] << 8)
		| data[base_index + 2]) << 8)
	      | data[base_index + 1]) << 8)
	    | data[base_index]);
}

static rc_fontdir *
create_fontdir_entry(bfd_byte *data, const char *device, const char *face)
{
  #define FONT_HEADER_SIZE 56
  #define FONT_DATA_OFFSET 58
  
  long fontdatalength = FONT_DATA_OFFSET + strlen (device) + strlen (face);
  bfd_byte *fontdata = (bfd_byte *) res_alloc (fontdatalength);
  
  memcpy (fontdata, data, FONT_HEADER_SIZE);
  strcpy ((char *) fontdata + FONT_HEADER_SIZE, device);
  strcpy ((char *) fontdata + FONT_HEADER_SIZE + 1 + strlen (device), face);

  rc_fontdir *fd = (rc_fontdir *) res_alloc (sizeof (rc_fontdir));
  fd->next = NULL;
  fd->index = fonts;
  fd->length = fontdatalength;
  fd->data = fontdata;
  
  return fd;
}

static void
define_font_rcdata (rc_res_id id, const rc_res_res_info *resinfo,
		    rc_rcdata_item *data)
{
  rc_res_resource *r;
  rc_uint_type len_data;
  bfd_byte *pb_data;

  r = define_standard_resource (&resources, RT_FONT, id,
				resinfo->language, 0);

  pb_data = rcdata_render_as_buffer (data, &len_data);

  r->type = RES_TYPE_FONT;
  r->u.data.length = len_data;
  r->u.data.data = pb_data;
  r->res_info = *resinfo;
}

/* Define the fontdirs resource.  This is called after the entire rc
   file has been parsed, if any font resources were seen.  */

static void define_fontdirs(void)
{
    rc_res_resource *r;
    rc_res_id id;

    id.named = 0;
    id.u.id = 1;

    r = define_standard_resource(&resources, RT_FONTDIR, id, 0x409, 0);

    r->type = RES_TYPE_FONTDIR;
    r->u.fontdir = fontdirs;
    r->res_info = fontdirs_resinfo;
}

static rc_uint_type calculate_total_length(const rc_rcdata_item *data)
{
    rc_uint_type len = 0;
    const rc_rcdata_item *d;
    
    for (d = data; d != NULL; d = d->next)
        len += rcdata_copy(d, NULL);
    
    return len;
}

static void copy_all_items(const rc_rcdata_item *data, bfd_byte *buffer)
{
    const rc_rcdata_item *d;
    bfd_byte *pret = buffer;
    
    for (d = data; d != NULL; d = d->next)
        pret += rcdata_copy(d, pret);
}

static bfd_byte *rcdata_render_as_buffer(const rc_rcdata_item *data, rc_uint_type *plen)
{
    rc_uint_type len = calculate_total_length(data);
    bfd_byte *ret = NULL;
    
    if (len != 0)
    {
        ret = (bfd_byte *) res_alloc(len);
        copy_all_items(data, ret);
    }
    
    if (plen)
        *plen = len;
        
    return ret;
}

static rc_fontdir* create_fontdir_entry(bfd_byte *pb_data, rc_uint_type *off, rc_uint_type len_data)
{
    rc_fontdir *fd;
    size_t device_name_len;
    rc_uint_type safe_pos = *off;
    const struct bin_fontdir_item *bfi;

    bfi = (const struct bin_fontdir_item *) pb_data + *off;
    fd = (rc_fontdir *) res_alloc (sizeof (rc_fontdir));
    fd->index = target_get_16 (bfi->index, len_data - *off);
    fd->data = pb_data + *off;
    fd->next = NULL;
    
    *off += 56;
    device_name_len = strlen ((char *) bfi->device_name) + 1;
    *off += (rc_uint_type) device_name_len;
    *off += (rc_uint_type) strlen ((char *) bfi->device_name + device_name_len) + 1;
    fd->length = (*off - safe_pos);
    
    return fd;
}

static rc_fontdir* process_fontdir_data(bfd_byte *pb_data, rc_uint_type len_data)
{
    rc_fontdir *fd_first = NULL;
    rc_fontdir *fd_cur = NULL;
    rc_uint_type count;
    rc_uint_type off = 2;
    rc_uint_type i;
    
    if (!pb_data)
        return NULL;
        
    count = target_get_16 (pb_data, len_data);
    
    for (i = 0; i < count; i++)
    {
        rc_fontdir *fd = create_fontdir_entry(pb_data, &off, len_data);
        
        if (fd_first == NULL)
            fd_first = fd;
        else
            fd_cur->next = fd;
        fd_cur = fd;
    }
    
    return fd_first;
}

static void define_fontdir_rcdata (rc_res_id id, const rc_res_res_info *resinfo, rc_rcdata_item *data)
{
    rc_res_resource *r;
    rc_uint_type len_data;
    bfd_byte *pb_data;
    
    #define DEFAULT_LANG_ID 0x409
    
    r = define_standard_resource (&resources, RT_FONTDIR, id, DEFAULT_LANG_ID, 0);
    pb_data = rcdata_render_as_buffer (data, &len_data);
    
    r->type = RES_TYPE_FONTDIR;
    r->u.fontdir = process_fontdir_data(pb_data, len_data);
    r->res_info = *resinfo;
}

static void define_messagetable_rcdata (rc_res_id id, const rc_res_res_info *resinfo,
					rc_rcdata_item *data)
{
  rc_res_resource *r;
  rc_uint_type len_data;
  bfd_byte *pb_data;

  r = define_standard_resource (&resources, RT_MESSAGETABLE, id, resinfo->language, 0);

  pb_data = rcdata_render_as_buffer (data, &len_data);
  r->type = RES_TYPE_MESSAGETABLE;
  r->u.data.length = len_data;
  r->u.data.data = pb_data;
  r->res_info = *resinfo;
}

/* Define an icon resource.  An icon file may contain a set of
   bitmaps, each representing the same icon at various different
   resolutions.  They each get written out with a different ID.  The
   real icon resource is then a group resource which can be used to
   select one of the actual icon bitmaps.  */

void define_icon(rc_res_id id, const rc_res_res_info *resinfo, const char *filename)
{
    FILE *e;
    char *real_filename;
    struct icondir *icondirs;
    rc_group_icon *first;
    
    e = open_file_search(filename, FOPEN_RB, "icon file", &real_filename);
    
    int count = read_icon_header(e, real_filename);
    icondirs = read_icon_directory(e, real_filename, count);
    
    int first_icon = icons;
    define_individual_icons(e, real_filename, icondirs, count, resinfo);
    
    fclose(e);
    free(real_filename);
    
    first = create_icon_group(icondirs, count, first_icon);
    free(icondirs);
    
    define_group_icon_resource(id, resinfo, first);
}

static int read_icon_header(FILE *e, const char *real_filename)
{
    const int ICON_TYPE = 1;
    
    get_word(e, real_filename);
    int type = get_word(e, real_filename);
    int count = get_word(e, real_filename);
    
    if (type != ICON_TYPE)
        fatal(_("icon file `%s' does not contain icon data"), real_filename);
    
    return count;
}

static struct icondir *read_icon_directory(FILE *e, const char *real_filename, int count)
{
    struct icondir *icondirs = (struct icondir *)xmalloc(count * sizeof *icondirs);
    
    for (int i = 0; i < count; i++)
    {
        read_single_icon_entry(e, real_filename, &icondirs[i]);
    }
    
    return icondirs;
}

static void read_single_icon_entry(FILE *e, const char *real_filename, struct icondir *dir)
{
    dir->width = getc(e);
    dir->height = getc(e);
    dir->colorcount = getc(e);
    getc(e);
    dir->u.icon.planes = get_word(e, real_filename);
    dir->u.icon.bits = get_word(e, real_filename);
    dir->bytes = get_long(e, real_filename);
    dir->offset = get_long(e, real_filename);
    
    if (feof(e))
        unexpected_eof(real_filename);
}

static void define_individual_icons(FILE *e, const char *real_filename, 
                                   struct icondir *icondirs, int count, 
                                   const rc_res_res_info *resinfo)
{
    for (int i = 0; i < count; i++)
    {
        define_single_icon(e, real_filename, &icondirs[i], resinfo);
    }
}

static void define_single_icon(FILE *e, const char *real_filename, 
                              struct icondir *icondir, const rc_res_res_info *resinfo)
{
    if (fseek(e, icondir->offset, SEEK_SET) != 0)
        fatal(_("%s: fseek to %lu failed: %s"), real_filename,
              icondir->offset, strerror(errno));
    
    bfd_byte *data = (bfd_byte *)res_alloc(icondir->bytes);
    get_data(e, data, icondir->bytes, real_filename);
    
    ++icons;
    
    rc_res_id name;
    name.named = 0;
    name.u.id = icons;
    
    rc_res_resource *r = define_standard_resource(&resources, RT_ICON, name,
                                                  resinfo->language, 0);
    r->type = RES_TYPE_ICON;
    r->u.data.length = icondir->bytes;
    r->u.data.data = data;
    r->res_info = *resinfo;
}

static rc_group_icon *create_icon_group(struct icondir *icondirs, int count, int first_icon)
{
    rc_group_icon *first = NULL;
    rc_group_icon **pp = &first;
    
    for (int i = 0; i < count; i++)
    {
        rc_group_icon *cg = create_group_icon_entry(&icondirs[i], first_icon + i + 1);
        *pp = cg;
        pp = &(*pp)->next;
    }
    
    return first;
}

static rc_group_icon *create_group_icon_entry(struct icondir *icondir, int index)
{
    rc_group_icon *cg = (rc_group_icon *)res_alloc(sizeof(rc_group_icon));
    
    cg->next = NULL;
    cg->width = icondir->width;
    cg->height = icondir->height;
    cg->colors = icondir->colorcount;
    cg->planes = get_planes_value(icondir);
    cg->bits = get_bits_value(icondir, cg->colors);
    cg->bytes = icondir->bytes;
    cg->index = index;
    
    return cg;
}

static int get_planes_value(struct icondir *icondir)
{
    const int DEFAULT_PLANES = 1;
    return icondir->u.icon.planes ? icondir->u.icon.planes : DEFAULT_PLANES;
}

static int get_bits_value(struct icondir *icondir, int colors)
{
    if (icondir->u.icon.bits)
        return icondir->u.icon.bits;
    
    int bits = 0;
    while ((1L << bits) < colors)
        ++bits;
    
    return bits;
}

static void define_group_icon_resource(rc_res_id id, const rc_res_res_info *resinfo, 
                                      rc_group_icon *first)
{
    rc_res_resource *r = define_standard_resource(&resources, RT_GROUP_ICON, id,
                                                  resinfo->language, 0);
    r->type = RES_TYPE_GROUP_ICON;
    r->u.group_icon = first;
    r->res_info = *resinfo;
}

static void validate_group_icon_type(unsigned short type)
{
    if (type != 1)
        fatal(_("unexpected group icon type %d"), type);
}

static void validate_data_size(rc_uint_type len_data, rc_uint_type required_size, const char *error_msg)
{
    if (len_data < required_size)
        fatal(error_msg);
}

static rc_group_icon* create_group_icon(bfd_byte *pb_data, rc_uint_type len_data)
{
    rc_group_icon *cg = (rc_group_icon *) res_alloc(sizeof(rc_group_icon));
    cg->next = NULL;
    cg->width = pb_data[0];
    cg->height = pb_data[1];
    cg->colors = pb_data[2];
    cg->planes = target_get_16(pb_data + 4, len_data - 4);
    cg->bits = target_get_16(pb_data + 6, len_data - 6);
    cg->bytes = target_get_32(pb_data + 8, len_data - 8);
    cg->index = target_get_16(pb_data + 12, len_data - 12);
    return cg;
}

static void append_group_icon(rc_group_icon **first, rc_group_icon **cur, rc_group_icon *new_icon)
{
    if (!*first)
        *first = new_icon;
    else
        (*cur)->next = new_icon;
    *cur = new_icon;
}

static rc_group_icon* process_group_icons(bfd_byte *pb_data, rc_uint_type len_data, int count)
{
    #define ICON_ENTRY_SIZE 14
    rc_group_icon *first = NULL;
    rc_group_icon *cur = NULL;
    
    for (int i = 0; i < count; i++)
    {
        validate_data_size(len_data, ICON_ENTRY_SIZE, "too small group icon rcdata");
        rc_group_icon *cg = create_group_icon(pb_data, len_data);
        append_group_icon(&first, &cur, cg);
        pb_data += ICON_ENTRY_SIZE;
        len_data -= ICON_ENTRY_SIZE;
    }
    
    return first;
}

static rc_group_icon* parse_group_icon_data(bfd_byte **pb_data, rc_uint_type *len_data)
{
    #define HEADER_SIZE 6
    #define TYPE_OFFSET 2
    #define COUNT_OFFSET 4
    
    rc_group_icon *first = NULL;
    
    while (*len_data >= HEADER_SIZE)
    {
        unsigned short type = target_get_16(*pb_data + TYPE_OFFSET, *len_data - TYPE_OFFSET);
        validate_group_icon_type(type);
        
        int count = target_get_16(*pb_data + COUNT_OFFSET, *len_data - COUNT_OFFSET);
        *len_data -= HEADER_SIZE;
        *pb_data += HEADER_SIZE;
        
        rc_group_icon *icons = process_group_icons(*pb_data, *len_data, count);
        if (!first)
            first = icons;
        
        *pb_data += count * 14;
        *len_data -= count * 14;
    }
    
    return first;
}

static void define_group_icon_rcdata(rc_res_id id, const rc_res_res_info *resinfo, rc_rcdata_item *data)
{
    rc_uint_type len_data;
    bfd_byte *pb_data = rcdata_render_as_buffer(data, &len_data);
    
    rc_group_icon *first = parse_group_icon_data(&pb_data, &len_data);
    
    rc_res_resource *r = define_standard_resource(&resources, RT_GROUP_ICON, id, resinfo->language, 0);
    r->type = RES_TYPE_GROUP_ICON;
    r->u.group_icon = first;
    r->res_info = *resinfo;
}

static const int GROUP_CURSOR_HEADER_SIZE = 6;
static const int GROUP_CURSOR_ENTRY_SIZE = 14;
static const int EXPECTED_GROUP_TYPE = 2;

static void validate_group_type(unsigned short type)
{
    if (type != EXPECTED_GROUP_TYPE)
        fatal(_("unexpected group cursor type %d"), type);
}

static void validate_data_size(rc_uint_type len_data, int required_size, const char *error_msg)
{
    if (len_data < required_size)
        fatal(error_msg);
}

static rc_group_cursor* create_group_cursor(bfd_byte *pb_data, rc_uint_type len_data)
{
    rc_group_cursor *cg = (rc_group_cursor *) res_alloc(sizeof(rc_group_cursor));
    cg->next = NULL;
    cg->width = target_get_16(pb_data, len_data);
    cg->height = target_get_16(pb_data + 2, len_data - 2);
    cg->planes = target_get_16(pb_data + 4, len_data - 4);
    cg->bits = target_get_16(pb_data + 6, len_data - 6);
    cg->bytes = target_get_32(pb_data + 8, len_data - 8);
    cg->index = target_get_16(pb_data + 12, len_data - 12);
    return cg;
}

static void append_cursor(rc_group_cursor **first, rc_group_cursor **cur, rc_group_cursor *cg)
{
    if (!*first)
        *first = cg;
    else
        (*cur)->next = cg;
    *cur = cg;
}

static rc_group_cursor* parse_group_cursors(bfd_byte **pb_data, rc_uint_type *len_data)
{
    rc_group_cursor *first = NULL;
    rc_group_cursor *cur = NULL;
    
    unsigned short type = target_get_16(*pb_data + 2, *len_data - 2);
    validate_group_type(type);
    
    int count = target_get_16(*pb_data + 4, *len_data - 4);
    *len_data -= GROUP_CURSOR_HEADER_SIZE;
    *pb_data += GROUP_CURSOR_HEADER_SIZE;
    
    for (int i = 0; i < count; i++)
    {
        validate_data_size(*len_data, GROUP_CURSOR_ENTRY_SIZE, "too small group icon rcdata");
        rc_group_cursor *cg = create_group_cursor(*pb_data, *len_data);
        append_cursor(&first, &cur, cg);
        *pb_data += GROUP_CURSOR_ENTRY_SIZE;
        *len_data -= GROUP_CURSOR_ENTRY_SIZE;
    }
    
    return first;
}

static void define_group_cursor_rcdata(rc_res_id id, const rc_res_res_info *resinfo,
                                       rc_rcdata_item *data)
{
    rc_uint_type len_data;
    bfd_byte *pb_data = rcdata_render_as_buffer(data, &len_data);
    
    rc_group_cursor *first = NULL;
    
    while (len_data >= GROUP_CURSOR_HEADER_SIZE)
    {
        rc_group_cursor *group = parse_group_cursors(&pb_data, &len_data);
        if (!first)
            first = group;
    }
    
    rc_res_resource *r = define_standard_resource(&resources, RT_GROUP_ICON, id,
                                                  resinfo->language, 0);
    r->type = RES_TYPE_GROUP_CURSOR;
    r->u.group_cursor = first;
    r->res_info = *resinfo;
}

static rc_cursor* create_cursor_from_data(bfd_byte *pb_data, rc_uint_type len_data, rc_rcdata_item *data)
{
    rc_cursor *c = (rc_cursor *) res_alloc (sizeof (rc_cursor));
    c->xhotspot = target_get_16 (pb_data, len_data);
    c->yhotspot = target_get_16 (pb_data + 2, len_data - 2);
    c->length = len_data - BIN_CURSOR_SIZE;
    c->data = (const bfd_byte *) (data + BIN_CURSOR_SIZE);
    return c;
}

static void define_cursor_rcdata (rc_res_id id, const rc_res_res_info *resinfo, rc_rcdata_item *data)
{
    rc_uint_type len_data;
    bfd_byte *pb_data = rcdata_render_as_buffer (data, &len_data);
    
    rc_cursor *c = create_cursor_from_data(pb_data, len_data, data);
    
    rc_res_resource *r = define_standard_resource (&resources, RT_CURSOR, id, resinfo->language, 0);
    r->type = RES_TYPE_CURSOR;
    r->u.cursor = c;
    r->res_info = *resinfo;
}

static void
define_bitmap_rcdata (rc_res_id id, const rc_res_res_info *resinfo,
		      rc_rcdata_item *data)
{
  rc_res_resource *r;
  rc_uint_type len_data;
  bfd_byte *pb_data;

  pb_data = rcdata_render_as_buffer (data, &len_data);

  r = define_standard_resource (&resources, RT_BITMAP, id, resinfo->language, 0);
  r->type = RES_TYPE_BITMAP;
  r->u.data.length = len_data;
  r->u.data.data = pb_data;
  r->res_info = *resinfo;
}

static void
define_icon_rcdata (rc_res_id id, const rc_res_res_info *resinfo,
		    rc_rcdata_item *data)
{
  rc_res_resource *r;
  rc_uint_type len_data;
  bfd_byte *pb_data;

  pb_data = rcdata_render_as_buffer (data, &len_data);

  r = define_standard_resource (&resources, RT_ICON, id, resinfo->language, 0);
  r->type = RES_TYPE_ICON;
  r->u.data.length = len_data;
  r->u.data.data = pb_data;
  r->res_info = *resinfo;
}

/* Define a menu resource.  */

void
define_menu (rc_res_id id, const rc_res_res_info *resinfo,
	     rc_menuitem *menuitems)
{
  rc_menu *m;
  rc_res_resource *r;

  m = (rc_menu *) res_alloc (sizeof (rc_menu));
  m->items = menuitems;
  m->help = 0;

  r = define_standard_resource (&resources, RT_MENU, id, resinfo->language, 0);
  r->type = RES_TYPE_MENU;
  r->u.menu = m;
  r->res_info = *resinfo;
}

/* Define a menu item.  This does not define a resource, but merely
   allocates and fills in a structure.  */

rc_menuitem *
define_menuitem (const unichar *text, rc_uint_type menuid, rc_uint_type type,
		 rc_uint_type state, rc_uint_type help,
		 rc_menuitem *menuitems)
{
  rc_menuitem *mi;

  mi = (rc_menuitem *) res_alloc (sizeof (rc_menuitem));
  mi->next = NULL;
  mi->type = type;
  mi->state = state;
  mi->id = menuid;
  mi->text = unichar_dup (text);
  mi->help = help;
  mi->popup = menuitems;
  return mi;
}

/* Define a messagetable resource.  */

void
define_messagetable (rc_res_id id, const rc_res_res_info *resinfo,
		     const char *filename)
{
  bfd_byte *data = read_file_data(filename, "messagetable file");
  size_t data_size = get_last_file_size();
  
  rc_res_resource *r = define_standard_resource (&resources, RT_MESSAGETABLE, id,
				resinfo->language, 0);

  r->type = RES_TYPE_MESSAGETABLE;
  r->u.data.length = data_size;
  r->u.data.data = data;
  r->res_info = *resinfo;
}

static size_t last_file_size;

static size_t get_last_file_size(void)
{
  return last_file_size;
}

static bfd_byte* read_file_data(const char *filename, const char *file_type)
{
  char *real_filename;
  FILE *e = open_file_search (filename, FOPEN_RB, file_type, &real_filename);
  
  size_t file_size = get_file_size(real_filename, filename);
  bfd_byte *data = (bfd_byte *) res_alloc (file_size);
  
  get_data (e, data, file_size, real_filename);
  
  fclose (e);
  free (real_filename);
  
  last_file_size = file_size;
  return data;
}

static size_t get_file_size(const char *real_filename, const char *display_filename)
{
  struct stat s;
  if (stat (real_filename, &s) < 0)
    fatal (_("stat failed on bitmap file `%s': %s"), display_filename,
	   strerror (errno));
  return s.st_size;
}

/* Define an rcdata resource.  */

void define_rcdata(rc_res_id id, const rc_res_res_info *resinfo, rc_rcdata_item *data)
{
    rc_res_resource *r = define_standard_resource(&resources, RT_RCDATA, id, resinfo->language, 0);
    r->type = RES_TYPE_RCDATA;
    r->u.rcdata = data;
    r->res_info = *resinfo;
}

/* Create an rcdata item holding a string.  */

rc_rcdata_item *
define_rcdata_string (const char *string, rc_uint_type len)
{
  rc_rcdata_item *ri;
  char *s;

  ri = (rc_rcdata_item *) res_alloc (sizeof (rc_rcdata_item));
  ri->next = NULL;
  ri->type = RCDATA_STRING;
  ri->u.string.length = len;
  s = (char *) res_alloc (len);
  memcpy (s, string, len);
  ri->u.string.s = s;

  return ri;
}

/* Create an rcdata item holding a unicode string.  */

rc_rcdata_item *
define_rcdata_unistring (const unichar *string, rc_uint_type len)
{
  rc_rcdata_item *ri = (rc_rcdata_item *) res_alloc (sizeof (rc_rcdata_item));
  ri->next = NULL;
  ri->type = RCDATA_WSTRING;
  ri->u.wstring.length = len;
  
  size_t string_size = len * sizeof (unichar);
  unichar *s = (unichar *) res_alloc (string_size);
  memcpy (s, string, string_size);
  ri->u.wstring.w = s;

  return ri;
}

/* Create an rcdata item holding a number.  */

rc_rcdata_item *
define_rcdata_number (rc_uint_type val, int dword)
{
  rc_rcdata_item *ri;

  ri = (rc_rcdata_item *) res_alloc (sizeof (rc_rcdata_item));
  ri->next = NULL;
  ri->type = dword ? RCDATA_DWORD : RCDATA_WORD;
  ri->u.word = val;

  return ri;
}

/* Define a stringtable resource.  This is called for each string
   which appears in a STRINGTABLE statement.  */

void initialize_stringtable_entries(rc_stringtable *stringtable)
{
    int i;
    for (i = 0; i < 16; i++)
    {
        stringtable->strings[i].length = 0;
        stringtable->strings[i].string = NULL;
    }
}

rc_res_resource* get_or_create_stringtable_resource(const rc_res_res_info *resinfo, rc_uint_type stringid)
{
    rc_res_id id;
    rc_res_resource *r;
    
    id.named = 0;
    id.u.id = (stringid >> 4) + 1;
    r = define_standard_resource(&resources, RT_STRING, id, resinfo->language, 1);
    
    if (r->type == RES_TYPE_UNINITIALIZED)
    {
        r->type = RES_TYPE_STRINGTABLE;
        r->u.stringtable = (rc_stringtable *)res_alloc(sizeof(rc_stringtable));
        initialize_stringtable_entries(r->u.stringtable);
        r->res_info = *resinfo;
    }
    
    return r;
}

unichar* allocate_and_copy_string(const unichar *string, int len)
{
    unichar *h = (unichar *)res_alloc((len + 1) * sizeof(unichar));
    if (len)
        memcpy(h, string, len * sizeof(unichar));
    h[len] = 0;
    return h;
}

void define_stringtable(const rc_res_res_info *resinfo, rc_uint_type stringid, const unichar *string, int len)
{
    #define STRING_INDEX_MASK 0xf
    
    rc_res_resource *r = get_or_create_stringtable_resource(resinfo, stringid);
    unichar *h = allocate_and_copy_string(string, len);
    
    int string_index = stringid & STRING_INDEX_MASK;
    r->u.stringtable->strings[string_index].length = (rc_uint_type)len;
    r->u.stringtable->strings[string_index].string = h;
}

void define_toolbar(rc_res_id id, rc_res_res_info *resinfo, rc_uint_type width, rc_uint_type height,
                   rc_toolbar_item *items)
{
    rc_toolbar *t = (rc_toolbar *) res_alloc(sizeof(rc_toolbar));
    t->button_width = width;
    t->button_height = height;
    t->nitems = count_toolbar_items(items);
    t->items = items;
    
    rc_res_resource *r = define_standard_resource(&resources, RT_TOOLBAR, id, resinfo->language, 0);
    r->type = RES_TYPE_TOOLBAR;
    r->u.toolbar = t;
    r->res_info = *resinfo;
}

static rc_uint_type count_toolbar_items(rc_toolbar_item *items)
{
    rc_uint_type count = 0;
    while (items != NULL)
    {
        count++;
        items = items->next;
    }
    return count;
}

/* Define a user data resource where the data is in the rc file.  */

void
define_user_data (rc_res_id id, rc_res_id type,
		  const rc_res_res_info *resinfo,
		  rc_rcdata_item *data)
{
  if (handle_special_resource_type(id, type, resinfo, data))
    return;

  create_userdata_resource(id, type, resinfo, data);
}

static int
handle_special_resource_type(rc_res_id id, rc_res_id type,
                             const rc_res_res_info *resinfo,
                             rc_rcdata_item *data)
{
  if (type.named != 0)
    return 0;

  switch (type.u.id)
  {
  case RT_FONTDIR:
    define_fontdir_rcdata (id, resinfo, data);
    return 1;
  case RT_FONT:
    define_font_rcdata (id, resinfo, data);
    return 1;
  case RT_ICON:
    define_icon_rcdata (id, resinfo, data);
    return 1;
  case RT_BITMAP:
    define_bitmap_rcdata (id, resinfo, data);
    return 1;
  case RT_CURSOR:
    define_cursor_rcdata (id, resinfo, data);
    return 1;
  case RT_GROUP_ICON:
    define_group_icon_rcdata (id, resinfo, data);
    return 1;
  case RT_GROUP_CURSOR:
    define_group_cursor_rcdata (id, resinfo, data);
    return 1;
  case RT_MESSAGETABLE:
    define_messagetable_rcdata (id, resinfo, data);
    return 1;
  default:
    return 0;
  }
}

static void
create_userdata_resource(rc_res_id id, rc_res_id type,
                        const rc_res_res_info *resinfo,
                        rc_rcdata_item *data)
{
  rc_res_id ids[3];
  rc_res_resource *r;
  
  ids[0] = type;
  ids[1] = id;
  ids[2].named = 0;
  ids[2].u.id = resinfo->language;

  r = define_resource (&resources, 3, ids, 0);
  r->type = RES_TYPE_USERDATA;
  r->u.userdata = allocate_userdata_item(data);
  r->res_info = *resinfo;
}

static rc_rcdata_item *
allocate_userdata_item(rc_rcdata_item *data)
{
  rc_rcdata_item *userdata;
  bfd_byte *pb_data;
  rc_uint_type len_data;

  userdata = (rc_rcdata_item *) res_alloc (sizeof (rc_rcdata_item));
  userdata->next = NULL;
  userdata->type = RCDATA_BUFFER;
  
  pb_data = rcdata_render_as_buffer (data, &len_data);
  userdata->u.buffer.length = len_data;
  userdata->u.buffer.data = pb_data;
  
  return userdata;
}

void
define_rcdata_file (rc_res_id id, const rc_res_res_info *resinfo,
		    const char *filename)
{
  FILE *e;
  char *real_filename;
  struct stat s;
  bfd_byte *data;

  e = open_file_search (filename, FOPEN_RB, "file", &real_filename);

  if (stat (real_filename, &s) < 0)
    fatal (_("stat failed on file `%s': %s"), real_filename,
	   strerror (errno));

  data = (bfd_byte *) res_alloc (s.st_size);
  get_data (e, data, s.st_size, real_filename);
  fclose (e);
  free (real_filename);

  define_rcdata (id, resinfo, create_buffer_item (data, s.st_size));
}

static rc_rcdata_item *
create_buffer_item (bfd_byte *data, size_t length)
{
  rc_rcdata_item *ri = (rc_rcdata_item *) res_alloc (sizeof (rc_rcdata_item));
  ri->next = NULL;
  ri->type = RCDATA_BUFFER;
  ri->u.buffer.length = length;
  ri->u.buffer.data = data;
  return ri;
}

/* Define a user data resource where the data is in a file.  */

void
define_user_file (rc_res_id id, rc_res_id type,
		  const rc_res_res_info *resinfo, const char *filename)
{
  bfd_byte *data = read_file_data(filename);
  size_t file_size = get_last_file_size();
  rc_res_resource *r = create_resource(type, id, resinfo);
  attach_userdata_to_resource(r, data, file_size, resinfo);
}

static bfd_byte *
read_file_data(const char *filename)
{
  char *real_filename;
  FILE *e = open_file_search(filename, FOPEN_RB, "file", &real_filename);
  
  struct stat s;
  if (stat(real_filename, &s) < 0)
    fatal(_("stat failed on file `%s': %s"), real_filename, strerror(errno));
  
  bfd_byte *data = (bfd_byte *) res_alloc(s.st_size);
  get_data(e, data, s.st_size, real_filename);
  
  fclose(e);
  free(real_filename);
  
  last_file_size = s.st_size;
  return data;
}

static size_t last_file_size;

static size_t
get_last_file_size(void)
{
  return last_file_size;
}

static rc_res_resource *
create_resource(rc_res_id type, rc_res_id id, const rc_res_res_info *resinfo)
{
  rc_res_id ids[3];
  ids[0] = type;
  ids[1] = id;
  ids[2].named = 0;
  ids[2].u.id = resinfo->language;
  
  return define_resource(&resources, 3, ids, 0);
}

static void
attach_userdata_to_resource(rc_res_resource *r, bfd_byte *data, 
                           size_t data_size, const rc_res_res_info *resinfo)
{
  r->type = RES_TYPE_USERDATA;
  r->u.userdata = (rc_rcdata_item *) res_alloc(sizeof(rc_rcdata_item));
  r->u.userdata->next = NULL;
  r->u.userdata->type = RCDATA_BUFFER;
  r->u.userdata->u.buffer.length = data_size;
  r->u.userdata->u.buffer.data = data;
  r->res_info = *resinfo;
}

/* Define a versioninfo resource.  */

void define_versioninfo(rc_res_id id, rc_uint_type language,
                        rc_fixed_versioninfo *fixedverinfo,
                        rc_ver_info *verinfo)
{
    rc_res_resource *r = define_standard_resource(&resources, RT_VERSION, id, language, 0);
    
    r->type = RES_TYPE_VERSIONINFO;
    r->u.versioninfo = (rc_versioninfo *)res_alloc(sizeof(rc_versioninfo));
    r->u.versioninfo->fixed = fixedverinfo;
    r->u.versioninfo->var = verinfo;
    r->res_info.language = language;
}

/* Add string version info to a list of version information.  */

rc_ver_info *
append_ver_stringfileinfo (rc_ver_info *verinfo,
			   rc_ver_stringtable *stringtables)
{
  rc_ver_info *vi = (rc_ver_info *) res_alloc (sizeof (rc_ver_info));
  vi->next = NULL;
  vi->type = VERINFO_STRING;
  vi->u.string.stringtables = stringtables;

  rc_ver_info **pp = &verinfo;
  while (*pp != NULL)
    pp = &(*pp)->next;
  *pp = vi;

  return verinfo;
}

rc_ver_stringtable *
append_ver_stringtable (rc_ver_stringtable *stringtable,
			const char *language,
			rc_ver_stringinfo *strings)
{
  rc_ver_stringtable *vst = (rc_ver_stringtable *) res_alloc (sizeof (rc_ver_stringtable));
  vst->next = NULL;
  unicode_from_ascii ((rc_uint_type *) NULL, &vst->language, language);
  vst->strings = strings;

  rc_ver_stringtable **pp = &stringtable;
  while (*pp != NULL)
    pp = &(*pp)->next;
  *pp = vst;

  return stringtable;
}

/* Add variable version info to a list of version information.  */

rc_ver_info *
append_ver_varfileinfo (rc_ver_info *verinfo, const unichar *key,
			rc_ver_varinfo *var)
{
  rc_ver_info *vi = (rc_ver_info *) res_alloc (sizeof *vi);
  vi->next = NULL;
  vi->type = VERINFO_VAR;
  vi->u.var.key = unichar_dup (key);
  vi->u.var.var = var;

  rc_ver_info **pp = &verinfo;
  while (*pp != NULL)
    pp = &(*pp)->next;
  *pp = vi;

  return verinfo;
}

/* Append version string information to a list.  */

rc_ver_stringinfo *
append_verval (rc_ver_stringinfo *strings, const unichar *key,
	       const unichar *value)
{
  rc_ver_stringinfo *vs = (rc_ver_stringinfo *) res_alloc (sizeof (rc_ver_stringinfo));
  vs->next = NULL;
  vs->key = unichar_dup (key);
  vs->value = unichar_dup (value);

  rc_ver_stringinfo **pp = &strings;
  while (*pp != NULL)
    pp = &(*pp)->next;
  *pp = vs;

  return strings;
}

/* Append version variable information to a list.  */

rc_ver_varinfo *
append_vertrans (rc_ver_varinfo *var, rc_uint_type language,
		 rc_uint_type charset)
{
  rc_ver_varinfo *vv = (rc_ver_varinfo *) res_alloc (sizeof (rc_ver_varinfo));
  vv->next = NULL;
  vv->language = language;
  vv->charset = charset;

  rc_ver_varinfo **pp = &var;
  while (*pp != NULL)
    pp = &(*pp)->next;
  *pp = vv;

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

static void
indent (FILE *e, int c)
{
  int i;

  for (i = 0; i < c; i++)
    putc (' ', e);
}

/* Dump the resources we have read in the format of an rc file.

   Reasoned by the fact, that some resources need to be stored into file and
   refer to that file, we use the user-data model for that to express it binary
   without the need to store it somewhere externally.  */

bool
write_rc_file (const char *filename, const rc_res_directory *res_dir)
{
  FILE *e;
  rc_uint_type language;

  if (filename == NULL)
    e = stdout;
  else
    {
      e = fopen (filename, FOPEN_WT);
      if (e == NULL)
	{
	  non_fatal (_("can't open `%s' for output: %s"),
		     filename, strerror (errno));
	  return false;
	}
    }

  language = (rc_uint_type) ((bfd_signed_vma) -1);
  write_rc_directory (e, res_dir, (const rc_res_id *) NULL,
		      (const rc_res_id *) NULL, &language, 1);
  return true;
}

/* Write out a directory.  E is the file to write to.  RD is the
   directory.  TYPE is a pointer to the level 1 ID which serves as the
   resource type.  NAME is a pointer to the level 2 ID which serves as
   an individual resource name.  LANGUAGE is a pointer to the current
   language.  LEVEL is the level in the tree.  */

static void print_coff_information(FILE *e, const rc_res_directory *rd)
{
    if (rd->time == 0 && rd->characteristics == 0 && rd->major == 0 && rd->minor == 0)
        return;
    
    wr_printcomment(e, "COFF information not part of RC");
    if (rd->time != 0)
        wr_printcomment(e, "Time stamp: %u", rd->time);
    if (rd->characteristics != 0)
        wr_printcomment(e, "Characteristics: %u", rd->characteristics);
    if (rd->major != 0 || rd->minor != 0)
        wr_printcomment(e, "Version major:%d minor:%d", rd->major, rd->minor);
}

static void update_language_if_needed(FILE *e, const rc_res_id *id, rc_uint_type *language)
{
    if (!id->named && 
        id->u.id != (unsigned long)(unsigned int)*language &&
        (id->u.id & 0xffff) == id->u.id)
    {
        wr_print(e, "LANGUAGE %u, %u\n",
                id->u.id & ((1 << SUBLANG_SHIFT) - 1),
                (id->u.id >> SUBLANG_SHIFT) & 0xff);
        *language = id->u.id;
    }
}

static void process_resource_entry(FILE *e, const rc_res_entry *re, 
                                  const rc_res_id **type, const rc_res_id **name,
                                  rc_uint_type *language, int level)
{
    switch (level)
    {
    case 1:
        *type = &re->id;
        break;
    case 2:
        *name = &re->id;
        break;
    case 3:
        update_language_if_needed(e, &re->id, language);
        break;
    default:
        break;
    }
}

static void write_entry_resource(FILE *e, const rc_res_entry *re,
                                const rc_res_id *type, const rc_res_id *name,
                                rc_uint_type *language, int level)
{
    if (level == 3)
    {
        write_rc_resource(e, type, name, re->u.res, language);
    }
    else
    {
        wr_printcomment(e, "Resource at unexpected level %d", level);
        write_rc_resource(e, type, (rc_res_id *)NULL, re->u.res, language);
    }
}

static void write_rc_directory(FILE *e, const rc_res_directory *rd,
                              const rc_res_id *type, const rc_res_id *name,
                              rc_uint_type *language, int level)
{
    const rc_res_entry *re;
    
    print_coff_information(e, rd);
    
    for (re = rd->entries; re != NULL; re = re->next)
    {
        process_resource_entry(e, re, &type, &name, language, level);
        
        if (re->subdir)
            write_rc_subdir(e, re, type, name, language, level);
        else
            write_entry_resource(e, re, type, name, language, level);
    }
    
    if (rd->entries == NULL)
    {
        wr_print_flush(e);
    }
}

/* Write out a subdirectory entry.  E is the file to write to.  RE is
   the subdirectory entry.  TYPE and NAME are pointers to higher level
   IDs, or NULL.  LANGUAGE is a pointer to the current language.
   LEVEL is the level in the tree.  */

static const char* get_resource_type_name(rc_uint_type id)
{
    switch (id)
    {
    case RT_CURSOR: return "cursor";
    case RT_BITMAP: return "bitmap";
    case RT_ICON: return "icon";
    case RT_MENU: return "menu";
    case RT_DIALOG: return "dialog";
    case RT_STRING: return "stringtable";
    case RT_FONTDIR: return "fontdir";
    case RT_FONT: return "font";
    case RT_ACCELERATOR: return "accelerators";
    case RT_RCDATA: return "rcdata";
    case RT_MESSAGETABLE: return "messagetable";
    case RT_GROUP_CURSOR: return "group cursor";
    case RT_GROUP_ICON: return "group icon";
    case RT_VERSION: return "version";
    case RT_DLGINCLUDE: return "dlginclude";
    case RT_PLUGPLAY: return "plugplay";
    case RT_VXD: return "vxd";
    case RT_ANICURSOR: return "anicursor";
    case RT_ANIICON: return "aniicon";
    case RT_TOOLBAR: return "toolbar";
    case RT_HTML: return "html";
    default: return NULL;
    }
}

static void write_type_comment(FILE *e, const rc_res_entry *re)
{
    wr_printcomment (e, "Type: ");
    if (re->id.named)
    {
        res_id_print (e, re->id, 1);
        return;
    }
    
    const char *s = get_resource_type_name(re->id.u.id);
    if (s != NULL)
        fprintf (e, "%s", s);
    else
        res_id_print (e, re->id, 1);
}

static void write_level_comment(FILE *e, int level, const rc_res_entry *re)
{
    switch (level)
    {
    case 1:
        write_type_comment(e, re);
        break;
    case 2:
        wr_printcomment (e, "Name: ");
        res_id_print (e, re->id, 1);
        break;
    case 3:
        wr_printcomment (e, "Language: ");
        res_id_print (e, re->id, 1);
        break;
    default:
        wr_printcomment (e, "Level %d: ", level);
        res_id_print (e, re->id, 1);
        break;
    }
}

static void
write_rc_subdir (FILE *e, const rc_res_entry *re,
		 const rc_res_id *type, const rc_res_id *name,
		 rc_uint_type *language, int level)
{
    fprintf (e, "\n");
    write_level_comment(e, level, re);
    write_rc_directory (e, re->u.dir, type, name, language, level + 1);
}

/* Write out a single resource.  E is the file to write to.  TYPE is a
   pointer to the type of the resource.  NAME is a pointer to the name
   of the resource; it will be NULL if there is a level mismatch.  RES
   is the resource data.  LANGUAGE is a pointer to the current
   language.  */

static const char* get_resource_type_string(int res_type, int *rt, int *menuex, const rc_res_resource *res)
{
    *menuex = 0;
    
    switch (res_type)
    {
    case RES_TYPE_ACCELERATOR:
        *rt = RT_ACCELERATOR;
        return "ACCELERATORS";
    case RES_TYPE_BITMAP:
        *rt = RT_BITMAP;
        return "2 /* RT_BITMAP */";
    case RES_TYPE_CURSOR:
        *rt = RT_CURSOR;
        return "1 /* RT_CURSOR */";
    case RES_TYPE_GROUP_CURSOR:
        *rt = RT_GROUP_CURSOR;
        return "12 /* RT_GROUP_CURSOR */";
    case RES_TYPE_DIALOG:
        *rt = RT_DIALOG;
        return extended_dialog(res->u.dialog) ? "DIALOGEX" : "DIALOG";
    case RES_TYPE_FONT:
        *rt = RT_FONT;
        return "8 /* RT_FONT */";
    case RES_TYPE_FONTDIR:
        *rt = RT_FONTDIR;
        return "7 /* RT_FONTDIR */";
    case RES_TYPE_ICON:
        *rt = RT_ICON;
        return "3 /* RT_ICON */";
    case RES_TYPE_GROUP_ICON:
        *rt = RT_GROUP_ICON;
        return "14 /* RT_GROUP_ICON */";
    case RES_TYPE_MENU:
        *rt = RT_MENU;
        *menuex = extended_menu(res->u.menu);
        return *menuex ? "MENUEX" : "MENU";
    case RES_TYPE_MESSAGETABLE:
        *rt = RT_MESSAGETABLE;
        return "11 /* RT_MESSAGETABLE */";
    case RES_TYPE_RCDATA:
        *rt = RT_RCDATA;
        return "RCDATA";
    case RES_TYPE_STRINGTABLE:
        *rt = RT_STRING;
        return "STRINGTABLE";
    case RES_TYPE_USERDATA:
        *rt = 0;
        return NULL;
    case RES_TYPE_VERSIONINFO:
        *rt = RT_VERSION;
        return "VERSIONINFO";
    case RES_TYPE_TOOLBAR:
        *rt = RT_TOOLBAR;
        return "TOOLBAR";
    default:
        abort();
    }
}

static void print_type_mismatch(FILE *e, int rt, const rc_res_id *type)
{
    if (rt != 0 && type != NULL && (type->named || type->u.id != (unsigned long) rt))
    {
        wr_printcomment(e, "Unexpected resource type mismatch: ");
        res_id_print(e, *type, 1);
        fprintf(e, " != %d", rt);
    }
}

static void print_coff_info(FILE *e, const rc_res_resource *res)
{
    if (res->coff_info.codepage != 0)
        wr_printcomment(e, "Code page: %u", res->coff_info.codepage);
    if (res->coff_info.reserved != 0)
        wr_printcomment(e, "COFF reserved value: %u", res->coff_info.reserved);
}

static void print_resource_name(FILE *e, const rc_res_id *name, int rt)
{
    if (rt != RT_STRING)
    {
        if (name != NULL)
            res_id_print(e, *name, 1);
        else
            fprintf(e, "??Unknown-Name??");
        fprintf(e, " ");
    }
}

static void print_rt_name_case(FILE *e, unsigned int rt_id)
{
    fprintf(e, "%u /* %s */", rt_id, #rt_id);
}

#define PRINT_RT_NAME(NAME) case NAME: print_rt_name_case(e, NAME); break

static void print_resource_type_id(FILE *e, const rc_res_id *type)
{
    if (!type->named)
    {
        switch (type->u.id)
        {
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
        }
    }
    else
        res_id_print(e, *type, 1);
}

#undef PRINT_RT_NAME

static void print_resource_type(FILE *e, const char *s, const rc_res_id *type)
{
    if (s != NULL)
        fprintf(e, "%s", s);
    else if (type != NULL)
        print_resource_type_id(e, type);
    else
        fprintf(e, "??Unknown-Type??");
}

static void print_memory_flags(FILE *e, const rc_res_resource *res)
{
    if (res->res_info.memflags == 0)
        return;
        
    if ((res->res_info.memflags & MEMFLAG_MOVEABLE) != 0)
        fprintf(e, " MOVEABLE");
    if ((res->res_info.memflags & MEMFLAG_PURE) != 0)
        fprintf(e, " PURE");
    if ((res->res_info.memflags & MEMFLAG_PRELOAD) != 0)
        fprintf(e, " PRELOAD");
    if ((res->res_info.memflags & MEMFLAG_DISCARDABLE) != 0)
        fprintf(e, " DISCARDABLE");
}

static void print_dialog_dimensions(FILE *e, const rc_res_resource *res)
{
    if (res->type == RES_TYPE_DIALOG)
    {
        fprintf(e, " %d, %d, %d, %d",
                (int) res->u.dialog->x, (int) res->u.dialog->y,
                (int) res->u.dialog->width, (int) res->u.dialog->height);
        if (res->u.dialog->ex != NULL && res->u.dialog->ex->help != 0)
            fprintf(e, ", %u", (unsigned int) res->u.dialog->ex->help);
    }
    else if (res->type == RES_TYPE_TOOLBAR)
    {
        fprintf(e, " %d, %d", (int) res->u.toolbar->button_width,
                (int) res->u.toolbar->button_height);
    }
}

#define SUBLANG_SHIFT 10

static int needs_modifiers(int res_type)
{
    switch (res_type)
    {
    case RES_TYPE_ACCELERATOR:
    case RES_TYPE_DIALOG:
    case RES_TYPE_MENU:
    case RES_TYPE_RCDATA:
    case RES_TYPE_STRINGTABLE:
        return 1;
    default:
        return 0;
    }
}

static void print_resource_modifiers(FILE *e, const rc_res_resource *res, rc_uint_type *language)
{
    if ((res->res_info.language != 0 && res->res_info.language != *language) ||
        res->res_info.characteristics != 0 ||
        res->res_info.version != 0)
    {
        int modifiers = needs_modifiers(res->type);
        
        if (res->res_info.language != 0 && res->res_info.language != *language)
            fprintf(e, "%sLANGUAGE %d, %d\n",
                    modifiers ? "// " : "",
                    (int) res->res_info.language & ((1<<SUBLANG_SHIFT)-1),
                    (int) (res->res_info.language >> SUBLANG_SHIFT) & 0xff);
        if (res->res_info.characteristics != 0)
            fprintf(e, "%sCHARACTERISTICS %u\n",
                    modifiers ? "// " : "",
                    (unsigned int) res->res_info.characteristics);
        if (res->res_info.version != 0)
            fprintf(e, "%sVERSION %u\n",
                    modifiers ? "// " : "",
                    (unsigned int) res->res_info.version);
    }
}

static void write_resource_data(FILE *e, const rc_res_resource *res, const rc_res_id *name, int menuex)
{
    switch (res->type)
    {
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

static void write_rc_resource(FILE *e, const rc_res_id *type,
                             const rc_res_id *name, const rc_res_resource *res,
                             rc_uint_type *language)
{
    int rt;
    int menuex = 0;
    
    const char *s = get_resource_type_string(res->type, &rt, &menuex, res);
    
    print_type_mismatch(e, rt, type);
    print_coff_info(e, res);
    
    wr_print(e, "\n");
    print_resource_name(e, name, rt);
    print_resource_type(e, s, type);
    print_memory_flags(e, res);
    print_dialog_dimensions(e, res);
    fprintf(e, "\n");
    
    print_resource_modifiers(e, res, language);
    write_resource_data(e, res, name, menuex);
}

/* Write out accelerator information.  */

static void write_accelerator_key(FILE *e, const rc_accelerator *acc, int *printable)
{
    if ((acc->key & 0x7f) == acc->key && ISPRINT(acc->key) && (acc->flags & ACC_VIRTKEY) == 0)
    {
        fprintf(e, "\"%c\"", (char)acc->key);
        *printable = 1;
    }
    else
    {
        fprintf(e, "%d", (int)acc->key);
        *printable = 0;
    }
}

static void write_key_type(FILE *e, const rc_accelerator *acc, int printable)
{
    if (!printable)
    {
        if ((acc->flags & ACC_VIRTKEY) != 0)
            fprintf(e, ", VIRTKEY");
        else
            fprintf(e, ", ASCII");
    }
}

static void write_modifier_flags(FILE *e, const rc_accelerator *acc)
{
    if ((acc->flags & ACC_SHIFT) != 0)
        fprintf(e, ", SHIFT");
    if ((acc->flags & ACC_CONTROL) != 0)
        fprintf(e, ", CONTROL");
    if ((acc->flags & ACC_ALT) != 0)
        fprintf(e, ", ALT");
}

static void write_single_accelerator(FILE *e, const rc_accelerator *acc)
{
    int printable;

    fprintf(e, "  ");
    write_accelerator_key(e, acc, &printable);
    fprintf(e, ", %d", (int)acc->id);
    write_key_type(e, acc, printable);
    write_modifier_flags(e, acc);
    fprintf(e, "\n");
}

static void write_rc_accelerators(FILE *e, const rc_accelerator *accelerators)
{
    const rc_accelerator *acc;

    fprintf(e, "BEGIN\n");
    for (acc = accelerators; acc != NULL; acc = acc->next)
    {
        write_single_accelerator(e, acc);
    }
    fprintf(e, "END\n");
}

/* Write out cursor information.  This would normally be in a separate
   file, which the rc file would include.  */

static void write_cursor_hotspot(FILE *e, const rc_cursor *cursor)
{
    fprintf(e, " 0x%x, 0x%x,\t/* Hotspot x: %d, y: %d.  */\n",
            (unsigned int) cursor->xhotspot, (unsigned int) cursor->yhotspot,
            (int) cursor->xhotspot, (int) cursor->yhotspot);
}

static void write_rc_cursor(FILE *e, const rc_cursor *cursor)
{
    fprintf(e, "BEGIN\n");
    indent(e, 2);
    write_cursor_hotspot(e, cursor);
    write_rc_datablock(e, (rc_uint_type) cursor->length, (const bfd_byte *) cursor->data,
                      0, 0, 0);
    fprintf(e, "END\n");
}

/* Write out group cursor data.  This would normally be built from the
   cursor data.  */

static int count_group_cursors(const rc_group_cursor *group_cursor)
{
    int count = 0;
    const rc_group_cursor *gc = group_cursor;
    while (gc != NULL) {
        count++;
        gc = gc->next;
    }
    return count;
}

static void write_group_cursor_header(FILE *e, int count)
{
    fprintf(e, "BEGIN\n");
    indent(e, 2);
    fprintf(e, "0, 2, %d%s\t /* Having %d items.  */\n", 
            count, (count != 0 ? "," : ""), count);
    indent(e, 4);
    fprintf(e, "/* width, height, planes, bits, bytes, index.  */\n");
}

static void write_cursor_element(FILE *e, const rc_group_cursor *gc, int element_num, int has_next)
{
    indent(e, 4);
    fprintf(e, "%d, %d, %d, %d, 0x%xL, %d%s /* Element %d. */\n",
            (int) gc->width, (int) gc->height, (int) gc->planes, (int) gc->bits,
            (unsigned int) gc->bytes, (int) gc->index, 
            (has_next ? "," : ""), element_num);
    fprintf(e, "/* width: %d; height %d; planes %d; bits %d.  */\n",
            (int) gc->width, (int) gc->height, (int) gc->planes,
            (int) gc->bits);
}

static void write_group_cursor_elements(FILE *e, const rc_group_cursor *group_cursor)
{
    const rc_group_cursor *gc = group_cursor;
    int element_num = 1;
    
    while (gc != NULL) {
        write_cursor_element(e, gc, element_num, gc->next != NULL);
        gc = gc->next;
        element_num++;
    }
}

static void write_rc_group_cursor(FILE *e, const rc_group_cursor *group_cursor)
{
    int count = count_group_cursors(group_cursor);
    write_group_cursor_header(e, count);
    write_group_cursor_elements(e, group_cursor);
    fprintf(e, "END\n");
}

/* Write dialog data.  */

static void write_style(FILE *e, const rc_dialog *dialog)
{
    fprintf(e, "STYLE 0x%x\n", dialog->style);
}

static void write_exstyle(FILE *e, const rc_dialog *dialog)
{
    if (dialog->exstyle != 0)
        fprintf(e, "EXSTYLE 0x%x\n", (unsigned int) dialog->exstyle);
}

static int has_valid_res_id(const rc_res_id *res_id)
{
    return (res_id->named && res_id->u.n.length > 0) || res_id->u.id != 0;
}

static void write_res_id_line(FILE *e, const char *prefix, const rc_res_id *res_id, int quote_flag)
{
    if (!has_valid_res_id(res_id))
        return;
    
    fprintf(e, "%s ", prefix);
    res_id_print(e, *res_id, quote_flag);
    fprintf(e, "\n");
}

static void write_caption(FILE *e, const rc_dialog *dialog)
{
    if (dialog->caption == NULL)
        return;
    
    fprintf(e, "CAPTION ");
    unicode_print_quoted(e, dialog->caption, -1);
    fprintf(e, "\n");
}

static int has_extended_font_attributes(const rc_dialog_ex *ex)
{
    return ex != NULL && (ex->weight != 0 || ex->italic != 0 || ex->charset != 1);
}

static void write_extended_font_attributes(FILE *e, const rc_dialog_ex *ex)
{
    fprintf(e, ", %d, %d, %d",
            (int) ex->weight,
            (int) ex->italic,
            (int) ex->charset);
}

static void write_font(FILE *e, const rc_dialog *dialog)
{
    if (dialog->font == NULL)
        return;
    
    fprintf(e, "FONT %d, ", (int) dialog->pointsize);
    unicode_print_quoted(e, dialog->font, -1);
    
    if (has_extended_font_attributes(dialog->ex))
        write_extended_font_attributes(e, dialog->ex);
    
    fprintf(e, "\n");
}

static void write_dialog_controls(FILE *e, const rc_dialog *dialog)
{
    const rc_dialog_control *control;
    
    fprintf(e, "BEGIN\n");
    
    for (control = dialog->controls; control != NULL; control = control->next)
        write_rc_dialog_control(e, control);
    
    fprintf(e, "END\n");
}

static void write_rc_dialog(FILE *e, const rc_dialog *dialog)
{
    write_style(e, dialog);
    write_exstyle(e, dialog);
    write_res_id_line(e, "CLASS", &dialog->class, 1);
    write_caption(e, dialog);
    write_res_id_line(e, "MENU", &dialog->menu, 0);
    write_font(e, dialog);
    write_dialog_controls(e, dialog);
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

static int is_text_excluded_control(const struct control_info *ci)
{
    return ci && (ci->class == CTL_EDIT ||
                  ci->class == CTL_COMBOBOX ||
                  ci->class == CTL_LISTBOX ||
                  ci->class == CTL_SCROLLBAR);
}

static int has_text_to_print(const rc_dialog_control *control, const struct control_info *ci)
{
    return (control->text.named || control->text.u.id != 0) && 
           !is_text_excluded_control(ci);
}

static int needs_extended_attributes(const rc_dialog_control *control)
{
    return control->style != SS_ICON ||
           control->exstyle != 0 ||
           control->width != 0 ||
           control->height != 0 ||
           control->help != 0;
}

static const struct control_info *find_control_info(const rc_dialog_control *control)
{
    const struct control_info *ci;
    
    if (control->class.named)
        return NULL;
    
    for (ci = control_info; ci->name != NULL; ++ci)
    {
        if (ci->class == control->class.u.id &&
            (ci->style == (unsigned long) -1 || 
             ci->style == (control->style & 0xff)))
            return ci;
    }
    
    return NULL;
}

static void print_control_name(FILE *e, const struct control_info *ci)
{
    if (ci == NULL || ci->name == NULL)
        fprintf(e, "CONTROL");
    else
        fprintf(e, "%s", ci->name);
}

static void print_control_text(FILE *e, const rc_dialog_control *control, const struct control_info *ci)
{
    if (has_text_to_print(control, ci))
    {
        fprintf(e, " ");
        res_id_print(e, control->text, 1);
        fprintf(e, ",");
    }
}

static void print_control_class(FILE *e, const rc_dialog_control *control)
{
    if (control->class.named)
        fprintf(e, "\"");
    res_id_print(e, control->class, 0);
    if (control->class.named)
        fprintf(e, "\"");
    fprintf(e, ", 0x%x, ", (unsigned int) control->style);
}

static void print_extended_attributes(FILE *e, const rc_dialog_control *control, const struct control_info *ci)
{
    fprintf(e, ", %d, %d", (int) control->width, (int) control->height);
    
    if (ci != NULL)
        fprintf(e, ", 0x%x", (unsigned int) control->style);
    
    if (control->exstyle != 0 || control->help != 0)
        fprintf(e, ", 0x%x, %u", (unsigned int) control->exstyle,
                (unsigned int) control->help);
}

static void write_rc_dialog_control(FILE *e, const rc_dialog_control *control)
{
    const struct control_info *ci;
    
    fprintf(e, "  ");
    
    ci = find_control_info(control);
    print_control_name(e, ci);
    print_control_text(e, control, ci);
    
    fprintf(e, " %d, ", (int) control->id);
    
    if (ci == NULL)
        print_control_class(e, control);
    
    fprintf(e, "%d, %d", (int) control->x, (int) control->y);
    
    if (needs_extended_attributes(control))
        print_extended_attributes(e, control, ci);
    
    fprintf(e, "\n");
    
    if (control->data != NULL)
        write_rc_rcdata(e, control->data, 2);
}

/* Write out font directory data.  This would normally be built from
   the font data.  */

static int count_fontdir_elements(const rc_fontdir *fontdir)
{
    int count = 0;
    const rc_fontdir *fc = fontdir;
    while (fc != NULL) {
        count++;
        fc = fc->next;
    }
    return count;
}

static void write_fontdir_header(FILE *e, int element_count)
{
    fprintf(e, "BEGIN\n");
    indent(e, 2);
    fprintf(e, "%d%s\t /* Has %d elements.  */\n", 
            element_count, 
            (element_count != 0 ? "," : ""), 
            element_count);
}

static void write_fontdir_element(FILE *e, const rc_fontdir *fc, int font_number)
{
    indent(e, 4);
    fprintf(e, "%d,\t/* Font no %d with index %d.  */\n",
            (int) fc->index, font_number, (int) fc->index);
    write_rc_datablock(e, (rc_uint_type) fc->length - 2,
                      (const bfd_byte *) fc->data + 4, fc->next != NULL,
                      0, 0);
}

static void write_fontdir_elements(FILE *e, const rc_fontdir *fontdir)
{
    const rc_fontdir *fc = fontdir;
    int font_number = 1;
    
    while (fc != NULL) {
        write_fontdir_element(e, fc, font_number);
        fc = fc->next;
        font_number++;
    }
}

static void write_rc_fontdir(FILE *e, const rc_fontdir *fontdir)
{
    int element_count = count_fontdir_elements(fontdir);
    
    write_fontdir_header(e, element_count);
    write_fontdir_elements(e, fontdir);
    fprintf(e, "END\n");
}

/* Write out group icon data.  This would normally be built from the
   icon data.  */

static int count_group_icons(const rc_group_icon *group_icon)
{
    int count = 0;
    const rc_group_icon *gi = group_icon;
    while (gi != NULL) {
        count++;
        gi = gi->next;
    }
    return count;
}

static void write_group_icon_header(FILE *e, int count)
{
    fprintf(e, "BEGIN\n");
    indent(e, 2);
    fprintf(e, " 0, 1, %d%s\t /* Has %d elements.  */\n", 
            count, (count != 0 ? "," : ""), count);
    indent(e, 4);
    fprintf(e, "/* \"width height colors pad\", planes, bits, bytes, index.  */\n");
}

static void write_group_icon_element(FILE *e, const rc_group_icon *gi, int element_num, int has_next)
{
    indent(e, 4);
    fprintf(e, "\"\\%03o\\%03o\\%03o\\%03o\", %d, %d, 0x%xL, %d%s\t/* Element no %d.  */\n",
            gi->width, gi->height, gi->colors, 0, 
            (int)gi->planes, (int)gi->bits,
            (unsigned int)gi->bytes, (int)gi->index, 
            (has_next ? "," : ""), element_num);
}

static void write_rc_group_icon(FILE *e, const rc_group_icon *group_icon)
{
    int count = count_group_icons(group_icon);
    
    write_group_icon_header(e, count);
    
    const rc_group_icon *gi = group_icon;
    int element_num = 1;
    while (gi != NULL) {
        write_group_icon_element(e, gi, element_num, gi->next != NULL);
        gi = gi->next;
        element_num++;
    }
    
    fprintf(e, "END\n");
}

/* Write out a menu resource.  */

static void
write_rc_menu (FILE *e, const rc_menu *menu, int menuex)
{
  if (menu->help != 0)
    fprintf (e, "// Help ID: %u\n", (unsigned int) menu->help);
  write_rc_menuitems (e, menu->items, menuex, 0);
}

static void write_toolbar_separator(FILE *e)
{
    indent(e, 2);
    fprintf(e, "SEPARATOR\n");
}

static void write_toolbar_button(FILE *e, int button_id)
{
    indent(e, 2);
    fprintf(e, "BUTTON %d\n", button_id);
}

static void write_toolbar_item(FILE *e, const rc_toolbar_item *item)
{
    if (item->id.u.id == 0)
        write_toolbar_separator(e);
    else
        write_toolbar_button(e, (int)item->id.u.id);
}

static void write_toolbar_items(FILE *e, const rc_toolbar_item *items)
{
    const rc_toolbar_item *current = items;
    while (current != NULL)
    {
        write_toolbar_item(e, current);
        current = current->next;
    }
}

static void write_rc_toolbar(FILE *e, const rc_toolbar *tb)
{
    indent(e, 0);
    fprintf(e, "BEGIN\n");
    write_toolbar_items(e, tb->items);
    indent(e, 0);
    fprintf(e, "END\n");
}

/* Write out menuitems.  */

static void
write_menuitem_flags(FILE *e, unsigned int type)
{
  if ((type & MENUITEM_CHECKED) != 0)
    fprintf (e, ", CHECKED");
  if ((type & MENUITEM_GRAYED) != 0)
    fprintf (e, ", GRAYED");
  if ((type & MENUITEM_HELP) != 0)
    fprintf (e, ", HELP");
  if ((type & MENUITEM_INACTIVE) != 0)
    fprintf (e, ", INACTIVE");
  if ((type & MENUITEM_MENUBARBREAK) != 0)
    fprintf (e, ", MENUBARBREAK");
  if ((type & MENUITEM_MENUBREAK) != 0)
    fprintf (e, ", MENUBREAK");
  if ((type & MENUITEM_OWNERDRAW) != 0)
    fprintf (e, ", OWNERDRAW");
  if ((type & MENUITEM_BITMAP) != 0)
    fprintf (e, ", BITMAP");
}

static int
is_separator(const rc_menuitem *mi, int menuex)
{
  return !menuex && mi->popup == NULL && mi->text == NULL && 
         mi->type == 0 && mi->id == 0;
}

static void
write_menuitem_text(FILE *e, const rc_menuitem *mi)
{
  if (mi->text == NULL)
    fprintf (e, " \"\"");
  else
    {
      fprintf (e, " ");
      unicode_print_quoted (e, mi->text, -1);
    }
}

static void
write_menuitem_extended_attributes(FILE *e, const rc_menuitem *mi)
{
  if (mi->id != 0 || mi->type != 0 || mi->state != 0 || mi->help != 0)
    {
      fprintf (e, ", %d", (int) mi->id);
      if (mi->type != 0 || mi->state != 0 || mi->help != 0)
        {
          fprintf (e, ", %u", (unsigned int) mi->type);
          if (mi->state != 0 || mi->help != 0)
            {
              fprintf (e, ", %u", (unsigned int) mi->state);
              if (mi->help != 0)
                fprintf (e, ", %u", (unsigned int) mi->help);
            }
        }
    }
}

static void
write_menuitem_standard_attributes(FILE *e, const rc_menuitem *mi)
{
  if (mi->popup == NULL)
    fprintf (e, ", %d", (int) mi->id);
  write_menuitem_flags(e, mi->type);
}

static void
write_single_menuitem(FILE *e, const rc_menuitem *mi, int menuex, int ind)
{
  indent (e, ind + 2);

  if (mi->popup == NULL)
    fprintf (e, "MENUITEM");
  else
    fprintf (e, "POPUP");

  if (is_separator(mi, menuex))
    {
      fprintf (e, " SEPARATOR\n");
      return;
    }

  write_menuitem_text(e, mi);

  if (!menuex)
    write_menuitem_standard_attributes(e, mi);
  else
    write_menuitem_extended_attributes(e, mi);

  fprintf (e, "\n");

  if (mi->popup != NULL)
    write_rc_menuitems (e, mi->popup, menuex, ind + 2);
}

static void
write_rc_menuitems (FILE *e, const rc_menuitem *menuitems, int menuex,
		    int ind)
{
  const rc_menuitem *mi;

  indent (e, ind);
  fprintf (e, "BEGIN\n");

  for (mi = menuitems; mi != NULL; mi = mi->next)
    {
      write_single_menuitem(e, mi, menuex, ind);
    }

  indent (e, ind);
  fprintf (e, "END\n");
}

static int
test_rc_datablock_unicode (rc_uint_type length, const bfd_byte *data)
{
  if ((length & 1) != 0)
    return 0;

  rc_uint_type i;
  for (i = 0; i < length; i += 2)
    {
      if (data[i] == 0 && data[i + 1] == 0 && (i + 2) < length)
        return 0;
      if (data[i] == 0xff && data[i + 1] == 0xff)
        return 0;
    }
  return 1;
}

static int is_valid_text_character(const bfd_byte *data, rc_uint_type i, rc_uint_type length)
{
    if (ISPRINT(data[i]))
        return 1;
    if (data[i] == '\n')
        return 1;
    if (data[i] == '\r' && (i + 1) < length && data[i + 1] == '\n')
        return 1;
    if (data[i] == '\t')
        return 1;
    if (data[i] == 0 && (i + 1) != length)
        return 1;
    return 0;
}

static int count_newlines(const bfd_byte *data, rc_uint_type length)
{
    int count = 0;
    rc_uint_type i;
    
    for (i = 0; i < length; i++)
    {
        if (data[i] == '\n')
            count++;
    }
    return count;
}

static rc_uint_type count_invalid_characters(const bfd_byte *data, rc_uint_type length)
{
    rc_uint_type count = 0;
    rc_uint_type i;
    
    for (i = 0; i < length; i++)
    {
        if (!is_valid_text_character(data, i, length))
        {
            if (data[i] <= 7)
                return length;
            count++;
        }
    }
    return count;
}

#define MIN_TEXT_LENGTH 2
#define LONG_LINE_THRESHOLD 80
#define INVALID_CHAR_PERCENTAGE_THRESHOLD 150
#define PERCENTAGE_FACTOR 10000
#define PERCENTAGE_DIVISOR 100

static int test_rc_datablock_text(rc_uint_type length, const bfd_byte *data)
{
    rc_uint_type invalid_count;
    rc_uint_type percentage;
    int newline_count;
    
    if (length < MIN_TEXT_LENGTH)
        return 0;
    
    invalid_count = count_invalid_characters(data, length);
    if (invalid_count == length)
        return 0;
    
    newline_count = count_newlines(data, length);
    
    if (length > LONG_LINE_THRESHOLD && !newline_count)
        return 0;
    
    percentage = (((invalid_count * PERCENTAGE_FACTOR) + (length / PERCENTAGE_DIVISOR) - 1)) / length;
    if (percentage >= INVALID_CHAR_PERCENTAGE_THRESHOLD)
        return 0;
    
    return 1;
}

static int validate_messagetable_size(rc_uint_type length, rc_uint_type block_count)
{
    return length >= (BIN_MESSAGETABLE_SIZE + block_count * BIN_MESSAGETABLE_BLOCK_SIZE);
}

static int validate_item_bounds(rc_uint_type offset, rc_uint_type item_length, rc_uint_type total_length)
{
    if ((offset + BIN_MESSAGETABLE_ITEM_SIZE) > total_length)
        return 0;
    if ((offset + item_length) > total_length)
        return 0;
    return 1;
}

static void print_message_header(FILE *e, rc_uint_type message_id)
{
    wr_printcomment(e, "MessageId = 0x%x", message_id);
    wr_printcomment(e, "");
}

static void print_message_data(FILE *e, const struct bin_messagetable_item *mti, 
                               rc_uint_type elen, rc_uint_type flags)
{
    if ((flags & MESSAGE_RESOURCE_UNICODE) == MESSAGE_RESOURCE_UNICODE)
    {
        if (elen > BIN_MESSAGETABLE_ITEM_SIZE * 2)
            unicode_print(e, (const unichar *) mti->data,
                         (elen - BIN_MESSAGETABLE_ITEM_SIZE) / 2);
    }
    else
    {
        if (elen > BIN_MESSAGETABLE_ITEM_SIZE)
            ascii_print(e, (const char *) mti->data,
                       (elen - BIN_MESSAGETABLE_ITEM_SIZE));
    }
    wr_printcomment(e, "");
}

static int process_message_item(FILE *e, const bfd_byte *data, rc_uint_type length,
                                rc_uint_type *offset, rc_uint_type message_id)
{
    const struct bin_messagetable_item *mti;
    rc_uint_type elen, flags;
    
    if (!validate_item_bounds(*offset, 0, length))
        return 0;
    
    mti = (const struct bin_messagetable_item *) &data[*offset];
    elen = windres_get_16(&wrtarget, mti->length);
    flags = windres_get_16(&wrtarget, mti->flags);
    
    if (!validate_item_bounds(*offset, elen, length))
        return 0;
    
    print_message_header(e, message_id);
    print_message_data(e, mti, elen, flags);
    
    *offset += elen;
    return 1;
}

static int process_message_block(FILE *e, const bfd_byte *data, rc_uint_type length,
                                 const struct bin_messagetable_block *block)
{
    rc_uint_type low, high, offset;
    
    low = windres_get_32(&wrtarget, block->lowid);
    high = windres_get_32(&wrtarget, block->highid);
    offset = windres_get_32(&wrtarget, block->offset);
    
    while (low <= high)
    {
        if (!process_message_item(e, data, length, &offset, low))
            return 0;
        ++low;
    }
    return 1;
}

static int process_messagetable(FILE *e, const bfd_byte *data, rc_uint_type length)
{
    const struct bin_messagetable *mt;
    rc_uint_type block_count, i;
    
    if (length < BIN_MESSAGETABLE_SIZE)
        return 0;
    
    mt = (const struct bin_messagetable *) data;
    block_count = target_get_32(mt->cblocks, length);
    
    if (!validate_messagetable_size(length, block_count))
        return 0;
    
    for (i = 0; i < block_count; i++)
    {
        if (!process_message_block(e, data, length, &mt->items[i]))
            return 0;
    }
    return 1;
}

static void write_rc_messagetable(FILE *e, rc_uint_type length, const bfd_byte *data)
{
    int has_error = 0;
    
    fprintf(e, "BEGIN\n");
    write_rc_datablock(e, length, data, 0, 0, 0);
    fprintf(e, "\n");
    wr_printcomment(e, "MC syntax dump");
    
    has_error = !process_messagetable(e, data, length);
    
    if (has_error)
        wr_printcomment(e, "Illegal data");
    wr_print_flush(e);
    fprintf(e, "END\n");
}

static void write_block_wrapper(FILE *e, int hasblock, int has_next, int is_begin)
{
    if (hasblock && is_begin)
        fprintf(e, "BEGIN\n");
    else if (hasblock && !is_begin)
        fprintf(e, "END\n");
    else if (has_next && !is_begin)
        fprintf(e, ",");
}

static void write_empty_string(FILE *e, int is_unicode)
{
    indent(e, 2);
    fprintf(e, is_unicode ? "L\"\"" : "\"\"");
}

static void write_text_line(FILE *e, const bfd_byte *data, rc_uint_type start, rc_uint_type count)
{
    indent(e, 2);
    fprintf(e, "\"");
    ascii_print(e, (const char *)&data[start], count);
    fprintf(e, "\"");
}

static void write_unicode_line(FILE *e, const unichar *u, rc_uint_type count)
{
    indent(e, 2);
    fprintf(e, "L\"");
    unicode_print(e, u, count);
    fprintf(e, "\"");
}

static rc_uint_type process_text_chunk(FILE *e, const bfd_byte *data, rc_uint_type i, rc_uint_type length)
{
    rc_uint_type c;
    for (c = 0; i + c < length && c < 160 && data[i + c] != '\n'; c++)
        ;
    if (i + c < length && data[i + c] == '\n')
        ++c;
    write_text_line(e, data, i, c);
    return c;
}

static rc_uint_type process_unicode_chunk(FILE *e, const bfd_byte *data, rc_uint_type i, rc_uint_type length)
{
    rc_uint_type c;
    const unichar *u = (const unichar *)&data[i];
    for (c = 0; i + (c * 2) < length && c < 160 && u[c] != '\n'; c++)
        ;
    if (i + (c * 2) < length && u[c] == '\n')
        ++c;
    write_unicode_line(e, u, c);
    return c * 2;
}

static void write_text_data(FILE *e, rc_uint_type length, const bfd_byte *data, int has_next, int hasblock)
{
    rc_uint_type i;
    
    write_block_wrapper(e, hasblock, 0, 1);
    
    for (i = 0; i < length;)
    {
        i += process_text_chunk(e, data, i, length);
        if (i < length)
            fprintf(e, "\n");
    }
    
    if (length == 0)
        write_empty_string(e, 0);
    
    write_block_wrapper(e, 0, has_next, 0);
    fprintf(e, "\n");
    write_block_wrapper(e, hasblock, 0, 0);
}

static void write_unicode_data(FILE *e, rc_uint_type length, const bfd_byte *data, int has_next, int hasblock)
{
    rc_uint_type i;
    
    write_block_wrapper(e, hasblock, 0, 1);
    
    for (i = 0; i < length;)
    {
        i += process_unicode_chunk(e, data, i, length);
        if (i < length)
            fprintf(e, "\n");
    }
    
    if (length == 0)
        write_empty_string(e, 1);
    
    write_block_wrapper(e, 0, has_next, 0);
    fprintf(e, "\n");
    write_block_wrapper(e, hasblock, 0, 0);
}

static void write_comment(FILE *e, const bfd_byte *data, rc_uint_type start, rc_uint_type length)
{
    fprintf(e, "\t/* ");
    ascii_print(e, (const char *)&data[start], length);
    fprintf(e, ".  */");
}

static int write_dword_value(FILE *e, const bfd_byte *data, rc_uint_type i, rc_uint_type length, int first_in_row)
{
    int plen;
    if (first_in_row)
        plen = fprintf(e, "0x%lxL", (unsigned long)target_get_32(data + i, length - i));
    else
        plen = fprintf(e, " 0x%lxL", (unsigned long)target_get_32(data + i, length - i)) - 1;
    return plen;
}

static void write_dword_row(FILE *e, const bfd_byte *data, rc_uint_type *i, rc_uint_type length, 
                           int has_next, int show_comment, int max_row)
{
    rc_uint_type k;
    rc_uint_type comment_start = *i;
    
    for (k = 0; k < max_row && *i + 3 < length; k++, *i += 4)
    {
        int plen = write_dword_value(e, data, *i, length, k == 0);
        if (has_next || (*i + 4) < length)
        {
            if (plen > 0 && plen < 11)
                indent(e, 11 - plen);
            fprintf(e, ",");
        }
    }
    
    if (show_comment)
        write_comment(e, data, comment_start, *i - comment_start);
    
    fprintf(e, "\n");
}

static void write_word_value(FILE *e, const bfd_byte *data, rc_uint_type i, rc_uint_type length,
                            int has_next, int show_comment)
{
    int plen = fprintf(e, "0x%x", (int)target_get_16(data + i, length - i));
    if (has_next || i + 2 < length)
    {
        if (plen > 0 && plen < 11)
            indent(e, 11 - plen);
        fprintf(e, ",");
    }
    if (show_comment)
        write_comment(e, data, i, 2);
    fprintf(e, "\n");
}

static void write_byte_value(FILE *e, const bfd_byte *data, rc_uint_type i, int has_next)
{
    fprintf(e, "\"");
    ascii_print(e, (const char *)&data[i], 1);
    fprintf(e, "\"");
    if (has_next)
        fprintf(e, ",");
    fprintf(e, "\n");
}

static void write_binary_data(FILE *e, rc_uint_type length, const bfd_byte *data, 
                             int has_next, int hasblock, int show_comment)
{
    rc_uint_type i;
    int first = 1;
    int max_row = show_comment ? 4 : 8;
    
    write_block_wrapper(e, hasblock, 0, 1);
    
    if (length != 0)
    {
        for (i = 0; i + 3 < length;)
        {
            if (!first)
                indent(e, 2);
            else
                indent(e, 2);
            
            write_dword_row(e, data, &i, length, has_next, show_comment, max_row);
            first = 0;
        }
        
        if (i + 1 < length)
        {
            if (!first)
                indent(e, 2);
            write_word_value(e, data, i, length, has_next, show_comment);
            i += 2;
            first = 0;
        }
        
        if (i < length)
        {
            if (!first)
                indent(e, 2);
            write_byte_value(e, data, i, has_next);
        }
    }
    
    write_block_wrapper(e, hasblock, 0, 0);
}

static void write_rc_datablock(FILE *e, rc_uint_type length, const bfd_byte *data,
                              int has_next, int hasblock, int show_comment)
{
    if (show_comment == -1)
    {
        if (test_rc_datablock_text(length, data))
        {
            write_text_data(e, length, data, has_next, hasblock);
            return;
        }
        if (test_rc_datablock_unicode(length, data))
        {
            write_unicode_data(e, length, data, has_next, hasblock);
            return;
        }
        show_comment = 0;
    }
    
    write_binary_data(e, length, data, has_next, hasblock, show_comment);
}

/* Write out an rcdata resource.  This is also used for other types of
   resources that need to print arbitrary data.  */

static void write_rcdata_word(FILE *e, int ind, const rc_rcdata_item *ri)
{
    indent(e, ind + 2);
    fprintf(e, "%ld", (long)(ri->u.word & 0xffff));
}

static void write_rcdata_dword(FILE *e, int ind, const rc_rcdata_item *ri)
{
    indent(e, ind + 2);
    fprintf(e, "%luL", (unsigned long)ri->u.dword);
}

static void write_rcdata_string(FILE *e, int ind, const rc_rcdata_item *ri)
{
    indent(e, ind + 2);
    fprintf(e, "\"");
    ascii_print(e, ri->u.string.s, ri->u.string.length);
    fprintf(e, "\"");
}

static void write_rcdata_wstring(FILE *e, int ind, const rc_rcdata_item *ri)
{
    indent(e, ind + 2);
    fprintf(e, "L\"");
    unicode_print(e, ri->u.wstring.w, ri->u.wstring.length);
    fprintf(e, "\"");
}

static void write_rcdata_buffer(FILE *e, const rc_rcdata_item *ri)
{
    write_rc_datablock(e, (rc_uint_type)ri->u.buffer.length,
                      (const bfd_byte *)ri->u.buffer.data,
                      ri->next != NULL, 0, -1);
}

static int should_skip_item(const rc_rcdata_item *ri)
{
    return ri->type == RCDATA_BUFFER && ri->u.buffer.length == 0;
}

static void write_item_suffix(FILE *e, const rc_rcdata_item *ri)
{
    if (ri->type != RCDATA_BUFFER)
    {
        if (ri->next != NULL)
            fprintf(e, ",");
        fprintf(e, "\n");
    }
}

static void write_rcdata_item(FILE *e, int ind, const rc_rcdata_item *ri)
{
    switch (ri->type)
    {
    case RCDATA_WORD:
        write_rcdata_word(e, ind, ri);
        break;
    case RCDATA_DWORD:
        write_rcdata_dword(e, ind, ri);
        break;
    case RCDATA_STRING:
        write_rcdata_string(e, ind, ri);
        break;
    case RCDATA_WSTRING:
        write_rcdata_wstring(e, ind, ri);
        break;
    case RCDATA_BUFFER:
        write_rcdata_buffer(e, ri);
        break;
    default:
        abort();
    }
}

static void write_rc_rcdata(FILE *e, const rc_rcdata_item *rcdata, int ind)
{
    const rc_rcdata_item *ri;

    indent(e, ind);
    fprintf(e, "BEGIN\n");

    for (ri = rcdata; ri != NULL; ri = ri->next)
    {
        if (should_skip_item(ri))
            continue;

        write_rcdata_item(e, ind, ri);
        write_item_suffix(e, ri);
    }

    indent(e, ind);
    fprintf(e, "END\n");
}

/* Write out a stringtable resource.  */

static rc_uint_type calculate_offset(const rc_res_id *name)
{
    if (name != NULL && !name->named)
        return (name->u.id - 1) << 4;
    return 0;
}

static void print_offset_warning(FILE *e, const rc_res_id *name)
{
    const char *status = (name == NULL) ? "Missing" : "Invalid";
    fprintf(e, "/* %s string table name.  */\n", status);
}

static void write_string_entry(FILE *e, rc_uint_type offset, int index, 
                               const rc_string *string)
{
    fprintf(e, "  %lu, ", (unsigned long) offset + index);
    unicode_print_quoted(e, string->string, string->length);
    fprintf(e, "\n");
}

static void write_string_entries(FILE *e, const rc_stringtable *stringtable, 
                                 rc_uint_type offset)
{
    #define MAX_STRINGS 16
    
    for (int i = 0; i < MAX_STRINGS; i++)
    {
        if (stringtable->strings[i].length != 0)
            write_string_entry(e, offset, i, &stringtable->strings[i]);
    }
}

static void write_rc_stringtable(FILE *e, const rc_res_id *name,
                                 const rc_stringtable *stringtable)
{
    rc_uint_type offset = calculate_offset(name);
    
    if (offset == 0)
        print_offset_warning(e, name);
    
    fprintf(e, "BEGIN\n");
    write_string_entries(e, stringtable, offset);
    fprintf(e, "END\n");
}

/* Write out a versioninfo resource.  */

#define VERSION_MASK 0xffff
#define VERSION_SHIFT 16

static void write_version_quad(FILE *e, const char *prefix, unsigned int ms, unsigned int ls)
{
    fprintf(e, " %s %u, %u, %u, %u\n", prefix,
            (unsigned int)((ms >> VERSION_SHIFT) & VERSION_MASK),
            (unsigned int)(ms & VERSION_MASK),
            (unsigned int)((ls >> VERSION_SHIFT) & VERSION_MASK),
            (unsigned int)(ls & VERSION_MASK));
}

static void write_hex_value(FILE *e, const char *name, unsigned int value)
{
    fprintf(e, " %s 0x%x\n", name, value);
}

static void write_string_block(FILE *e, const rc_ver_stringtable *vst)
{
    fprintf(e, "    BLOCK ");
    unicode_print_quoted(e, vst->language, -1);
    fprintf(e, "\n");
    fprintf(e, "    BEGIN\n");
    
    const rc_ver_stringinfo *vs;
    for (vs = vst->strings; vs != NULL; vs = vs->next)
    {
        fprintf(e, "      VALUE ");
        unicode_print_quoted(e, vs->key, -1);
        fprintf(e, ", ");
        unicode_print_quoted(e, vs->value, -1);
        fprintf(e, "\n");
    }
    
    fprintf(e, "    END\n");
}

static void write_string_file_info(FILE *e, const rc_ver_info *vi)
{
    fprintf(e, "  BLOCK \"StringFileInfo\"\n");
    fprintf(e, "  BEGIN\n");
    
    const rc_ver_stringtable *vst;
    for (vst = vi->u.string.stringtables; vst != NULL; vst = vst->next)
    {
        write_string_block(e, vst);
    }
    
    fprintf(e, "  END\n");
}

static void write_var_file_info(FILE *e, const rc_ver_info *vi)
{
    fprintf(e, "  BLOCK \"VarFileInfo\"\n");
    fprintf(e, "  BEGIN\n");
    fprintf(e, "    VALUE ");
    unicode_print_quoted(e, vi->u.var.key, -1);
    
    const rc_ver_varinfo *vv;
    for (vv = vi->u.var.var; vv != NULL; vv = vv->next)
    {
        fprintf(e, ", 0x%x, %d", (unsigned int)vv->language, (int)vv->charset);
    }
    
    fprintf(e, "\n  END\n");
}

static void write_fixed_info(FILE *e, const rc_fixed_versioninfo *f)
{
    if (f->file_version_ms != 0 || f->file_version_ls != 0)
        write_version_quad(e, "FILEVERSION", f->file_version_ms, f->file_version_ls);
    
    if (f->product_version_ms != 0 || f->product_version_ls != 0)
        write_version_quad(e, "PRODUCTVERSION", f->product_version_ms, f->product_version_ls);
    
    if (f->file_flags_mask != 0)
        write_hex_value(e, "FILEFLAGSMASK", f->file_flags_mask);
    
    if (f->file_flags != 0)
        write_hex_value(e, "FILEFLAGS", f->file_flags);
    
    if (f->file_os != 0)
        write_hex_value(e, "FILEOS", f->file_os);
    
    if (f->file_type != 0)
        write_hex_value(e, "FILETYPE", f->file_type);
    
    if (f->file_subtype != 0)
        write_hex_value(e, "FILESUBTYPE", f->file_subtype);
    
    if (f->file_date_ms != 0 || f->file_date_ls != 0)
        fprintf(e, "/* Date: %u, %u.  */\n",
                (unsigned int)f->file_date_ms, (unsigned int)f->file_date_ls);
}

static void write_rc_versioninfo(FILE *e, const rc_versioninfo *versioninfo)
{
    write_fixed_info(e, versioninfo->fixed);
    
    fprintf(e, "BEGIN\n");
    
    const rc_ver_info *vi;
    for (vi = versioninfo->var; vi != NULL; vi = vi->next)
    {
        if (vi->type == VERINFO_STRING)
            write_string_file_info(e, vi);
        else if (vi->type == VERINFO_VAR)
            write_var_file_info(e, vi);
    }
    
    fprintf(e, "END\n");
}

static rc_uint_type copy_word(const rc_rcdata_item *src, bfd_byte *dst)
{
    if (dst)
        windres_put_16(&wrtarget, dst, (rc_uint_type)src->u.word);
    return 2;
}

static rc_uint_type copy_dword(const rc_rcdata_item *src, bfd_byte *dst)
{
    if (dst)
        windres_put_32(&wrtarget, dst, (rc_uint_type)src->u.dword);
    return 4;
}

static rc_uint_type copy_memory_if_needed(bfd_byte *dst, const void *src_data, size_t length)
{
    if (dst && length)
        memcpy(dst, src_data, length);
    return (rc_uint_type)length;
}

static rc_uint_type copy_string(const rc_rcdata_item *src, bfd_byte *dst)
{
    return copy_memory_if_needed(dst, src->u.string.s, src->u.string.length);
}

static rc_uint_type copy_wstring(const rc_rcdata_item *src, bfd_byte *dst)
{
    size_t byte_length = src->u.wstring.length * sizeof(unichar);
    return copy_memory_if_needed(dst, src->u.wstring.w, byte_length);
}

static rc_uint_type copy_buffer(const rc_rcdata_item *src, bfd_byte *dst)
{
    return copy_memory_if_needed(dst, src->u.buffer.data, src->u.buffer.length);
}

static rc_uint_type rcdata_copy(const rc_rcdata_item *src, bfd_byte *dst)
{
    if (!src)
        return 0;
    
    switch (src->type)
    {
    case RCDATA_WORD:
        return copy_word(src, dst);
    case RCDATA_DWORD:
        return copy_dword(src, dst);
    case RCDATA_STRING:
        return copy_string(src, dst);
    case RCDATA_WSTRING:
        return copy_wstring(src, dst);
    case RCDATA_BUFFER:
        return copy_buffer(src, dst);
    default:
        abort();
    }
}
