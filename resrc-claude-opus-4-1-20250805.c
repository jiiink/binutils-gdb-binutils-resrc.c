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

static int
run_cmd (char *cmd, const char *redir)
{
  char *s;
  int pid, wait_status, retcode;
  int i;
  const char **argv;
  char *errmsg_fmt = NULL, *errmsg_arg = NULL;
  char *temp_base = make_temp_file (NULL);
  int in_quote;
  char sep;
  int redir_handle = -1;
  int stdout_save = -1;

  i = 0;
  for (s = cmd; *s; s++)
    if (*s == ' ')
      i++;

  i++;
  argv = xmalloc (sizeof (char *) * (i + 3));
  i = 0;
  s = cmd;

  while (1)
    {
      while (*s == ' ' && *s != 0)
        s++;

      if (*s == 0)
        break;

      in_quote = (*s == '\'' || *s == '"');
      sep = (in_quote) ? *s++ : ' ';
      argv[i++] = s;

      while (*s != sep && *s != 0)
        s++;

      if (*s == 0)
        break;

      *s++ = 0;

      if (in_quote)
        s++;
    }
  argv[i++] = NULL;

  fflush (stdout);
  fflush (stderr);

  redir_handle = open (redir, O_WRONLY | O_TRUNC | O_CREAT, 0666);
  if (redir_handle == -1)
    {
      free (argv);
      fatal (_("can't open temporary file `%s': %s"), redir,
             strerror (errno));
    }

  stdout_save = dup (STDOUT_FILENO);
  if (stdout_save == -1)
    {
      close (redir_handle);
      free (argv);
      fatal (_("can't redirect stdout: `%s': %s"), redir, strerror (errno));
    }

  dup2 (redir_handle, STDOUT_FILENO);

  pid = pexecute (argv[0], (char * const *) argv, program_name, temp_base,
                  &errmsg_fmt, &errmsg_arg, PEXECUTE_ONE | PEXECUTE_SEARCH);

  dup2 (stdout_save, STDOUT_FILENO);
  close (stdout_save);
  close (redir_handle);
  free (argv);

  if (pid == -1)
    {
      fatal ("%s %s: %s", errmsg_fmt, errmsg_arg, strerror (errno));
    }

  retcode = 0;
  pid = pwait (pid, &wait_status, 0);

  if (pid == -1)
    {
      fatal (_("wait: %s"), strerror (errno));
    }
  else if (WIFSIGNALED (wait_status))
    {
      fatal (_("subprocess got fatal signal %d"), WTERMSIG (wait_status));
    }
  else if (WIFEXITED (wait_status))
    {
      if (WEXITSTATUS (wait_status) != 0)
        {
          fatal (_("%s exited with status %d"), cmd,
                 WEXITSTATUS (wait_status));
        }
    }
  else
    retcode = 1;

  return retcode;
}

static FILE *
open_input_stream (char *cmd)
{
  FILE *stream = NULL;
  
  if (cmd == NULL)
    {
      fatal (_("invalid command"));
      return NULL;
    }

  if (istream_type == ISTREAM_FILE)
    {
      char *fileprefix = make_temp_file (NULL);
      if (fileprefix == NULL)
        {
          fatal (_("can't create temporary file"));
          return NULL;
        }
      
      size_t len = strlen (fileprefix) + 5;
      cpp_temp_file = (char *) xmalloc (len);
      if (cpp_temp_file == NULL)
        {
          free (fileprefix);
          fatal (_("memory allocation failed"));
          return NULL;
        }
      
      snprintf (cpp_temp_file, len, "%s.irc", fileprefix);
      free (fileprefix);

      if (run_cmd (cmd, cpp_temp_file))
        {
          fatal (_("can't execute `%s': %s"), cmd, strerror (errno));
          return NULL;
        }

      stream = fopen (cpp_temp_file, FOPEN_RT);
      if (stream == NULL)
        {
          fatal (_("can't open temporary file `%s': %s"),
                 cpp_temp_file, strerror (errno));
          return NULL;
        }

      if (verbose)
        fprintf (stderr,
                 _("Using temporary file `%s' to read preprocessor output\n"),
                 cpp_temp_file);
    }
  else
    {
      stream = popen (cmd, FOPEN_RT);
      if (stream == NULL)
        {
          fatal (_("can't popen `%s': %s"), cmd, strerror (errno));
          return NULL;
        }
      
      if (verbose)
        fprintf (stderr, _("Using popen to read preprocessor output\n"));
    }

  cpp_pipe = stream;
  xatexit (close_input_stream);
  return cpp_pipe;
}

/* Determine if FILENAME contains special characters that
   can cause problems unless the entire filename is quoted.  */

static int filename_need_quotes(const char *filename)
{
    if (filename == NULL) {
        return 0;
    }
    
    if (filename[0] == '-' && filename[1] == '\0') {
        return 0;
    }

    const char *special_chars = "&<>|% ";
    
    for (const char *p = filename; *p != '\0'; p++) {
        if (strchr(special_chars, *p) != NULL) {
            return 1;
        }
    }
    
    return 0;
}

/* Look for the preprocessor program.  */

static FILE *
look_for_default (char *cmd, const char *prefix, int end_prefix,
		  const char *preprocargs, const char *filename)
{
  struct stat s;
  const char *fnquotes = "";
  char *out;
  int found = 0;
  
  if (cmd == NULL || prefix == NULL || filename == NULL) {
    return NULL;
  }
  
  if (filename_need_quotes (filename)) {
    fnquotes = "\"";
  }

  memcpy (cmd, prefix, end_prefix);
  out = stpcpy (cmd + end_prefix, DEFAULT_PREPROCESSOR_CMD);

  if (has_path_separator (cmd)) {
    found = (stat (cmd, &s) == 0);
#ifdef HAVE_EXECUTABLE_SUFFIX
    if (!found) {
      strcat (cmd, EXECUTABLE_SUFFIX);
      found = (stat (cmd, &s) == 0);
    }
#endif
    if (!found) {
      if (verbose) {
        fprintf (stderr, _("Tried `%s'\n"), cmd);
      }
      return NULL;
    }
  }

  if (filename_need_quotes (cmd)) {
    memmove (cmd + 1, cmd, out - cmd);
    cmd[0] = '"';
    out++;
    *out++ = '"';
  }

  sprintf (out, " %s %s %s%s%s",
           DEFAULT_PREPROCESSOR_ARGS, preprocargs, fnquotes, filename, fnquotes);

  if (verbose) {
    fprintf (stderr, _("Using `%s'\n"), cmd);
  }

  cpp_pipe = open_input_stream (cmd);
  return cpp_pipe;
}

static int has_path_separator (const char *cmd)
{
  if (cmd == NULL) {
    return 0;
  }
#if defined (__DJGPP__) || defined (__CYGWIN__) || defined (_WIN32)
  return (strchr (cmd, '\\') != NULL || strchr (cmd, '/') != NULL);
#else
  return (strchr (cmd, '/') != NULL);
#endif
}

/* Read an rc file.  */

rc_res_directory *
read_rc_file (const char *filename, const char *preprocessor,
              const char *preprocargs, int language, int use_temp_file)
{
  char *cmd = NULL;
  const char *fnquotes;
  const char *actual_filename;
  
  actual_filename = (filename != NULL) ? filename : "-";
  fnquotes = (filename_need_quotes(actual_filename) ? "\"" : "");
  
  if (filename != NULL)
    {
      setup_import_path(filename);
    }
  
  istream_type = (use_temp_file) ? ISTREAM_FILE : ISTREAM_PIPE;
  
  if (preprocargs == NULL)
    preprocargs = "";
  
  if (preprocessor)
    {
      cmd = create_preprocessor_command(preprocessor, preprocargs, 
                                        actual_filename, fnquotes);
      cpp_pipe = open_input_stream(cmd);
    }
  else
    {
      cmd = create_default_command();
      cpp_pipe = find_preprocessor(cmd, preprocargs, actual_filename);
    }
  
  free(cmd);
  
  rc_filename = xstrdup(actual_filename);
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
  
  return resources;
}

static void setup_import_path(const char *filename)
{
  char *edit, *dir;
  
  if (strchr(filename, '/') == NULL && strchr(filename, '\\') == NULL)
    return;
  
  dir = xmalloc(strlen(filename) + 3);
  edit = dir;
  
  if (filename[0] != '/' && filename[0] != '\\' && filename[1] != ':')
    {
      *edit++ = '.';
      *edit++ = '/';
    }
  
  edit = stpcpy(edit, filename);
  
  while (edit > dir && edit[-1] != '\\' && edit[-1] != '/')
    --edit;
  
  *--edit = '\0';
  
  while ((edit = strchr(dir, '\\')) != NULL)
    *edit = '/';
  
  windres_add_include_dir(dir);
}

static char *create_preprocessor_command(const char *preprocessor,
                                         const char *preprocargs,
                                         const char *filename,
                                         const char *fnquotes)
{
  size_t cmd_size = strlen(preprocessor) + strlen(preprocargs) + 
                    strlen(filename) + strlen(fnquotes) * 2 + 10;
  char *cmd = xmalloc(cmd_size);
  
  sprintf(cmd, "%s %s %s%s%s", preprocessor, preprocargs,
          fnquotes, filename, fnquotes);
  
  return cmd;
}

static char *create_default_command(void)
{
  size_t cmd_size = strlen(program_name) + 
                    strlen(DEFAULT_PREPROCESSOR_CMD) +
                    strlen(DEFAULT_PREPROCESSOR_ARGS) + 256;
  
#ifdef HAVE_EXECUTABLE_SUFFIX
  cmd_size += strlen(EXECUTABLE_SUFFIX);
#endif
  
  return xmalloc(cmd_size);
}

static FILE *find_preprocessor(char *cmd, const char *preprocargs,
                               const char *filename)
{
  FILE *pipe = NULL;
  char *dash = NULL;
  char *slash = NULL;
  char *cp;
  
  for (cp = program_name; *cp; cp++)
    {
      if (*cp == '-')
        dash = cp;
      if (is_path_separator(*cp))
        {
          slash = cp;
          dash = NULL;
        }
    }
  
  if (dash)
    {
      pipe = look_for_default(cmd, program_name, 
                             dash - program_name + 1,
                             preprocargs, filename);
    }
  
  if (!pipe && slash)
    {
      pipe = look_for_default(cmd, program_name,
                             slash - program_name + 1,
                             preprocargs, filename);
    }
  
  if (!pipe)
    {
      pipe = look_for_default(cmd, "", 0, preprocargs, filename);
    }
  
  return pipe;
}

static int is_path_separator(char c)
{
#if defined (__DJGPP__) || defined (__CYGWIN__) || defined(_WIN32)
  return (c == ':' || c == '\\' || c == '/');
#else
  return (c == '/');
#endif
}

/* Close the input stream if it is open.  */

static void close_input_stream(void)
{
    if (cpp_pipe == NULL) {
        return;
    }

    if (istream_type == ISTREAM_FILE) {
        fclose(cpp_pipe);
        if (cpp_temp_file != NULL) {
            int saved_errno = errno;
            unlink(cpp_temp_file);
            errno = saved_errno;
            free(cpp_temp_file);
        }
    } else {
        int err = pclose(cpp_pipe);
        if (err != 0 || errno == ECHILD) {
            cpp_pipe = NULL;
            cpp_temp_file = NULL;
            fatal(_("preprocessing failed."));
        }
    }

    cpp_pipe = NULL;
    cpp_temp_file = NULL;
}

/* Report an error while reading an rc file.  */

void yyerror(const char *msg)
{
    if (msg == NULL) {
        fatal("%s:%d: (null)", rc_filename, rc_lineno);
        return;
    }
    fatal("%s:%d: %s", rc_filename, rc_lineno, msg);
}

/* Issue a warning while reading an rc file.  */

void rcparse_warning(const char *msg)
{
    if (msg == NULL || rc_filename == NULL) {
        return;
    }
    
    if (fprintf(stderr, "%s:%d: %s\n", rc_filename, rc_lineno, msg) < 0) {
        return;
    }
}

/* Die if we get an unexpected end of file.  */

static void unexpected_eof(const char *msg)
{
    if (msg == NULL) {
        fatal(_("unexpected EOF"));
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
    
    return ((b2 & 0xff) << 8) | (b1 & 0xff);
}

/* Read a 32 bit word from a file.  The data is assumed to be little
   endian.  */

static unsigned long
get_long (FILE *e, const char *msg)
{
  unsigned char bytes[4];
  
  if (fread(bytes, 1, 4, e) != 4)
    unexpected_eof (msg);
  
  unsigned long result = bytes[0];
  result |= ((unsigned long)bytes[1] << 8);
  result |= ((unsigned long)bytes[2] << 16);
  result |= ((unsigned long)bytes[3] << 24);
  
  return result;
}

/* Read data from a file.  This is a wrapper to do error checking.  */

static void
get_data (FILE *e, bfd_byte *p, rc_uint_type c, const char *msg)
{
  if (e == NULL || p == NULL || msg == NULL || c == 0)
    {
      fatal (_("Invalid parameters for get_data"));
    }

  size_t bytes_to_read = (size_t) c;
  size_t bytes_read = fread (p, 1, bytes_to_read, e);
  
  if (bytes_read != bytes_to_read)
    {
      fatal (_("%s: read of %lu returned %lu"),
             msg, (unsigned long) c, (unsigned long) bytes_read);
    }
}

static rc_uint_type
target_get_16 (const void *p, size_t len)
{
  if (len < 2)
    fatal (_("not enough data"));
  return windres_get_16 (&wrtarget, p);
}

static rc_uint_type
target_get_32 (const void *p, size_t len)
{
  if (len < 4)
    fatal (_("not enough data"));
  return windres_get_32 (&wrtarget, p);
}

/* Define an accelerator resource.  */

void define_accelerator(rc_res_id id, const rc_res_res_info *resinfo, rc_accelerator *data)
{
    if (resinfo == NULL || data == NULL) {
        return;
    }

    rc_res_resource *r = define_standard_resource(&resources, RT_ACCELERATOR, id, resinfo->language, 0);
    if (r == NULL) {
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

void
define_bitmap (rc_res_id id, const rc_res_res_info *resinfo,
	       const char *filename)
{
  FILE *e = NULL;
  char *real_filename = NULL;
  struct stat s;
  bfd_byte *data = NULL;
  rc_uint_type i;
  rc_res_resource *r;
  size_t data_size;

  if (!resinfo || !filename)
    fatal (_("Invalid parameters for define_bitmap"));

  e = open_file_search (filename, FOPEN_RB, "bitmap file", &real_filename);
  if (!e)
    fatal (_("Failed to open bitmap file"));

  if (stat (real_filename, &s) < 0)
    {
      fclose (e);
      free (real_filename);
      fatal (_("stat failed on bitmap file `%s': %s"), real_filename,
	     strerror (errno));
    }

  if (s.st_size <= BITMAP_SKIP)
    {
      fclose (e);
      free (real_filename);
      fatal (_("Bitmap file `%s' too small"), real_filename);
    }

  data_size = s.st_size - BITMAP_SKIP;
  data = (bfd_byte *) res_alloc (data_size);
  if (!data)
    {
      fclose (e);
      free (real_filename);
      fatal (_("Memory allocation failed for bitmap data"));
    }

  for (i = 0; i < BITMAP_SKIP; i++)
    {
      if (getc (e) == EOF)
        {
          fclose (e);
          free (real_filename);
          fatal (_("Unexpected end of file in bitmap `%s'"), real_filename);
        }
    }

  get_data (e, data, data_size, real_filename);

  fclose (e);
  free (real_filename);

  r = define_standard_resource (&resources, RT_BITMAP, id,
				resinfo->language, 0);
  if (!r)
    fatal (_("Failed to define standard resource"));

  r->type = RES_TYPE_BITMAP;
  r->u.data.length = data_size;
  r->u.data.data = data;
  r->res_info = *resinfo;
}

/* Define a cursor resource.  A cursor file may contain a set of
   bitmaps, each representing the same cursor at various different
   resolutions.  They each get written out with a different ID.  The
   real cursor resource is then a group resource which can be used to
   select one of the actual cursors.  */

void
define_cursor (rc_res_id id, const rc_res_res_info *resinfo,
	       const char *filename)
{
  FILE *e = NULL;
  char *real_filename = NULL;
  int type, count, i;
  struct icondir *icondirs = NULL;
  int first_cursor;
  rc_res_resource *r;
  rc_group_cursor *first = NULL, **pp;

  e = open_file_search (filename, FOPEN_RB, "cursor file", &real_filename);
  if (!e)
    fatal (_("cannot open cursor file `%s'"), filename);

  get_word (e, real_filename);
  type = get_word (e, real_filename);
  count = get_word (e, real_filename);
  if (type != 2)
    {
      fclose (e);
      free (real_filename);
      fatal (_("cursor file `%s' does not contain cursor data"), real_filename);
    }

  if (count <= 0 || count > 65536)
    {
      fclose (e);
      free (real_filename);
      fatal (_("invalid cursor count in `%s'"), real_filename);
    }

  icondirs = (struct icondir *) xmalloc (count * sizeof *icondirs);

  for (i = 0; i < count; i++)
    {
      int ch;
      ch = getc (e);
      if (ch == EOF)
        {
          free (icondirs);
          fclose (e);
          free (real_filename);
          unexpected_eof (real_filename);
        }
      icondirs[i].width = ch;
      
      ch = getc (e);
      if (ch == EOF)
        {
          free (icondirs);
          fclose (e);
          free (real_filename);
          unexpected_eof (real_filename);
        }
      icondirs[i].height = ch;
      
      ch = getc (e);
      if (ch == EOF)
        {
          free (icondirs);
          fclose (e);
          free (real_filename);
          unexpected_eof (real_filename);
        }
      icondirs[i].colorcount = ch;
      
      if (getc (e) == EOF)
        {
          free (icondirs);
          fclose (e);
          free (real_filename);
          unexpected_eof (real_filename);
        }
      
      icondirs[i].u.cursor.xhotspot = get_word (e, real_filename);
      icondirs[i].u.cursor.yhotspot = get_word (e, real_filename);
      icondirs[i].bytes = get_long (e, real_filename);
      icondirs[i].offset = get_long (e, real_filename);
    }

  first_cursor = cursors;

  for (i = 0; i < count; i++)
    {
      bfd_byte *data;
      rc_res_id name;
      rc_cursor *c;

      if (fseek (e, icondirs[i].offset, SEEK_SET) != 0)
        {
          free (icondirs);
          fclose (e);
          free (real_filename);
          fatal (_("%s: fseek to %lu failed: %s"), real_filename,
                 icondirs[i].offset, strerror (errno));
        }

      data = (bfd_byte *) res_alloc (icondirs[i].bytes);
      get_data (e, data, icondirs[i].bytes, real_filename);

      c = (rc_cursor *) res_alloc (sizeof (rc_cursor));
      c->xhotspot = icondirs[i].u.cursor.xhotspot;
      c->yhotspot = icondirs[i].u.cursor.yhotspot;
      c->length = icondirs[i].bytes;
      c->data = data;

      ++cursors;

      name.named = 0;
      name.u.id = cursors;

      r = define_standard_resource (&resources, RT_CURSOR, name,
				    resinfo->language, 0);
      r->type = RES_TYPE_CURSOR;
      r->u.cursor = c;
      r->res_info = *resinfo;
    }

  fclose (e);
  free (real_filename);

  pp = &first;
  for (i = 0; i < count; i++)
    {
      rc_group_cursor *cg;

      cg = (rc_group_cursor *) res_alloc (sizeof (rc_group_cursor));
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

  free (icondirs);

  r = define_standard_resource (&resources, RT_GROUP_CURSOR, id,
				resinfo->language, 0);
  r->type = RES_TYPE_GROUP_CURSOR;
  r->u.group_cursor = first;
  r->res_info = *resinfo;
}

/* Define a dialog resource.  */

void define_dialog(rc_res_id id, const rc_res_res_info *resinfo, const rc_dialog *dialog)
{
    if (resinfo == NULL || dialog == NULL) {
        return;
    }

    rc_dialog *copy = (rc_dialog *)res_alloc(sizeof(rc_dialog));
    if (copy == NULL) {
        return;
    }

    *copy = *dialog;

    rc_res_resource *r = define_standard_resource(&resources, RT_DIALOG, id, resinfo->language, 0);
    if (r == NULL) {
        return;
    }

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
  rc_dialog_control *n = (rc_dialog_control *) res_alloc (sizeof (rc_dialog_control));
  if (n == NULL) {
    return NULL;
  }
  
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
  if (n == NULL)
    return NULL;
  
  n->text = iid;
  n->help = help;
  n->data = data;
  
  if (!ex)
    {
      if (help != 0)
        rcparse_warning (_("help ID requires DIALOGEX"));
      if (data != NULL)
        rcparse_warning (_("control data requires DIALOGEX"));
    }

  return n;
}

/* Define a font resource.  */

void
define_font (rc_res_id id, const rc_res_res_info *resinfo,
	     const char *filename)
{
  FILE *e = NULL;
  char *real_filename = NULL;
  struct stat s;
  bfd_byte *data = NULL;
  rc_res_resource *r;
  long offset;
  long fontdatalength;
  bfd_byte *fontdata;
  rc_fontdir *fd;
  const char *device, *face;
  rc_fontdir **pp;

  if (!resinfo || !filename)
    fatal (_("Invalid parameters for define_font"));

  e = open_file_search (filename, FOPEN_RB, "font file", &real_filename);
  if (!e)
    fatal (_("Failed to open font file"));

  if (stat (real_filename, &s) < 0)
    {
      fclose (e);
      free (real_filename);
      fatal (_("stat failed on font file `%s': %s"), real_filename,
	     strerror (errno));
    }

  if (s.st_size < 52)
    {
      fclose (e);
      free (real_filename);
      fatal (_("Font file `%s' is too small"), real_filename);
    }

  data = (bfd_byte *) res_alloc (s.st_size);
  if (!data)
    {
      fclose (e);
      free (real_filename);
      fatal (_("Memory allocation failed"));
    }

  get_data (e, data, s.st_size, real_filename);

  fclose (e);
  free (real_filename);

  r = define_standard_resource (&resources, RT_FONT, id,
				resinfo->language, 0);
  if (!r)
    fatal (_("Failed to define standard resource"));

  r->type = RES_TYPE_FONT;
  r->u.data.length = s.st_size;
  r->u.data.data = data;
  r->res_info = *resinfo;

  offset = (long)data[44] | ((long)data[45] << 8) | 
           ((long)data[46] << 16) | ((long)data[47] << 24);
  device = (offset > 0 && offset < s.st_size) ? (char *) data + offset : "";

  offset = (long)data[48] | ((long)data[49] << 8) | 
           ((long)data[50] << 16) | ((long)data[51] << 24);
  face = (offset > 0 && offset < s.st_size) ? (char *) data + offset : "";

  ++fonts;

  fontdatalength = 58 + strlen (device) + strlen (face);
  fontdata = (bfd_byte *) res_alloc (fontdatalength);
  if (!fontdata)
    fatal (_("Memory allocation failed"));

  memcpy (fontdata, data, 56);
  strcpy ((char *) fontdata + 56, device);
  strcpy ((char *) fontdata + 57 + strlen (device), face);

  fd = (rc_fontdir *) res_alloc (sizeof (rc_fontdir));
  if (!fd)
    fatal (_("Memory allocation failed"));

  fd->next = NULL;
  fd->index = fonts;
  fd->length = fontdatalength;
  fd->data = fontdata;

  pp = &fontdirs;
  while (*pp != NULL)
    pp = &(*pp)->next;
  *pp = fd;

  fontdirs_resinfo = *resinfo;
}

static void
define_font_rcdata (rc_res_id id, const rc_res_res_info *resinfo,
                    rc_rcdata_item *data)
{
  rc_res_resource *r;
  rc_uint_type len_data;
  bfd_byte *pb_data;

  if (resinfo == NULL || data == NULL)
    return;

  r = define_standard_resource (&resources, RT_FONT, id,
                                resinfo->language, 0);
  if (r == NULL)
    return;

  pb_data = rcdata_render_as_buffer (data, &len_data);
  if (pb_data == NULL)
    return;

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

    memset(&id, 0, sizeof(id));
    id.u.id = 1;

    r = define_standard_resource(&resources, RT_FONTDIR, id, 0x409, 0);
    if (r == NULL) {
        return;
    }

    r->type = RES_TYPE_FONTDIR;
    r->u.fontdir = fontdirs;
    r->res_info = fontdirs_resinfo;
}

static bfd_byte *
rcdata_render_as_buffer (const rc_rcdata_item *data, rc_uint_type *plen)
{
  const rc_rcdata_item *d;
  bfd_byte *ret = NULL;
  bfd_byte *pret = NULL;
  rc_uint_type len = 0;

  for (d = data; d != NULL; d = d->next)
    {
      len += rcdata_copy (d, NULL);
    }
    
  if (len == 0)
    {
      if (plen != NULL)
        {
          *plen = 0;
        }
      return NULL;
    }
    
  ret = (bfd_byte *) res_alloc (len);
  if (ret == NULL)
    {
      if (plen != NULL)
        {
          *plen = 0;
        }
      return NULL;
    }
    
  pret = ret;
  for (d = data; d != NULL; d = d->next)
    {
      pret += rcdata_copy (d, pret);
    }
    
  if (plen != NULL)
    {
      *plen = len;
    }
    
  return ret;
}

static void
define_fontdir_rcdata (rc_res_id id, const rc_res_res_info *resinfo,
                      rc_rcdata_item *data)
{
  rc_res_resource *r;
  rc_fontdir *fd_first = NULL;
  rc_fontdir *fd_cur = NULL;
  rc_uint_type len_data = 0;
  bfd_byte *pb_data;
  rc_uint_type count;
  rc_uint_type off = 2;

  r = define_standard_resource (&resources, RT_FONTDIR, id, 0x409, 0);
  if (!r)
    return;

  pb_data = rcdata_render_as_buffer (data, &len_data);
  if (!pb_data || len_data < 2)
    {
      r->type = RES_TYPE_FONTDIR;
      r->u.fontdir = NULL;
      r->res_info = *resinfo;
      return;
    }

  count = target_get_16 (pb_data, len_data);
  
  while (count > 0 && off < len_data)
    {
      const struct bin_fontdir_item *bfi;
      rc_fontdir *fd;
      size_t device_name_len;
      size_t face_name_len;
      rc_uint_type item_start = off;
      
      if (len_data - off < sizeof(struct bin_fontdir_item))
        break;
      
      bfi = (const struct bin_fontdir_item *)(pb_data + off);
      
      fd = (rc_fontdir *) res_alloc (sizeof (rc_fontdir));
      if (!fd)
        break;
      
      fd->index = target_get_16 ((bfd_byte *)&bfi->index, len_data - off);
      fd->data = pb_data + off;
      fd->next = NULL;
      
      off += 56;
      if (off >= len_data)
        {
          free(fd);
          break;
        }
      
      device_name_len = strnlen((char *)(pb_data + off), len_data - off);
      if (device_name_len >= len_data - off)
        {
          free(fd);
          break;
        }
      off += device_name_len + 1;
      
      if (off >= len_data)
        {
          free(fd);
          break;
        }
      
      face_name_len = strnlen((char *)(pb_data + off), len_data - off);
      if (face_name_len >= len_data - off)
        {
          free(fd);
          break;
        }
      off += face_name_len + 1;
      
      fd->length = off - item_start;
      
      if (!fd_first)
        fd_first = fd;
      else
        fd_cur->next = fd;
      fd_cur = fd;
      
      count--;
    }
  
  r->type = RES_TYPE_FONTDIR;
  r->u.fontdir = fd_first;
  r->res_info = *resinfo;
}

static void define_messagetable_rcdata(rc_res_id id, const rc_res_res_info *resinfo, rc_rcdata_item *data)
{
    rc_res_resource *r;
    rc_uint_type len_data;
    bfd_byte *pb_data;

    if (resinfo == NULL || data == NULL) {
        return;
    }

    r = define_standard_resource(&resources, RT_MESSAGETABLE, id, resinfo->language, 0);
    if (r == NULL) {
        return;
    }

    pb_data = rcdata_render_as_buffer(data, &len_data);
    if (pb_data == NULL) {
        return;
    }

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

void
define_icon (rc_res_id id, const rc_res_res_info *resinfo,
	     const char *filename)
{
  FILE *e;
  char *real_filename;
  int type, count, i;
  struct icondir *icondirs = NULL;
  int first_icon;
  rc_res_resource *r;
  rc_group_icon *first = NULL, **pp;

  e = open_file_search (filename, FOPEN_RB, "icon file", &real_filename);
  if (!e)
    fatal (_("cannot open icon file `%s'"), filename);

  get_word (e, real_filename);
  type = get_word (e, real_filename);
  count = get_word (e, real_filename);
  if (type != 1)
    {
      fclose (e);
      free (real_filename);
      fatal (_("icon file `%s' does not contain icon data"), real_filename);
    }

  if (count <= 0 || count > 65535)
    {
      fclose (e);
      free (real_filename);
      fatal (_("invalid icon count in `%s'"), real_filename);
    }

  icondirs = (struct icondir *) xmalloc (count * sizeof *icondirs);

  for (i = 0; i < count; i++)
    {
      int ch;
      
      ch = getc (e);
      if (ch == EOF)
        {
          free (icondirs);
          fclose (e);
          free (real_filename);
          unexpected_eof (real_filename);
        }
      icondirs[i].width = ch;
      
      ch = getc (e);
      if (ch == EOF)
        {
          free (icondirs);
          fclose (e);
          free (real_filename);
          unexpected_eof (real_filename);
        }
      icondirs[i].height = ch;
      
      ch = getc (e);
      if (ch == EOF)
        {
          free (icondirs);
          fclose (e);
          free (real_filename);
          unexpected_eof (real_filename);
        }
      icondirs[i].colorcount = ch;
      
      if (getc (e) == EOF)
        {
          free (icondirs);
          fclose (e);
          free (real_filename);
          unexpected_eof (real_filename);
        }
        
      icondirs[i].u.icon.planes = get_word (e, real_filename);
      icondirs[i].u.icon.bits = get_word (e, real_filename);
      icondirs[i].bytes = get_long (e, real_filename);
      icondirs[i].offset = get_long (e, real_filename);

      if (feof (e))
        {
          free (icondirs);
          fclose (e);
          free (real_filename);
          unexpected_eof (real_filename);
        }
    }

  first_icon = icons;

  for (i = 0; i < count; i++)
    {
      bfd_byte *data;
      rc_res_id name;

      if (fseek (e, icondirs[i].offset, SEEK_SET) != 0)
        {
          free (icondirs);
          fclose (e);
          free (real_filename);
          fatal (_("%s: fseek to %lu failed: %s"), real_filename,
                 icondirs[i].offset, strerror (errno));
        }

      data = (bfd_byte *) res_alloc (icondirs[i].bytes);

      get_data (e, data, icondirs[i].bytes, real_filename);

      ++icons;

      name.named = 0;
      name.u.id = icons;

      r = define_standard_resource (&resources, RT_ICON, name,
				    resinfo->language, 0);
      r->type = RES_TYPE_ICON;
      r->u.data.length = icondirs[i].bytes;
      r->u.data.data = data;
      r->res_info = *resinfo;
    }

  fclose (e);
  free (real_filename);

  pp = &first;
  for (i = 0; i < count; i++)
    {
      rc_group_icon *cg;

      cg = (rc_group_icon *) res_alloc (sizeof (rc_group_icon));
      cg->next = NULL;
      cg->width = icondirs[i].width;
      cg->height = icondirs[i].height;
      cg->colors = icondirs[i].colorcount;

      cg->planes = icondirs[i].u.icon.planes ? icondirs[i].u.icon.planes : 1;

      if (icondirs[i].u.icon.bits)
        cg->bits = icondirs[i].u.icon.bits;
      else
        {
          cg->bits = 0;
          while ((1L << cg->bits) < cg->colors)
            ++cg->bits;
        }

      cg->bytes = icondirs[i].bytes;
      cg->index = first_icon + i + 1;

      *pp = cg;
      pp = &(*pp)->next;
    }

  free (icondirs);

  r = define_standard_resource (&resources, RT_GROUP_ICON, id,
				resinfo->language, 0);
  r->type = RES_TYPE_GROUP_ICON;
  r->u.group_icon = first;
  r->res_info = *resinfo;
}

static void
define_group_icon_rcdata (rc_res_id id, const rc_res_res_info *resinfo,
			  rc_rcdata_item *data)
{
  rc_res_resource *r;
  rc_group_icon *first = NULL;
  rc_group_icon *cur = NULL;
  rc_uint_type len_data;
  bfd_byte *pb_data;

  pb_data = rcdata_render_as_buffer (data, &len_data);

  while (len_data >= 6)
    {
      unsigned short type = target_get_16 (pb_data + 2, len_data - 2);
      if (type != 1)
	fatal (_("unexpected group icon type %d"), type);
      
      int c = target_get_16 (pb_data + 4, len_data - 4);
      len_data -= 6;
      pb_data += 6;

      for (int i = 0; i < c; i++)
	{
	  if (len_data < 14)
	    fatal ("too small group icon rcdata");
	    
	  rc_group_icon *cg = (rc_group_icon *) res_alloc (sizeof (rc_group_icon));
	  cg->next = NULL;
	  cg->width = pb_data[0];
	  cg->height = pb_data[1];
	  cg->colors = pb_data[2];
	  cg->planes = target_get_16 (pb_data + 4, len_data - 4);
	  cg->bits = target_get_16 (pb_data + 6, len_data - 6);
	  cg->bytes = target_get_32 (pb_data + 8, len_data - 8);
	  cg->index = target_get_16 (pb_data + 12, len_data - 12);
	  
	  if (!first)
	    first = cg;
	  else
	    cur->next = cg;
	  cur = cg;
	  
	  pb_data += 14;
	  len_data -= 14;
	}
    }
    
  r = define_standard_resource (&resources, RT_GROUP_ICON, id,
				resinfo->language, 0);
  r->type = RES_TYPE_GROUP_ICON;
  r->u.group_icon = first;
  r->res_info = *resinfo;
}

static void
define_group_cursor_rcdata (rc_res_id id, const rc_res_res_info *resinfo,
			    rc_rcdata_item *data)
{
  rc_res_resource *r;
  rc_group_cursor *first = NULL;
  rc_group_cursor *cur = NULL;
  rc_uint_type len_data;
  bfd_byte *pb_data;
  const rc_uint_type HEADER_SIZE = 6;
  const rc_uint_type CURSOR_ENTRY_SIZE = 14;
  const unsigned short EXPECTED_TYPE = 2;

  pb_data = rcdata_render_as_buffer (data, &len_data);
  if (!pb_data) {
    fatal (_("failed to render rcdata"));
  }

  while (len_data >= HEADER_SIZE)
    {
      unsigned short type;
      int cursor_count;
      int i;

      if (len_data < 4) {
        fatal (_("insufficient data for group cursor header"));
      }
      
      type = target_get_16 (pb_data + 2, len_data - 2);
      if (type != EXPECTED_TYPE) {
        fatal (_("unexpected group cursor type %d"), type);
      }
      
      cursor_count = target_get_16 (pb_data + 4, len_data - 4);
      len_data -= HEADER_SIZE;
      pb_data += HEADER_SIZE;

      if (len_data < (rc_uint_type)(cursor_count * CURSOR_ENTRY_SIZE)) {
        fatal (_("insufficient data for group cursor entries"));
      }

      for (i = 0; i < cursor_count; i++)
        {
          rc_group_cursor *cg;
          
          if (len_data < CURSOR_ENTRY_SIZE) {
            fatal (_("too small group icon rcdata"));
          }
          
          cg = (rc_group_cursor *) res_alloc (sizeof (rc_group_cursor));
          if (!cg) {
            fatal (_("memory allocation failed"));
          }
          
          cg->next = NULL;
          cg->width = target_get_16 (pb_data, len_data);
          cg->height = target_get_16 (pb_data + 2, len_data - 2);
          cg->planes = target_get_16 (pb_data + 4, len_data - 4);
          cg->bits = target_get_16 (pb_data + 6, len_data - 6);
          cg->bytes = target_get_32 (pb_data + 8, len_data - 8);
          cg->index = target_get_16 (pb_data + 12, len_data - 12);
          
          if (!first) {
            first = cg;
            cur = cg;
          } else {
            cur->next = cg;
            cur = cg;
          }
          
          pb_data += CURSOR_ENTRY_SIZE;
          len_data -= CURSOR_ENTRY_SIZE;
        }
    }

  r = define_standard_resource (&resources, RT_GROUP_ICON, id,
				resinfo->language, 0);
  if (!r) {
    fatal (_("failed to define standard resource"));
  }
  
  r->type = RES_TYPE_GROUP_CURSOR;
  r->u.group_cursor = first;
  r->res_info = *resinfo;
}

static void
define_cursor_rcdata (rc_res_id id, const rc_res_res_info *resinfo,
		      rc_rcdata_item *data)
{
  rc_cursor *c;
  rc_res_resource *r;
  rc_uint_type len_data;
  bfd_byte *pb_data;

  if (!data || !resinfo) {
    return;
  }

  pb_data = rcdata_render_as_buffer (data, &len_data);
  if (!pb_data || len_data < BIN_CURSOR_SIZE) {
    return;
  }

  c = (rc_cursor *) res_alloc (sizeof (rc_cursor));
  if (!c) {
    return;
  }

  c->xhotspot = target_get_16 (pb_data, len_data);
  c->yhotspot = target_get_16 (pb_data + 2, len_data - 2);
  c->length = len_data - BIN_CURSOR_SIZE;
  c->data = (const bfd_byte *) (data + BIN_CURSOR_SIZE);

  r = define_standard_resource (&resources, RT_CURSOR, id, resinfo->language, 0);
  if (!r) {
    return;
  }

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

  if (resinfo == NULL || data == NULL) {
    return;
  }

  pb_data = rcdata_render_as_buffer (data, &len_data);
  if (pb_data == NULL) {
    return;
  }

  r = define_standard_resource (&resources, RT_BITMAP, id, resinfo->language, 0);
  if (r == NULL) {
    free(pb_data);
    return;
  }

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

  if (resinfo == NULL || data == NULL) {
    return;
  }

  pb_data = rcdata_render_as_buffer (data, &len_data);
  if (pb_data == NULL) {
    return;
  }

  r = define_standard_resource (&resources, RT_ICON, id, resinfo->language, 0);
  if (r == NULL) {
    free (pb_data);
    return;
  }

  r->type = RES_TYPE_ICON;
  r->u.data.length = len_data;
  r->u.data.data = pb_data;
  r->res_info = *resinfo;
}

/* Define a menu resource.  */

void define_menu(rc_res_id id, const rc_res_res_info *resinfo, rc_menuitem *menuitems)
{
    if (resinfo == NULL) {
        return;
    }

    rc_menu *menu = (rc_menu *)res_alloc(sizeof(rc_menu));
    if (menu == NULL) {
        return;
    }

    menu->items = menuitems;
    menu->help = 0;

    rc_res_resource *resource = define_standard_resource(&resources, RT_MENU, id, resinfo->language, 0);
    if (resource == NULL) {
        return;
    }

    resource->type = RES_TYPE_MENU;
    resource->u.menu = menu;
    resource->res_info = *resinfo;
}

/* Define a menu item.  This does not define a resource, but merely
   allocates and fills in a structure.  */

rc_menuitem *
define_menuitem (const unichar *text, rc_uint_type menuid, rc_uint_type type,
		 rc_uint_type state, rc_uint_type help,
		 rc_menuitem *menuitems)
{
  rc_menuitem *mi;

  if (text == NULL)
    return NULL;

  mi = (rc_menuitem *) res_alloc (sizeof (rc_menuitem));
  if (mi == NULL)
    return NULL;

  mi->next = NULL;
  mi->type = type;
  mi->state = state;
  mi->id = menuid;
  mi->text = unichar_dup (text);
  if (mi->text == NULL)
    {
      free (mi);
      return NULL;
    }
  mi->help = help;
  mi->popup = menuitems;
  return mi;
}

/* Define a messagetable resource.  */

void define_messagetable(rc_res_id id, const rc_res_res_info *resinfo, const char *filename)
{
    FILE *file = NULL;
    char *real_filename = NULL;
    struct stat file_stats;
    bfd_byte *data = NULL;
    rc_res_resource *resource = NULL;
    
    if (!resinfo || !filename) {
        fatal(_("Invalid parameters for define_messagetable"));
    }
    
    file = open_file_search(filename, FOPEN_RB, "messagetable file", &real_filename);
    if (!file) {
        fatal(_("Failed to open messagetable file '%s'"), filename);
    }
    
    if (stat(real_filename, &file_stats) < 0) {
        fclose(file);
        free(real_filename);
        fatal(_("stat failed on bitmap file '%s': %s"), real_filename, strerror(errno));
    }
    
    if (file_stats.st_size == 0) {
        fclose(file);
        free(real_filename);
        fatal(_("Empty messagetable file '%s'"), real_filename);
    }
    
    data = (bfd_byte *)res_alloc(file_stats.st_size);
    if (!data) {
        fclose(file);
        free(real_filename);
        fatal(_("Memory allocation failed for messagetable data"));
    }
    
    get_data(file, data, file_stats.st_size, real_filename);
    
    fclose(file);
    
    resource = define_standard_resource(&resources, RT_MESSAGETABLE, id, resinfo->language, 0);
    if (!resource) {
        free(real_filename);
        fatal(_("Failed to define standard resource for messagetable"));
    }
    
    resource->type = RES_TYPE_MESSAGETABLE;
    resource->u.data.length = file_stats.st_size;
    resource->u.data.data = data;
    resource->res_info = *resinfo;
    
    free(real_filename);
}

/* Define an rcdata resource.  */

void define_rcdata(rc_res_id id, const rc_res_res_info *resinfo, rc_rcdata_item *data)
{
    if (resinfo == NULL) {
        return;
    }
    
    rc_res_resource *r = define_standard_resource(&resources, RT_RCDATA, id, resinfo->language, 0);
    if (r == NULL) {
        return;
    }
    
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

  if (string == NULL || len == 0)
    return NULL;

  ri = (rc_rcdata_item *) res_alloc (sizeof (rc_rcdata_item));
  if (ri == NULL)
    return NULL;

  s = (char *) res_alloc (len);
  if (s == NULL)
    {
      free (ri);
      return NULL;
    }

  memcpy (s, string, len);
  
  ri->next = NULL;
  ri->type = RCDATA_STRING;
  ri->u.string.length = len;
  ri->u.string.s = s;

  return ri;
}

/* Create an rcdata item holding a unicode string.  */

rc_rcdata_item *
define_rcdata_unistring (const unichar *string, rc_uint_type len)
{
  rc_rcdata_item *ri;
  unichar *s;
  size_t alloc_size;

  if (string == NULL || len == 0)
    return NULL;

  ri = (rc_rcdata_item *) res_alloc (sizeof (rc_rcdata_item));
  if (ri == NULL)
    return NULL;

  alloc_size = len * sizeof (unichar);
  s = (unichar *) res_alloc (alloc_size);
  if (s == NULL)
    return NULL;

  memcpy (s, string, alloc_size);

  ri->next = NULL;
  ri->type = RCDATA_WSTRING;
  ri->u.wstring.length = len;
  ri->u.wstring.w = s;

  return ri;
}

/* Create an rcdata item holding a number.  */

rc_rcdata_item *
define_rcdata_number (rc_uint_type val, int dword)
{
  rc_rcdata_item *ri = (rc_rcdata_item *) res_alloc (sizeof (rc_rcdata_item));
  if (ri == NULL)
    return NULL;
    
  ri->next = NULL;
  ri->type = (dword != 0) ? RCDATA_DWORD : RCDATA_WORD;
  ri->u.word = val;

  return ri;
}

/* Define a stringtable resource.  This is called for each string
   which appears in a STRINGTABLE statement.  */

void define_stringtable(const rc_res_res_info *resinfo,
                        rc_uint_type stringid, const unichar *string, int len)
{
    if (!resinfo) {
        return;
    }

    rc_res_id id;
    id.named = 0;
    id.u.id = (stringid >> 4) + 1;
    
    rc_res_resource *r = define_standard_resource(&resources, RT_STRING, id,
                                                  resinfo->language, 1);
    if (!r) {
        return;
    }

    if (r->type == RES_TYPE_UNINITIALIZED) {
        r->type = RES_TYPE_STRINGTABLE;
        r->u.stringtable = (rc_stringtable *)res_alloc(sizeof(rc_stringtable));
        if (!r->u.stringtable) {
            return;
        }
        
        for (int i = 0; i < 16; i++) {
            r->u.stringtable->strings[i].length = 0;
            r->u.stringtable->strings[i].string = NULL;
        }
        
        r->res_info = *resinfo;
    }
    
    if (!r->u.stringtable) {
        return;
    }
    
    size_t alloc_size = ((size_t)len + 1) * sizeof(unichar);
    unichar *h = (unichar *)res_alloc(alloc_size);
    if (!h) {
        return;
    }
    
    if (len > 0 && string) {
        memcpy(h, string, (size_t)len * sizeof(unichar));
    }
    h[len] = 0;
    
    int index = stringid & 0xf;
    r->u.stringtable->strings[index].length = (rc_uint_type)len;
    r->u.stringtable->strings[index].string = h;
}

void define_toolbar(rc_res_id id, rc_res_res_info *resinfo, rc_uint_type width, rc_uint_type height, rc_toolbar_item *items)
{
    if (resinfo == NULL) {
        return;
    }

    rc_toolbar *t = (rc_toolbar *)res_alloc(sizeof(rc_toolbar));
    if (t == NULL) {
        return;
    }

    t->button_width = width;
    t->button_height = height;
    t->items = items;
    
    size_t count = 0;
    rc_toolbar_item *current = items;
    while (current != NULL) {
        count++;
        current = current->next;
    }
    t->nitems = count;
    
    rc_res_resource *r = define_standard_resource(&resources, RT_TOOLBAR, id, resinfo->language, 0);
    if (r == NULL) {
        return;
    }
    
    r->type = RES_TYPE_TOOLBAR;
    r->u.toolbar = t;
    r->res_info = *resinfo;
}

/* Define a user data resource where the data is in the rc file.  */

void
define_user_data (rc_res_id id, rc_res_id type,
		  const rc_res_res_info *resinfo,
		  rc_rcdata_item *data)
{
  rc_res_id ids[3];
  rc_res_resource *r;
  bfd_byte *pb_data;
  rc_uint_type len_data;

  if (!resinfo || !data)
    return;

  if (type.named == 0)
    {
      switch (type.u.id)
      {
      case RT_FONTDIR:
	define_fontdir_rcdata (id, resinfo, data);
	return;
      case RT_FONT:
	define_font_rcdata (id, resinfo, data);
	return;
      case RT_ICON:
	define_icon_rcdata (id, resinfo, data);
	return;
      case RT_BITMAP:
	define_bitmap_rcdata (id, resinfo, data);
	return;
      case RT_CURSOR:
	define_cursor_rcdata (id, resinfo, data);
	return;
      case RT_GROUP_ICON:
	define_group_icon_rcdata (id, resinfo, data);
	return;
      case RT_GROUP_CURSOR:
	define_group_cursor_rcdata (id, resinfo, data);
	return;
      case RT_MESSAGETABLE:
	define_messagetable_rcdata (id, resinfo, data);
	return;
      default:
	break;
      }
    }
  
  ids[0] = type;
  ids[1] = id;
  ids[2].named = 0;
  ids[2].u.id = resinfo->language;

  r = define_resource (&resources, 3, ids, 0);
  if (!r)
    return;
    
  r->type = RES_TYPE_USERDATA;
  r->u.userdata = (rc_rcdata_item *) res_alloc (sizeof (rc_rcdata_item));
  if (!r->u.userdata)
    return;
    
  r->u.userdata->next = NULL;
  r->u.userdata->type = RCDATA_BUFFER;
  
  pb_data = rcdata_render_as_buffer (data, &len_data);
  if (!pb_data)
    {
      r->u.userdata = NULL;
      return;
    }
    
  r->u.userdata->u.buffer.length = len_data;
  r->u.userdata->u.buffer.data = pb_data;
  r->res_info = *resinfo;
}

void define_rcdata_file(rc_res_id id, const rc_res_res_info *resinfo, const char *filename)
{
    if (filename == NULL) {
        fatal(_("NULL filename provided"));
    }

    char *real_filename = NULL;
    FILE *e = open_file_search(filename, FOPEN_RB, "file", &real_filename);
    if (e == NULL) {
        fatal(_("Failed to open file `%s'"), filename);
    }

    struct stat s;
    if (stat(real_filename, &s) < 0) {
        int saved_errno = errno;
        fclose(e);
        free(real_filename);
        fatal(_("stat failed on file `%s': %s"), real_filename, strerror(saved_errno));
    }

    if (s.st_size < 0 || s.st_size > SIZE_MAX) {
        fclose(e);
        free(real_filename);
        fatal(_("Invalid file size for `%s'"), real_filename);
    }

    bfd_byte *data = (bfd_byte *)res_alloc(s.st_size);
    if (data == NULL && s.st_size > 0) {
        fclose(e);
        free(real_filename);
        fatal(_("Memory allocation failed for file `%s'"), real_filename);
    }

    get_data(e, data, s.st_size, real_filename);
    fclose(e);
    free(real_filename);

    rc_rcdata_item *ri = (rc_rcdata_item *)res_alloc(sizeof(rc_rcdata_item));
    if (ri == NULL) {
        fatal(_("Memory allocation failed for rcdata item"));
    }

    ri->next = NULL;
    ri->type = RCDATA_BUFFER;
    ri->u.buffer.length = s.st_size;
    ri->u.buffer.data = data;

    define_rcdata(id, resinfo, ri);
}

/* Define a user data resource where the data is in a file.  */

void
define_user_file (rc_res_id id, rc_res_id type,
		  const rc_res_res_info *resinfo, const char *filename)
{
  FILE *e = NULL;
  char *real_filename = NULL;
  struct stat s;
  bfd_byte *data = NULL;
  rc_res_id ids[3];
  rc_res_resource *r;
  rc_rcdata_item *userdata;

  if (!resinfo || !filename)
    fatal (_("Invalid parameters for define_user_file"));

  e = open_file_search (filename, FOPEN_RB, "file", &real_filename);
  if (!e)
    fatal (_("Cannot open file `%s'"), filename);

  if (stat (real_filename, &s) < 0)
    {
      fclose (e);
      free (real_filename);
      fatal (_("stat failed on file `%s': %s"), real_filename,
	     strerror (errno));
    }

  if (s.st_size == 0 || s.st_size > INT_MAX)
    {
      fclose (e);
      free (real_filename);
      fatal (_("Invalid file size for `%s'"), real_filename);
    }

  data = (bfd_byte *) res_alloc (s.st_size);
  if (!data)
    {
      fclose (e);
      free (real_filename);
      fatal (_("Memory allocation failed for file `%s'"), real_filename);
    }

  get_data (e, data, s.st_size, real_filename);

  fclose (e);
  free (real_filename);

  ids[0] = type;
  ids[1] = id;
  ids[2].named = 0;
  ids[2].u.id = resinfo->language;

  r = define_resource (&resources, 3, ids, 0);
  if (!r)
    fatal (_("Failed to define resource"));

  userdata = (rc_rcdata_item *) res_alloc (sizeof (rc_rcdata_item));
  if (!userdata)
    fatal (_("Memory allocation failed for userdata"));

  userdata->next = NULL;
  userdata->type = RCDATA_BUFFER;
  userdata->u.buffer.length = s.st_size;
  userdata->u.buffer.data = data;

  r->type = RES_TYPE_USERDATA;
  r->u.userdata = userdata;
  r->res_info = *resinfo;
}

/* Define a versioninfo resource.  */

void define_versioninfo(rc_res_id id, rc_uint_type language,
                        rc_fixed_versioninfo *fixedverinfo,
                        rc_ver_info *verinfo)
{
    rc_res_resource *r = define_standard_resource(&resources, RT_VERSION, id, language, 0);
    if (r == NULL) {
        return;
    }

    rc_versioninfo *version_info = (rc_versioninfo *)res_alloc(sizeof(rc_versioninfo));
    if (version_info == NULL) {
        return;
    }

    version_info->fixed = fixedverinfo;
    version_info->var = verinfo;

    r->type = RES_TYPE_VERSIONINFO;
    r->u.versioninfo = version_info;
    r->res_info.language = language;
}

/* Add string version info to a list of version information.  */

rc_ver_info *
append_ver_stringfileinfo (rc_ver_info *verinfo,
                          rc_ver_stringtable *stringtables)
{
  rc_ver_info *vi;
  rc_ver_info **pp;

  if (stringtables == NULL) {
    return verinfo;
  }

  vi = (rc_ver_info *) res_alloc (sizeof (rc_ver_info));
  if (vi == NULL) {
    return verinfo;
  }

  vi->next = NULL;
  vi->type = VERINFO_STRING;
  vi->u.string.stringtables = stringtables;

  pp = &verinfo;
  while (*pp != NULL) {
    pp = &(*pp)->next;
  }
  *pp = vi;

  return verinfo;
}

rc_ver_stringtable *
append_ver_stringtable (rc_ver_stringtable *stringtable,
			const char *language,
			rc_ver_stringinfo *strings)
{
  rc_ver_stringtable *vst;
  rc_ver_stringtable **pp;

  if (language == NULL || strings == NULL) {
    return stringtable;
  }

  vst = (rc_ver_stringtable *) res_alloc (sizeof (rc_ver_stringtable));
  if (vst == NULL) {
    return stringtable;
  }

  vst->next = NULL;
  vst->strings = strings;
  
  if (unicode_from_ascii ((rc_uint_type *) NULL, &vst->language, language) != 0) {
    return stringtable;
  }

  pp = &stringtable;
  while (*pp != NULL) {
    pp = &(*pp)->next;
  }
  *pp = vst;

  return stringtable;
}

/* Add variable version info to a list of version information.  */

rc_ver_info *
append_ver_varfileinfo (rc_ver_info *verinfo, const unichar *key,
			rc_ver_varinfo *var)
{
  rc_ver_info *vi;
  rc_ver_info **pp;

  if (key == NULL || var == NULL) {
    return verinfo;
  }

  vi = (rc_ver_info *) res_alloc (sizeof *vi);
  if (vi == NULL) {
    return verinfo;
  }

  vi->next = NULL;
  vi->type = VERINFO_VAR;
  vi->u.var.key = unichar_dup (key);
  if (vi->u.var.key == NULL) {
    return verinfo;
  }
  vi->u.var.var = var;

  pp = &verinfo;
  while (*pp != NULL) {
    pp = &(*pp)->next;
  }
  *pp = vi;

  return verinfo;
}

/* Append version string information to a list.  */

rc_ver_stringinfo *
append_verval (rc_ver_stringinfo *strings, const unichar *key,
	       const unichar *value)
{
  rc_ver_stringinfo *vs;
  rc_ver_stringinfo **pp;

  if (key == NULL || value == NULL)
    return strings;

  vs = (rc_ver_stringinfo *) res_alloc (sizeof (rc_ver_stringinfo));
  if (vs == NULL)
    return strings;

  vs->next = NULL;
  vs->key = unichar_dup (key);
  if (vs->key == NULL)
    {
      free (vs);
      return strings;
    }

  vs->value = unichar_dup (value);
  if (vs->value == NULL)
    {
      free (vs->key);
      free (vs);
      return strings;
    }

  pp = &strings;
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
  rc_ver_varinfo *vv;
  rc_ver_varinfo **pp;

  vv = (rc_ver_varinfo *) res_alloc (sizeof (rc_ver_varinfo));
  if (vv == NULL)
    return var;
    
  vv->next = NULL;
  vv->language = language;
  vv->charset = charset;

  pp = &var;
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

static void indent(FILE *e, int c)
{
    if (e == NULL || c <= 0) {
        return;
    }
    
    for (int i = 0; i < c; i++) {
        if (putc(' ', e) == EOF) {
            break;
        }
    }
}

/* Dump the resources we have read in the format of an rc file.

   Reasoned by the fact, that some resources need to be stored into file and
   refer to that file, we use the user-data model for that to express it binary
   without the need to store it somewhere externally.  */

bool
write_rc_file (const char *filename, const rc_res_directory *res_dir)
{
  FILE *e = stdout;
  rc_uint_type language = (rc_uint_type) ((bfd_signed_vma) -1);

  if (filename != NULL)
    {
      e = fopen (filename, FOPEN_WT);
      if (e == NULL)
	{
	  non_fatal (_("can't open `%s' for output: %s"),
		     filename, strerror (errno));
	  return false;
	}
    }

  write_rc_directory (e, res_dir, NULL, NULL, &language, 1);
  
  if (filename != NULL && e != NULL)
    {
      if (fclose (e) != 0)
	{
	  non_fatal (_("error closing `%s': %s"),
		     filename, strerror (errno));
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

static void
write_rc_directory (FILE *e, const rc_res_directory *rd,
		    const rc_res_id *type, const rc_res_id *name,
		    rc_uint_type *language, int level)
{
  const rc_res_entry *re;

  if (rd->time != 0 || rd->characteristics != 0 || rd->major != 0 || rd->minor != 0)
    {
      wr_printcomment (e, "COFF information not part of RC");
      if (rd->time != 0)
        wr_printcomment (e, "Time stamp: %u", rd->time);
      if (rd->characteristics != 0)
        wr_printcomment (e, "Characteristics: %u", rd->characteristics);
      if (rd->major != 0 || rd->minor != 0)
        wr_printcomment (e, "Version major:%d minor:%d", rd->major, rd->minor);
    }

  for (re = rd->entries; re != NULL; re = re->next)
    {
      process_resource_entry(e, re, &type, &name, language, level);
    }
  
  if (rd->entries == NULL)
    {
      wr_print_flush (e);
    }
}

static void
process_resource_entry(FILE *e, const rc_res_entry *re,
                      const rc_res_id **type, const rc_res_id **name,
                      rc_uint_type *language, int level)
{
  update_resource_context(re, type, name, language, level, e);
  
  if (re->subdir)
    {
      write_rc_subdir (e, re, *type, *name, language, level);
    }
  else
    {
      output_resource_data(e, *type, *name, re->u.res, language, level);
    }
}

static void
update_resource_context(const rc_res_entry *re,
                       const rc_res_id **type, const rc_res_id **name,
                       rc_uint_type *language, int level, FILE *e)
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
      update_language_if_needed(re, language, e);
      break;
    default:
      break;
    }
}

static void
update_language_if_needed(const rc_res_entry *re, rc_uint_type *language, FILE *e)
{
  if (!re->id.named &&
      re->id.u.id != (unsigned long)(unsigned int)*language &&
      (re->id.u.id & 0xffff) == re->id.u.id)
    {
      wr_print (e, "LANGUAGE %u, %u\n",
               re->id.u.id & ((1 << SUBLANG_SHIFT) - 1),
               (re->id.u.id >> SUBLANG_SHIFT) & 0xff);
      *language = re->id.u.id;
    }
}

static void
output_resource_data(FILE *e, const rc_res_id *type, const rc_res_id *name,
                    const rc_resource *res, rc_uint_type *language, int level)
{
  if (level == 3)
    {
      write_rc_resource (e, type, name, res, language);
    }
  else
    {
      wr_printcomment (e, "Resource at unexpected level %d", level);
      write_rc_resource (e, type, (rc_res_id *) NULL, res, language);
    }
}

/* Write out a subdirectory entry.  E is the file to write to.  RE is
   the subdirectory entry.  TYPE and NAME are pointers to higher level
   IDs, or NULL.  LANGUAGE is a pointer to the current language.
   LEVEL is the level in the tree.  */

static void
write_rc_subdir (FILE *e, const rc_res_entry *re,
		 const rc_res_id *type, const rc_res_id *name,
		 rc_uint_type *language, int level)
{
  if (e == NULL || re == NULL) {
    return;
  }

  fprintf (e, "\n");
  
  if (level == 1) {
    wr_printcomment (e, "Type: ");
    if (re->id.named) {
      res_id_print (e, re->id, 1);
    } else {
      const char *s = get_resource_type_name(re->id.u.id);
      if (s != NULL) {
        fprintf (e, "%s", s);
      } else {
        res_id_print (e, re->id, 1);
      }
    }
  } else if (level == 2) {
    wr_printcomment (e, "Name: ");
    res_id_print (e, re->id, 1);
  } else if (level == 3) {
    wr_printcomment (e, "Language: ");
    res_id_print (e, re->id, 1);
  } else {
    wr_printcomment (e, "Level %d: ", level);
    res_id_print (e, re->id, 1);
  }

  write_rc_directory (e, re->u.dir, type, name, language, level + 1);
}

static const char *
get_resource_type_name(unsigned int id)
{
  switch (id) {
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

/* Write out a single resource.  E is the file to write to.  TYPE is a
   pointer to the type of the resource.  NAME is a pointer to the name
   of the resource; it will be NULL if there is a level mismatch.  RES
   is the resource data.  LANGUAGE is a pointer to the current
   language.  */

static void
write_rc_resource (FILE *e, const rc_res_id *type,
		   const rc_res_id *name, const rc_res_resource *res,
		   rc_uint_type *language)
{
  const char *s;
  int rt;
  int menuex = 0;

  if (!e || !res || !language)
    return;

  switch (res->type)
    {
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
      menuex = extended_menu(res->u.menu);
      s = menuex ? "MENUEX" : "MENU";
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
      return;
    }

  if (rt != 0 && type && (type->named || type->u.id != (unsigned long)rt))
    {
      wr_printcomment(e, "Unexpected resource type mismatch: ");
      res_id_print(e, *type, 1);
      fprintf(e, " != %d", rt);
    }

  if (res->coff_info.codepage != 0)
    wr_printcomment(e, "Code page: %u", res->coff_info.codepage);
  if (res->coff_info.reserved != 0)
    wr_printcomment(e, "COFF reserved value: %u", res->coff_info.reserved);

  wr_print(e, "\n");
  
  if (rt != RT_STRING)
    {
      if (name)
        res_id_print(e, *name, 1);
      else
        fprintf(e, "??Unknown-Name??");
      fprintf(e, " ");
    }

  if (s)
    fprintf(e, "%s", s);
  else if (type)
    {
      if (!type->named)
        {
          switch (type->u.id)
            {
            case RT_MANIFEST:
              fprintf(e, "%u /* RT_MANIFEST */", RT_MANIFEST);
              break;
            case RT_ANICURSOR:
              fprintf(e, "%u /* RT_ANICURSOR */", RT_ANICURSOR);
              break;
            case RT_ANIICON:
              fprintf(e, "%u /* RT_ANIICON */", RT_ANIICON);
              break;
            case RT_RCDATA:
              fprintf(e, "%u /* RT_RCDATA */", RT_RCDATA);
              break;
            case RT_ICON:
              fprintf(e, "%u /* RT_ICON */", RT_ICON);
              break;
            case RT_CURSOR:
              fprintf(e, "%u /* RT_CURSOR */", RT_CURSOR);
              break;
            case RT_BITMAP:
              fprintf(e, "%u /* RT_BITMAP */", RT_BITMAP);
              break;
            case RT_PLUGPLAY:
              fprintf(e, "%u /* RT_PLUGPLAY */", RT_PLUGPLAY);
              break;
            case RT_VXD:
              fprintf(e, "%u /* RT_VXD */", RT_VXD);
              break;
            case RT_FONT:
              fprintf(e, "%u /* RT_FONT */", RT_FONT);
              break;
            case RT_FONTDIR:
              fprintf(e, "%u /* RT_FONTDIR */", RT_FONTDIR);
              break;
            case RT_HTML:
              fprintf(e, "%u /* RT_HTML */", RT_HTML);
              break;
            case RT_MESSAGETABLE:
              fprintf(e, "%u /* RT_MESSAGETABLE */", RT_MESSAGETABLE);
              break;
            case RT_DLGINCLUDE:
              fprintf(e, "%u /* RT_DLGINCLUDE */", RT_DLGINCLUDE);
              break;
            case RT_DLGINIT:
              fprintf(e, "%u /* RT_DLGINIT */", RT_DLGINIT);
              break;
            default:
              res_id_print(e, *type, 0);
              break;
            }
        }
      else
        res_id_print(e, *type, 1);
    }
  else
    fprintf(e, "??Unknown-Type??");

  if (res->res_info.memflags != 0)
    {
      if (res->res_info.memflags & MEMFLAG_MOVEABLE)
        fprintf(e, " MOVEABLE");
      if (res->res_info.memflags & MEMFLAG_PURE)
        fprintf(e, " PURE");
      if (res->res_info.memflags & MEMFLAG_PRELOAD)
        fprintf(e, " PRELOAD");
      if (res->res_info.memflags & MEMFLAG_DISCARDABLE)
        fprintf(e, " DISCARDABLE");
    }

  if (res->type == RES_TYPE_DIALOG && res->u.dialog)
    {
      fprintf(e, " %d, %d, %d, %d",
              (int)res->u.dialog->x, (int)res->u.dialog->y,
              (int)res->u.dialog->width, (int)res->u.dialog->height);
      if (res->u.dialog->ex && res->u.dialog->ex->help != 0)
        fprintf(e, ", %u", (unsigned int)res->u.dialog->ex->help);
    }
  else if (res->type == RES_TYPE_TOOLBAR && res->u.toolbar)
    {
      fprintf(e, " %d, %d", (int)res->u.toolbar->button_width,
              (int)res->u.toolbar->button_height);
    }

  fprintf(e, "\n");

  if ((res->res_info.language != 0 && res->res_info.language != *language)
      || res->res_info.characteristics != 0
      || res->res_info.version != 0)
    {
      int modifiers = 0;

      switch (res->type)
        {
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

      if (res->res_info.language != 0 && res->res_info.language != *language)
        fprintf(e, "%sLANGUAGE %d, %d\n",
                modifiers ? "// " : "",
                (int)res->res_info.language & ((1 << SUBLANG_SHIFT) - 1),
                (int)(res->res_info.language >> SUBLANG_SHIFT) & 0xff);
      if (res->res_info.characteristics != 0)
        fprintf(e, "%sCHARACTERISTICS %u\n",
                modifiers ? "// " : "",
                (unsigned int)res->res_info.characteristics);
      if (res->res_info.version != 0)
        fprintf(e, "%sVERSION %u\n",
                modifiers ? "// " : "",
                (unsigned int)res->res_info.version);
    }

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
      break;
    }
}

/* Write out accelerator information.  */

static void
write_rc_accelerators (FILE *e, const rc_accelerator *accelerators)
{
  if (e == NULL || accelerators == NULL) {
    return;
  }

  if (fprintf(e, "BEGIN\n") < 0) {
    return;
  }

  for (const rc_accelerator *acc = accelerators; acc != NULL; acc = acc->next)
    {
      if (fprintf(e, "  ") < 0) {
        return;
      }

      int is_printable_char = ((acc->key & 0x7f) == acc->key) &&
                              ISPRINT(acc->key) &&
                              ((acc->flags & ACC_VIRTKEY) == 0);

      if (is_printable_char)
        {
          if (fprintf(e, "\"%c\"", (char) acc->key) < 0) {
            return;
          }
        }
      else
        {
          if (fprintf(e, "%d", (int) acc->key) < 0) {
            return;
          }
        }

      if (fprintf(e, ", %d", (int) acc->id) < 0) {
        return;
      }

      if (!is_printable_char)
        {
          const char *key_type = ((acc->flags & ACC_VIRTKEY) != 0) ? ", VIRTKEY" : ", ASCII";
          if (fprintf(e, "%s", key_type) < 0) {
            return;
          }
        }

      if ((acc->flags & ACC_SHIFT) != 0)
        {
          if (fprintf(e, ", SHIFT") < 0) {
            return;
          }
        }
      if ((acc->flags & ACC_CONTROL) != 0)
        {
          if (fprintf(e, ", CONTROL") < 0) {
            return;
          }
        }
      if ((acc->flags & ACC_ALT) != 0)
        {
          if (fprintf(e, ", ALT") < 0) {
            return;
          }
        }

      if (fprintf(e, "\n") < 0) {
        return;
      }
    }

  fprintf(e, "END\n");
}

/* Write out cursor information.  This would normally be in a separate
   file, which the rc file would include.  */

static void
write_rc_cursor(FILE *e, const rc_cursor *cursor)
{
    if (e == NULL || cursor == NULL) {
        return;
    }

    if (fprintf(e, "BEGIN\n") < 0) {
        return;
    }
    
    indent(e, 2);
    
    if (fprintf(e, " 0x%x, 0x%x,\t/* Hotspot x: %d, y: %d.  */\n",
                (unsigned int)cursor->xhotspot, 
                (unsigned int)cursor->yhotspot,
                (int)cursor->xhotspot, 
                (int)cursor->yhotspot) < 0) {
        return;
    }
    
    write_rc_datablock(e, (rc_uint_type)cursor->length, 
                      (const bfd_byte *)cursor->data, 0, 0, 0);
    
    if (fprintf(e, "END\n") < 0) {
        return;
    }
}

/* Write out group cursor data.  This would normally be built from the
   cursor data.  */

static void
write_rc_group_cursor(FILE *e, const rc_group_cursor *group_cursor)
{
    if (!e || !group_cursor) {
        return;
    }

    int item_count = 0;
    for (const rc_group_cursor *gc = group_cursor; gc != NULL; gc = gc->next) {
        item_count++;
    }

    if (fprintf(e, "BEGIN\n") < 0) {
        return;
    }

    indent(e, 2);
    if (fprintf(e, "0, 2, %d%s\t /* Having %d items.  */\n", 
                item_count, (item_count != 0 ? "," : ""), item_count) < 0) {
        return;
    }

    indent(e, 4);
    if (fprintf(e, "/* width, height, planes, bits, bytes, index.  */\n") < 0) {
        return;
    }

    int index = 1;
    for (const rc_group_cursor *gc = group_cursor; gc != NULL; gc = gc->next, index++) {
        indent(e, 4);
        if (fprintf(e, "%d, %d, %d, %d, 0x%xL, %d%s /* Element %d. */\n",
                    (int)gc->width, (int)gc->height, (int)gc->planes, (int)gc->bits,
                    (unsigned int)gc->bytes, (int)gc->index, 
                    (gc->next != NULL ? "," : ""), index) < 0) {
            return;
        }
        
        if (fprintf(e, "/* width: %d; height %d; planes %d; bits %d.  */\n",
                    (int)gc->width, (int)gc->height, (int)gc->planes,
                    (int)gc->bits) < 0) {
            return;
        }
    }

    fprintf(e, "END\n");
}

/* Write dialog data.  */

static void
write_rc_dialog (FILE *e, const rc_dialog *dialog)
{
  if (e == NULL || dialog == NULL)
    return;

  fprintf (e, "STYLE 0x%x\n", dialog->style);

  if (dialog->exstyle != 0)
    fprintf (e, "EXSTYLE 0x%x\n", (unsigned int) dialog->exstyle);

  if ((dialog->class.named && dialog->class.u.n.length > 0) || dialog->class.u.id != 0)
    {
      fprintf (e, "CLASS ");
      res_id_print (e, dialog->class, 1);
      fprintf (e, "\n");
    }

  if (dialog->caption != NULL)
    {
      fprintf (e, "CAPTION ");
      unicode_print_quoted (e, dialog->caption, -1);
      fprintf (e, "\n");
    }

  if ((dialog->menu.named && dialog->menu.u.n.length > 0) || dialog->menu.u.id != 0)
    {
      fprintf (e, "MENU ");
      res_id_print (e, dialog->menu, 0);
      fprintf (e, "\n");
    }

  if (dialog->font != NULL)
    {
      fprintf (e, "FONT %d, ", (int) dialog->pointsize);
      unicode_print_quoted (e, dialog->font, -1);
      
      if (dialog->ex != NULL)
        {
          int needs_extended = (dialog->ex->weight != 0 || 
                                dialog->ex->italic != 0 || 
                                dialog->ex->charset != 1);
          if (needs_extended)
            fprintf (e, ", %d, %d, %d",
                    (int) dialog->ex->weight,
                    (int) dialog->ex->italic,
                    (int) dialog->ex->charset);
        }
      fprintf (e, "\n");
    }

  fprintf (e, "BEGIN\n");

  const rc_dialog_control *control = dialog->controls;
  while (control != NULL)
    {
      write_rc_dialog_control (e, control);
      control = control->next;
    }

  fprintf (e, "END\n");
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
write_rc_dialog_control (FILE *e, const rc_dialog_control *control)
{
  const struct control_info *ci;
  int should_print_text;
  int need_extended_info;

  fprintf (e, "  ");

  ci = NULL;
  if (!control->class.named)
    {
      for (ci = control_info; ci->name != NULL; ++ci)
        {
          if (ci->class == control->class.u.id &&
              (ci->style == (unsigned long) -1 || ci->style == (control->style & 0xff)))
            break;
        }
      if (ci->name == NULL)
        ci = NULL;
    }

  if (ci != NULL && ci->name != NULL)
    fprintf (e, "%s", ci->name);
  else
    fprintf (e, "CONTROL");

  should_print_text = (control->text.named || control->text.u.id != 0);
  if (ci != NULL)
    {
      should_print_text = should_print_text &&
                         ci->class != CTL_EDIT &&
                         ci->class != CTL_COMBOBOX &&
                         ci->class != CTL_LISTBOX &&
                         ci->class != CTL_SCROLLBAR;
    }

  if (should_print_text)
    {
      fprintf (e, " ");
      res_id_print (e, control->text, 1);
      fprintf (e, ",");
    }

  fprintf (e, " %d, ", (int) control->id);

  if (ci == NULL)
    {
      if (control->class.named)
        fprintf (e, "\"");
      res_id_print (e, control->class, 0);
      if (control->class.named)
        fprintf (e, "\"");
      fprintf (e, ", 0x%x, ", (unsigned int) control->style);
    }

  fprintf (e, "%d, %d", (int) control->x, (int) control->y);

  need_extended_info = control->style != SS_ICON ||
                      control->exstyle != 0 ||
                      control->width != 0 ||
                      control->height != 0 ||
                      control->help != 0;

  if (need_extended_info)
    {
      fprintf (e, ", %d, %d", (int) control->width, (int) control->height);

      if (ci != NULL)
        fprintf (e, ", 0x%x", (unsigned int) control->style);

      if (control->exstyle != 0 || control->help != 0)
        fprintf (e, ", 0x%x, %u", (unsigned int) control->exstyle,
                 (unsigned int) control->help);
    }

  fprintf (e, "\n");

  if (control->data != NULL)
    write_rc_rcdata (e, control->data, 2);
}

/* Write out font directory data.  This would normally be built from
   the font data.  */

static void
write_rc_fontdir (FILE *e, const rc_fontdir *fontdir)
{
  const rc_fontdir *fc;
  int count;
  int index;

  if (e == NULL || fontdir == NULL) {
    return;
  }

  count = 0;
  for (fc = fontdir; fc != NULL; fc = fc->next) {
    count++;
  }

  if (fprintf(e, "BEGIN\n") < 0) {
    return;
  }
  
  indent(e, 2);
  
  if (fprintf(e, "%d%s\t /* Has %d elements.  */\n", 
              count, (count != 0 ? "," : ""), count) < 0) {
    return;
  }
  
  index = 1;
  for (fc = fontdir; fc != NULL; fc = fc->next) {
    indent(e, 4);
    
    if (fprintf(e, "%d,\t/* Font no %d with index %d.  */\n",
                (int)fc->index, index, (int)fc->index) < 0) {
      return;
    }
    
    if (fc->length > 2 && fc->data != NULL) {
      write_rc_datablock(e, (rc_uint_type)(fc->length - 2),
                        (const bfd_byte *)fc->data + 4, 
                        fc->next != NULL, 0, 0);
    }
    
    index++;
  }
  
  if (fprintf(e, "END\n") < 0) {
    return;
  }
}

/* Write out group icon data.  This would normally be built from the
   icon data.  */

static void
write_rc_group_icon (FILE *e, const rc_group_icon *group_icon)
{
  const rc_group_icon *gi;
  int count;
  int index;

  if (e == NULL || group_icon == NULL) {
    return;
  }

  count = 0;
  for (gi = group_icon; gi != NULL; gi = gi->next) {
    count++;
  }

  if (fprintf(e, "BEGIN\n") < 0) {
    return;
  }
  
  indent(e, 2);
  if (fprintf(e, " 0, 1, %d%s\t /* Has %d elements.  */\n", 
              count, (count != 0 ? "," : ""), count) < 0) {
    return;
  }

  indent(e, 4);
  if (fprintf(e, "/* \"width height colors pad\", planes, bits, bytes, index.  */\n") < 0) {
    return;
  }

  index = 1;
  for (gi = group_icon; gi != NULL; gi = gi->next) {
    indent(e, 4);
    if (fprintf(e, "\"\\%03o\\%03o\\%03o\\%03o\", %d, %d, 0x%xL, %d%s\t/* Element no %d.  */\n",
                gi->width, gi->height, gi->colors, 0, 
                (int)gi->planes, (int)gi->bits,
                (unsigned int)gi->bytes, (int)gi->index, 
                (gi->next != NULL ? "," : ""), index) < 0) {
      return;
    }
    index++;
  }

  fprintf(e, "END\n");
}

/* Write out a menu resource.  */

static void
write_rc_menu (FILE *e, const rc_menu *menu, int menuex)
{
  if (!e || !menu) {
    return;
  }
  
  if (menu->help != 0) {
    fprintf (e, "// Help ID: %u\n", (unsigned int) menu->help);
  }
  
  write_rc_menuitems (e, menu->items, menuex, 0);
}

static void
write_rc_toolbar(FILE *e, const rc_toolbar *tb)
{
    if (e == NULL || tb == NULL) {
        return;
    }

    indent(e, 0);
    if (fprintf(e, "BEGIN\n") < 0) {
        return;
    }

    const rc_toolbar_item *it = tb->items;
    while (it != NULL) {
        indent(e, 2);
        if (it->id.u.id == 0) {
            if (fprintf(e, "SEPARATOR\n") < 0) {
                return;
            }
        } else {
            if (fprintf(e, "BUTTON %d\n", (int)it->id.u.id) < 0) {
                return;
            }
        }
        it = it->next;
    }

    indent(e, 0);
    fprintf(e, "END\n");
}

/* Write out menuitems.  */

static void
write_rc_menuitems (FILE *e, const rc_menuitem *menuitems, int menuex,
		    int ind)
{
  const rc_menuitem *mi;

  if (e == NULL || menuitems == NULL || ind < 0)
    return;

  indent (e, ind);
  fprintf (e, "BEGIN\n");

  for (mi = menuitems; mi != NULL; mi = mi->next)
    {
      indent (e, ind + 2);

      if (mi->popup == NULL)
	fprintf (e, "MENUITEM");
      else
	fprintf (e, "POPUP");

      if (! menuex
	  && mi->popup == NULL
	  && mi->text == NULL
	  && mi->type == 0
	  && mi->id == 0)
	{
	  fprintf (e, " SEPARATOR\n");
	  continue;
	}

      if (mi->text == NULL)
	fprintf (e, " \"\"");
      else
	{
	  fprintf (e, " ");
	  unicode_print_quoted (e, mi->text, -1);
	}

      if (! menuex)
	{
	  if (mi->popup == NULL)
	    fprintf (e, ", %d", (int) mi->id);

	  if ((mi->type & MENUITEM_CHECKED) != 0)
	    fprintf (e, ", CHECKED");
	  if ((mi->type & MENUITEM_GRAYED) != 0)
	    fprintf (e, ", GRAYED");
	  if ((mi->type & MENUITEM_HELP) != 0)
	    fprintf (e, ", HELP");
	  if ((mi->type & MENUITEM_INACTIVE) != 0)
	    fprintf (e, ", INACTIVE");
	  if ((mi->type & MENUITEM_MENUBARBREAK) != 0)
	    fprintf (e, ", MENUBARBREAK");
	  if ((mi->type & MENUITEM_MENUBREAK) != 0)
	    fprintf (e, ", MENUBREAK");
	  if ((mi->type & MENUITEM_OWNERDRAW) != 0)
	    fprintf (e, ", OWNERDRAW");
	  if ((mi->type & MENUITEM_BITMAP) != 0)
	    fprintf (e, ", BITMAP");
	}
      else
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

      fprintf (e, "\n");

      if (mi->popup != NULL)
	write_rc_menuitems (e, mi->popup, menuex, ind + 2);
    }

  indent (e, ind);
  fprintf (e, "END\n");
}

static int
test_rc_datablock_unicode(rc_uint_type length, const bfd_byte *data)
{
    if (data == NULL || (length & 1) != 0) {
        return 0;
    }

    for (rc_uint_type i = 0; i < length; i += 2) {
        if ((data[i] == 0 && data[i + 1] == 0 && (i + 2) < length) ||
            (data[i] == 0xFF && data[i + 1] == 0xFF)) {
            return 0;
        }
    }
    
    return 1;
}

static int
test_rc_datablock_text (rc_uint_type length, const bfd_byte *data)
{
  rc_uint_type non_printable_count = 0;
  int newline_count = 0;
  rc_uint_type i;

  if (length <= 1)
    return 0;

  for (i = 0; i < length; i++)
    {
      bfd_byte current = data[i];
      
      if (current == '\n')
        {
          newline_count++;
          continue;
        }
      
      if (ISPRINT(current) || current == '\t')
        continue;
      
      if (current == '\r' && (i + 1) < length && data[i + 1] == '\n')
        continue;
      
      if (current == 0 && (i + 1) == length)
        continue;
      
      if (current <= 7)
        return 0;
      
      non_printable_count++;
    }
  
  if (length > 80 && newline_count == 0)
    return 0;
  
  rc_uint_type threshold = (non_printable_count * 10000) / length;
  if (threshold >= 150)
    return 0;
  
  return 1;
}

static void
write_rc_messagetable (FILE *e, rc_uint_type length, const bfd_byte *data)
{
  const struct bin_messagetable *mt;
  rc_uint_type m, i;

  fprintf (e, "BEGIN\n");
  write_rc_datablock (e, length, data, 0, 0, 0);
  fprintf (e, "\n");
  wr_printcomment (e, "MC syntax dump");

  if (length < BIN_MESSAGETABLE_SIZE)
    {
      wr_printcomment (e, "Illegal data");
      wr_print_flush (e);
      fprintf (e, "END\n");
      return;
    }

  mt = (const struct bin_messagetable *) data;
  m = target_get_32 (mt->cblocks, length);

  if (length < (BIN_MESSAGETABLE_SIZE + m * BIN_MESSAGETABLE_BLOCK_SIZE))
    {
      wr_printcomment (e, "Illegal data");
      wr_print_flush (e);
      fprintf (e, "END\n");
      return;
    }

  for (i = 0; i < m; i++)
    {
      rc_uint_type low, high, offset;

      low = windres_get_32 (&wrtarget, mt->items[i].lowid);
      high = windres_get_32 (&wrtarget, mt->items[i].highid);
      offset = windres_get_32 (&wrtarget, mt->items[i].offset);

      while (low <= high)
        {
          const struct bin_messagetable_item *mti;
          rc_uint_type elen, flags;

          if ((offset + BIN_MESSAGETABLE_ITEM_SIZE) > length)
            {
              wr_printcomment (e, "Illegal data");
              wr_print_flush (e);
              fprintf (e, "END\n");
              return;
            }

          mti = (const struct bin_messagetable_item *) &data[offset];
          elen = windres_get_16 (&wrtarget, mti->length);
          flags = windres_get_16 (&wrtarget, mti->flags);

          if ((offset + elen) > length)
            {
              wr_printcomment (e, "Illegal data");
              wr_print_flush (e);
              fprintf (e, "END\n");
              return;
            }

          wr_printcomment (e, "MessageId = 0x%x", low);
          wr_printcomment (e, "");

          if ((flags & MESSAGE_RESOURCE_UNICODE) == MESSAGE_RESOURCE_UNICODE)
            {
              if (elen > BIN_MESSAGETABLE_ITEM_SIZE * 2)
                unicode_print (e, (const unichar *) mti->data,
                             (elen - BIN_MESSAGETABLE_ITEM_SIZE) / 2);
            }
          else
            {
              if (elen > BIN_MESSAGETABLE_ITEM_SIZE)
                ascii_print (e, (const char *) mti->data,
                           (elen - BIN_MESSAGETABLE_ITEM_SIZE));
            }

          wr_printcomment (e,"");
          ++low;
          offset += elen;
        }
    }

  wr_print_flush (e);
  fprintf (e, "END\n");
}

static void
write_rc_datablock (FILE *e, rc_uint_type length, const bfd_byte *data,
		    int has_next, int hasblock, int show_comment)
{
  if (hasblock)
    fprintf (e, "BEGIN\n");

  if (length == 0)
    {
      if (hasblock)
        fprintf (e, "END\n");
      return;
    }

  if (show_comment == -1)
    {
      if (test_rc_datablock_text(length, data))
        {
          write_text_data(e, length, data, has_next);
          if (hasblock)
            fprintf (e, "END\n");
          return;
        }
      if (test_rc_datablock_unicode (length, data))
        {
          write_unicode_data(e, length, data, has_next);
          if (hasblock)
            fprintf (e, "END\n");
          return;
        }
      show_comment = 0;
    }

  write_binary_data(e, length, data, has_next, show_comment);
  
  if (hasblock)
    fprintf (e, "END\n");
}

static void
write_text_data(FILE *e, rc_uint_type length, const bfd_byte *data, int has_next)
{
  rc_uint_type i, c;
  
  for (i = 0; i < length;)
    {
      indent (e, 2);
      fprintf (e, "\"");
      
      for (c = 0; i < length && c < 160 && data[i] != '\n'; c++, i++)
        ;
      if (i < length && data[i] == '\n')
        ++i, ++c;
      ascii_print(e, (const char *) &data[i - c], c);
      fprintf (e, "\"");
      if (i < length)
        fprintf (e, "\n");
    }
  
  if (length == 0)
    {
      indent (e, 2);
      fprintf (e, "\"\"");
    }
  if (has_next)
    fprintf (e, ",");
  fprintf (e, "\n");
}

static void
write_unicode_data(FILE *e, rc_uint_type length, const bfd_byte *data, int has_next)
{
  rc_uint_type i, c;
  
  for (i = 0; i < length;)
    {
      const unichar *u = (const unichar *) &data[i];
      indent (e, 2);
      fprintf (e, "L\"");
      
      for (c = 0; i < length && c < 160 && u[c] != '\n'; c++, i += 2)
        ;
      if (i < length && u[c] == '\n')
        i += 2, ++c;
      unicode_print (e, u, c);
      fprintf (e, "\"");
      if (i < length)
        fprintf (e, "\n");
    }
  
  if (length == 0)
    {
      indent (e, 2);
      fprintf (e, "L\"\"");
    }
  if (has_next)
    fprintf (e, ",");
  fprintf (e, "\n");
}

static void
write_binary_data(FILE *e, rc_uint_type length, const bfd_byte *data, 
                   int has_next, int show_comment)
{
  rc_uint_type i;
  rc_uint_type max_row = show_comment ? 4 : 8;
  int first = 1;
  
  for (i = 0; i + 3 < length;)
    {
      rc_uint_type comment_start = i;
      
      if (!first)
        indent (e, 2);
      
      write_dword_row(e, data, length, &i, max_row, has_next);
      
      if (show_comment)
        write_comment(e, data, comment_start, i);
      
      fprintf (e, "\n");
      first = 0;
    }
  
  if (i + 1 < length)
    {
      write_word_value(e, data, length, &i, has_next, show_comment, first);
      first = 0;
    }
  
  if (i < length)
    {
      write_byte_value(e, data, &i, has_next, first);
    }
}

static void
write_dword_row(FILE *e, const bfd_byte *data, rc_uint_type length,
                rc_uint_type *i, rc_uint_type max_row, int has_next)
{
  rc_uint_type k;
  int plen;
  
  for (k = 0; k < max_row && *i + 3 < length; k++, *i += 4)
    {
      if (k == 0)
        plen = fprintf (e, "0x%lxL",
                        (unsigned long) target_get_32 (data + *i, length - *i));
      else
        plen = fprintf (e, " 0x%lxL",
                        (unsigned long) target_get_32 (data + *i, length - *i)) - 1;
      
      if (has_next || (*i + 4) < length)
        {
          if (plen > 0 && plen < 11)
            indent (e, 11 - plen);
          fprintf (e, ",");
        }
    }
}

static void
write_word_value(FILE *e, const bfd_byte *data, rc_uint_type length,
                 rc_uint_type *i, int has_next, int show_comment, int first)
{
  int plen;
  
  if (!first)
    indent (e, 2);
  
  plen = fprintf (e, "0x%x", (int) target_get_16 (data + *i, length - *i));
  
  if (has_next || *i + 2 < length)
    {
      if (plen > 0 && plen < 11)
        indent (e, 11 - plen);
      fprintf (e, ",");
    }
  
  if (show_comment)
    {
      fprintf (e, "\t/* ");
      ascii_print (e, (const char *) &data[*i], 2);
      fprintf (e, ".  */");
    }
  
  fprintf (e, "\n");
  *i += 2;
}

static void
write_byte_value(FILE *e, const bfd_byte *data, rc_uint_type *i, 
                 int has_next, int first)
{
  if (!first)
    indent (e, 2);
  
  fprintf (e, "\"");
  ascii_print (e, (const char *) &data[*i], 1);
  fprintf (e, "\"");
  
  if (has_next)
    fprintf (e, ",");
  
  fprintf (e, "\n");
  (*i)++;
}

static void
write_comment(FILE *e, const bfd_byte *data, rc_uint_type start, rc_uint_type end)
{
  fprintf (e, "\t/* ");
  ascii_print (e, (const char *) &data[start], end - start);
  fprintf (e, ".  */");
}

/* Write out an rcdata resource.  This is also used for other types of
   resources that need to print arbitrary data.  */

static void
write_rc_rcdata(FILE *e, const rc_rcdata_item *rcdata, int ind)
{
    if (e == NULL || rcdata == NULL || ind < 0) {
        return;
    }

    indent(e, ind);
    if (fprintf(e, "BEGIN\n") < 0) {
        return;
    }

    const rc_rcdata_item *ri = rcdata;
    while (ri != NULL) {
        if (ri->type == RCDATA_BUFFER && ri->u.buffer.length == 0) {
            ri = ri->next;
            continue;
        }

        int needs_comma = (ri->next != NULL);
        
        switch (ri->type) {
        case RCDATA_WORD:
            indent(e, ind + 2);
            fprintf(e, "%ld", (long)(ri->u.word & 0xffff));
            if (needs_comma) {
                fprintf(e, ",");
            }
            fprintf(e, "\n");
            break;

        case RCDATA_DWORD:
            indent(e, ind + 2);
            fprintf(e, "%luL", (unsigned long)ri->u.dword);
            if (needs_comma) {
                fprintf(e, ",");
            }
            fprintf(e, "\n");
            break;

        case RCDATA_STRING:
            indent(e, ind + 2);
            fprintf(e, "\"");
            ascii_print(e, ri->u.string.s, ri->u.string.length);
            fprintf(e, "\"");
            if (needs_comma) {
                fprintf(e, ",");
            }
            fprintf(e, "\n");
            break;

        case RCDATA_WSTRING:
            indent(e, ind + 2);
            fprintf(e, "L\"");
            unicode_print(e, ri->u.wstring.w, ri->u.wstring.length);
            fprintf(e, "\"");
            if (needs_comma) {
                fprintf(e, ",");
            }
            fprintf(e, "\n");
            break;

        case RCDATA_BUFFER:
            write_rc_datablock(e, (rc_uint_type)ri->u.buffer.length,
                             (const bfd_byte *)ri->u.buffer.data,
                             needs_comma, 0, -1);
            break;

        default:
            break;
        }

        ri = ri->next;
    }

    indent(e, ind);
    fprintf(e, "END\n");
}

/* Write out a stringtable resource.  */

static void
write_rc_stringtable (FILE *e, const rc_res_id *name,
		      const rc_stringtable *stringtable)
{
  rc_uint_type offset;
  const char *table_comment;

  if (e == NULL || stringtable == NULL) {
    return;
  }

  if (name != NULL && !name->named) {
    offset = (name->u.id - 1) << 4;
    table_comment = NULL;
  } else {
    offset = 0;
    table_comment = (name == NULL) ? "Missing" : "Invalid";
  }

  if (table_comment != NULL) {
    fprintf (e, "/* %s string table name.  */\n", table_comment);
  }

  fprintf (e, "BEGIN\n");

  for (int i = 0; i < 16; i++) {
    if (stringtable->strings[i].length == 0) {
      continue;
    }
    
    fprintf (e, "  %lu, ", (unsigned long) (offset + i));
    unicode_print_quoted (e, stringtable->strings[i].string,
                         stringtable->strings[i].length);
    fprintf (e, "\n");
  }

  fprintf (e, "END\n");
}

/* Write out a versioninfo resource.  */

static void
write_version_number(FILE *e, const char *label, unsigned int ms, unsigned int ls)
{
  if (ms == 0 && ls == 0)
    return;
  
  fprintf(e, " %s %u, %u, %u, %u\n",
          label,
          (ms >> 16) & 0xffff,
          ms & 0xffff,
          (ls >> 16) & 0xffff,
          ls & 0xffff);
}

static void
write_fixed_field(FILE *e, const char *label, unsigned int value)
{
  if (value == 0)
    return;
  
  fprintf(e, " %s 0x%x\n", label, value);
}

static void
write_string_info(FILE *e, const rc_ver_stringtable *stringtables)
{
  fprintf(e, "  BLOCK \"StringFileInfo\"\n");
  fprintf(e, "  BEGIN\n");
  
  for (const rc_ver_stringtable *vst = stringtables; vst != NULL; vst = vst->next)
  {
    fprintf(e, "    BLOCK ");
    unicode_print_quoted(e, vst->language, -1);
    fprintf(e, "\n");
    fprintf(e, "    BEGIN\n");
    
    for (const rc_ver_stringinfo *vs = vst->strings; vs != NULL; vs = vs->next)
    {
      fprintf(e, "      VALUE ");
      unicode_print_quoted(e, vs->key, -1);
      fprintf(e, ", ");
      unicode_print_quoted(e, vs->value, -1);
      fprintf(e, "\n");
    }
    
    fprintf(e, "    END\n");
  }
  
  fprintf(e, "  END\n");
}

static void
write_var_info(FILE *e, const rc_ver_info *vi)
{
  fprintf(e, "  BLOCK \"VarFileInfo\"\n");
  fprintf(e, "  BEGIN\n");
  fprintf(e, "    VALUE ");
  unicode_print_quoted(e, vi->u.var.key, -1);
  
  for (const rc_ver_varinfo *vv = vi->u.var.var; vv != NULL; vv = vv->next)
  {
    fprintf(e, ", 0x%x, %d", vv->language, vv->charset);
  }
  
  fprintf(e, "\n  END\n");
}

static void
write_rc_versioninfo(FILE *e, const rc_versioninfo *versioninfo)
{
  if (e == NULL || versioninfo == NULL || versioninfo->fixed == NULL)
    return;
  
  const rc_fixed_versioninfo *f = versioninfo->fixed;
  
  write_version_number(e, "FILEVERSION", f->file_version_ms, f->file_version_ls);
  write_version_number(e, "PRODUCTVERSION", f->product_version_ms, f->product_version_ls);
  
  write_fixed_field(e, "FILEFLAGSMASK", f->file_flags_mask);
  write_fixed_field(e, "FILEFLAGS", f->file_flags);
  write_fixed_field(e, "FILEOS", f->file_os);
  write_fixed_field(e, "FILETYPE", f->file_type);
  write_fixed_field(e, "FILESUBTYPE", f->file_subtype);
  
  if (f->file_date_ms != 0 || f->file_date_ls != 0)
  {
    fprintf(e, "/* Date: %u, %u.  */\n", f->file_date_ms, f->file_date_ls);
  }
  
  fprintf(e, "BEGIN\n");
  
  for (const rc_ver_info *vi = versioninfo->var; vi != NULL; vi = vi->next)
  {
    switch (vi->type)
    {
      case VERINFO_STRING:
        write_string_info(e, vi->u.string.stringtables);
        break;
        
      case VERINFO_VAR:
        write_var_info(e, vi);
        break;
        
      default:
        break;
    }
  }
  
  fprintf(e, "END\n");
}

static rc_uint_type
rcdata_copy (const rc_rcdata_item *src, bfd_byte *dst)
{
  if (!src)
    return 0;

  switch (src->type)
    {
    case RCDATA_WORD:
      if (dst)
        windres_put_16 (&wrtarget, dst, (rc_uint_type) src->u.word);
      return 2;

    case RCDATA_DWORD:
      if (dst)
        windres_put_32 (&wrtarget, dst, (rc_uint_type) src->u.dword);
      return 4;

    case RCDATA_STRING:
      if (dst && src->u.string.length > 0)
        memcpy (dst, src->u.string.s, src->u.string.length);
      return (rc_uint_type) src->u.string.length;

    case RCDATA_WSTRING:
      {
        rc_uint_type byte_length = (rc_uint_type) (src->u.wstring.length * sizeof (unichar));
        if (dst && src->u.wstring.length > 0)
          memcpy (dst, src->u.wstring.w, byte_length);
        return byte_length;
      }

    case RCDATA_BUFFER:
      if (dst && src->u.buffer.length > 0)
        memcpy (dst, src->u.buffer.data, src->u.buffer.length);
      return (rc_uint_type) src->u.buffer.length;

    default:
      return 0;
    }
}
