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
  char **argv = NULL;
  char *s;
  size_t argc;
  size_t i;
  int in_quote;
  char sep;
  char *errmsg_fmt = NULL, *errmsg_arg = NULL;
  char *temp_base = make_temp_file (NULL);
  int redir_handle = -1;
  int stdout_save = -1;
  int pid;
  int wait_status;
  int retcode = 1;

  argc = 0;
  for (s = cmd; *s;)
    {
      while (isspace ((unsigned char) *s))
	s++;
      if (*s == '\0')
	break;

      argc++;
      sep = (*s == '\'' || *s == '"') ? *s++ : ' ';
      while (*s != '\0' && *s != sep)
	s++;
      if (*s != '\0')
	s++;
    }

  argv = xmalloc (sizeof (char *) * (argc + 1));

  i = 0;
  s = cmd;
  while (*s)
    {
      while (isspace ((unsigned char) *s))
	s++;
      if (*s == '\0')
	break;

      in_quote = (*s == '\'' || *s == '"');
      sep = in_quote ? *s++ : ' ';
      argv[i++] = s;

      while (*s != '\0' && *s != sep)
	s++;
      if (*s == '\0')
	break;

      *s++ = '\0';
      if (in_quote)
	s++;
    }
  argv[i] = NULL;

  fflush (stdout);
  fflush (stderr);

  redir_handle =
    open (redir, O_WRONLY | O_TRUNC | O_CREAT, S_IRUSR | S_IWUSR);
  if (redir_handle == -1)
    fatal (_("can't open temporary file `%s': %s"), redir, strerror (errno));

  stdout_save = dup (STDOUT_FILENO);
  if (stdout_save == -1)
    fatal (_("can't save stdout: %s"), strerror (errno));

  if (dup2 (redir_handle, STDOUT_FILENO) == -1)
    fatal (_("can't redirect stdout to `%s': %s"), redir, strerror (errno));

  close (redir_handle);

  pid = pexecute (argv[0], (char *const *) argv, program_name, temp_base,
		  &errmsg_fmt, &errmsg_arg, PEXECUTE_ONE | PEXECUTE_SEARCH);

  if (dup2 (stdout_save, STDOUT_FILENO) == -1)
    fatal (_("can't restore stdout: %s"), strerror (errno));

  close (stdout_save);

  if (pid == -1)
    fatal ("%s %s: %s", errmsg_fmt, errmsg_arg, strerror (errno));

  if (pwait (pid, &wait_status, 0) == -1)
    fatal (_("wait: %s"), strerror (errno));

  if (WIFEXITED (wait_status))
    {
      if (WEXITSTATUS (wait_status) == 0)
	{
	  retcode = 0;
	}
      else
	{
	  fatal (_("%s exited with status %d"), argv[0],
		 WEXITSTATUS (wait_status));
	}
    }
  else if (WIFSIGNALED (wait_status))
    {
      fatal (_("subprocess got fatal signal %d"), WTERMSIG (wait_status));
    }
  else
    {
      fatal (_("subprocess for %s exited with an unknown status"), argv[0]);
    }

  free (errmsg_arg);
  free (temp_base);
  free (argv);

  return retcode;
}

static FILE *
open_input_stream (char *cmd)
{
  FILE *stream;

  if (istream_type == ISTREAM_FILE)
    {
      char *fileprefix = make_temp_file (NULL);
      const char *suffix = ".irc";
      size_t len = strlen (fileprefix) + strlen (suffix) + 1;

      cpp_temp_file = xmalloc (len);
      int ret = snprintf (cpp_temp_file, len, "%s%s", fileprefix, suffix);
      free (fileprefix);

      if (ret < 0 || (size_t) ret >= len)
        fatal (_("failed to create temporary filename"));

      if (run_cmd (cmd, cpp_temp_file))
        fatal (_("can't execute `%s': %s"), cmd, strerror (errno));

      stream = fopen (cpp_temp_file, FOPEN_RT);
      if (stream == NULL)
        fatal (_("can't open temporary file `%s': %s"),
               cpp_temp_file, strerror (errno));

      if (verbose)
        fprintf (stderr,
                 _("Using temporary file `%s' to read preprocessor output\n"),
                 cpp_temp_file);
    }
  else
    {
      stream = popen (cmd, FOPEN_RT);
      if (stream == NULL)
        fatal (_("can't popen `%s': %s"), cmd, strerror (errno));

      if (verbose)
        fprintf (stderr, _("Using popen to read preprocessor output\n"));
    }

  cpp_pipe = stream;
  xatexit (close_input_stream);
  return cpp_pipe;
}

/* Determine if FILENAME contains special characters that
   can cause problems unless the entire filename is quoted.  */

static int
filename_need_quotes (const char *filename)
{
  if (filename == NULL || (filename[0] == '-' && filename[1] == '\0'))
    {
      return 0;
    }

  return strpbrk(filename, "& <>|%") != NULL;
}

/* Look for the preprocessor program.  */

static FILE *
look_for_default (char *cmd, const char *prefix, int end_prefix,
		  const char *preprocargs, const char *filename)
{
  struct stat s;

  memcpy (cmd, prefix, end_prefix);
  char *out = stpcpy (cmd + end_prefix, DEFAULT_PREPROCESSOR_CMD);

  bool has_path_sep = strchr (cmd, '/');
#if defined (__DJGPP__) || defined (__CYGWIN__) || defined (_WIN32)
  has_path_sep = has_path_sep || (strchr (cmd, '\\') != NULL);
#endif

  if (has_path_sep)
    {
      bool found = (stat (cmd, &s) == 0);

#ifdef HAVE_EXECUTABLE_SUFFIX
      if (!found)
	{
	  char *cmd_end_before_suffix = out;
	  out = stpcpy (out, EXECUTABLE_SUFFIX);
	  if (stat (cmd, &s) == 0)
	    {
	      found = true;
	    }
	  else
	    {
	      *cmd_end_before_suffix = '\0';
	    }
	}
#endif
      if (!found)
	{
	  if (verbose)
	    fprintf (stderr, _("Tried `%s'\n"), cmd);
	  return NULL;
	}
    }

  if (filename_need_quotes (cmd))
    {
      size_t cmd_len = out - cmd;
      memmove (cmd + 1, cmd, cmd_len);
      cmd[0] = '"';
      out++;
      *out++ = '"';
    }

  const char *fnquotes = filename_need_quotes (filename) ? "\"" : "";
  size_t required_len = (out - cmd)
    + 1 + strlen (DEFAULT_PREPROCESSOR_ARGS)
    + 1 + strlen (preprocargs)
    + strlen (fnquotes) * 2 + strlen (filename) + 1;

  if (required_len > PATH_MAX)
    {
        if (verbose)
            fprintf (stderr, _("Command line is too long\n"));
        return NULL;
    }

  sprintf (out, " %s %s %s%s%s",
	   DEFAULT_PREPROCESSOR_ARGS, preprocargs, fnquotes, filename, fnquotes);

  if (verbose)
    fprintf (stderr, _("Using `%s'\n"), cmd);

  cpp_pipe = open_input_stream (cmd);
  return cpp_pipe;
}

/* Read an rc file.  */

static void
setup_rc_include_path_from_filename (const char *filename)
{
  if (strchr (filename, '/') == NULL && strchr (filename, '\\') == NULL)
    return;

  size_t len = strlen (filename);
  char *dir = xmalloc (len + 3);
  char *p = dir;

  if (filename[0] != '/' && filename[0] != '\\'
      && !(len > 1 && isalpha ((unsigned char) filename[0]) && filename[1] == ':'))
    {
      *p++ = '.';
      *p++ = '/';
    }

  memcpy (p, filename, len + 1);
  p += len;

  while (p > dir && p[-1] != '/' && p[-1] != '\\')
    --p;

  if (p > dir)
    p[-1] = '\0';
  else
    *p = '\0';

  for (char *c = dir; *c != '\0'; ++c)
    {
      if (*c == '\\')
	*c = '/';
    }

  windres_add_include_dir (dir);
}

static FILE *
find_default_preprocessor (char *cmd_buffer, const char *preprocargs,
			   const char *filename)
{
  const char *dash = NULL;
  const char *slash = NULL;
  for (const char *cp = program_name; *cp != '\0'; ++cp)
    {
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

  FILE *pipe = NULL;

  if (dash != NULL)
    pipe = look_for_default (cmd_buffer, program_name, dash - program_name + 1,
			     preprocargs, filename);

  if (pipe == NULL && slash != NULL)
    pipe = look_for_default (cmd_buffer, program_name, slash - program_name + 1,
			     preprocargs, filename);

  if (pipe == NULL)
    pipe = look_for_default (cmd_buffer, "", 0, preprocargs, filename);

  return pipe;
}

rc_res_directory *
read_rc_file (const char *filename, const char *preprocessor,
	      const char *preprocargs, int language, int use_temp_file)
{
  if (filename == NULL)
    filename = "-";
  else
    setup_rc_include_path_from_filename (filename);

  istream_type = use_temp_file ? ISTREAM_FILE : ISTREAM_PIPE;

  const char *safe_preprocargs = (preprocargs != NULL) ? preprocargs : "";
  const char *fnquotes = filename_need_quotes (filename) ? "\"" : "";

  size_t preproc_len = preprocessor ? strlen (preprocessor) : 0;
  size_t max_len = preproc_len
    + strlen (program_name)
    + strlen (DEFAULT_PREPROCESSOR_CMD)
    + strlen (DEFAULT_PREPROCESSOR_ARGS)
    + strlen (safe_preprocargs)
    + strlen (filename)
    + strlen (fnquotes) * 2
#ifdef HAVE_EXECUTABLE_SUFFIX
    + strlen (EXECUTABLE_SUFFIX)
#endif
    + 10;

  char *cmd = xmalloc (max_len);

  if (preprocessor)
    {
      snprintf (cmd, max_len, "%s %s %s%s%s", preprocessor, safe_preprocargs,
		fnquotes, filename, fnquotes);
      cpp_pipe = open_input_stream (cmd);
    }
  else
    {
      cpp_pipe = find_default_preprocessor (cmd, safe_preprocargs, filename);
    }

  free (cmd);

  rc_filename = xstrdup (filename);
  rc_lineno = 1;

  if (language != -1)
    rcparse_set_language (language);

  yyparse ();
  rcparse_discard_strings ();

  close_input_stream ();

  if (fontdirs != NULL)
    define_fontdirs ();

  free (rc_filename);
  rc_filename = NULL;

  return resources;
}

/* Close the input stream if it is open.  */

static void
close_input_stream (void)
{
  if (cpp_pipe != NULL)
    {
      if (istream_type == ISTREAM_FILE)
        {
          fclose (cpp_pipe);
        }
      else
        {
          int err = pclose (cpp_pipe);
          if (err != 0 || errno == ECHILD)
            {
              cpp_pipe = NULL;
              cpp_temp_file = NULL;
              fatal (_("preprocessing failed."));
            }
        }
    }

  if (istream_type == ISTREAM_FILE && cpp_temp_file != NULL)
    {
      int errno_save = errno;
      unlink (cpp_temp_file);
      errno = errno_save;
      free (cpp_temp_file);
    }

  cpp_pipe = NULL;
  cpp_temp_file = NULL;
}

/* Report an error while reading an rc file.  */

void yyerror(const char *msg)
{
    const char * const filename = rc_filename ? rc_filename : "<unknown file>";
    const char * const message = msg ? msg : "syntax error";

    fatal("%s:%d: %s", filename, rc_lineno, message);
}

/* Issue a warning while reading an rc file.  */

void
rcparse_warning (const char *filename, int lineno, const char *msg)
{
  const char * const safe_filename = filename ? filename : "<unknown file>";
  const char * const safe_msg = msg ? msg : "<no message>";

  if (fprintf (stderr, "%s:%d: %s\n", safe_filename, lineno, safe_msg) < 0)
  {
  }
}

/* Die if we get an unexpected end of file.  */

static void
unexpected_eof (const char *msg)
{
  fatal (_("%s: unexpected EOF"), msg ? msg : "(unknown context)");
}

/* Read a 16 bit word from a file.  The data is assumed to be little
   endian.  */

static int
get_word (FILE *e, const char *msg)
{
  const int b1 = getc (e);
  const int b2 = getc (e);

  if (b2 == EOF)
    {
      unexpected_eof (msg);
    }

  return ((b2 & 0xff) << 8) | (b1 & 0xff);
}

/* Read a 32 bit word from a file.  The data is assumed to be little
   endian.  */

static unsigned long
get_long (FILE *e, const char *msg)
{
  unsigned char b[4];

  if (fread (b, sizeof (unsigned char), 4, e) != 4)
    {
      unexpected_eof (msg);
      return 0;
    }

  return (unsigned long) b[0] |
         ((unsigned long) b[1] << 8) |
         ((unsigned long) b[2] << 16) |
         ((unsigned long) b[3] << 24);
}

/* Read data from a file.  This is a wrapper to do error checking.  */

static void
get_data (FILE *e, bfd_byte *p, rc_uint_type c, const char *msg)
{
  size_t got = fread (p, 1, c, e);

  if (got != c)
    {
      fatal (_("%s: read of %lu returned %lu"),
	     msg, (unsigned long) c, (unsigned long) got);
    }
}

static rc_uint_type
target_get_16 (const void *p, size_t len)
{
  if (len < 2)
  {
    fatal (_("not enough data"));
  }
  return windres_get_16 (&wrtarget, p);
}

static rc_uint_type
target_get_32 (const void *p, size_t len)
{
  if (!p || len < sizeof (uint32_t))
    {
      fatal (_("not enough data"));
    }
  return windres_get_32 (&wrtarget, p);
}

/* Define an accelerator resource.  */

void
define_accelerator (rc_res_id id, const rc_res_res_info *resinfo,
		    rc_accelerator *data)
{
  rc_res_resource *r;

  if (resinfo == NULL || data == NULL)
    return;

  r = define_standard_resource (&resources, RT_ACCELERATOR, id,
				resinfo->language, 0);
  if (r == NULL)
    return;

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
  FILE *e;
  char *real_filename;
  struct stat s;
  bfd_byte *data;
  size_t data_size;
  rc_res_resource *r;

  e = open_file_search (filename, FOPEN_RB, "bitmap file", &real_filename);
  if (e == NULL)
    {
      /* This case was missing. The original code would crash on the subsequent
         call to stat with an uninitialized real_filename. Assume
         open_file_search has already reported an error. A fatal error here
         ensures termination. */
      fatal (_("could not open bitmap file `%s'"), filename);
    }

  if (stat (real_filename, &s) < 0)
    {
      fatal (_("stat failed on bitmap file `%s': %s"), real_filename,
	     strerror (errno));
    }

  if (s.st_size < BITMAP_SKIP)
    {
      fatal (_("bitmap file `%s' is too small"), real_filename);
    }

  data_size = s.st_size - BITMAP_SKIP;
  data = (bfd_byte *) res_alloc (data_size);

  if (fseek (e, BITMAP_SKIP, SEEK_SET) != 0)
    {
      fatal (_("seek failed on bitmap file `%s': %s"), real_filename,
	     strerror (errno));
    }

  if (fread (data, 1, data_size, e) != data_size)
    {
      fatal (_("read failed on bitmap file `%s': %s"), real_filename,
	     feof (e) ? _("unexpected end of file") : strerror (errno));
    }

  fclose (e);
  free (real_filename);

  r = define_standard_resource (&resources, RT_BITMAP, id,
				resinfo->language, 0);

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

#define CURSOR_FILE_TYPE 2
#define MAX_CURSORS_PER_FILE 256
#define MAX_CURSOR_BYTES (1024 * 1024)

static void
read_and_validate_header (FILE *e, const char *filename, int *out_count)
{
  get_word (e, filename);
  int type = get_word (e, filename);
  int count = get_word (e, filename);

  if (type != CURSOR_FILE_TYPE)
    fatal (_("cursor file `%s' does not contain cursor data"), filename);

  if (count <= 0 || count > MAX_CURSORS_PER_FILE)
    fatal (_("cursor file `%s' has an invalid number of cursors: %d"),
           filename, count);

  *out_count = count;
}

static struct icondir *
read_and_validate_directories (FILE *e, const char *filename, int count)
{
  struct icondir *icondirs = (struct icondir *) xmalloc (count * sizeof (*icondirs));
  for (int i = 0; i < count; i++)
    {
      icondirs[i].width = getc (e);
      icondirs[i].height = getc (e);
      icondirs[i].colorcount = getc (e);
      getc (e);
      icondirs[i].u.cursor.xhotspot = get_word (e, filename);
      icondirs[i].u.cursor.yhotspot = get_word (e, filename);
      icondirs[i].bytes = get_long (e, filename);
      icondirs[i].offset = get_long (e, filename);

      if (feof (e))
	unexpected_eof (filename);

      if (icondirs[i].bytes == 0 || icondirs[i].bytes > MAX_CURSOR_BYTES)
	fatal (_("cursor file `%s' has an entry with invalid size: %lu"),
	       filename, (unsigned long) icondirs[i].bytes);
    }
  return icondirs;
}

static void
define_one_cursor_from_file (const struct icondir *idir, FILE *e,
			     const char *filename,
			     const rc_res_res_info *resinfo, int cursor_id)
{
  if (fseek (e, idir->offset, SEEK_SET) != 0)
    fatal (_("%s: fseek to %lu failed: %s"), filename,
	   (unsigned long) idir->offset, strerror (errno));

  bfd_byte *data = (bfd_byte *) res_alloc (idir->bytes);
  get_data (e, data, idir->bytes, filename);

  rc_cursor *c = (rc_cursor *) res_alloc (sizeof (rc_cursor));
  c->xhotspot = idir->u.cursor.xhotspot;
  c->yhotspot = idir->u.cursor.yhotspot;
  c->length = idir->bytes;
  c->data = data;

  rc_res_id name;
  name.named = 0;
  name.u.id = cursor_id;

  rc_res_resource *r = define_standard_resource (&resources, RT_CURSOR, name,
						 resinfo->language, 0);
  r->type = RES_TYPE_CURSOR;
  r->u.cursor = c;
  r->res_info = *resinfo;
}

static rc_group_cursor *
create_cursor_group (int count, const struct icondir *icondirs,
		     int first_cursor_id_base)
{
  rc_group_cursor *first = NULL;
  rc_group_cursor **pp = &first;

  for (int i = 0; i < count; i++)
    {
      rc_group_cursor *cg =
	(rc_group_cursor *) res_alloc (sizeof (rc_group_cursor));
      cg->width = icondirs[i].width;
      cg->height = 2 * icondirs[i].height;
      cg->bytes = icondirs[i].bytes + 4;
      cg->index = first_cursor_id_base + i + 1;

      /* FIXME: What should these be set to?  */
      cg->planes = 1;
      cg->bits = 1;

      cg->next = NULL;
      *pp = cg;
      pp = &cg->next;
    }
  return first;
}

void
define_cursor (rc_res_id id, const rc_res_res_info *resinfo,
	       const char *filename)
{
  char *real_filename = NULL;
  FILE *e = open_file_search (filename, FOPEN_RB, "cursor file", &real_filename);

  int count;
  read_and_validate_header (e, real_filename, &count);

  struct icondir *icondirs =
    read_and_validate_directories (e, real_filename, count);

  const int first_cursor_id_base = cursors;
  for (int i = 0; i < count; i++)
    {
      define_one_cursor_from_file (&icondirs[i], e, real_filename, resinfo,
				   first_cursor_id_base + i + 1);
    }
  cursors += count;

  rc_group_cursor *group =
    create_cursor_group (count, icondirs, first_cursor_id_base);

  rc_res_resource *r =
    define_standard_resource (&resources, RT_GROUP_CURSOR, id, resinfo->language,
			      0);
  r->type = RES_TYPE_GROUP_CURSOR;
  r->u.group_cursor = group;
  r->res_info = *resinfo;

  free (icondirs);
  fclose (e);
  free (real_filename);
}

/* Define a dialog resource.  */

void
define_dialog (rc_res_id id, const rc_res_res_info *resinfo,
	       const rc_dialog *dialog)
{
  rc_dialog *copy = res_alloc (sizeof (*copy));
  if (copy == NULL)
    {
      return;
    }
  *copy = *dialog;

  rc_res_resource *r = define_standard_resource (&resources, RT_DIALOG, id,
						 resinfo->language, 0);
  if (r == NULL)
    {
      res_free (copy);
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
  rc_dialog_control *n = res_alloc (sizeof (*n));
  if (!n)
    {
      return NULL;
    }

  *n = (rc_dialog_control) {
    .id = id,
    .style = style,
    .exstyle = exstyle,
    .x = x,
    .y = y,
    .width = width,
    .height = height,
    .class = class,
    .text = iid,
    .next = NULL,
    .data = NULL,
    .help = 0
  };

  return n;
}

rc_dialog_control *
define_icon_control (rc_res_id iid, rc_uint_type id, rc_uint_type x,
		     rc_uint_type y, rc_uint_type style,
		     rc_uint_type exstyle, rc_uint_type help,
		     rc_rcdata_item *data, rc_dialog_ex *ex)
{
  if (style == 0)
  {
    style = SS_ICON | WS_CHILD | WS_VISIBLE;
  }

  rc_res_id tid;
  res_string_to_id (&tid, "");

  rc_res_id cid;
  cid.named = 0;
  cid.u.id = CTL_STATIC;

  rc_dialog_control *new_control =
    define_control (tid, id, x, y, 0, 0, cid, style, exstyle);
  if (new_control == NULL)
  {
    return NULL;
  }

  new_control->text = iid;
  new_control->help = help;
  new_control->data = data;

  if (ex == NULL)
  {
    if (help != 0)
    {
      rcparse_warning (_("help ID requires DIALOGEX"));
    }
    if (data != NULL)
    {
      rcparse_warning (_("control data requires DIALOGEX"));
    }
  }

  return new_control;
}

/* Define a font resource.  */

void
define_font (rc_res_id id, const rc_res_res_info *resinfo,
	     const char *filename)
{
  char *real_filename = NULL;
  FILE *font_file;
  struct stat file_stat;
  long file_size;
  bfd_byte *file_data;
  rc_res_resource *font_resource;
  const char *device_name;
  const char *face_name;
  long device_offset;
  long face_offset;
  size_t device_len;
  size_t face_len;
  long fontdir_data_length;
  bfd_byte *fontdir_data;
  rc_fontdir *fontdir_node;
  rc_fontdir **link_ptr;

  font_file = open_file_search (filename, FOPEN_RB, "font file", &real_filename);

  if (stat (real_filename, &file_stat) < 0)
    fatal (_("stat failed on font file `%s': %s"), real_filename,
	   strerror (errno));
  file_size = file_stat.st_size;

  file_data = (bfd_byte *) res_alloc (file_size);
  get_data (font_file, file_data, file_size, real_filename);

  fclose (font_file);
  free (real_filename);

  font_resource = define_standard_resource (&resources, RT_FONT, id,
					    resinfo->language, 0);
  font_resource->type = RES_TYPE_FONT;
  font_resource->u.data.length = file_size;
  font_resource->u.data.data = file_data;
  font_resource->res_info = *resinfo;

  device_name = "";
  if (file_size >= 48)
    {
      device_offset = ((long) file_data[47] << 24) | ((long) file_data[46] << 16)
	| ((long) file_data[45] << 8) | (long) file_data[44];
      if (device_offset > 0 && device_offset < file_size)
	device_name = (const char *) file_data + device_offset;
    }

  face_name = "";
  if (file_size >= 52)
    {
      face_offset = ((long) file_data[51] << 24) | ((long) file_data[50] << 16)
	| ((long) file_data[49] << 8) | (long) file_data[48];
      if (face_offset > 0 && face_offset < file_size)
	face_name = (const char *) file_data + face_offset;
    }

  device_len = strlen (device_name);
  face_len = strlen (face_name);
  fontdir_data_length = 56 + device_len + 1 + face_len + 1;
  fontdir_data = (bfd_byte *) res_alloc (fontdir_data_length);

  memcpy (fontdir_data, file_data, 56);
  memcpy (fontdir_data + 56, device_name, device_len + 1);
  memcpy (fontdir_data + 56 + device_len + 1, face_name, face_len + 1);

  fontdir_node = (rc_fontdir *) res_alloc (sizeof (rc_fontdir));
  fontdir_node->next = NULL;
  fontdir_node->index = ++fonts;
  fontdir_node->length = fontdir_data_length;
  fontdir_node->data = fontdir_data;

  for (link_ptr = &fontdirs; *link_ptr != NULL; link_ptr = &(*link_ptr)->next)
    {
    }
  *link_ptr = fontdir_node;

  fontdirs_resinfo = *resinfo;
}

static void
define_font_rcdata(rc_res_id id, const rc_res_res_info *resinfo,
                   const rc_rcdata_item *data)
{
  rc_res_resource *resource = define_standard_resource(&resources, RT_FONT, id,
                                                       resinfo->language, 0);
  if (resource == NULL)
  {
    return;
  }

  rc_uint_type data_length = 0;
  bfd_byte *data_buffer = rcdata_render_as_buffer(data, &data_length);

  resource->type = RES_TYPE_FONT;
  resource->u.data.length = data_length;
  resource->u.data.data = data_buffer;
  resource->res_info = *resinfo;
}

/* Define the fontdirs resource.  This is called after the entire rc
   file has been parsed, if any font resources were seen.  */

static void
define_fontdirs (void)
{
  rc_res_id id = { .named = 0, .u.id = FONTDIR_RESOURCE_ID };

  rc_res_resource *r = define_standard_resource (&resources, RT_FONTDIR, id,
                                                 LANG_ENGLISH_US, DEFAULT_MEM_FLAGS);
  if (!r)
    {
      return;
    }

  r->type = RES_TYPE_FONTDIR;
  r->u.fontdir = fontdirs;
  r->res_info = fontdirs_resinfo;
}

static bfd_byte *
rcdata_render_as_buffer (const rc_rcdata_item *data, rc_uint_type *plen)
{
  rc_uint_type len = 0;
  for (const rc_rcdata_item *d = data; d != NULL; d = d->next)
    {
      len += rcdata_copy (d, NULL);
    }

  bfd_byte *buffer = NULL;
  if (len > 0)
    {
      buffer = res_alloc (len);
      if (buffer != NULL)
        {
          bfd_byte *current_pos = buffer;
          for (const rc_rcdata_item *d = data; d != NULL; d = d->next)
            {
              current_pos += rcdata_copy (d, current_pos);
            }
        }
    }

  if (plen)
    {
      *plen = len;
    }

  return buffer;
}

#include <stddef.h>

#define LANG_US_ENGLISH 0x409
#define FONTDIR_HEADER_SIZE 2
#define FONTDIR_FIXED_ITEM_SIZE 56

static size_t
safe_get_two_nul_strings_len (const bfd_byte *start, rc_uint_type max_len)
{
  const bfd_byte *end = start + max_len;
  const bfd_byte *p = start;

  while (p < end && *p != '\0')
    p++;
  if (p >= end)
    return 0;
  p++;

  const bfd_byte *p2 = p;
  while (p2 < end && *p2 != '\0')
    p2++;
  if (p2 >= end)
    return 0;
  p2++;

  return (size_t) (p2 - start);
}

static void
define_fontdir_rcdata (rc_res_id id, const rc_res_res_info *resinfo,
		       rc_rcdata_item *data)
{
  rc_res_resource *r;
  rc_uint_type len_data;
  bfd_byte *pb_data;
  rc_fontdir *fd_head = NULL;
  rc_fontdir **pp_next = &fd_head;

  r = define_standard_resource (&resources, RT_FONTDIR, id, LANG_US_ENGLISH, 0);

  pb_data = rcdata_render_as_buffer (data, &len_data);
  if (!pb_data || len_data < FONTDIR_HEADER_SIZE)
    {
      r->type = RES_TYPE_FONTDIR;
      r->u.fontdir = NULL;
      r->res_info = *resinfo;
      return;
    }

  rc_uint_type num_entries = target_get_16 (pb_data, len_data);
  const bfd_byte *p = pb_data + FONTDIR_HEADER_SIZE;
  rc_uint_type len_rem = len_data - FONTDIR_HEADER_SIZE;

  for (rc_uint_type i = 0; i < num_entries; i++)
    {
      if (len_rem < FONTDIR_FIXED_ITEM_SIZE)
	break;

      const bfd_byte *name_start = p + FONTDIR_FIXED_ITEM_SIZE;
      rc_uint_type name_max_len = len_rem - FONTDIR_FIXED_ITEM_SIZE;
      size_t name_len = safe_get_two_nul_strings_len (name_start, name_max_len);

      if (name_len == 0)
	break;

      rc_uint_type item_len = FONTDIR_FIXED_ITEM_SIZE + (rc_uint_type) name_len;
      rc_fontdir *fd = (rc_fontdir *) res_alloc (sizeof (rc_fontdir));
      if (!fd)
	break;

      fd->index = target_get_16 (p, len_rem);
      fd->data = (bfd_byte *) p;
      fd->length = item_len;
      fd->next = NULL;

      *pp_next = fd;
      pp_next = &fd->next;

      p += item_len;
      len_rem -= item_len;
    }

  r->type = RES_TYPE_FONTDIR;
  r->u.fontdir = fd_head;
  r->res_info = *resinfo;
}

static void define_messagetable_rcdata(rc_res_id id, const rc_res_res_info *resinfo,
                                       rc_rcdata_item *data)
{
    rc_res_resource *r = define_standard_resource(&resources, RT_MESSAGETABLE, id, resinfo->language, 0);
    if (!r)
    {
        return;
    }

    rc_uint_type len_data = 0;
    bfd_byte *pb_data = rcdata_render_as_buffer(data, &len_data);

    r->type = RES_TYPE_MESSAGETABLE;
    r->u.data.length = pb_data ? len_data : 0;
    r->u.data.data = pb_data;
    r->res_info = *resinfo;
}

/* Define an icon resource.  An icon file may contain a set of
   bitmaps, each representing the same icon at various different
   resolutions.  They each get written out with a different ID.  The
   real icon resource is then a group resource which can be used to
   select one of the actual icon bitmaps.  */

#define ICON_TYPE_ICON 1
#define MAX_ICONS_IN_FILE 256
#define MAX_ICON_SIZE (1024 * 1024)

static int
read_icon_header (FILE *e, const char *filename)
{
  get_word (e, filename);
  int type = get_word (e, filename);
  if (type != ICON_TYPE_ICON)
    fatal (_("icon file `%s' does not contain icon data"), filename);

  int count = get_word (e, filename);
  if (count <= 0 || count > MAX_ICONS_IN_FILE)
    fatal (_("invalid number of icons (%d) in file `%s'"), count, filename);

  return count;
}

static struct icondir *
read_icon_directories (FILE *e, const char *filename, int count)
{
  struct icondir *icondirs =
    (struct icondir *) xmalloc (count * sizeof (*icondirs));
  for (int i = 0; i < count; i++)
    {
      unsigned char entry_header[4];
      if (fread (entry_header, 1, sizeof (entry_header), e) !=
	  sizeof (entry_header))
	unexpected_eof (filename);

      icondirs[i].width = entry_header[0];
      icondirs[i].height = entry_header[1];
      icondirs[i].colorcount = entry_header[2];

      icondirs[i].u.icon.planes = get_word (e, filename);
      icondirs[i].u.icon.bits = get_word (e, filename);
      icondirs[i].bytes = get_long (e, filename);
      icondirs[i].offset = get_long (e, filename);

      if (icondirs[i].bytes > MAX_ICON_SIZE)
	fatal (_("unreasonably large icon size (%lu) in file `%s'"),
	       (unsigned long) icondirs[i].bytes, filename);
    }
  return icondirs;
}

static void
define_individual_icons (int *icons_p, const rc_res_res_info *resinfo, FILE *e,
			 const char *filename,
			 const struct icondir *icondirs, int count)
{
  for (int i = 0; i < count; i++)
    {
      if (fseek (e, icondirs[i].offset, SEEK_SET) != 0)
	fatal (_("%s: fseek to %lu failed: %s"), filename,
	       (unsigned long) icondirs[i].offset, strerror (errno));

      bfd_byte *data = (bfd_byte *) res_alloc (icondirs[i].bytes);
      get_data (e, data, icondirs[i].bytes, filename);

      ++(*icons_p);

      rc_res_id name = { .named = 0, .u.id = *icons_p };

      rc_res_resource *r =
	define_standard_resource (&resources, RT_ICON, name,
				    resinfo->language, 0);
      r->type = RES_TYPE_ICON;
      r->u.data.length = icondirs[i].bytes;
      r->u.data.data = data;
      r->res_info = *resinfo;
    }
}

static rc_group_icon *
create_icon_group_list (const struct icondir *icondirs, int count,
			int first_icon_id)
{
  rc_group_icon *first = NULL;
  rc_group_icon **pp = &first;

  for (int i = 0; i < count; i++)
    {
      rc_group_icon *cg =
	(rc_group_icon *) res_alloc (sizeof (rc_group_icon));

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
      cg->index = first_icon_id + i + 1;
      cg->next = NULL;

      *pp = cg;
      pp = &cg->next;
    }
  return first;
}

void
define_icon (rc_res_id id, const rc_res_res_info *resinfo,
	     const char *filename)
{
  char *real_filename;
  FILE *e = open_file_search (filename, FOPEN_RB, "icon file", &real_filename);

  int count = read_icon_header (e, real_filename);
  struct icondir *icondirs = read_icon_directories (e, real_filename, count);

  int first_icon = icons;
  define_individual_icons (&icons, resinfo, e, real_filename, icondirs,
			   count);

  fclose (e);
  free (real_filename);

  rc_group_icon *group_list =
    create_icon_group_list (icondirs, count, first_icon);
  free (icondirs);

  rc_res_resource *r =
    define_standard_resource (&resources, RT_GROUP_ICON, id,
				resinfo->language, 0);
  r->type = RES_TYPE_GROUP_ICON;
  r->u.group_icon = group_list;
  r->res_info = *resinfo;
}

static void
define_group_icon_rcdata (rc_res_id id, const rc_res_res_info *resinfo,
			  rc_rcdata_item *data)
{
  rc_uint_type len_data;
  const bfd_byte *p = rcdata_render_as_buffer (data, &len_data);
  const bfd_byte * const end = p + len_data;
  rc_group_icon *head = NULL;
  rc_group_icon **p_next = &head;

  enum { GRPICONDIR_SIZE = 6 };
  enum { GRPICONDIRENTRY_SIZE = 14 };
  enum { GRPICON_TYPE = 1 };

  while (p + GRPICONDIR_SIZE <= end)
    {
      const unsigned short type = target_get_16 (p + 2, end - (p + 2));
      if (type != GRPICON_TYPE)
	fatal (_("unexpected group icon type %d"), type);

      const int count = target_get_16 (p + 4, end - (p + 4));
      p += GRPICONDIR_SIZE;

      for (int i = 0; i < count; i++)
	{
	  if (p + GRPICONDIRENTRY_SIZE > end)
	    fatal ("too small group icon rcdata");

	  rc_group_icon *cg = (rc_group_icon *) res_alloc (sizeof (rc_group_icon));
	  cg->next = NULL;
	  cg->width = p[0];
	  cg->height = p[1];
	  cg->colors = p[2];
	  cg->planes = target_get_16 (p + 4, end - (p + 4));
	  cg->bits =  target_get_16 (p + 6, end - (p + 6));
	  cg->bytes = target_get_32 (p + 8, end - (p + 8));
	  cg->index = target_get_16 (p + 12, end - (p + 12));

	  *p_next = cg;
	  p_next = &cg->next;

	  p += GRPICONDIRENTRY_SIZE;
	}
    }

  rc_res_resource *r = define_standard_resource (&resources, RT_GROUP_ICON, id,
				resinfo->language, 0);
  r->type = RES_TYPE_GROUP_ICON;
  r->u.group_icon = head;
  r->res_info = *resinfo;
}

static void
define_group_cursor_rcdata (rc_res_id id, const rc_res_res_info *resinfo,
			    rc_rcdata_item *data)
{
  rc_res_resource *r;
  rc_group_cursor *first = NULL;
  rc_group_cursor **next_p = &first;
  rc_uint_type len_data;
  bfd_byte *pb_data;

  const unsigned int GROUP_CURSOR_HEADER_SIZE = 6;
  const unsigned int GROUP_CURSOR_ENTRY_SIZE = 14;
  const unsigned short EXPECTED_GROUP_CURSOR_TYPE = 2;

  pb_data = rcdata_render_as_buffer (data, &len_data);

  if (len_data < GROUP_CURSOR_HEADER_SIZE)
    fatal (_("group cursor rcdata is too small for header"));

  unsigned short type = target_get_16 (pb_data + 2, len_data - 2);
  if (type != EXPECTED_GROUP_CURSOR_TYPE)
    fatal (_("unexpected group cursor type %d"), type);

  int count = target_get_16 (pb_data + 4, len_data - 4);
  pb_data += GROUP_CURSOR_HEADER_SIZE;
  len_data -= GROUP_CURSOR_HEADER_SIZE;

  for (int i = 0; i < count; i++)
    {
      if (len_data < GROUP_CURSOR_ENTRY_SIZE)
	fatal ("too small group icon rcdata");

      rc_group_cursor *cg = (rc_group_cursor *) res_alloc (sizeof (rc_group_cursor));

      cg->width = target_get_16 (pb_data, len_data);
      cg->height = target_get_16 (pb_data + 2, len_data - 2);
      cg->planes = target_get_16 (pb_data + 4, len_data - 4);
      cg->bits =  target_get_16 (pb_data + 6, len_data - 6);
      cg->bytes = target_get_32 (pb_data + 8, len_data - 8);
      cg->index = target_get_16 (pb_data + 12, len_data - 12);
      cg->next = NULL;

      *next_p = cg;
      next_p = &cg->next;

      pb_data += GROUP_CURSOR_ENTRY_SIZE;
      len_data -= GROUP_CURSOR_ENTRY_SIZE;
    }

  r = define_standard_resource (&resources, RT_GROUP_ICON, id,
				resinfo->language, 0);
  r->type = RES_TYPE_GROUP_CURSOR;
  r->u.group_cursor = first;
  r->res_info = *resinfo;
}

static void
define_cursor_rcdata (rc_res_id id, const rc_res_res_info *resinfo,
		      rc_rcdata_item *data)
{
  rc_uint_type len_data;
  bfd_byte *pb_data = rcdata_render_as_buffer (data, &len_data);

  if (pb_data == NULL || len_data < BIN_CURSOR_SIZE)
    {
      free (pb_data);
      return;
    }

  rc_cursor *c = res_alloc (sizeof (*c));
  if (c == NULL)
    {
      free (pb_data);
      return;
    }

  c->xhotspot = target_get_16 (pb_data, len_data);
  c->yhotspot = target_get_16 (pb_data + 2, len_data - 2);
  c->length = len_data - BIN_CURSOR_SIZE;
  c->data = pb_data + BIN_CURSOR_SIZE;

  rc_res_resource *r = define_standard_resource (&resources, RT_CURSOR, id,
						 resinfo->language, 0);
  if (r == NULL)
    {
      res_free (c);
      free (pb_data);
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
  if (!resinfo || !data)
    {
      return;
    }

  rc_uint_type len_data;
  bfd_byte *pb_data = rcdata_render_as_buffer (data, &len_data);
  if (!pb_data)
    {
      return;
    }

  rc_res_resource *r =
    define_standard_resource (&resources, RT_BITMAP, id, resinfo->language, 0);
  if (!r)
    {
      free (pb_data);
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
  if (resinfo == NULL || data == NULL)
    {
      abort ();
    }

  rc_uint_type icon_data_length = 0;
  bfd_byte *icon_data_buffer = rcdata_render_as_buffer (data, &icon_data_length);

  if (icon_data_buffer == NULL)
    {
      abort ();
    }

  rc_res_resource *resource =
    define_standard_resource (&resources, RT_ICON, id, resinfo->language, 0);

  if (resource == NULL)
    {
      free (icon_data_buffer);
      abort ();
    }

  resource->type = RES_TYPE_ICON;
  resource->u.data.length = icon_data_length;
  resource->u.data.data = icon_data_buffer;
  resource->res_info = *resinfo;
}

/* Define a menu resource.  */

void
define_menu (rc_res_id id, const rc_res_res_info *resinfo,
	     rc_menuitem *menuitems)
{
  if (resinfo == NULL)
    {
      return;
    }

  rc_menu *m = res_alloc (sizeof (*m));
  if (m == NULL)
    {
      return;
    }

  m->items = menuitems;
  m->help = 0;

  rc_res_resource *r = define_standard_resource (&resources, RT_MENU, id,
						 resinfo->language, 0);
  if (r == NULL)
    {
      /* A corresponding deallocation for 'm' should be called here. */
      return;
    }

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
  rc_menuitem *mi = res_alloc (sizeof (*mi));
  if (!mi)
    {
      return NULL;
    }

  mi->text = unichar_dup (text);
  if (text && !mi->text)
    {
      res_free (mi);
      return NULL;
    }

  mi->next = NULL;
  mi->type = type;
  mi->state = state;
  mi->id = menuid;
  mi->help = help;
  mi->popup = menuitems;

  return mi;
}

/* Define a messagetable resource.  */

void
define_messagetable (rc_res_id id, const rc_res_res_info *resinfo,
		     const char *filename)
{
  FILE *file_stream = NULL;
  char *real_filename = NULL;
  bfd_byte *data = NULL;
  rc_res_resource *resource = NULL;
  struct stat stat_buf;
  size_t file_size = 0;
  int result = 1;

  file_stream = open_file_search (filename, FOPEN_RB, "messagetable file",
				  &real_filename);
  if (file_stream == NULL)
    {
      windres_error (_("could not open messagetable file `%s'"), filename);
      goto cleanup;
    }

  if (stat (real_filename, &stat_buf) < 0)
    {
      windres_error (_("stat failed on messagetable file `%s': %s"), real_filename,
		     strerror (errno));
      goto cleanup;
    }

  if (stat_buf.st_size < 0)
    {
      windres_error (_("invalid size for messagetable file `%s'"), real_filename);
      goto cleanup;
    }
  file_size = (size_t) stat_buf.st_size;

  data = (bfd_byte *) res_alloc (file_size);
  if (data == NULL && file_size > 0)
    {
      windres_error (_("memory allocation failed for messagetable file `%s'"),
		     real_filename);
      goto cleanup;
    }

  get_data (file_stream, data, file_size, real_filename);
  if (ferror (file_stream))
    {
      windres_error (_("error reading from messagetable file `%s'"), real_filename);
      goto cleanup;
    }

  resource = define_standard_resource (&resources, RT_MESSAGETABLE, id,
				       resinfo->language, 0);
  if (resource == NULL)
    {
      windres_error (_("failed to define resource for messagetable from `%s'"),
		     real_filename);
      goto cleanup;
    }

  resource->type = RES_TYPE_MESSAGETABLE;
  resource->u.data.length = file_size;
  resource->u.data.data = data;
  resource->res_info = *resinfo;

  data = NULL;
  result = 0;

cleanup:
  if (file_stream != NULL)
    {
      fclose (file_stream);
    }
  free (real_filename);
  free (data);

  if (result != 0)
    {
      fatal (_("could not process messagetable file"));
    }
}

/* Define an rcdata resource.  */

void
define_rcdata (rc_res_id id, const rc_res_res_info *resinfo,
	       rc_rcdata_item *data)
{
  if (resinfo == NULL)
    {
      return;
    }

  rc_res_resource *r = define_standard_resource (&resources, RT_RCDATA, id,
						 resinfo->language, 0);
  if (r == NULL)
    {
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
  char *s = res_alloc (len);
  if (s == NULL && len > 0)
  {
    return NULL;
  }

  rc_rcdata_item *ri = res_alloc (sizeof (*ri));
  if (ri == NULL)
  {
    res_free (s);
    return NULL;
  }

  if (len > 0)
  {
    memcpy (s, string, len);
  }

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
  if (len > 0 && !string)
  {
    return NULL;
  }

  rc_rcdata_item *ri = res_alloc (sizeof (rc_rcdata_item));
  if (!ri)
  {
    return NULL;
  }

  ri->next = NULL;
  ri->type = RCDATA_WSTRING;
  ri->u.wstring.length = len;
  ri->u.wstring.w = NULL;

  if (len > 0)
  {
    if (len > ((size_t) -1) / sizeof (unichar))
    {
      res_free (ri);
      return NULL;
    }

    const size_t buffer_size = len * sizeof (unichar);
    unichar *s = res_alloc (buffer_size);

    if (!s)
    {
      res_free (ri);
      return NULL;
    }

    memcpy (s, string, buffer_size);
    ri->u.wstring.w = s;
  }

  return ri;
}

/* Create an rcdata item holding a number.  */

rc_rcdata_item *
define_rcdata_number (rc_uint_type val, int dword)
{
  rc_rcdata_item *ri = res_alloc (sizeof (*ri));
  if (ri == NULL)
    {
      return NULL;
    }

  ri->next = NULL;
  ri->type = dword ? RCDATA_DWORD : RCDATA_WORD;
  ri->u.word = val;

  return ri;
}

/* Define a stringtable resource.  This is called for each string
   which appears in a STRINGTABLE statement.  */

void
define_stringtable (const rc_res_res_info *resinfo,
		    rc_uint_type stringid, const unichar *string, int len)
{
  rc_res_id id;
  rc_res_resource *r;
  unichar *new_string;
  const rc_uint_type block_size = 16;
  rc_uint_type index_in_block;

  if (len < 0)
    return;

  id.named = 0;
  id.u.id = (stringid / block_size) + 1;
  r = define_standard_resource (&resources, RT_STRING, id,
				resinfo->language, 1);
  if (r == NULL)
    return;

  if (r->type == RES_TYPE_UNINITIALIZED)
    {
      r->u.stringtable = res_alloc (sizeof (rc_stringtable));
      if (r->u.stringtable == NULL)
	return;

      memset (r->u.stringtable, 0, sizeof (rc_stringtable));
      r->type = RES_TYPE_STRINGTABLE;
      r->res_info = *resinfo;
    }

  const size_t string_len = (size_t) len;
  new_string = res_alloc ((string_len + 1) * sizeof (unichar));
  if (new_string == NULL)
    return;

  if (string_len > 0)
    memcpy (new_string, string, string_len * sizeof (unichar));
  new_string[string_len] = 0;

  index_in_block = stringid % block_size;
  r->u.stringtable->strings[index_in_block].length = (rc_uint_type) string_len;
  r->u.stringtable->strings[index_in_block].string = new_string;
}

void
define_toolbar (rc_res_id id, rc_res_res_info *resinfo, rc_uint_type width, rc_uint_type height,
                rc_toolbar_item *items)
{
  if (resinfo == NULL)
    {
      return;
    }

  rc_toolbar *t = (rc_toolbar *) res_alloc (sizeof (rc_toolbar));
  if (t == NULL)
    {
      return;
    }

  t->button_width = width;
  t->button_height = height;
  t->items = items;
  t->nitems = 0;

  for (const rc_toolbar_item *it = items; it != NULL; it = it->next)
    {
      t->nitems++;
    }

  rc_res_resource *r = define_standard_resource (&resources, RT_TOOLBAR, id, resinfo->language, 0);
  if (r == NULL)
    {
      /* Leaks 't' but prevents a crash, as no 'res_free' is available. */
      return;
    }

  r->type = RES_TYPE_TOOLBAR;
  r->u.toolbar = t;
  r->res_info = *resinfo;
}

/* Define a user data resource where the data is in the rc file.  */

typedef void (*special_rcdata_definer_fn) (rc_res_id, const rc_res_res_info *,
					   rc_rcdata_item *);

typedef struct
{
  int id;
  special_rcdata_definer_fn definer;
} special_rcdata_definer;

static const special_rcdata_definer special_definers[] = {
  {RT_FONTDIR, define_fontdir_rcdata},
  {RT_FONT, define_font_rcdata},
  {RT_ICON, define_icon_rcdata},
  {RT_BITMAP, define_bitmap_rcdata},
  {RT_CURSOR, define_cursor_rcdata},
  {RT_GROUP_ICON, define_group_icon_rcdata},
  {RT_GROUP_CURSOR, define_group_cursor_rcdata},
  {RT_MESSAGETABLE, define_messagetable_rcdata}
};

void
define_user_data (rc_res_id id, rc_res_id type,
		  const rc_res_res_info *resinfo,
		  rc_rcdata_item *data)
{
  if (type.named == 0)
    {
      const size_t num_definers
	= sizeof (special_definers) / sizeof (special_definers[0]);
      for (size_t i = 0; i < num_definers; ++i)
	{
	  if (type.u.id == special_definers[i].id)
	    {
	      special_definers[i].definer (id, resinfo, data);
	      return;
	    }
	}
    }

  rc_res_id ids[3];
  rc_res_resource *r;
  bfd_byte *pb_data;
  rc_uint_type len_data;

  ids[0] = type;
  ids[1] = id;
  ids[2].named = 0;
  ids[2].u.id = resinfo->language;

  r = define_resource (&resources, sizeof (ids) / sizeof (ids[0]), ids, 0);

  r->type = RES_TYPE_USERDATA;
  r->u.userdata = (rc_rcdata_item *) res_alloc (sizeof (rc_rcdata_item));
  if (r->u.userdata == NULL)
    {
      return;
    }

  r->u.userdata->next = NULL;
  r->u.userdata->type = RCDATA_BUFFER;

  pb_data = rcdata_render_as_buffer (data, &len_data);
  if (pb_data == NULL)
    {
      res_free (r->u.userdata);
      r->u.userdata = NULL;
      return;
    }

  r->u.userdata->u.buffer.length = len_data;
  r->u.userdata->u.buffer.data = pb_data;
  r->res_info = *resinfo;
}

void
define_rcdata_file (rc_res_id id, const rc_res_res_info *resinfo,
		    const char *filename)
{
  FILE *e = NULL;
  char *real_filename = NULL;
  bfd_byte *data = NULL;
  rc_rcdata_item *ri = NULL;
  struct stat s;
  int success = 0;

  e = open_file_search (filename, FOPEN_RB, "file", &real_filename);

  if (stat (real_filename, &s) < 0)
    goto cleanup;

  data = (bfd_byte *) res_alloc (s.st_size);

  get_data (e, data, s.st_size, real_filename);

  ri = (rc_rcdata_item *) res_alloc (sizeof (rc_rcdata_item));
  ri->next = NULL;
  ri->type = RCDATA_BUFFER;
  ri->u.buffer.length = s.st_size;
  ri->u.buffer.data = data;

  define_rcdata (id, resinfo, ri);

  success = 1;

cleanup:
  if (e != NULL)
    fclose (e);

  if (!success)
    fatal (_("stat failed on file `%s': %s"), real_filename,
	   strerror (errno));

  free (real_filename);
}

/* Define a user data resource where the data is in a file.  */

void
define_user_file (rc_res_id id, rc_res_id type,
		  const rc_res_res_info *resinfo, const char *filename)
{
  char *real_filename = NULL;
  FILE *e = open_file_search (filename, FOPEN_RB, "file", &real_filename);
  if (e == NULL)
    fatal (_("could not find or open file `%s'"), filename);

  struct stat s;
  if (fstat (fileno (e), &s) < 0)
    fatal (_("fstat failed on file `%s': %s"), real_filename,
	   strerror (errno));

  if (!S_ISREG (s.st_mode))
    fatal (_("not a regular file: `%s'"), real_filename);

  bfd_byte *data = res_alloc (s.st_size);
  if (data == NULL && s.st_size > 0)
    fatal (_("memory allocation failed for `%s'"), real_filename);

  get_data (e, data, s.st_size, real_filename);

  fclose (e);
  free (real_filename);

  rc_res_id ids[3];
  ids[0] = type;
  ids[1] = id;
  ids[2].named = 0;
  ids[2].u.id = resinfo->language;

  rc_res_resource *r =
    define_resource (&resources, sizeof (ids) / sizeof (ids[0]), ids, 0);
  if (r == NULL)
    fatal (_("failed to define resource for `%s'"), filename);

  rc_rcdata_item *userdata = res_alloc (sizeof (rc_rcdata_item));
  if (userdata == NULL)
    fatal (_("memory allocation failed for resource item for `%s'"), filename);

  userdata->next = NULL;
  userdata->type = RCDATA_BUFFER;
  userdata->u.buffer.length = s.st_size;
  userdata->u.buffer.data = data;

  r->type = RES_TYPE_USERDATA;
  r->u.userdata = userdata;
  r->res_info = *resinfo;
}

/* Define a versioninfo resource.  */

void
define_versioninfo (rc_res_id id, rc_uint_type language,
		    rc_fixed_versioninfo *fixedverinfo,
		    rc_ver_info *verinfo)
{
  rc_res_resource *r = define_standard_resource (&resources, RT_VERSION, id, language, 0);
  if (r == NULL)
    {
      return;
    }

  rc_versioninfo *new_info = res_alloc (sizeof (*new_info));
  if (new_info == NULL)
    {
      r->u.versioninfo = NULL;
      return;
    }

  new_info->fixed = fixedverinfo;
  new_info->var = verinfo;

  r->type = RES_TYPE_VERSIONINFO;
  r->u.versioninfo = new_info;
  r->res_info.language = language;
}

/* Add string version info to a list of version information.  */

rc_ver_info *
append_ver_stringfileinfo(rc_ver_info *verinfo,
                          rc_ver_stringtable *stringtables)
{
    rc_ver_info *new_info = res_alloc(sizeof(*new_info));
    if (new_info == NULL)
    {
        return verinfo;
    }

    new_info->next = NULL;
    new_info->type = VERINFO_STRING;
    new_info->u.string.stringtables = stringtables;

    rc_ver_info **p_next = &verinfo;
    while (*p_next != NULL)
    {
        p_next = &(*p_next)->next;
    }

    *p_next = new_info;

    return verinfo;
}

rc_ver_stringtable *
append_ver_stringtable (rc_ver_stringtable *stringtable,
                        const char *language,
                        rc_ver_stringinfo *strings)
{
  rc_ver_stringtable *vst = res_alloc (sizeof (*vst));
  if (vst == NULL)
    {
      return stringtable;
    }

  vst->next = NULL;
  vst->strings = strings;
  unicode_from_ascii ((rc_uint_type *) NULL, &vst->language, language);

  rc_ver_stringtable **pp = &stringtable;
  while (*pp != NULL)
    {
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
  rc_ver_info *new_node = res_alloc (sizeof *new_node);
  if (!new_node)
    {
      return verinfo;
    }

  new_node->u.var.key = unichar_dup (key);
  if (!new_node->u.var.key)
    {
      res_free (new_node);
      return verinfo;
    }

  new_node->type = VERINFO_VAR;
  new_node->u.var.var = var;
  new_node->next = NULL;

  if (!verinfo)
    {
      return new_node;
    }

  rc_ver_info *current = verinfo;
  while (current->next != NULL)
    {
      current = current->next;
    }
  current->next = new_node;

  return verinfo;
}

/* Append version string information to a list.  */

rc_ver_stringinfo *
append_verval (rc_ver_stringinfo *strings, const unichar *key,
	       const unichar *value)
{
  rc_ver_stringinfo *vs = res_alloc (sizeof (*vs));
  if (!vs)
    {
      return strings;
    }

  vs->key = unichar_dup (key);
  if (!vs->key)
    {
      res_free (vs);
      return strings;
    }

  vs->value = unichar_dup (value);
  if (!vs->value)
    {
      res_free (vs->key);
      res_free (vs);
      return strings;
    }

  vs->next = NULL;

  rc_ver_stringinfo **p_next = &strings;
  while (*p_next)
    {
      p_next = &(*p_next)->next;
    }
  *p_next = vs;

  return strings;
}

/* Append version variable information to a list.  */

rc_ver_varinfo *
append_vertrans (rc_ver_varinfo *var, rc_uint_type language,
                 rc_uint_type charset)
{
  rc_ver_varinfo *new_node = res_alloc (sizeof (rc_ver_varinfo));
  if (!new_node)
    {
      return var;
    }

  new_node->language = language;
  new_node->charset = charset;
  new_node->next = NULL;

  if (!var)
    {
      return new_node;
    }

  rc_ver_varinfo *current = var;
  while (current->next)
    {
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

static void indent(FILE *stream, int count)
{
    if (stream == NULL || count <= 0) {
        return;
    }

    fprintf(stream, "%*s", count, "");
}

/* Dump the resources we have read in the format of an rc file.

   Reasoned by the fact, that some resources need to be stored into file and
   refer to that file, we use the user-data model for that to express it binary
   without the need to store it somewhere externally.  */

bool
write_rc_file (const char *filename, const rc_res_directory *res_dir)
{
  rc_uint_type language = (rc_uint_type) ((bfd_signed_vma) -1);

  if (filename == NULL)
    {
      write_rc_directory (stdout, res_dir, NULL, NULL, &language, 1);
      return ferror (stdout) == 0;
    }

  FILE *e = fopen (filename, FOPEN_WT);
  if (e == NULL)
    {
      non_fatal (_("can't open `%s' for output: %s"), filename,
		 strerror (errno));
      return false;
    }

  write_rc_directory (e, res_dir, NULL, NULL, &language, 1);

  if (fclose (e) != 0)
    {
      non_fatal (_("error closing `%s': %s"), filename, strerror (errno));
      return false;
    }

  return true;
}

/* Write out a directory.  E is the file to write to.  RD is the
   directory.  TYPE is a pointer to the level 1 ID which serves as the
   resource type.  NAME is a pointer to the level 2 ID which serves as
   an individual resource name.  LANGUAGE is a pointer to the current
   language.  LEVEL is the level in the tree.  */

static void
write_coff_info (FILE *e, const rc_res_directory *rd)
{
  if (rd->time == 0 && rd->characteristics == 0 && rd->major == 0 && rd->minor == 0)
    {
      return;
    }

  wr_printcomment (e, "COFF information not part of RC");

  if (rd->time != 0)
    {
      wr_printcomment (e, "Time stamp: %u", rd->time);
    }
  if (rd->characteristics != 0)
    {
      wr_printcomment (e, "Characteristics: %u", rd->characteristics);
    }
  if (rd->major != 0 || rd->minor != 0)
    {
      wr_printcomment (e, "Version major:%d minor:%d", rd->major, rd->minor);
    }
}

static void
update_language_if_needed (FILE *e, const rc_res_id *id, rc_uint_type *current_language)
{
  if (id->named || (id->u.id & 0xffff) != id->u.id)
    {
      return;
    }

  if (id->u.id == (unsigned long) (unsigned int) *current_language)
    {
      return;
    }

  wr_print (e, "LANGUAGE %u, %u\n",
	    id->u.id & ((1 << SUBLANG_SHIFT) - 1),
	    (id->u.id >> SUBLANG_SHIFT) & 0xff);
  *current_language = id->u.id;
}

static void
process_resource_leaf (FILE *e, const rc_res_entry *re,
                       const rc_res_id *type, const rc_res_id *name,
                       rc_uint_type *language, int level)
{
  const rc_res_id *res_name = name;

  if (level != 3)
    {
      wr_printcomment (e, "Resource at unexpected level %d", level);
      res_name = NULL;
    }
  write_rc_resource (e, type, res_name, re->u.res, language);
}

static void
write_rc_directory (FILE *e, const rc_res_directory *rd,
		    const rc_res_id *type, const rc_res_id *name,
		    rc_uint_type *language, int level)
{
  const rc_res_entry *re;

  write_coff_info (e, rd);

  for (re = rd->entries; re != NULL; re = re->next)
    {
      switch (level)
	{
	case 1:
	  type = &re->id;
	  break;
	case 2:
	  name = &re->id;
	  break;
	case 3:
	  update_language_if_needed (e, &re->id, language);
	  break;
	default:
	  break;
	}

      if (re->subdir)
	{
	  write_rc_subdir (e, re, type, name, language, level);
	}
      else
	{
	  process_resource_leaf (e, re, type, name, language, level);
	}
    }

  if (rd->entries == NULL)
    {
      wr_print_flush (e);
    }
}

/* Write out a subdirectory entry.  E is the file to write to.  RE is
   the subdirectory entry.  TYPE and NAME are pointers to higher level
   IDs, or NULL.  LANGUAGE is a pointer to the current language.
   LEVEL is the level in the tree.  */

static const char *
get_resource_type_string (rc_uint_type id)
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

static void
write_rc_subdir (FILE *e, const rc_res_entry *re,
		 const rc_res_id *type, const rc_res_id *name,
		 rc_uint_type *language, int level)
{
  fprintf (e, "\n");
  switch (level)
    {
    case 1:
      {
	wr_printcomment (e, "Type: ");
	const char *s = NULL;
	if (!re->id.named)
	  s = get_resource_type_string (re->id.u.id);

	if (s)
	  fprintf (e, "%s", s);
	else
	  res_id_print (e, re->id, 1);
	break;
      }

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

  write_rc_directory (e, re->u.dir, type, name, language, level + 1);
}

/* Write out a single resource.  E is the file to write to.  TYPE is a
   pointer to the type of the resource.  NAME is a pointer to the name
   of the resource; it will be NULL if there is a level mismatch.  RES
   is the resource data.  LANGUAGE is a pointer to the current
   language.  */

typedef struct
{
  const char *type_name;
  int rt_val;
  int is_menuex;
} resource_info_t;

static resource_info_t
get_resource_type_info (const rc_res_resource *res)
{
  resource_info_t info = { NULL, 0, 0 };

  switch (res->type)
    {
    case RES_TYPE_ACCELERATOR:
      info.type_name = "ACCELERATORS";
      info.rt_val = RT_ACCELERATOR;
      break;
    case RES_TYPE_BITMAP:
      info.type_name = "2 /* RT_BITMAP */";
      info.rt_val = RT_BITMAP;
      break;
    case RES_TYPE_CURSOR:
      info.type_name = "1 /* RT_CURSOR */";
      info.rt_val = RT_CURSOR;
      break;
    case RES_TYPE_GROUP_CURSOR:
      info.type_name = "12 /* RT_GROUP_CURSOR */";
      info.rt_val = RT_GROUP_CURSOR;
      break;
    case RES_TYPE_DIALOG:
      info.type_name = extended_dialog (res->u.dialog) ? "DIALOGEX" : "DIALOG";
      info.rt_val = RT_DIALOG;
      break;
    case RES_TYPE_FONT:
      info.type_name = "8 /* RT_FONT */";
      info.rt_val = RT_FONT;
      break;
    case RES_TYPE_FONTDIR:
      info.type_name = "7 /* RT_FONTDIR */";
      info.rt_val = RT_FONTDIR;
      break;
    case RES_TYPE_ICON:
      info.type_name = "3 /* RT_ICON */";
      info.rt_val = RT_ICON;
      break;
    case RES_TYPE_GROUP_ICON:
      info.type_name = "14 /* RT_GROUP_ICON */";
      info.rt_val = RT_GROUP_ICON;
      break;
    case RES_TYPE_MENU:
      if (extended_menu (res->u.menu))
	{
	  info.type_name = "MENUEX";
	  info.is_menuex = 1;
	}
      else
	{
	  info.type_name = "MENU";
	}
      info.rt_val = RT_MENU;
      break;
    case RES_TYPE_MESSAGETABLE:
      info.type_name = "11 /* RT_MESSAGETABLE */";
      info.rt_val = RT_MESSAGETABLE;
      break;
    case RES_TYPE_RCDATA:
      info.type_name = "RCDATA";
      info.rt_val = RT_RCDATA;
      break;
    case RES_TYPE_STRINGTABLE:
      info.type_name = "STRINGTABLE";
      info.rt_val = RT_STRING;
      break;
    case RES_TYPE_USERDATA:
      break;
    case RES_TYPE_VERSIONINFO:
      info.type_name = "VERSIONINFO";
      info.rt_val = RT_VERSION;
      break;
    case RES_TYPE_TOOLBAR:
      info.type_name = "TOOLBAR";
      info.rt_val = RT_TOOLBAR;
      break;
    default:
      info.rt_val = -1;
      break;
    }
  return info;
}

static void
print_type_identifier (FILE *e, const rc_res_id *type, const char *type_string)
{
  if (type_string != NULL)
    {
      fprintf (e, "%s", type_string);
      return;
    }
  if (type == NULL)
    {
      fprintf (e, "??Unknown-Type??");
      return;
    }
  if (type->named)
    {
      res_id_print (e, *type, 1);
      return;
    }

  const char *name = NULL;
  switch (type->u.id)
    {
    case RT_MANIFEST: name = "RT_MANIFEST"; break;
    case RT_ANICURSOR: name = "RT_ANICURSOR"; break;
    case RT_ANIICON: name = "RT_ANIICON"; break;
    case RT_RCDATA: name = "RT_RCDATA"; break;
    case RT_ICON: name = "RT_ICON"; break;
    case RT_CURSOR: name = "RT_CURSOR"; break;
    case RT_BITMAP: name = "RT_BITMAP"; break;
    case RT_PLUGPLAY: name = "RT_PLUGPLAY"; break;
    case RT_VXD: name = "RT_VXD"; break;
    case RT_FONT: name = "RT_FONT"; break;
    case RT_FONTDIR: name = "RT_FONTDIR"; break;
    case RT_HTML: name = "RT_HTML"; break;
    case RT_MESSAGETABLE: name = "RT_MESSAGETABLE"; break;
    case RT_DLGINCLUDE: name = "RT_DLGINCLUDE"; break;
    case RT_DLGINIT: name = "RT_DLGINIT"; break;
    default: break;
    }

  if (name)
    fprintf (e, "%u /* %s */", (unsigned int) type->u.id, name);
  else
    res_id_print (e, *type, 0);
}

static void
write_resource_memflags (FILE *e, rc_uint_type memflags)
{
  if ((memflags & MEMFLAG_MOVEABLE) != 0)
    fprintf (e, " MOVEABLE");
  if ((memflags & MEMFLAG_PURE) != 0)
    fprintf (e, " PURE");
  if ((memflags & MEMFLAG_PRELOAD) != 0)
    fprintf (e, " PRELOAD");
  if ((memflags & MEMFLAG_DISCARDABLE) != 0)
    fprintf (e, " DISCARDABLE");
}

static void
write_specific_header (FILE *e, const rc_res_resource *res)
{
  if (res->type == RES_TYPE_DIALOG)
    {
      fprintf (e, " %d, %d, %d, %d",
	       (int) res->u.dialog->x, (int) res->u.dialog->y,
	       (int) res->u.dialog->width, (int) res->u.dialog->height);
      if (res->u.dialog->ex != NULL && res->u.dialog->ex->help != 0)
	fprintf (e, ", %u", (unsigned int) res->u.dialog->ex->help);
    }
  else if (res->type == RES_TYPE_TOOLBAR)
    {
      fprintf (e, " %d, %d", (int) res->u.toolbar->button_width,
	       (int) res->u.toolbar->button_height);
    }
}

static void
write_resource_modifiers (FILE *e, const rc_res_resource *res, rc_uint_type language)
{
  if ((res->res_info.language == 0 || res->res_info.language == language)
      && res->res_info.characteristics == 0 && res->res_info.version == 0)
    {
      return;
    }

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
  const char *prefix = modifiers ? "// " : "";

  if (res->res_info.language != 0 && res->res_info.language != language)
    fprintf (e, "%sLANGUAGE %d, %d\n", prefix,
	     (int) res->res_info.language & ((1 << SUBLANG_SHIFT) - 1),
	     (int) (res->res_info.language >> SUBLANG_SHIFT) & 0xff);
  if (res->res_info.characteristics != 0)
    fprintf (e, "%sCHARACTERISTICS %u\n", prefix, (unsigned int) res->res_info.characteristics);
  if (res->res_info.version != 0)
    fprintf (e, "%sVERSION %u\n", prefix, (unsigned int) res->res_info.version);
}

static void
write_resource_data (FILE *e, const rc_res_id *name, const rc_res_resource *res, int is_menuex)
{
  switch (res->type)
    {
    case RES_TYPE_ACCELERATOR:
      write_rc_accelerators (e, res->u.acc);
      break;
    case RES_TYPE_CURSOR:
      write_rc_cursor (e, res->u.cursor);
      break;
    case RES_TYPE_GROUP_CURSOR:
      write_rc_group_cursor (e, res->u.group_cursor);
      break;
    case RES_TYPE_DIALOG:
      write_rc_dialog (e, res->u.dialog);
      break;
    case RES_TYPE_FONTDIR:
      write_rc_fontdir (e, res->u.fontdir);
      break;
    case RES_TYPE_GROUP_ICON:
      write_rc_group_icon (e, res->u.group_icon);
      break;
    case RES_TYPE_MENU:
      write_rc_menu (e, res->u.menu, is_menuex);
      break;
    case RES_TYPE_RCDATA:
      write_rc_rcdata (e, res->u.rcdata, 0);
      break;
    case RES_TYPE_STRINGTABLE:
      write_rc_stringtable (e, name, res->u.stringtable);
      break;
    case RES_TYPE_USERDATA:
      write_rc_rcdata (e, res->u.userdata, 0);
      break;
    case RES_TYPE_TOOLBAR:
      write_rc_toolbar (e, res->u.toolbar);
      break;
    case RES_TYPE_VERSIONINFO:
      write_rc_versioninfo (e, res->u.versioninfo);
      break;
    case RES_TYPE_BITMAP:
    case RES_TYPE_FONT:
    case RES_TYPE_ICON:
      write_rc_datablock (e, res->u.data.length, res->u.data.data, 0, 1, 0);
      break;
    case RES_TYPE_MESSAGETABLE:
      write_rc_messagetable (e, res->u.data.length, res->u.data.data);
      break;
    default:
      break;
    }
}

static void
write_rc_resource (FILE *e, const rc_res_id *type,
		   const rc_res_id *name, const rc_res_resource *res,
		   rc_uint_type *language)
{
  if (e == NULL || res == NULL || language == NULL)
    return;

  resource_info_t info = get_resource_type_info (res);
  if (info.rt_val < 0)
    {
      wr_printcomment (e, "Unsupported resource type: %d", res->type);
      return;
    }

  if (info.rt_val != 0 && type != NULL
      && (type->named || type->u.id != (unsigned long) info.rt_val))
    {
      wr_printcomment (e, "Unexpected resource type mismatch: ");
      res_id_print (e, *type, 1);
      fprintf (e, " != %d", info.rt_val);
    }

  if (res->coff_info.codepage != 0)
    wr_printcomment (e, "Code page: %u", res->coff_info.codepage);
  if (res->coff_info.reserved != 0)
    wr_printcomment (e, "COFF reserved value: %u", res->coff_info.reserved);

  fprintf (e, "\n");

  if (info.rt_val != RT_STRING)
    {
      if (name != NULL)
	res_id_print (e, *name, 1);
      else
	fprintf (e, "??Unknown-Name??");
      fprintf (e, " ");
    }

  print_type_identifier (e, type, info.type_name);
  write_resource_memflags (e, res->res_info.memflags);
  write_specific_header (e, res);

  fprintf (e, "\n");

  write_resource_modifiers (e, res, *language);
  write_resource_data (e, name, res, info.is_menuex);
}

/* Write out accelerator information.  */

static void
write_rc_accelerators (FILE *e, const rc_accelerator *accelerators)
{
  const rc_accelerator *acc;

  fprintf (e, "BEGIN\n");
  for (acc = accelerators; acc != NULL; acc = acc->next)
    {
      const int is_printable_key = ((acc->key & 0x7f) == acc->key)
                                   && ISPRINT (acc->key)
                                   && ((acc->flags & ACC_VIRTKEY) == 0);

      fprintf (e, "  ");

      if (is_printable_key)
	{
	  fprintf (e, "\"%c\"", (char) acc->key);
	}
      else
	{
	  fprintf (e, "%d", acc->key);
	  if ((acc->flags & ACC_VIRTKEY) != 0)
	    fprintf (e, ", VIRTKEY");
	  else
	    fprintf (e, ", ASCII");
	}

      fprintf (e, ", %d", acc->id);

      if ((acc->flags & ACC_SHIFT) != 0)
	fprintf (e, ", SHIFT");
      if ((acc->flags & ACC_CONTROL) != 0)
	fprintf (e, ", CONTROL");
      if ((acc->flags & ACC_ALT) != 0)
	fprintf (e, ", ALT");

      fprintf (e, "\n");
    }

  fprintf (e, "END\n");
}

/* Write out cursor information.  This would normally be in a separate
   file, which the rc file would include.  */

static void
write_rc_cursor (FILE *e, const rc_cursor *cursor)
{
  static const int hotspot_indent = 2;
  static const int datablock_indent = 0;
  static const int use_dwords = 0;
  static const int allow_split = 0;
  static const char *const hotspot_format =
    " 0x%x, 0x%x,\t/* Hotspot x: %u, y: %u.  */\n";

  const unsigned int xhot = cursor->xhotspot;
  const unsigned int yhot = cursor->yhotspot;

  fprintf (e, "BEGIN\n");
  indent (e, hotspot_indent);
  fprintf (e, hotspot_format, xhot, yhot, xhot, yhot);
  write_rc_datablock (e, (rc_uint_type) cursor->length,
		      (const bfd_byte *) cursor->data,
		      datablock_indent, use_dwords, allow_split);
  fprintf (e, "END\n");
}

/* Write out group cursor data.  This would normally be built from the
   cursor data.  */

static int
write_rc_group_cursor (FILE *e, const rc_group_cursor *group_cursor)
{
  if (e == NULL)
    {
      return -1;
    }

  int count = 0;
  for (const rc_group_cursor *gc = group_cursor; gc != NULL; gc = gc->next)
    {
      count++;
    }

  if (fprintf (e, "BEGIN\n") < 0)
    {
      return -1;
    }

  indent (e, 2);
  if (fprintf (e, "0, 2, %d%s\t /* Having %d items.  */\n", count, (count > 0 ? "," : ""), count) < 0)
    {
      return -1;
    }

  indent (e, 4);
  if (fprintf (e, "/* width, height, planes, bits, bytes, index.  */\n") < 0)
    {
      return -1;
    }

  int item_index = 1;
  for (const rc_group_cursor *gc = group_cursor; gc != NULL; gc = gc->next)
    {
      indent (e, 4);
      if (fprintf (e, "%d, %d, %d, %d, 0x%x, %d%s /* Element %d. */\n",
                   (int) gc->width, (int) gc->height, (int) gc->planes, (int) gc->bits,
                   (unsigned int) gc->bytes, (int) gc->index, (gc->next != NULL ? "," : ""),
                   item_index) < 0)
        {
          return -1;
        }
      if (fprintf (e, "/* width: %d; height %d; planes %d; bits %d.  */\n",
                   (int) gc->width, (int) gc->height, (int) gc->planes,
                   (int) gc->bits) < 0)
        {
          return -1;
        }
      item_index++;
    }

  if (fprintf (e, "END\n") < 0)
    {
      return -1;
    }

  return 0;
}

/* Write dialog data.  */

static bool
res_id_is_set (const res_id *id)
{
  return (id->named && id->u.n.length > 0) || id->u.id != 0;
}

static void
write_rc_dialog_exstyle (FILE *e, unsigned int exstyle)
{
  if (exstyle != 0)
    {
      fprintf (e, "EXSTYLE 0x%x\n", exstyle);
    }
}

static void
write_rc_dialog_class (FILE *e, const res_id *class_id)
{
  if (res_id_is_set (class_id))
    {
      fprintf (e, "CLASS ");
      res_id_print (e, *class_id, 1);
      fprintf (e, "\n");
    }
}

static void
write_rc_dialog_caption (FILE *e, const unicode_string *caption)
{
  if (caption != NULL)
    {
      fprintf (e, "CAPTION ");
      unicode_print_quoted (e, caption, -1);
      fprintf (e, "\n");
    }
}

static void
write_rc_dialog_menu (FILE *e, const res_id *menu_id)
{
  if (res_id_is_set (menu_id))
    {
      fprintf (e, "MENU ");
      res_id_print (e, *menu_id, 0);
      fprintf (e, "\n");
    }
}

static void
write_rc_font_extras (FILE *e, const rc_dialog_ex *ex)
{
  if (ex != NULL
      && (ex->weight != 0 || ex->italic != 0 || ex->charset != 1))
    {
      fprintf (e, ", %d, %d, %d", (int) ex->weight, (int) ex->italic,
	       (int) ex->charset);
    }
}

static void
write_rc_dialog_font (FILE *e, const unicode_string *font,
                      unsigned short pointsize, const rc_dialog_ex *ex)
{
  if (font != NULL)
    {
      fprintf (e, "FONT %d, ", (int) pointsize);
      unicode_print_quoted (e, font, -1);
      write_rc_font_extras (e, ex);
      fprintf (e, "\n");
    }
}

static void
write_rc_dialog_controls (FILE *e, const rc_dialog_control *controls)
{
  for (const rc_dialog_control *control = controls; control != NULL;
       control = control->next)
    {
      write_rc_dialog_control (e, control);
    }
}

static void
write_rc_dialog (FILE *e, const rc_dialog *dialog)
{
  fprintf (e, "STYLE 0x%x\n", dialog->style);
  write_rc_dialog_exstyle (e, dialog->exstyle);
  write_rc_dialog_class (e, &dialog->class);
  write_rc_dialog_caption (e, dialog->caption);
  write_rc_dialog_menu (e, &dialog->menu);
  write_rc_dialog_font (e, dialog->font, dialog->pointsize, dialog->ex);

  fprintf (e, "BEGIN\n");
  write_rc_dialog_controls (e, dialog->controls);
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

static const struct control_info *
find_control_info (const rc_dialog_control *control)
{
  if (control->class.named)
    return NULL;

  for (const struct control_info *ci = control_info; ci->name != NULL; ++ci)
    {
      if (ci->class == control->class.u.id
	  && (ci->style == (unsigned long) -1
	      || ci->style == (control->style & 0xff)))
	return ci;
    }

  return NULL;
}

static int
should_dump_text (const rc_dialog_control *control,
		  const struct control_info *ci)
{
  if (!control->text.named && control->text.u.id == 0)
    return 0;

  if (ci == NULL)
    return 1;

  switch (ci->class)
    {
    case CTL_EDIT:
    case CTL_COMBOBOX:
    case CTL_LISTBOX:
    case CTL_SCROLLBAR:
      return 0;
    default:
      return 1;
    }
}

static int
has_extended_attributes (const rc_dialog_control *control)
{
  return (control->style != SS_ICON
	  || control->exstyle != 0
	  || control->width != 0
	  || control->height != 0
	  || control->help != 0);
}

static void
write_rc_dialog_control (FILE *e, const rc_dialog_control *control)
{
  const struct control_info *ci = find_control_info (control);

  fprintf (e, "  %s", (ci != NULL) ? ci->name : "CONTROL");

  if (should_dump_text (control, ci))
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

  if (has_extended_attributes (control))
    {
      fprintf (e, ", %d, %d", (int) control->width, (int) control->height);

      if (ci != NULL)
	{
	  /* FIXME: We don't need to print the style if it is the default.
	     More importantly, in certain cases we actually need to turn
	     off parts of the forced style, by using NOT.  */
	  fprintf (e, ", 0x%x", (unsigned int) control->style);
	}

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
write_rc_fontdir (FILE *out_file, const rc_fontdir *fontdir)
{
  const rc_fontdir *current_font;
  int count = 0;
  int font_number;

  for (current_font = fontdir; current_font != NULL; current_font = current_font->next)
    {
      count++;
    }

  fprintf (out_file, "BEGIN\n");
  indent (out_file, 2);
  fprintf (out_file, "%d%s\t /* Has %d elements.  */\n", count, count > 0 ? "," : "", count);

  font_number = 1;
  for (current_font = fontdir; current_font != NULL; current_font = current_font->next)
    {
      indent (out_file, 4);
      fprintf (out_file, "%d,\t/* Font no %d with index %d.  */\n",
               (int) current_font->index, font_number, (int) current_font->index);
      write_rc_datablock (out_file,
                          (rc_uint_type) current_font->length - 2,
                          (const bfd_byte *) current_font->data + 4,
                          current_font->next != NULL,
                          0, 0);
      font_number++;
    }

  fprintf (out_file, "END\n");
}

/* Write out group icon data.  This would normally be built from the
   icon data.  */

static void
write_rc_group_icon (FILE *e, const rc_group_icon *group_icon)
{
  int count = 0;
  for (const rc_group_icon *gi = group_icon; gi != NULL; gi = gi->next)
    {
      count++;
    }

  fprintf (e, "BEGIN\n");
  indent (e, 2);
  fprintf (e, " 0, 1, %d%s\t /* Has %d elements.  */\n", count, (count > 0 ? "," : ""), count);

  indent (e, 4);
  fprintf (e, "/* \"width height colors pad\", planes, bits, bytes, index.  */\n");

  int element_no = 1;
  for (const rc_group_icon *gi = group_icon; gi != NULL; gi = gi->next, element_no++)
    {
      indent (e, 4);
      fprintf (e, "\"\\%03o\\%03o\\%03o\\%03o\", %d, %d, 0x%xL, %d%s\t/* Element no %d.  */\n",
	       gi->width, gi->height, gi->colors, 0,
	       (int) gi->planes, (int) gi->bits,
	       (unsigned int) gi->bytes, (int) gi->index,
	       (gi->next != NULL ? "," : ""), element_no);
    }
  fprintf (e, "END\n");
}

/* Write out a menu resource.  */

static void
write_rc_menu (FILE *e, const rc_menu *menu, int menuex)
{
  if (e == NULL || menu == NULL)
  {
    return;
  }

  if (menu->help != 0)
  {
    (void) fprintf (e, "// Help ID: %u\n", (unsigned int) menu->help);
  }

  write_rc_menuitems (e, menu->items, menuex, 0);
}

static void
write_rc_toolbar (FILE *e, const rc_toolbar *tb)
{
  if (!e || !tb)
  {
    return;
  }

  indent (e, 0);
  fprintf (e, "BEGIN\n");

  for (const rc_toolbar_item *it = tb->items; it != NULL; it = it->next)
  {
    indent (e, 2);
    if (it->id.u.id == 0)
    {
      fprintf (e, "SEPARATOR\n");
    }
    else
    {
      fprintf (e, "BUTTON %d\n", (int) it->id.u.id);
    }
  }

  indent (e, 0);
  fprintf (e, "END\n");
}

/* Write out menuitems.  */

static bool
is_separator (const rc_menuitem * mi)
{
  return mi->popup == NULL && mi->text == NULL && mi->type == 0 && mi->id == 0;
}

static void
write_menu_text (FILE * e, const char *text)
{
  if (text == NULL)
    {
      fprintf (e, " \"\"");
    }
  else
    {
      fprintf (e, " ");
      unicode_print_quoted (e, text, -1);
    }
}

static void
write_standard_menu_attributes (FILE * e, const rc_menuitem * mi)
{
  typedef struct
  {
    unsigned int flag;
    const char *name;
  } menu_flag_info;

  static const menu_flag_info menu_flags[] = {
    {MENUITEM_CHECKED, ", CHECKED"},
    {MENUITEM_GRAYED, ", GRAYED"},
    {MENUITEM_HELP, ", HELP"},
    {MENUITEM_INACTIVE, ", INACTIVE"},
    {MENUITEM_MENUBARBREAK, ", MENUBARBREAK"},
    {MENUITEM_MENUBREAK, ", MENUBREAK"},
    {MENUITEM_OWNERDRAW, ", OWNERDRAW"},
    {MENUITEM_BITMAP, ", BITMAP"}
  };

  if (mi->popup == NULL)
    {
      fprintf (e, ", %d", (int) mi->id);
    }

  for (size_t i = 0; i < sizeof (menu_flags) / sizeof (menu_flags[0]); ++i)
    {
      if ((mi->type & menu_flags[i].flag) != 0)
	{
	  fprintf (e, "%s", menu_flags[i].name);
	}
    }
}

static void
write_extended_menu_attributes (FILE * e, const rc_menuitem * mi)
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
		{
		  fprintf (e, ", %u", (unsigned int) mi->help);
		}
	    }
	}
    }
}

static void
write_rc_menuitems (FILE * e, const rc_menuitem * menuitems, int menuex,
		    int ind)
{
  if (e == NULL)
    {
      return;
    }

  indent (e, ind);
  fprintf (e, "BEGIN\n");

  for (const rc_menuitem * mi = menuitems; mi != NULL; mi = mi->next)
    {
      indent (e, ind + 2);
      fprintf (e, "%s", (mi->popup == NULL) ? "MENUITEM" : "POPUP");

      if (!menuex && is_separator (mi))
	{
	  fprintf (e, " SEPARATOR\n");
	  continue;
	}

      write_menu_text (e, mi->text);

      if (!menuex)
	{
	  write_standard_menu_attributes (e, mi);
	}
      else
	{
	  write_extended_menu_attributes (e, mi);
	}

      fprintf (e, "\n");

      if (mi->popup != NULL)
	{
	  write_rc_menuitems (e, mi->popup, menuex, ind + 2);
	}
    }

  indent (e, ind);
  fprintf (e, "END\n");
}

static int
test_rc_datablock_unicode (rc_uint_type length, const bfd_byte *data)
{
  if ((length & 1) != 0)
    {
      return 0;
    }

  if (length > 0 && !data)
    {
      return 0;
    }

  for (rc_uint_type i = 0; i < length; i += 2)
    {
      if (data[i] == 0 && data[i + 1] == 0 && (i + 2) < length)
        {
          return 0;
        }

      if (data[i] == 0xff && data[i + 1] == 0xff)
        {
          return 0;
        }
    }

  return 1;
}

static int
test_rc_datablock_text (rc_uint_type length, const bfd_byte *data)
{
  const rc_uint_type min_length = 2;
  const int low_char_threshold = 7;
  const rc_uint_type max_len_no_newline = 80;
  const unsigned long long non_printable_multiplier = 10000;
  const rc_uint_type len_divisor_for_score = 100;
  const rc_uint_type score_threshold = 150;

  if (length < min_length)
    {
      return 0;
    }

  rc_uint_type non_printable_count = 0;
  int newline_count = 0;

  for (rc_uint_type i = 0; i < length; i++)
    {
      const bfd_byte current_char = data[i];

      if (ISPRINT (current_char) || current_char == '\t')
	{
	  continue;
	}

      if (current_char == '\n')
	{
	  newline_count++;
	  continue;
	}

      if (current_char == '\r' && (i + 1) < length && data[i + 1] == '\n')
	{
	  continue;
	}

      if (current_char == 0 && (i + 1) == length)
	{
	  continue;
	}

      if (current_char <= low_char_threshold)
	{
	  return 0;
	}
      non_printable_count++;
    }

  if (length > max_len_no_newline && newline_count == 0)
    {
      return 0;
    }

  rc_uint_type adjustment = 0;
  if (length >= len_divisor_for_score)
    {
      adjustment = (length / len_divisor_for_score) - 1;
    }

  unsigned long long numerator =
      (unsigned long long)non_printable_count * non_printable_multiplier
      + adjustment;

  if ((numerator / length) >= score_threshold)
    {
      return 0;
    }

  return 1;
}

static int
dump_message_entry (FILE *e, rc_uint_type length, const bfd_byte *data,
                    rc_uint_type id, rc_uint_type *offset)
{
  if ((*offset + BIN_MESSAGETABLE_ITEM_SIZE) > length)
    {
      return 1;
    }

  const struct bin_messagetable_item *mti =
    (const struct bin_messagetable_item *) &data[*offset];
  const rc_uint_type elen = windres_get_16 (&wrtarget, mti->length);
  const rc_uint_type flags = windres_get_16 (&wrtarget, mti->flags);

  if ((*offset + elen) > length)
    {
      return 1;
    }

  wr_printcomment (e, "MessageId = 0x%x", id);
  wr_printcomment (e, "");

  if ((flags & MESSAGE_RESOURCE_UNICODE) == MESSAGE_RESOURCE_UNICODE)
    {
      /* PR 17512: file: 5c3232dc.  */
      if (elen > BIN_MESSAGETABLE_ITEM_SIZE * 2)
	{
	  unicode_print (e, (const unichar *) mti->data,
			 (elen - BIN_MESSAGETABLE_ITEM_SIZE) / 2);
	}
    }
  else
    {
      if (elen > BIN_MESSAGETABLE_ITEM_SIZE)
	{
	  ascii_print (e, (const char *) mti->data,
		       elen - BIN_MESSAGETABLE_ITEM_SIZE);
	}
    }

  wr_printcomment (e, "");
  *offset += elen;
  return 0;
}

static int
dump_message_table_syntax (FILE *e, rc_uint_type length, const bfd_byte *data)
{
  if (length < BIN_MESSAGETABLE_SIZE)
    {
      return 1;
    }

  const struct bin_messagetable *mt = (const struct bin_messagetable *) data;
  const rc_uint_type m = target_get_32 (mt->cblocks, length);

  if (length < (BIN_MESSAGETABLE_SIZE + m * BIN_MESSAGETABLE_BLOCK_SIZE))
    {
      return 1;
    }

  for (rc_uint_type i = 0; i < m; i++)
    {
      const rc_uint_type low = windres_get_32 (&wrtarget, mt->items[i].lowid);
      const rc_uint_type high = windres_get_32 (&wrtarget, mt->items[i].highid);
      rc_uint_type offset = windres_get_32 (&wrtarget, mt->items[i].offset);

      for (rc_uint_type id = low; id <= high; ++id)
	{
	  if (dump_message_entry (e, length, data, id, &offset))
	    {
	      return 1;
	    }
	}
    }
  return 0;
}

static void
write_rc_messagetable (FILE *e, rc_uint_type length, const bfd_byte *data)
{
  fprintf (e, "BEGIN\n");

  write_rc_datablock (e, length, data, 0, 0, 0);

  fprintf (e, "\n");
  wr_printcomment (e, "MC syntax dump");

  if (dump_message_table_syntax (e, length, data))
    {
      wr_printcomment (e, "Illegal data");
    }

  wr_print_flush (e);
  fprintf (e, "END\n");
}

#define MAX_CHARS_PER_LINE 160
#define MAX_LONGS_PER_ROW_COMMENTED 4
#define MAX_LONGS_PER_ROW_NO_COMMENT 8
#define NUMERIC_PADDING 11

static void
write_rc_text_block (FILE *e, rc_uint_type length, const bfd_byte *data)
{
  if (length == 0)
    {
      indent (e, 2);
      fprintf (e, "\"\"");
      return;
    }

  rc_uint_type i = 0;
  while (i < length)
    {
      rc_uint_type c = 0;
      rc_uint_type line_start = i;

      while (i < length && c < MAX_CHARS_PER_LINE && data[i] != '\n')
	{
	  c++;
	  i++;
	}
      if (i < length && data[i] == '\n')
	{
	  c++;
	  i++;
	}

      indent (e, 2);
      fprintf (e, "\"");
      ascii_print (e, (const char *) &data[line_start], c);
      fprintf (e, "\"");

      if (i < length)
	fprintf (e, "\n");
    }
}

static void
write_rc_unicode_block (FILE *e, rc_uint_type length, const bfd_byte *data)
{
  if (length == 0)
    {
      indent (e, 2);
      fprintf (e, "L\"\"");
      return;
    }

  rc_uint_type i = 0;
  while (i < length)
    {
      rc_uint_type c = 0;
      const unichar *u = (const unichar *) &data[i];

      while (i < length && c < MAX_CHARS_PER_LINE && u[c] != '\n')
	{
	  c++;
	  i += 2;
	}
      if (i < length && u[c] == '\n')
	{
	  c++;
	  i += 2;
	}

      indent (e, 2);
      fprintf (e, "L\"");
      unicode_print (e, u, c);
      fprintf (e, "\"");

      if (i < length)
	fprintf (e, "\n");
    }
}

static void
write_rc_numeric_block (FILE *e, rc_uint_type length, const bfd_byte *data,
			int show_comment, int has_next)
{
  if (length == 0)
    return;

  rc_uint_type i = 0;
  int first_line = 1;
  const rc_uint_type max_row =
    show_comment ? MAX_LONGS_PER_ROW_COMMENTED : MAX_LONGS_PER_ROW_NO_COMMENT;

  while (i + 3 < length)
    {
      if (!first_line)
	indent (e, 2);
      first_line = 0;

      rc_uint_type comment_start = i;
      for (rc_uint_type k = 0; k < max_row && i + 3 < length; k++, i += 4)
	{
	  if (k > 0)
	    fprintf (e, " ");

	  char buffer[32];
	  unsigned long val = target_get_32 (data + i, length - i);
	  int plen = snprintf (buffer, sizeof (buffer), "0x%lxL", val);
	  fprintf (e, "%s", buffer);

	  if (has_next || (i + 4) < length)
	    {
	      if (plen > 0 && plen < NUMERIC_PADDING)
		indent (e, NUMERIC_PADDING - plen);
	      fprintf (e, ",");
	    }
	}

      if (show_comment)
	{
	  fprintf (e, "\t/* ");
	  ascii_print (e, (const char *) &data[comment_start],
		       i - comment_start);
	  fprintf (e, ".  */");
	}
      fprintf (e, "\n");
    }

  if (i + 1 < length)
    {
      if (!first_line)
	indent (e, 2);
      first_line = 0;

      char buffer[32];
      int val = target_get_16 (data + i, length - i);
      int plen = snprintf (buffer, sizeof (buffer), "0x%x", val);
      fprintf (e, "%s", buffer);

      if (has_next || (i + 2) < length)
	{
	  if (plen > 0 && plen < NUMERIC_PADDING)
	    indent (e, NUMERIC_PADDING - plen);
	  fprintf (e, ",");
	}

      if (show_comment)
	{
	  fprintf (e, "\t/* ");
	  ascii_print (e, (const char *) &data[i], 2);
	  fprintf (e, ".  */");
	}
      fprintf (e, "\n");
      i += 2;
    }

  if (i < length)
    {
      if (!first_line)
	indent (e, 2);
      fprintf (e, "\"");
      ascii_print (e, (const char *) &data[i], 1);
      fprintf (e, "\"");
      if (has_next)
	fprintf (e, ",");
      fprintf (e, "\n");
    }
}

static void
write_rc_datablock (FILE *e, rc_uint_type length, const bfd_byte *data,
		    int has_next, int hasblock, int show_comment)
{
  if (hasblock)
    fprintf (e, "BEGIN\n");

  int effective_show_comment = show_comment;
  int is_text_like = 0;

  if (show_comment == -1)
    {
      if (test_rc_datablock_text (length, data))
	{
	  write_rc_text_block (e, length, data);
	  is_text_like = 1;
	}
      else if (test_rc_datablock_unicode (length, data))
	{
	  write_rc_unicode_block (e, length, data);
	  is_text_like = 1;
	}
      else
	{
	  effective_show_comment = 0;
	}
    }

  if (is_text_like)
    {
      if (has_next)
	fprintf (e, ",");
      fprintf (e, "\n");
    }
  else
    {
      write_rc_numeric_block (e, length, data, effective_show_comment,
			      has_next);
    }

  if (hasblock)
    fprintf (e, "END\n");
}

/* Write out an rcdata resource.  This is also used for other types of
   resources that need to print arbitrary data.  */

static void
write_rc_rcdata (FILE *e, const rc_rcdata_item *rcdata, int ind)
{
  const rc_rcdata_item *ri;

  indent (e, ind);
  fprintf (e, "BEGIN\n");

  for (ri = rcdata; ri != NULL; ri = ri->next)
    {
      if (ri->type == RCDATA_BUFFER)
	{
	  if (ri->u.buffer.length > 0)
	    {
	      write_rc_datablock (e, (rc_uint_type) ri->u.buffer.length,
				  (const bfd_byte *) ri->u.buffer.data,
				  ri->next != NULL, 0, -1);
	    }
	}
      else
	{
	  indent (e, ind + 2);
	  switch (ri->type)
	    {
	    case RCDATA_WORD:
	      fprintf (e, "%ld", (long) (ri->u.word & 0xffff));
	      break;

	    case RCDATA_DWORD:
	      fprintf (e, "%luL", (unsigned long) ri->u.dword);
	      break;

	    case RCDATA_STRING:
	      fprintf (e, "\"");
	      ascii_print (e, ri->u.string.s, ri->u.string.length);
	      fprintf (e, "\"");
	      break;

	    case RCDATA_WSTRING:
	      fprintf (e, "L\"");
	      unicode_print (e, ri->u.wstring.w, ri->u.wstring.length);
	      fprintf (e, "\"");
	      break;

	    default:
	      abort ();
	    }
	  fprintf (e, "%s", ri->next ? ",\n" : "\n");
	}
    }

  indent (e, ind);
  fprintf (e, "END\n");
}

/* Write out a stringtable resource.  */

static void
write_rc_stringtable (FILE *e, const rc_res_id *name,
		      const rc_stringtable *stringtable)
{
  const int strings_per_block = 16;
  rc_uint_type offset = 0;

  if (name != NULL && !name->named)
    {
      offset = (name->u.id - 1) * strings_per_block;
    }
  else
    {
      const char *reason = (name == NULL) ? "Missing" : "Invalid";
      fprintf (e, "/* %s string table name.  */\n", reason);
    }

  fprintf (e, "BEGIN\n");

  for (int i = 0; i < strings_per_block; i++)
    {
      const rc_string *entry = &stringtable->strings[i];
      if (entry->length != 0)
	{
	  fprintf (e, "  %lu, ", (unsigned long) offset + i);
	  unicode_print_quoted (e, entry->string, entry->length);
	  fprintf (e, "\n");
	}
    }

  fprintf (e, "END\n");
}

/* Write out a versioninfo resource.  */

static void
write_version_quad (FILE *e, const char *keyword, unsigned long ms, unsigned long ls)
{
  if (ms != 0 || ls != 0)
    fprintf (e, " %s %u, %u, %u, %u\n", keyword,
	     (unsigned int) ((ms >> 16) & 0xffff),
	     (unsigned int) (ms & 0xffff),
	     (unsigned int) ((ls >> 16) & 0xffff),
	     (unsigned int) (ls & 0xffff));
}

static void
write_hex_value (FILE *e, const char *keyword, unsigned long value)
{
  if (value != 0)
    fprintf (e, " %s 0x%x\n", keyword, (unsigned int) value);
}

static void
write_fixed_info (FILE *e, const rc_fixed_versioninfo *f)
{
  if (f == NULL)
    return;

  write_version_quad (e, "FILEVERSION", f->file_version_ms, f->file_version_ls);
  write_version_quad (e, "PRODUCTVERSION", f->product_version_ms, f->product_version_ls);
  write_hex_value (e, "FILEFLAGSMASK", f->file_flags_mask);
  write_hex_value (e, "FILEFLAGS", f->file_flags);
  write_hex_value (e, "FILEOS", f->file_os);
  write_hex_value (e, "FILETYPE", f->file_type);
  write_hex_value (e, "FILESUBTYPE", f->file_subtype);

  if (f->file_date_ms != 0 || f->file_date_ls != 0)
    fprintf (e, "/* Date: %u, %u.  */\n",
	     (unsigned int) f->file_date_ms, (unsigned int) f->file_date_ls);
}

static void
write_string_file_info_block (FILE *e, const rc_ver_string *ver_string)
{
  const rc_ver_stringtable *vst;
  const rc_ver_stringinfo *vs;

  fprintf (e, "  BLOCK \"StringFileInfo\"\n");
  fprintf (e, "  BEGIN\n");

  for (vst = ver_string->stringtables; vst != NULL; vst = vst->next)
    {
      fprintf (e, "    BLOCK ");
      unicode_print_quoted (e, vst->language, -1);
      fprintf (e, "\n    BEGIN\n");

      for (vs = vst->strings; vs != NULL; vs = vs->next)
	{
	  fprintf (e, "      VALUE ");
	  unicode_print_quoted (e, vs->key, -1);
	  fprintf (e, ", ");
	  unicode_print_quoted (e, vs->value, -1);
	  fprintf (e, "\n");
	}
      fprintf (e, "    END\n");
    }
  fprintf (e, "  END\n");
}

static void
write_var_file_info_block (FILE *e, const rc_ver_var *ver_var)
{
  const rc_ver_varinfo *vv;

  fprintf (e, "  BLOCK \"VarFileInfo\"\n");
  fprintf (e, "  BEGIN\n");
  fprintf (e, "    VALUE ");
  unicode_print_quoted (e, ver_var->key, -1);

  for (vv = ver_var->var; vv != NULL; vv = vv->next)
    fprintf (e, ", 0x%x, %d", (unsigned int) vv->language, (int) vv->charset);

  fprintf (e, "\n  END\n");
}

static void
write_rc_versioninfo (FILE *e, const rc_versioninfo *versioninfo)
{
  const rc_ver_info *vi;

  if (e == NULL || versioninfo == NULL)
    return;

  write_fixed_info (e, versioninfo->fixed);

  fprintf (e, "BEGIN\n");

  for (vi = versioninfo->var; vi != NULL; vi = vi->next)
    {
      switch (vi->type)
	{
	case VERINFO_STRING:
	  write_string_file_info_block (e, &vi->u.string);
	  break;
	case VERINFO_VAR:
	  write_var_file_info_block (e, &vi->u.var);
	  break;
	}
    }

  fprintf (e, "END\n");
}

static rc_uint_type
rcdata_copy (const rc_rcdata_item *src, bfd_byte *dst)
{
  rc_uint_type size;

  if (!src)
    {
      return 0;
    }

  switch (src->type)
    {
    case RCDATA_WORD:
      size = 2;
      if (dst)
        {
          windres_put_16 (&wrtarget, dst, (rc_uint_type) src->u.word);
        }
      break;
    case RCDATA_DWORD:
      size = 4;
      if (dst)
        {
          windres_put_32 (&wrtarget, dst, (rc_uint_type) src->u.dword);
        }
      break;
    case RCDATA_STRING:
      size = (rc_uint_type) src->u.string.length;
      if (dst && size)
        {
          memcpy (dst, src->u.string.s, size);
        }
      break;
    case RCDATA_WSTRING:
      size = (rc_uint_type) (src->u.wstring.length * sizeof (unichar));
      if (dst && size)
        {
          memcpy (dst, src->u.wstring.w, size);
        }
      break;
    case RCDATA_BUFFER:
      size = (rc_uint_type) src->u.buffer.length;
      if (dst && size)
        {
          memcpy (dst, src->u.buffer.data, size);
        }
      break;
    default:
      abort ();
    }
  return size;
}
