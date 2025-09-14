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

  if (!cmd || !redir) {
    return 1;
  }

  i = 1;
  for (s = cmd; *s; s++) {
    if (*s == ' ') {
      i++;
    }
  }

  argv = xmalloc (sizeof (char *) * (i + 3));
  i = 0;
  s = cmd;

  while (1) {
    while (*s == ' ' && *s != 0) {
      s++;
    }

    if (*s == 0) {
      break;
    }

    in_quote = (*s == '\'' || *s == '"');
    sep = (in_quote) ? *s++ : ' ';
    argv[i++] = s;

    while (*s != sep && *s != 0) {
      s++;
    }

    if (*s == 0) {
      break;
    }

    *s++ = 0;

    if (in_quote && *s != 0) {
      s++;
    }
  }
  argv[i] = NULL;

  fflush (stdout);
  fflush (stderr);

  redir_handle = open (redir, O_WRONLY | O_TRUNC | O_CREAT, 0666);
  if (redir_handle == -1) {
    free (argv);
    fatal (_("can't open temporary file `%s': %s"), redir, strerror (errno));
    return 1;
  }

  stdout_save = dup (STDOUT_FILENO);
  if (stdout_save == -1) {
    close (redir_handle);
    free (argv);
    fatal (_("can't redirect stdout: `%s': %s"), redir, strerror (errno));
    return 1;
  }

  if (dup2 (redir_handle, STDOUT_FILENO) == -1) {
    close (stdout_save);
    close (redir_handle);
    free (argv);
    fatal (_("can't redirect stdout: `%s': %s"), redir, strerror (errno));
    return 1;
  }

  pid = pexecute (argv[0], (char * const *) argv, program_name, temp_base,
                  &errmsg_fmt, &errmsg_arg, PEXECUTE_ONE | PEXECUTE_SEARCH);

  dup2 (stdout_save, STDOUT_FILENO);
  close (stdout_save);
  close (redir_handle);
  free (argv);

  if (pid == -1) {
    fatal ("%s %s: %s", errmsg_fmt, errmsg_arg, strerror (errno));
    return 1;
  }

  retcode = 0;
  pid = pwait (pid, &wait_status, 0);

  if (pid == -1) {
    fatal (_("wait: %s"), strerror (errno));
    retcode = 1;
  } else if (WIFSIGNALED (wait_status)) {
    fatal (_("subprocess got fatal signal %d"), WTERMSIG (wait_status));
    retcode = 1;
  } else if (WIFEXITED (wait_status)) {
    if (WEXITSTATUS (wait_status) != 0) {
      fatal (_("%s exited with status %d"), cmd, WEXITSTATUS (wait_status));
      retcode = 1;
    }
  } else {
    retcode = 1;
  }

  return retcode;
}

static FILE *
open_input_stream (char *cmd)
{
  FILE *result = NULL;
  
  if (istream_type == ISTREAM_FILE)
    {
      char *fileprefix = make_temp_file (NULL);
      if (fileprefix == NULL)
        fatal (_("failed to create temporary file prefix"));
        
      size_t prefix_len = strlen (fileprefix);
      cpp_temp_file = (char *) xmalloc (prefix_len + 5);
      snprintf (cpp_temp_file, prefix_len + 5, "%s.irc", fileprefix);
      free (fileprefix);

      if (run_cmd (cmd, cpp_temp_file))
        fatal (_("can't execute `%s': %s"), cmd, strerror (errno));

      result = fopen (cpp_temp_file, FOPEN_RT);
      if (result == NULL)
        fatal (_("can't open temporary file `%s': %s"),
               cpp_temp_file, strerror (errno));

      if (verbose)
        fprintf (stderr,
                 _("Using temporary file `%s' to read preprocessor output\n"),
                 cpp_temp_file);
    }
  else
    {
      result = popen (cmd, FOPEN_RT);
      if (result == NULL)
        fatal (_("can't popen `%s': %s"), cmd, strerror (errno));
      if (verbose)
        fprintf (stderr, _("Using popen to read preprocessor output\n"));
    }

  cpp_pipe = result;
  xatexit (close_input_stream);
  return result;
}

/* Determine if FILENAME contains special characters that
   can cause problems unless the entire filename is quoted.  */

static int
filename_need_quotes (const char *filename)
{
  const char special_chars[] = {'&', ' ', '<', '>', '|', '%'};
  const size_t num_special_chars = sizeof(special_chars) / sizeof(special_chars[0]);
  size_t i;

  if (filename == NULL || (filename[0] == '-' && filename[1] == '\0'))
    return 0;

  while (*filename != '\0')
    {
      for (i = 0; i < num_special_chars; i++)
        {
          if (*filename == special_chars[i])
            return 1;
        }
      filename++;
    }
  return 0;
}

/* Look for the preprocessor program.  */

static FILE *
look_for_default (char *cmd, const char *prefix, int end_prefix,
		  const char *preprocargs, const char *filename)
{
  struct stat s;
  const char *fnquotes;
  char *out;
  int found = 0;
  size_t cmd_len;
  size_t remaining_space;

  if (!cmd || !prefix || !preprocargs || !filename || end_prefix < 0) {
    return NULL;
  }

  fnquotes = (filename_need_quotes (filename) ? "\"" : "");

  memcpy (cmd, prefix, end_prefix);

  out = stpcpy (cmd + end_prefix, DEFAULT_PREPROCESSOR_CMD);

  if (
#if defined (__DJGPP__) || defined (__CYGWIN__) || defined (_WIN32)
      strchr (cmd, '\\') ||
#endif
      strchr (cmd, '/'))
    {
      found = (stat (cmd, &s) == 0);
      
#ifdef HAVE_EXECUTABLE_SUFFIX
      if (!found) {
        cmd_len = strlen(cmd);
        if (cmd_len + strlen(EXECUTABLE_SUFFIX) < PATH_MAX) {
          strcat (cmd, EXECUTABLE_SUFFIX);
          found = (stat (cmd, &s) == 0);
          if (!found) {
            cmd[cmd_len] = '\0';
          }
        }
      }
#endif

      if (!found) {
	if (verbose)
	  fprintf (stderr, _("Tried `%s'\n"), cmd);
	return NULL;
      }
    }

  if (filename_need_quotes (cmd))
    {
      cmd_len = out - cmd;
      memmove (cmd + 1, cmd, cmd_len);
      cmd[0] = '"';
      out++;
      *out++ = '"';
    }

  remaining_space = PATH_MAX - (out - cmd);
  if (snprintf (out, remaining_space, " %s %s %s%s%s",
	        DEFAULT_PREPROCESSOR_ARGS, preprocargs, fnquotes, filename, fnquotes) >= remaining_space) {
    return NULL;
  }

  if (verbose)
    fprintf (stderr, _("Using `%s'\n"), cmd);

  cpp_pipe = open_input_stream (cmd);
  return cpp_pipe;
}

/* Read an rc file.  */

rc_res_directory *
read_rc_file (const char *filename, const char *preprocessor,
	      const char *preprocargs, int language, int use_temp_file)
{
  char *cmd = NULL;
  const char *fnquotes;
  const char *safe_filename;
  
  safe_filename = (filename != NULL) ? filename : "-";
  fnquotes = (filename_need_quotes (safe_filename) ? "\"" : "");
  
  if (filename != NULL && (strchr (filename, '/') != NULL || strchr (filename, '\\') != NULL))
    {
      char *dir = setup_include_directory(filename);
      if (dir != NULL)
        {
          windres_add_include_dir (dir);
          free (dir);
        }
    }

  istream_type = (use_temp_file) ? ISTREAM_FILE : ISTREAM_PIPE;

  if (preprocargs == NULL)
    preprocargs = "";

  if (preprocessor)
    {
      cmd = build_preprocessor_command(preprocessor, preprocargs, safe_filename, fnquotes);
      if (cmd == NULL)
        return NULL;
      cpp_pipe = open_input_stream (cmd);
    }
  else
    {
      cmd = xmalloc (strlen (program_name)
		     + strlen (DEFAULT_PREPROCESSOR_CMD)
		     + strlen (DEFAULT_PREPROCESSOR_ARGS)
		     + strlen (preprocargs)
		     + strlen (safe_filename)
		     + strlen (fnquotes) * 2
#ifdef HAVE_EXECUTABLE_SUFFIX
		     + strlen (EXECUTABLE_SUFFIX)
#endif
		     + 10);

      cpp_pipe = find_default_preprocessor(cmd, preprocargs, safe_filename);
    }

  free (cmd);

  rc_filename = xstrdup (safe_filename);
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

static char *
setup_include_directory(const char *filename)
{
  char *edit, *dir;
  size_t len = strlen (filename) + 3;
  
  dir = xmalloc (len);
  edit = dir;
  
  if (filename[0] != '/' && filename[0] != '\\' && filename[1] != ':')
    {
      *edit++ = '.';
      *edit++ = '/';
    }
  
  edit = stpcpy (edit, filename);

  while (edit > dir && (edit[-1] != '\\' && edit[-1] != '/'))
    --edit;

  if (edit > dir)
    *--edit = '\0';

  while ((edit = strchr (dir, '\\')) != NULL)
    *edit = '/';

  return dir;
}

static char *
build_preprocessor_command(const char *preprocessor, const char *preprocargs,
                          const char *filename, const char *fnquotes)
{
  char *cmd;
  size_t total_len = strlen (preprocessor) + strlen (preprocargs) + 
                     strlen (filename) + strlen (fnquotes) * 2 + 10;
  
  cmd = xmalloc (total_len);
  if (cmd == NULL)
    return NULL;
    
  sprintf (cmd, "%s %s %s%s%s", preprocessor, preprocargs,
           fnquotes, filename, fnquotes);
  return cmd;
}

static FILE *
find_default_preprocessor(char *cmd, const char *preprocargs, const char *filename)
{
  char *dash = NULL, *slash = NULL, *cp;
  FILE *pipe = NULL;

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
      pipe = look_for_default (cmd, program_name, dash - program_name + 1,
                               preprocargs, filename);
    }

  if (slash && !pipe)
    {
      pipe = look_for_default (cmd, program_name, slash - program_name + 1,
                               preprocargs, filename);
    }

  if (!pipe)
    {
      pipe = look_for_default (cmd, "", 0, preprocargs, filename);
    }

  return pipe;
}

static int
is_path_separator(char c)
{
#if defined (__DJGPP__) || defined (__CYGWIN__) || defined(_WIN32)
  return (c == ':' || c == '\\' || c == '/');
#else
  return (c == '/');
#endif
}

/* Close the input stream if it is open.  */

static void
close_input_stream(void)
{
    if (istream_type == ISTREAM_FILE)
    {
        if (cpp_pipe != NULL)
        {
            fclose(cpp_pipe);
        }

        if (cpp_temp_file != NULL)
        {
            int errno_save = errno;
            unlink(cpp_temp_file);
            errno = errno_save;
            free(cpp_temp_file);
        }
    }
    else
    {
        if (cpp_pipe != NULL)
        {
            int err = pclose(cpp_pipe);
            if (err != 0 || errno == ECHILD)
            {
                cpp_pipe = NULL;
                cpp_temp_file = NULL;
                fatal(_("preprocessing failed."));
            }
        }
    }

    cpp_pipe = NULL;
    cpp_temp_file = NULL;
}

/* Report an error while reading an rc file.  */

void
yyerror (const char *msg)
{
  if (msg == NULL) {
    msg = "Unknown error";
  }
  fatal ("%s:%d: %s", rc_filename ? rc_filename : "unknown", rc_lineno, msg);
}

/* Issue a warning while reading an rc file.  */

void
rcparse_warning(const char *msg)
{
  if (msg == NULL) {
    msg = "Unknown warning";
  }
  if (rc_filename == NULL) {
    rc_filename = "unknown";
  }
  fprintf(stderr, "%s:%d: %s\n", rc_filename, rc_lineno, msg);
}

/* Die if we get an unexpected end of file.  */

static void
unexpected_eof (const char *msg)
{
  if (msg == NULL) {
    fatal (_("unexpected EOF"));
  } else {
    fatal (_("%s: unexpected EOF"), msg);
  }
}

/* Read a 16 bit word from a file.  The data is assumed to be little
   endian.  */

static int
get_word(FILE *e, const char *msg)
{
    int b1, b2;
    
    if (e == NULL || msg == NULL) {
        return -1;
    }
    
    b1 = getc(e);
    if (b1 == EOF) {
        unexpected_eof(msg);
        return -1;
    }
    
    b2 = getc(e);
    if (b2 == EOF) {
        unexpected_eof(msg);
        return -1;
    }
    
    return ((b2 & 0xff) << 8) | (b1 & 0xff);
}

/* Read a 32 bit word from a file.  The data is assumed to be little
   endian.  */

static unsigned long
get_long(FILE *e, const char *msg)
{
    unsigned char bytes[4];
    
    if (fread(bytes, 1, 4, e) != 4) {
        unexpected_eof(msg);
    }
    
    return ((unsigned long)bytes[3] << 24) |
           ((unsigned long)bytes[2] << 16) |
           ((unsigned long)bytes[1] << 8) |
           (unsigned long)bytes[0];
}

/* Read data from a file.  This is a wrapper to do error checking.  */

static void
get_data (FILE *e, bfd_byte *p, rc_uint_type c, const char *msg)
{
  rc_uint_type got;

  if (!e || !p || !msg) {
    fatal (_("Invalid parameters to get_data"));
  }

  got = (rc_uint_type) fread (p, 1, c, e);
  if (got == c)
    return;

  fatal (_("%s: read of %lu returned %lu"),
	 msg, (unsigned long) c, (unsigned long) got);
}

static rc_uint_type
target_get_16 (const void *p, size_t len)
{
  if (p == NULL)
    fatal (_("null pointer"));
  if (len < 2)
    fatal (_("not enough data"));
  return windres_get_16 (&wrtarget, p);
}

static rc_uint_type
target_get_32 (const void *p, size_t len)
{
  if (p == NULL)
    fatal (_("null pointer"));
  if (len < 4)
    fatal (_("not enough data"));
  return windres_get_32 (&wrtarget, p);
}

/* Define an accelerator resource.  */

void
define_accelerator (rc_res_id id, const rc_res_res_info *resinfo,
		    rc_accelerator *data)
{
  rc_res_resource *r;

  if (resinfo == NULL || data == NULL) {
    return;
  }

  r = define_standard_resource (&resources, RT_ACCELERATOR, id,
				resinfo->language, 0);
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
define_bitmap(rc_res_id id, const rc_res_res_info *resinfo,
              const char *filename)
{
    FILE *e;
    char *real_filename;
    struct stat s;
    bfd_byte *data = NULL;
    rc_uint_type i;
    rc_res_resource *r;
    size_t data_size;

    if (!filename || !resinfo) {
        fatal("Invalid parameters to define_bitmap");
    }

    e = open_file_search(filename, FOPEN_RB, "bitmap file", &real_filename);
    if (!e) {
        fatal("Failed to open bitmap file");
    }

    if (stat(real_filename, &s) < 0) {
        fatal(_("stat failed on bitmap file `%s': %s"), real_filename,
              strerror(errno));
    }

    if (s.st_size < BITMAP_SKIP) {
        fclose(e);
        free(real_filename);
        fatal("Bitmap file too small");
    }

    data_size = s.st_size - BITMAP_SKIP;
    data = (bfd_byte *) res_alloc(data_size);
    if (!data) {
        fclose(e);
        free(real_filename);
        fatal("Memory allocation failed");
    }

    if (fseek(e, BITMAP_SKIP, SEEK_SET) != 0) {
        fclose(e);
        free(real_filename);
        fatal("Failed to skip bitmap header");
    }

    get_data(e, data, data_size, real_filename);

    fclose(e);
    free(real_filename);

    r = define_standard_resource(&resources, RT_BITMAP, id,
                                resinfo->language, 0);
    if (!r) {
        fatal("Failed to define standard resource");
    }

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
  FILE *e;
  char *real_filename;
  int type, count, i;
  struct icondir *icondirs;
  int first_cursor;
  rc_res_resource *r;
  rc_group_cursor *first, **pp;

  e = open_file_search (filename, FOPEN_RB, "cursor file", &real_filename);
  if (!e)
    return;

  get_word (e, real_filename);
  type = get_word (e, real_filename);
  count = get_word (e, real_filename);
  if (type != 2)
    {
      fclose (e);
      free (real_filename);
      fatal (_("cursor file `%s' does not contain cursor data"), real_filename);
    }

  if (count <= 0)
    {
      fclose (e);
      free (real_filename);
      return;
    }

  icondirs = (struct icondir *) xmalloc (count * sizeof (*icondirs));

  for (i = 0; i < count; i++)
    {
      icondirs[i].width = getc (e);
      icondirs[i].height = getc (e);
      icondirs[i].colorcount = getc (e);
      getc (e);
      icondirs[i].u.cursor.xhotspot = get_word (e, real_filename);
      icondirs[i].u.cursor.yhotspot = get_word (e, real_filename);
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

  first = NULL;
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
      pp = &(*pp)->next;
    }

  free (icondirs);

  r = define_standard_resource (&resources, RT_GROUP_CURSOR, id,
				resinfo->language, 0);
  r->type = RES_TYPE_GROUP_CURSOR;
  r->u.group_cursor = first;
  r->res_info = *resinfo;
}

/* Define a dialog resource.  */

void
define_dialog (rc_res_id id, const rc_res_res_info *resinfo,
	       const rc_dialog *dialog)
{
  rc_dialog *copy;
  rc_res_resource *r;

  if (!resinfo || !dialog) {
    return;
  }

  copy = (rc_dialog *) res_alloc (sizeof (*copy));
  if (!copy) {
    return;
  }
  *copy = *dialog;

  r = define_standard_resource (&resources, RT_DIALOG, id,
				resinfo->language, 0);
  if (!r) {
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
  rc_dialog_control *n;

  n = (rc_dialog_control *) res_alloc (sizeof (rc_dialog_control));
  if (n == NULL)
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
  
  if (help != 0 && ex == NULL)
    rcparse_warning (_("help ID requires DIALOGEX"));
  if (data != NULL && ex == NULL)
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
  long device_offset;
  long face_offset;
  long fontdatalength;
  bfd_byte *fontdata;
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

  device_offset = (data[47] << 24) | (data[46] << 16) | (data[45] << 8) | data[44];
  if (device_offset > 0 && device_offset < s.st_size)
    device = (char *) data + device_offset;
  else
    device = "";

  face_offset = (data[51] << 24) | (data[50] << 16) | (data[49] << 8) | data[48];
  if (face_offset > 0 && face_offset < s.st_size)
    face = (char *) data + face_offset;
  else
    face = "";

  ++fonts;

  fontdatalength = 58 + strlen (device) + strlen (face);
  fontdata = (bfd_byte *) res_alloc (fontdatalength);
  memcpy (fontdata, data, 56);
  strcpy ((char *) fontdata + 56, device);
  strcpy ((char *) fontdata + 57 + strlen (device), face);

  fd = (rc_fontdir *) res_alloc (sizeof (rc_fontdir));
  fd->next = NULL;
  fd->index = fonts;
  fd->length = fontdatalength;
  fd->data = fontdata;

  for (pp = &fontdirs; *pp != NULL; pp = &(*pp)->next)
    ;
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

  if (!resinfo || !data) {
    return;
  }

  r = define_standard_resource (&resources, RT_FONT, id,
				resinfo->language, 0);
  if (!r) {
    return;
  }

  pb_data = rcdata_render_as_buffer (data, &len_data);
  if (!pb_data) {
    return;
  }

  r->type = RES_TYPE_FONT;
  r->u.data.length = len_data;
  r->u.data.data = pb_data;
  r->res_info = *resinfo;
}

/* Define the fontdirs resource.  This is called after the entire rc
   file has been parsed, if any font resources were seen.  */

static void
define_fontdirs (void)
{
  rc_res_resource *r;
  rc_res_id id;

  memset(&id, 0, sizeof(id));
  id.named = 0;
  id.u.id = 1;

  r = define_standard_resource (&resources, RT_FONTDIR, id, 0x409, 0);
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
  bfd_byte *ret = NULL, *pret;
  rc_uint_type len = 0;

  if (data == NULL) {
    if (plen)
      *plen = 0;
    return NULL;
  }

  for (d = data; d != NULL; d = d->next)
    len += rcdata_copy (d, NULL);

  if (len == 0) {
    if (plen)
      *plen = 0;
    return NULL;
  }

  ret = (bfd_byte *) res_alloc (len);
  if (ret == NULL) {
    if (plen)
      *plen = 0;
    return NULL;
  }

  pret = ret;
  for (d = data; d != NULL; d = d->next)
    pret += rcdata_copy (d, pret);

  if (plen)
    *plen = len;
  return ret;
}

static void
define_fontdir_rcdata (rc_res_id id, const rc_res_res_info *resinfo,
                      rc_rcdata_item *data)
{
  rc_res_resource *r;
  rc_fontdir *fd_first = NULL;
  rc_fontdir *fd_cur = NULL;
  rc_uint_type len_data;
  bfd_byte *pb_data;
  rc_uint_type c;

  r = define_standard_resource (&resources, RT_FONTDIR, id, 0x409, 0);

  pb_data = rcdata_render_as_buffer (data, &len_data);

  if (pb_data && len_data >= 2)
    {
      rc_uint_type off = 2;
      c = target_get_16 (pb_data, len_data);
      
      while (c > 0 && off < len_data)
        {
          size_t device_name_len;
          size_t face_name_len;
          rc_uint_type safe_pos = off;
          const struct bin_fontdir_item *bfi;
          rc_fontdir *fd;

          if (off + sizeof(struct bin_fontdir_item) > len_data)
            break;

          bfi = (const struct bin_fontdir_item *) (pb_data + off);
          fd = (rc_fontdir *) res_alloc (sizeof (rc_fontdir));
          if (!fd)
            break;

          fd->index = target_get_16 (bfi->index, len_data - off);
          fd->data = pb_data + off;
          off += 56;

          if (off >= len_data)
            {
              res_free (fd);
              break;
            }

          device_name_len = strnlen ((char *) bfi->device_name, len_data - off);
          if (device_name_len == len_data - off)
            {
              res_free (fd);
              break;
            }
          off += (rc_uint_type) device_name_len + 1;

          if (off >= len_data)
            {
              res_free (fd);
              break;
            }

          face_name_len = strnlen ((char *) bfi->device_name + device_name_len + 1, len_data - off);
          if (face_name_len == len_data - off)
            {
              res_free (fd);
              break;
            }
          off += (rc_uint_type) face_name_len + 1;

          fd->length = (off - safe_pos);
          fd->next = NULL;
          
          if (fd_first == NULL)
            fd_first = fd;
          else
            fd_cur->next = fd;
          fd_cur = fd;
          
          c--;
        }
    }
  
  r->type = RES_TYPE_FONTDIR;
  r->u.fontdir = fd_first;
  r->res_info = *resinfo;
}

static void define_messagetable_rcdata (rc_res_id id, const rc_res_res_info *resinfo,
					rc_rcdata_item *data)
{
  rc_res_resource *r;
  rc_uint_type len_data;
  bfd_byte *pb_data;

  if (!resinfo || !data) {
    return;
  }

  r = define_standard_resource (&resources, RT_MESSAGETABLE, id, resinfo->language, 0);
  if (!r) {
    return;
  }

  pb_data = rcdata_render_as_buffer (data, &len_data);
  if (!pb_data && len_data > 0) {
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
  struct icondir *icondirs;
  int first_icon;
  rc_res_resource *r;
  rc_group_icon *first, **pp;

  e = open_file_search (filename, FOPEN_RB, "icon file", &real_filename);
  if (!e)
    return;

  get_word (e, real_filename);
  type = get_word (e, real_filename);
  count = get_word (e, real_filename);
  
  if (type != 1)
    {
      fclose (e);
      free (real_filename);
      fatal (_("icon file `%s' does not contain icon data"), real_filename);
    }

  if (count <= 0)
    {
      fclose (e);
      free (real_filename);
      return;
    }

  icondirs = (struct icondir *) xmalloc (count * sizeof *icondirs);

  for (i = 0; i < count; i++)
    {
      icondirs[i].width = getc (e);
      icondirs[i].height = getc (e);
      icondirs[i].colorcount = getc (e);
      getc (e);
      icondirs[i].u.icon.planes = get_word (e, real_filename);
      icondirs[i].u.icon.bits = get_word (e, real_filename);
      icondirs[i].bytes = get_long (e, real_filename);
      icondirs[i].offset = get_long (e, real_filename);

      if (feof (e))
	{
	  fclose (e);
	  free (real_filename);
	  free (icondirs);
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
	  fclose (e);
	  free (real_filename);
	  free (icondirs);
	  fatal (_("%s: fseek to %lu failed: %s"), real_filename,
		 icondirs[i].offset, strerror (errno));
	}

      if (icondirs[i].bytes == 0)
	continue;

      data = (bfd_byte *) res_alloc (icondirs[i].bytes);
      if (!data)
	{
	  fclose (e);
	  free (real_filename);
	  free (icondirs);
	  return;
	}

      get_data (e, data, icondirs[i].bytes, real_filename);

      ++icons;

      name.named = 0;
      name.u.id = icons;

      r = define_standard_resource (&resources, RT_ICON, name,
				    resinfo->language, 0);
      if (r)
	{
	  r->type = RES_TYPE_ICON;
	  r->u.data.length = icondirs[i].bytes;
	  r->u.data.data = data;
	  r->res_info = *resinfo;
	}
    }

  fclose (e);
  free (real_filename);

  first = NULL;
  pp = &first;
  for (i = 0; i < count; i++)
    {
      rc_group_icon *cg;

      cg = (rc_group_icon *) res_alloc (sizeof (rc_group_icon));
      if (!cg)
	{
	  free (icondirs);
	  return;
	}
      
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
  if (r)
    {
      r->type = RES_TYPE_GROUP_ICON;
      r->u.group_icon = first;
      r->res_info = *resinfo;
    }
}

static void
define_group_icon_rcdata (rc_res_id id, const rc_res_res_info *resinfo,
			  rc_rcdata_item *data)
{
  rc_res_resource *r;
  rc_group_icon *cg, *first, *cur;
  rc_uint_type len_data;
  bfd_byte *pb_data;
  int i;
  unsigned short type, count;
  const rc_uint_type ICON_HEADER_SIZE = 6;
  const rc_uint_type ICON_ENTRY_SIZE = 14;
  const unsigned short EXPECTED_ICON_TYPE = 1;

  pb_data = rcdata_render_as_buffer (data, &len_data);
  if (pb_data == NULL || len_data < ICON_HEADER_SIZE)
    fatal ("invalid group icon data");

  first = NULL;
  cur = NULL;

  type = target_get_16 (pb_data + 2, len_data - 2);
  if (type != EXPECTED_ICON_TYPE)
    fatal (_("unexpected group icon type %d"), type);
  
  count = target_get_16 (pb_data + 4, len_data - 4);
  len_data -= ICON_HEADER_SIZE;
  pb_data += ICON_HEADER_SIZE;

  if (len_data < (rc_uint_type)(count * ICON_ENTRY_SIZE))
    fatal ("too small group icon rcdata");

  for (i = 0; i < count; i++)
    {
      cg = (rc_group_icon *) res_alloc (sizeof (rc_group_icon));
      if (cg == NULL)
        fatal ("memory allocation failed");
        
      cg->next = NULL;
      cg->width = pb_data[0];
      cg->height = pb_data[1];
      cg->colors = pb_data[2];
      cg->planes = target_get_16 (pb_data + 4, len_data - 4);
      cg->bits = target_get_16 (pb_data + 6, len_data - 6);
      cg->bytes = target_get_32 (pb_data + 8, len_data - 8);
      cg->index = target_get_16 (pb_data + 12, len_data - 12);
      
      if (first == NULL)
        first = cg;
      else
        cur->next = cg;
      cur = cg;
      
      pb_data += ICON_ENTRY_SIZE;
      len_data -= ICON_ENTRY_SIZE;
    }

  r = define_standard_resource (&resources, RT_GROUP_ICON, id,
				resinfo->language, 0);
  if (r == NULL)
    fatal ("failed to define standard resource");
    
  r->type = RES_TYPE_GROUP_ICON;
  r->u.group_icon = first;
  r->res_info = *resinfo;
}

static void
define_group_cursor_rcdata (rc_res_id id, const rc_res_res_info *resinfo,
			    rc_rcdata_item *data)
{
  rc_res_resource *r;
  rc_group_cursor *first, *cur;
  rc_uint_type len_data;
  bfd_byte *pb_data;
  int c, i;
  unsigned short type;

  pb_data = rcdata_render_as_buffer (data, &len_data);
  first = cur = NULL;

  if (len_data < 6)
    return;

  type = target_get_16 (pb_data + 2, len_data - 2);
  if (type != 2)
    fatal (_("unexpected group cursor type %d"), type);
  
  c = target_get_16 (pb_data + 4, len_data - 4);
  len_data -= 6;
  pb_data += 6;

  for (i = 0; i < c; i++)
    {
      rc_group_cursor *cg;
      
      if (len_data < 14)
	fatal ("too small group icon rcdata");
      
      cg = (rc_group_cursor *) res_alloc (sizeof (rc_group_cursor));
      if (!cg)
        fatal ("memory allocation failed");
      
      cg->next = NULL;
      cg->width = target_get_16 (pb_data, len_data);
      cg->height = target_get_16 (pb_data + 2, len_data - 2);
      cg->planes = target_get_16 (pb_data + 4, len_data - 4);
      cg->bits =  target_get_16 (pb_data + 6, len_data - 6);
      cg->bytes = target_get_32 (pb_data + 8, len_data - 8);
      cg->index = target_get_16 (pb_data + 12, len_data - 12);
      
      if (first == NULL)
        first = cg;
      else
        cur->next = cg;
      
      cur = cg;
      pb_data += 14;
      len_data -= 14;
    }

  r = define_standard_resource (&resources, RT_GROUP_CURSOR, id,
				resinfo->language, 0);
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

  if (!resinfo || !data) {
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
  c->data = (const bfd_byte *) (pb_data + BIN_CURSOR_SIZE);

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

  if (!resinfo || !data)
    return;

  pb_data = rcdata_render_as_buffer (data, &len_data);
  if (!pb_data)
    return;

  r = define_standard_resource (&resources, RT_BITMAP, id, resinfo->language, 0);
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
  rc_res_resource *r;
  rc_uint_type len_data;
  bfd_byte *pb_data;

  if (!resinfo || !data) {
    return;
  }

  pb_data = rcdata_render_as_buffer (data, &len_data);
  if (!pb_data) {
    return;
  }

  r = define_standard_resource (&resources, RT_ICON, id, resinfo->language, 0);
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

void
define_menu (rc_res_id id, const rc_res_res_info *resinfo,
	     rc_menuitem *menuitems)
{
  rc_menu *m;
  rc_res_resource *r;

  if (!resinfo) {
    return;
  }

  m = (rc_menu *) res_alloc (sizeof (rc_menu));
  if (!m) {
    return;
  }
  
  m->items = menuitems;
  m->help = 0;

  r = define_standard_resource (&resources, RT_MENU, id, resinfo->language, 0);
  if (!r) {
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
  rc_menuitem *mi;

  mi = (rc_menuitem *) res_alloc (sizeof (rc_menuitem));
  if (mi == NULL)
    return NULL;
  
  mi->next = NULL;
  mi->type = type;
  mi->state = state;
  mi->id = menuid;
  mi->text = text ? unichar_dup (text) : NULL;
  mi->help = help;
  mi->popup = menuitems;
  
  return mi;
}

/* Define a messagetable resource.  */

void
define_messagetable (rc_res_id id, const rc_res_res_info *resinfo,
		     const char *filename)
{
  FILE *e = NULL;
  char *real_filename = NULL;
  struct stat s;
  bfd_byte *data = NULL;
  rc_res_resource *r;

  if (!filename || !resinfo) {
    fatal (_("invalid arguments to define_messagetable"));
    return;
  }

  e = open_file_search (filename, FOPEN_RB, "messagetable file",
			&real_filename);
  if (!e) {
    fatal (_("failed to open messagetable file `%s'"), filename);
    return;
  }

  if (!real_filename) {
    fclose (e);
    fatal (_("failed to get real filename for `%s'"), filename);
    return;
  }

  if (stat (real_filename, &s) < 0) {
    fclose (e);
    free (real_filename);
    fatal (_("stat failed on messagetable file `%s': %s"), real_filename,
	   strerror (errno));
    return;
  }

  if (s.st_size <= 0) {
    fclose (e);
    free (real_filename);
    fatal (_("invalid file size for messagetable file `%s'"), real_filename);
    return;
  }

  data = (bfd_byte *) res_alloc (s.st_size);
  if (!data) {
    fclose (e);
    free (real_filename);
    fatal (_("memory allocation failed for messagetable file `%s'"), real_filename);
    return;
  }

  get_data (e, data, s.st_size, real_filename);

  fclose (e);
  free (real_filename);

  r = define_standard_resource (&resources, RT_MESSAGETABLE, id,
				resinfo->language, 0);
  if (!r) {
    fatal (_("failed to define standard resource"));
    return;
  }

  r->type = RES_TYPE_MESSAGETABLE;
  r->u.data.length = s.st_size;
  r->u.data.data = data;
  r->res_info = *resinfo;
}

/* Define an rcdata resource.  */

void
define_rcdata (rc_res_id id, const rc_res_res_info *resinfo,
	       rc_rcdata_item *data)
{
  rc_res_resource *r;

  if (resinfo == NULL)
    return;

  r = define_standard_resource (&resources, RT_RCDATA, id,
				resinfo->language, 0);
  if (r == NULL)
    return;
    
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

  if (!string || len == 0)
    return NULL;

  ri = (rc_rcdata_item *) res_alloc (sizeof (rc_rcdata_item));
  if (!ri)
    return NULL;

  s = (char *) res_alloc (len);
  if (!s)
    return NULL;

  ri->next = NULL;
  ri->type = RCDATA_STRING;
  ri->u.string.length = len;
  memcpy (s, string, len);
  ri->u.string.s = s;

  return ri;
}

/* Create an rcdata item holding a unicode string.  */

rc_rcdata_item *
define_rcdata_unistring (const unichar *string, rc_uint_type len)
{
  rc_rcdata_item *ri;
  unichar *s;
  size_t byte_size;

  if (string == NULL || len == 0) {
    return NULL;
  }

  if (len > SIZE_MAX / sizeof(unichar)) {
    return NULL;
  }

  byte_size = len * sizeof(unichar);

  ri = (rc_rcdata_item *) res_alloc (sizeof (rc_rcdata_item));
  if (ri == NULL) {
    return NULL;
  }

  s = (unichar *) res_alloc (byte_size);
  if (s == NULL) {
    return NULL;
  }

  ri->next = NULL;
  ri->type = RCDATA_WSTRING;
  ri->u.wstring.length = len;
  memcpy (s, string, byte_size);
  ri->u.wstring.w = s;

  return ri;
}

/* Create an rcdata item holding a number.  */

rc_rcdata_item *
define_rcdata_number (rc_uint_type val, int dword)
{
  rc_rcdata_item *ri = (rc_rcdata_item *) res_alloc (sizeof (rc_rcdata_item));
  if (!ri)
    return NULL;
  
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
  unichar *h;
  rc_res_id id;
  rc_res_resource *r;
  int string_index;

  if (!resinfo || !string || len < 0) {
    return;
  }

  id.named = 0;
  id.u.id = (stringid >> 4) + 1;
  r = define_standard_resource (&resources, RT_STRING, id,
				resinfo->language, 1);

  if (!r) {
    return;
  }

  if (r->type == RES_TYPE_UNINITIALIZED)
    {
      int i;

      r->type = RES_TYPE_STRINGTABLE;
      r->u.stringtable = ((rc_stringtable *)
			  res_alloc (sizeof (rc_stringtable)));
      if (!r->u.stringtable) {
        return;
      }

      for (i = 0; i < 16; i++)
	{
	  r->u.stringtable->strings[i].length = 0;
	  r->u.stringtable->strings[i].string = NULL;
	}

      r->res_info = *resinfo;
    }

  h = (unichar *) res_alloc ((len + 1) * sizeof (unichar));
  if (!h) {
    return;
  }

  if (len > 0) {
    memcpy (h, string, len * sizeof (unichar));
  }
  h[len] = 0;

  string_index = stringid & 0xf;
  r->u.stringtable->strings[string_index].length = (rc_uint_type) len;
  r->u.stringtable->strings[string_index].string = h;
}

void
define_toolbar (rc_res_id id, rc_res_res_info *resinfo, rc_uint_type width, rc_uint_type height,
		rc_toolbar_item *items)
{
  rc_toolbar *t;
  rc_res_resource *r;
  rc_toolbar_item *current_item;
  rc_uint_type item_count = 0;

  if (resinfo == NULL)
    return;

  t = (rc_toolbar *) res_alloc (sizeof (rc_toolbar));
  if (t == NULL)
    return;

  t->button_width = width;
  t->button_height = height;
  t->items = items;

  current_item = items;
  while (current_item != NULL)
  {
    item_count++;
    current_item = current_item->next;
  }
  t->nitems = item_count;

  r = define_standard_resource (&resources, RT_TOOLBAR, id, resinfo->language, 0);
  if (r == NULL)
    return;

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
  r->u.userdata = res_alloc (sizeof (rc_rcdata_item));
  if (!r->u.userdata)
    return;

  r->u.userdata->next = NULL;
  r->u.userdata->type = RCDATA_BUFFER;
  pb_data = rcdata_render_as_buffer (data, &len_data);
  if (!pb_data)
    {
      r->u.userdata->u.buffer.length = 0;
      r->u.userdata->u.buffer.data = NULL;
    }
  else
    {
      r->u.userdata->u.buffer.length = len_data;
      r->u.userdata->u.buffer.data = pb_data;
    }
  r->res_info = *resinfo;
}

void
define_rcdata_file (rc_res_id id, const rc_res_res_info *resinfo,
		    const char *filename)
{
  rc_rcdata_item *ri;
  FILE *e;
  char *real_filename;
  struct stat s;
  bfd_byte *data;

  if (!filename) {
    fatal (_("filename cannot be NULL"));
  }

  e = open_file_search (filename, FOPEN_RB, "file", &real_filename);
  if (!e) {
    fatal (_("failed to open file `%s'"), filename);
  }

  if (stat (real_filename, &s) < 0) {
    fclose (e);
    free (real_filename);
    fatal (_("stat failed on file `%s': %s"), real_filename,
	   strerror (errno));
  }

  if (s.st_size < 0) {
    fclose (e);
    free (real_filename);
    fatal (_("invalid file size for `%s'"), real_filename);
  }

  data = (bfd_byte *) res_alloc (s.st_size);
  if (!data) {
    fclose (e);
    free (real_filename);
    fatal (_("memory allocation failed for file `%s'"), real_filename);
  }

  get_data (e, data, s.st_size, real_filename);

  fclose (e);
  free (real_filename);

  ri = (rc_rcdata_item *) res_alloc (sizeof (rc_rcdata_item));
  if (!ri) {
    fatal (_("memory allocation failed for rcdata item"));
  }
  
  ri->next = NULL;
  ri->type = RCDATA_BUFFER;
  ri->u.buffer.length = s.st_size;
  ri->u.buffer.data = data;

  define_rcdata (id, resinfo, ri);
}

/* Define a user data resource where the data is in a file.  */

void
define_user_file (rc_res_id id, rc_res_id type,
		  const rc_res_res_info *resinfo, const char *filename)
{
  FILE *file_handle;
  char *real_filename;
  struct stat file_stats;
  bfd_byte *file_data;
  rc_res_id resource_ids[3];
  rc_res_resource *resource;

  if (!filename || !resinfo) {
    fatal (_("invalid parameters: filename or resinfo is NULL"));
  }

  file_handle = open_file_search (filename, FOPEN_RB, "file", &real_filename);
  if (!file_handle) {
    fatal (_("failed to open file `%s'"), filename);
  }

  if (stat (real_filename, &file_stats) < 0) {
    fclose (file_handle);
    free (real_filename);
    fatal (_("stat failed on file `%s': %s"), real_filename, strerror (errno));
  }

  if (file_stats.st_size < 0 || file_stats.st_size > SIZE_MAX) {
    fclose (file_handle);
    free (real_filename);
    fatal (_("invalid file size for `%s'"), real_filename);
  }

  file_data = (bfd_byte *) res_alloc (file_stats.st_size);
  if (!file_data) {
    fclose (file_handle);
    free (real_filename);
    fatal (_("memory allocation failed for file `%s'"), real_filename);
  }

  get_data (file_handle, file_data, file_stats.st_size, real_filename);

  fclose (file_handle);
  free (real_filename);

  resource_ids[0] = type;
  resource_ids[1] = id;
  resource_ids[2].named = 0;
  resource_ids[2].u.id = resinfo->language;

  resource = define_resource (&resources, 3, resource_ids, 0);
  if (!resource) {
    fatal (_("failed to define resource"));
  }

  resource->type = RES_TYPE_USERDATA;
  resource->u.userdata = (rc_rcdata_item *) res_alloc (sizeof (rc_rcdata_item));
  if (!resource->u.userdata) {
    fatal (_("memory allocation failed for userdata"));
  }

  resource->u.userdata->next = NULL;
  resource->u.userdata->type = RCDATA_BUFFER;
  resource->u.userdata->u.buffer.length = file_stats.st_size;
  resource->u.userdata->u.buffer.data = file_data;
  resource->res_info = *resinfo;
}

/* Define a versioninfo resource.  */

void
define_versioninfo (rc_res_id id, rc_uint_type language,
		    rc_fixed_versioninfo *fixedverinfo,
		    rc_ver_info *verinfo)
{
  rc_res_resource *r;
  rc_versioninfo *versioninfo;

  if (!fixedverinfo || !verinfo) {
    return;
  }

  r = define_standard_resource (&resources, RT_VERSION, id, language, 0);
  if (!r) {
    return;
  }

  versioninfo = (rc_versioninfo *) res_alloc (sizeof (rc_versioninfo));
  if (!versioninfo) {
    return;
  }

  r->type = RES_TYPE_VERSIONINFO;
  r->u.versioninfo = versioninfo;
  r->u.versioninfo->fixed = fixedverinfo;
  r->u.versioninfo->var = verinfo;
  r->res_info.language = language;
}

/* Add string version info to a list of version information.  */

rc_ver_info *
append_ver_stringfileinfo (rc_ver_info *verinfo,
			   rc_ver_stringtable *stringtables)
{
  rc_ver_info *vi, **pp;

  if (!stringtables) {
    return verinfo;
  }

  vi = (rc_ver_info *) res_alloc (sizeof (rc_ver_info));
  if (!vi) {
    return verinfo;
  }
  
  vi->next = NULL;
  vi->type = VERINFO_STRING;
  vi->u.string.stringtables = stringtables;

  if (!verinfo) {
    return vi;
  }

  for (pp = &verinfo; *pp != NULL; pp = &(*pp)->next)
    ;
  *pp = vi;

  return verinfo;
}

rc_ver_stringtable *
append_ver_stringtable (rc_ver_stringtable *stringtable,
			const char *language,
			rc_ver_stringinfo *strings)
{
  rc_ver_stringtable *vst, **pp;

  if (!language || !strings)
    return stringtable;

  vst = (rc_ver_stringtable *) res_alloc (sizeof (rc_ver_stringtable));
  if (!vst)
    return stringtable;

  vst->next = NULL;
  if (unicode_from_ascii ((rc_uint_type *) NULL, &vst->language, language) != 0) {
    res_free (vst);
    return stringtable;
  }
  vst->strings = strings;

  for (pp = &stringtable; *pp != NULL; pp = &(*pp)->next)
    ;
  *pp = vst;

  return stringtable;
}

/* Add variable version info to a list of version information.  */

rc_ver_info *
append_ver_varfileinfo (rc_ver_info *verinfo, const unichar *key,
			rc_ver_varinfo *var)
{
  rc_ver_info *vi, **pp;

  if (!key || !var) {
    return verinfo;
  }

  vi = (rc_ver_info *) res_alloc (sizeof (rc_ver_info));
  if (!vi) {
    return verinfo;
  }

  vi->next = NULL;
  vi->type = VERINFO_VAR;
  vi->u.var.key = unichar_dup (key);
  if (!vi->u.var.key) {
    res_free (vi);
    return verinfo;
  }
  vi->u.var.var = var;

  if (!verinfo) {
    return vi;
  }

  for (pp = &verinfo; *pp != NULL; pp = &(*pp)->next)
    ;
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

  if (!key || !value) {
    return strings;
  }

  vs = (rc_ver_stringinfo *) res_alloc (sizeof (rc_ver_stringinfo));
  if (!vs) {
    return strings;
  }

  vs->next = NULL;
  vs->key = unichar_dup (key);
  vs->value = unichar_dup (value);

  if (!vs->key || !vs->value) {
    return strings;
  }

  for (pp = &strings; *pp != NULL; pp = &(*pp)->next) {
    ;
  }
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

static void
indent(FILE *e, int c)
{
  if (e == NULL || c < 0)
    return;
    
  for (int i = 0; i < c; i++) {
    if (putc(' ', e) == EOF)
      break;
  }
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

  if (res_dir == NULL)
    return false;

  if (filename == NULL)
    {
      e = stdout;
    }
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

  if (filename != NULL && e != NULL)
    {
      if (fclose (e) != 0)
        {
          non_fatal (_("can't close `%s': %s"), filename, strerror (errno));
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

  if (!e || !rd || !language) {
    return;
  }

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
      if (level == 1)
        {
          type = &re->id;
        }
      else if (level == 2)
        {
          name = &re->id;
        }
      else if (level == 3)
        {
          if (!re->id.named
              && re->id.u.id != (unsigned long) (unsigned int) *language
              && (re->id.u.id & 0xffff) == re->id.u.id)
            {
              wr_print (e, "LANGUAGE %u, %u\n",
                       re->id.u.id & ((1 << SUBLANG_SHIFT) - 1),
                       (re->id.u.id >> SUBLANG_SHIFT) & 0xff);
              *language = re->id.u.id;
            }
        }

      if (re->subdir)
        {
          write_rc_subdir (e, re, type, name, language, level);
        }
      else
        {
          if (level == 3)
            {
              write_rc_resource (e, type, name, re->u.res, language);
            }
          else
            {
              wr_printcomment (e, "Resource at unexpected level %d", level);
              write_rc_resource (e, type, NULL, re->u.res, language);
            }
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
    }
  else
    {
      const char *type_name = get_resource_type_name(re->id.u.id);
      if (type_name != NULL)
        fprintf (e, "%s", type_name);
      else
        res_id_print (e, re->id, 1);
    }
}

static void
write_rc_subdir (FILE *e, const rc_res_entry *re,
		 const rc_res_id *type, const rc_res_id *name,
		 rc_uint_type *language, int level)
{
  if (e == NULL || re == NULL)
    return;

  fprintf (e, "\n");

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

  write_rc_directory (e, re->u.dir, type, name, language, level + 1);
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

  if (!e || !res) {
    return;
  }

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
      if (extended_dialog (res->u.dialog))
	s = "DIALOGEX";
      else
	s = "DIALOG";
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
      if (extended_menu (res->u.menu))
	{
	  s = "MENUEX";
	  menuex = 1;
	}
      else
	{
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
      return;
    }

  if (rt != 0
      && type != NULL
      && (type->named || type->u.id != (unsigned long) rt))
    {
      wr_printcomment (e, "Unexpected resource type mismatch: ");
      res_id_print (e, *type, 1);
      fprintf (e, " != %d", rt);
    }

  if (res->coff_info.codepage != 0)
    wr_printcomment (e, "Code page: %u", res->coff_info.codepage);
  if (res->coff_info.reserved != 0)
    wr_printcomment (e, "COFF reserved value: %u", res->coff_info.reserved);

  wr_print (e, "\n");
  if (rt != RT_STRING)
    {
      if (name != NULL)
	res_id_print (e, *name, 1);
      else
	fprintf (e, "??Unknown-Name??");
      fprintf (e, " ");
    }

  if (s != NULL)
    fprintf (e, "%s", s);
  else if (type != NULL)
    {
      if (type->named == 0)
	{
	  switch (type->u.id)
	    {
	    case RT_MANIFEST:
	      fprintf (e, "%u /* RT_MANIFEST */", (unsigned int) RT_MANIFEST);
	      break;
	    case RT_ANICURSOR:
	      fprintf (e, "%u /* RT_ANICURSOR */", (unsigned int) RT_ANICURSOR);
	      break;
	    case RT_ANIICON:
	      fprintf (e, "%u /* RT_ANIICON */", (unsigned int) RT_ANIICON);
	      break;
	    case RT_RCDATA:
	      fprintf (e, "%u /* RT_RCDATA */", (unsigned int) RT_RCDATA);
	      break;
	    case RT_ICON:
	      fprintf (e, "%u /* RT_ICON */", (unsigned int) RT_ICON);
	      break;
	    case RT_CURSOR:
	      fprintf (e, "%u /* RT_CURSOR */", (unsigned int) RT_CURSOR);
	      break;
	    case RT_BITMAP:
	      fprintf (e, "%u /* RT_BITMAP */", (unsigned int) RT_BITMAP);
	      break;
	    case RT_PLUGPLAY:
	      fprintf (e, "%u /* RT_PLUGPLAY */", (unsigned int) RT_PLUGPLAY);
	      break;
	    case RT_VXD:
	      fprintf (e, "%u /* RT_VXD */", (unsigned int) RT_VXD);
	      break;
	    case RT_FONT:
	      fprintf (e, "%u /* RT_FONT */", (unsigned int) RT_FONT);
	      break;
	    case RT_FONTDIR:
	      fprintf (e, "%u /* RT_FONTDIR */", (unsigned int) RT_FONTDIR);
	      break;
	    case RT_HTML:
	      fprintf (e, "%u /* RT_HTML */", (unsigned int) RT_HTML);
	      break;
	    case RT_MESSAGETABLE:
	      fprintf (e, "%u /* RT_MESSAGETABLE */", (unsigned int) RT_MESSAGETABLE);
	      break;
	    case RT_DLGINCLUDE:
	      fprintf (e, "%u /* RT_DLGINCLUDE */", (unsigned int) RT_DLGINCLUDE);
	      break;
	    case RT_DLGINIT:
	      fprintf (e, "%u /* RT_DLGINIT */", (unsigned int) RT_DLGINIT);
	      break;
	    default:
	      res_id_print (e, *type, 0);
	      break;
	    }
	}
      else
	res_id_print (e, *type, 1);
    }
  else
    fprintf (e, "??Unknown-Type??");

  if (res->res_info.memflags != 0)
    {
      if ((res->res_info.memflags & MEMFLAG_MOVEABLE) != 0)
	fprintf (e, " MOVEABLE");
      if ((res->res_info.memflags & MEMFLAG_PURE) != 0)
	fprintf (e, " PURE");
      if ((res->res_info.memflags & MEMFLAG_PRELOAD) != 0)
	fprintf (e, " PRELOAD");
      if ((res->res_info.memflags & MEMFLAG_DISCARDABLE) != 0)
	fprintf (e, " DISCARDABLE");
    }

  if (res->type == RES_TYPE_DIALOG)
    {
      fprintf (e, " %d, %d, %d, %d",
	       (int) res->u.dialog->x, (int) res->u.dialog->y,
	       (int) res->u.dialog->width, (int) res->u.dialog->height);
      if (res->u.dialog->ex != NULL
	  && res->u.dialog->ex->help != 0)
	fprintf (e, ", %u", (unsigned int) res->u.dialog->ex->help);
    }
  else if (res->type == RES_TYPE_TOOLBAR)
    {
      fprintf (e, " %d, %d", (int) res->u.toolbar->button_width,
	       (int) res->u.toolbar->button_height);
    }

  fprintf (e, "\n");

  if ((res->res_info.language != 0 && res->res_info.language != *language)
      || res->res_info.characteristics != 0
      || res->res_info.version != 0)
    {
      int modifiers;

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
	  modifiers = 0;
	  break;
	}

      if (res->res_info.language != 0 && res->res_info.language != *language)
	fprintf (e, "%sLANGUAGE %d, %d\n",
		 modifiers ? "// " : "",
		 (int) res->res_info.language & ((1<<SUBLANG_SHIFT)-1),
		 (int) (res->res_info.language >> SUBLANG_SHIFT) & 0xff);
      if (res->res_info.characteristics != 0)
	fprintf (e, "%sCHARACTERISTICS %u\n",
		 modifiers ? "// " : "",
		 (unsigned int) res->res_info.characteristics);
      if (res->res_info.version != 0)
	fprintf (e, "%sVERSION %u\n",
		 modifiers ? "// " : "",
		 (unsigned int) res->res_info.version);
    }

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
      write_rc_menu (e, res->u.menu, menuex);
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

/* Write out accelerator information.  */

static void
write_rc_accelerators (FILE *e, const rc_accelerator *accelerators)
{
  const rc_accelerator *acc;

  if (e == NULL) {
    return;
  }

  fprintf (e, "BEGIN\n");
  for (acc = accelerators; acc != NULL; acc = acc->next)
    {
      int printable = 0;
      unsigned char key_char;

      fprintf (e, "  ");

      key_char = (unsigned char)(acc->key & 0x7f);
      if (key_char == acc->key && ISPRINT(key_char) && (acc->flags & ACC_VIRTKEY) == 0)
	{
	  fprintf (e, "\"%c\"", key_char);
	  printable = 1;
	}
      else
	{
	  fprintf (e, "%d", (int) acc->key);
	}

      fprintf (e, ", %d", (int) acc->id);

      if (printable == 0)
	{
	  if ((acc->flags & ACC_VIRTKEY) != 0)
	    fprintf (e, ", VIRTKEY");
	  else
	    fprintf (e, ", ASCII");
	}

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
  if (e == NULL || cursor == NULL) {
    return;
  }

  fprintf (e, "BEGIN\n");
  indent (e, 2);
  fprintf (e, " 0x%x, 0x%x,\t/* Hotspot x: %d, y: %d.  */\n",
	   (unsigned int) cursor->xhotspot, (unsigned int) cursor->yhotspot,
	   (int) cursor->xhotspot, (int) cursor->yhotspot);
  write_rc_datablock (e, (rc_uint_type) cursor->length, (const bfd_byte *) cursor->data,
		      0, 0, 0);
  fprintf (e, "END\n");
}

/* Write out group cursor data.  This would normally be built from the
   cursor data.  */

static void
write_rc_group_cursor (FILE *e, const rc_group_cursor *group_cursor)
{
  const rc_group_cursor *gc;
  int count = 0;
  int element_index = 1;

  if (e == NULL) {
    return;
  }

  for (gc = group_cursor; gc != NULL; gc = gc->next) {
    count++;
  }

  fprintf (e, "BEGIN\n");

  indent (e, 2);
  fprintf (e, "0, 2, %d%s\t /* Having %d items.  */\n", 
          count, (count != 0 ? "," : ""), count);
  
  indent (e, 4);
  fprintf (e, "/* width, height, planes, bits, bytes, index.  */\n");

  for (gc = group_cursor; gc != NULL; gc = gc->next, element_index++) {
    indent (e, 4);
    fprintf (e, "%d, %d, %d, %d, 0x%xL, %d%s /* Element %d. */\n",
            (int) gc->width, (int) gc->height, (int) gc->planes, (int) gc->bits,
            (unsigned int) gc->bytes, (int) gc->index, 
            (gc->next != NULL ? "," : ""), element_index);
    
    fprintf (e, "/* width: %d; height %d; planes %d; bits %d.  */\n",
            (int) gc->width, (int) gc->height, (int) gc->planes,
            (int) gc->bits);
  }
  
  fprintf (e, "END\n");
}

/* Write dialog data.  */

static void
write_rc_dialog (FILE *e, const rc_dialog *dialog)
{
  const rc_dialog_control *control;

  if (e == NULL || dialog == NULL)
    return;

  fprintf (e, "STYLE 0x%x\n", dialog->style);

  if (dialog->exstyle != 0)
    fprintf (e, "EXSTYLE 0x%x\n", (unsigned int) dialog->exstyle);

  if ((dialog->class.named && dialog->class.u.n.length > 0)
      || dialog->class.u.id != 0)
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

  if ((dialog->menu.named && dialog->menu.u.n.length > 0)
      || dialog->menu.u.id != 0)
    {
      fprintf (e, "MENU ");
      res_id_print (e, dialog->menu, 0);
      fprintf (e, "\n");
    }

  if (dialog->font != NULL)
    {
      fprintf (e, "FONT %d, ", (int) dialog->pointsize);
      unicode_print_quoted (e, dialog->font, -1);
      if (dialog->ex != NULL
	  && (dialog->ex->weight != 0
	      || dialog->ex->italic != 0
	      || dialog->ex->charset != 1))
	fprintf (e, ", %d, %d, %d",
		 (int) dialog->ex->weight,
		 (int) dialog->ex->italic,
		 (int) dialog->ex->charset);
      fprintf (e, "\n");
    }

  fprintf (e, "BEGIN\n");

  for (control = dialog->controls; control != NULL; control = control->next)
    write_rc_dialog_control (e, control);

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

  if (!e || !control) 
    return;

  fprintf (e, "  ");

  ci = get_control_info(control);
  
  if (ci == NULL || ci->name == NULL)
    fprintf (e, "CONTROL");
  else
    fprintf (e, "%s", ci->name);

  if (should_print_control_text(control, ci))
    {
      fprintf (e, " ");
      res_id_print (e, control->text, 1);
      fprintf (e, ",");
    }

  fprintf (e, " %d, ", (int) control->id);

  if (ci == NULL)
    {
      print_control_class(e, control);
      fprintf (e, ", 0x%x, ", (unsigned int) control->style);
    }

  fprintf (e, "%d, %d", (int) control->x, (int) control->y);

  if (needs_additional_params(control))
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

static const struct control_info *
get_control_info(const rc_dialog_control *control)
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

static int
should_print_control_text(const rc_dialog_control *control, const struct control_info *ci)
{
  if (!control->text.named && control->text.u.id == 0)
    return 0;

  if (!ci)
    return 1;

  return (ci->class != CTL_EDIT &&
          ci->class != CTL_COMBOBOX &&
          ci->class != CTL_LISTBOX &&
          ci->class != CTL_SCROLLBAR);
}

static void
print_control_class(FILE *e, const rc_dialog_control *control)
{
  if (control->class.named)
    fprintf (e, "\"");
  res_id_print (e, control->class, 0);
  if (control->class.named)
    fprintf (e, "\"");
}

static int
needs_additional_params(const rc_dialog_control *control)
{
  return (control->style != SS_ICON ||
          control->exstyle != 0 ||
          control->width != 0 ||
          control->height != 0 ||
          control->help != 0);
}

/* Write out font directory data.  This would normally be built from
   the font data.  */

static void
write_rc_fontdir (FILE *e, const rc_fontdir *fontdir)
{
  const rc_fontdir *fc;
  int count;

  if (e == NULL) {
    return;
  }

  for (count = 0, fc = fontdir; fc != NULL; fc = fc->next, count++)
    ;
  
  fprintf (e, "BEGIN\n");
  indent (e, 2);
  fprintf (e, "%d%s\t /* Has %d elements.  */\n", count, (count != 0 ? "," : ""), count);
  
  for (count = 1, fc = fontdir; fc != NULL; fc = fc->next, count++)
    {
      if (fc->data == NULL || fc->length < 2) {
        continue;
      }
      
      indent (e, 4);
      fprintf (e, "%d,\t/* Font no %d with index %d.  */\n",
        (int) fc->index, count, (int) fc->index);
      write_rc_datablock (e, (rc_uint_type) fc->length - 2,
        (const bfd_byte *) fc->data + 4, fc->next != NULL,
        0, 0);
    }
  fprintf (e, "END\n");
}

/* Write out group icon data.  This would normally be built from the
   icon data.  */

static void
write_rc_group_icon(FILE *e, const rc_group_icon *group_icon)
{
    if (!e || !group_icon) {
        return;
    }

    const rc_group_icon *gi;
    int count = 0;

    for (gi = group_icon; gi != NULL; gi = gi->next) {
        count++;
    }

    fprintf(e, "BEGIN\n");
    indent(e, 2);
    fprintf(e, " 0, 1, %d%s\t /* Has %d elements.  */\n", 
            count, (count != 0 ? "," : ""), count);

    indent(e, 4);
    fprintf(e, "/* \"width height colors pad\", planes, bits, bytes, index.  */\n");
    
    int element_num = 1;
    for (gi = group_icon; gi != NULL; gi = gi->next, element_num++) {
        indent(e, 4);
        fprintf(e, "\"\\%03o\\%03o\\%03o\\%03o\", %d, %d, 0x%xL, %d%s\t/* Element no %d.  */\n",
                gi->width, gi->height, gi->colors, 0, 
                (int)gi->planes, (int)gi->bits,
                (unsigned int)gi->bytes, (int)gi->index, 
                (gi->next != NULL ? "," : ""), element_num);
    }
    fprintf(e, "END\n");
}

/* Write out a menu resource.  */

static void
write_rc_menu (FILE *e, const rc_menu *menu, int menuex)
{
  if (e == NULL || menu == NULL)
    return;
    
  if (menu->help != 0)
    fprintf (e, "// Help ID: %u\n", (unsigned int) menu->help);
  write_rc_menuitems (e, menu->items, menuex, 0);
}

static void
write_rc_toolbar (FILE *e, const rc_toolbar *tb)
{
  if (e == NULL || tb == NULL)
    return;
    
  indent (e, 0);
  fprintf (e, "BEGIN\n");
  
  for (rc_toolbar_item *it = tb->items; it != NULL; it = it->next)
  {
    indent (e, 2);
    if (it->id.u.id == 0)
      fprintf (e, "SEPARATOR\n");
    else
      fprintf (e, "BUTTON %d\n", (int) it->id.u.id);
  }
  
  indent (e, 0);
  fprintf (e, "END\n");
}

/* Write out menuitems.  */

static void write_menuitem_attributes(FILE *e, const rc_menuitem *mi)
{
    if ((mi->type & MENUITEM_CHECKED) != 0)
        fprintf(e, ", CHECKED");
    if ((mi->type & MENUITEM_GRAYED) != 0)
        fprintf(e, ", GRAYED");
    if ((mi->type & MENUITEM_HELP) != 0)
        fprintf(e, ", HELP");
    if ((mi->type & MENUITEM_INACTIVE) != 0)
        fprintf(e, ", INACTIVE");
    if ((mi->type & MENUITEM_MENUBARBREAK) != 0)
        fprintf(e, ", MENUBARBREAK");
    if ((mi->type & MENUITEM_MENUBREAK) != 0)
        fprintf(e, ", MENUBREAK");
    if ((mi->type & MENUITEM_OWNERDRAW) != 0)
        fprintf(e, ", OWNERDRAW");
    if ((mi->type & MENUITEM_BITMAP) != 0)
        fprintf(e, ", BITMAP");
}

static int is_separator_item(const rc_menuitem *mi, int menuex)
{
    return !menuex && mi->popup == NULL && mi->text == NULL && 
           mi->type == 0 && mi->id == 0;
}

static void write_menuex_parameters(FILE *e, const rc_menuitem *mi)
{
    if (mi->id == 0 && mi->type == 0 && mi->state == 0 && mi->help == 0)
        return;
        
    fprintf(e, ", %d", (int)mi->id);
    if (mi->type == 0 && mi->state == 0 && mi->help == 0)
        return;
        
    fprintf(e, ", %u", (unsigned int)mi->type);
    if (mi->state == 0 && mi->help == 0)
        return;
        
    fprintf(e, ", %u", (unsigned int)mi->state);
    if (mi->help == 0)
        return;
        
    fprintf(e, ", %u", (unsigned int)mi->help);
}

static void write_menuitem_text(FILE *e, const rc_menuitem *mi)
{
    if (mi->text == NULL)
        fprintf(e, " \"\"");
    else {
        fprintf(e, " ");
        unicode_print_quoted(e, mi->text, -1);
    }
}

static void
write_rc_menuitems(FILE *e, const rc_menuitem *menuitems, int menuex, int ind)
{
    if (e == NULL || menuitems == NULL)
        return;

    indent(e, ind);
    fprintf(e, "BEGIN\n");

    for (const rc_menuitem *mi = menuitems; mi != NULL; mi = mi->next) {
        indent(e, ind + 2);

        if (mi->popup == NULL)
            fprintf(e, "MENUITEM");
        else
            fprintf(e, "POPUP");

        if (is_separator_item(mi, menuex)) {
            fprintf(e, " SEPARATOR\n");
            continue;
        }

        write_menuitem_text(e, mi);

        if (!menuex) {
            if (mi->popup == NULL)
                fprintf(e, ", %d", (int)mi->id);
            write_menuitem_attributes(e, mi);
        } else {
            write_menuex_parameters(e, mi);
        }

        fprintf(e, "\n");

        if (mi->popup != NULL)
            write_rc_menuitems(e, mi->popup, menuex, ind + 2);
    }

    indent(e, ind);
    fprintf(e, "END\n");
}

static int
test_rc_datablock_unicode (rc_uint_type length, const bfd_byte *data)
{
  rc_uint_type i;
  
  if (!data)
    return 0;
    
  if ((length & 1) != 0)
    return 0;

  for (i = 0; i + 1 < length; i += 2)
    {
      if (data[i] == 0 && data[i + 1] == 0 && (i + 2) < length)
        return 0;
      if (data[i] == 0xff && data[i + 1] == 0xff)
        return 0;
    }
  return 1;
}

static int
test_rc_datablock_text (rc_uint_type length, const bfd_byte *data)
{
  int has_nl;
  rc_uint_type non_printable_count;
  rc_uint_type i;
  rc_uint_type percentage;

  if (length <= 1 || data == NULL)
    return 0;

  has_nl = 0;
  non_printable_count = 0;
  
  for (i = 0; i < length; i++)
    {
      if (is_acceptable_text_char(data, i, length))
        {
          if (data[i] == '\n')
            has_nl++;
        }
      else
        {
          if (data[i] <= 7)
            return 0;
          non_printable_count++;
        }
    }
  
  if (length > 80 && !has_nl)
    return 0;
    
  percentage = ((non_printable_count * 10000) / length);
  if (percentage >= 150)
    return 0;
    
  return 1;
}

static int
is_acceptable_text_char(const bfd_byte *data, rc_uint_type index, rc_uint_type length)
{
  bfd_byte current_char = data[index];
  
  if (ISPRINT(current_char))
    return 1;
    
  if (current_char == '\n' || current_char == '\t')
    return 1;
    
  if (current_char == '\r' && (index + 1) < length && data[index + 1] == '\n')
    return 1;
    
  if (current_char == 0 && (index + 1) != length)
    return 1;
    
  return 0;
}

static void
write_rc_messagetable (FILE *e, rc_uint_type length, const bfd_byte *data)
{
  int has_error = 0;
  const struct bin_messagetable *mt;

  if (!e || !data) {
    return;
  }

  fprintf (e, "BEGIN\n");
  write_rc_datablock (e, length, data, 0, 0, 0);
  fprintf (e, "\n");
  wr_printcomment (e, "MC syntax dump");

  if (length < BIN_MESSAGETABLE_SIZE) {
    has_error = 1;
  } else {
    rc_uint_type m, i;

    mt = (const struct bin_messagetable *) data;
    m = target_get_32 (mt->cblocks, length);

    if (length < (BIN_MESSAGETABLE_SIZE + m * BIN_MESSAGETABLE_BLOCK_SIZE)) {
      has_error = 1;
    } else {
      for (i = 0; i < m && !has_error; i++) {
        rc_uint_type low, high, offset;
        const struct bin_messagetable_item *mti;

        low = windres_get_32 (&wrtarget, mt->items[i].lowid);
        high = windres_get_32 (&wrtarget, mt->items[i].highid);
        offset = windres_get_32 (&wrtarget, mt->items[i].offset);

        while (low <= high && !has_error) {
          rc_uint_type elen, flags;
          
          if ((offset + BIN_MESSAGETABLE_ITEM_SIZE) > length) {
            has_error = 1;
            break;
          }
          
          mti = (const struct bin_messagetable_item *) &data[offset];
          elen = windres_get_16 (&wrtarget, mti->length);
          flags = windres_get_16 (&wrtarget, mti->flags);
          
          if ((offset + elen) > length) {
            has_error = 1;
            break;
          }
          
          wr_printcomment (e, "MessageId = 0x%x", low);
          wr_printcomment (e, "");

          if ((flags & MESSAGE_RESOURCE_UNICODE) == MESSAGE_RESOURCE_UNICODE) {
            if (elen > BIN_MESSAGETABLE_ITEM_SIZE * 2) {
              unicode_print (e, (const unichar *) mti->data,
                           (elen - BIN_MESSAGETABLE_ITEM_SIZE) / 2);
            }
          } else {
            if (elen > BIN_MESSAGETABLE_ITEM_SIZE) {
              ascii_print (e, (const char *) mti->data,
                         (elen - BIN_MESSAGETABLE_ITEM_SIZE));
            }
          }

          wr_printcomment (e,"");
          ++low;
          offset += elen;
        }
      }
    }
  }

  if (has_error) {
    wr_printcomment (e, "Illegal data");
  }
  
  wr_print_flush (e);
  fprintf (e, "END\n");
}

static void
write_rc_datablock (FILE *e, rc_uint_type length, const bfd_byte *data,
                    int has_next, int hasblock, int show_comment)
{
  if (!e || !data) {
    return;
  }

  if (hasblock) {
    fprintf (e, "BEGIN\n");
  }

  if (show_comment == -1) {
    if (test_rc_datablock_text(length, data)) {
      write_text_datablock(e, length, data, has_next, hasblock);
      return;
    }
    if (test_rc_datablock_unicode (length, data)) {
      write_unicode_datablock(e, length, data, has_next, hasblock);
      return;
    }
    show_comment = 0;
  }

  write_binary_datablock(e, length, data, has_next, show_comment);

  if (hasblock) {
    fprintf (e, "END\n");
  }
}

static void
write_text_datablock(FILE *e, rc_uint_type length, const bfd_byte *data,
                     int has_next, int hasblock)
{
  rc_uint_type i = 0;

  while (i < length) {
    rc_uint_type c = 0;
    indent (e, 2);
    fprintf (e, "\"");

    while (i < length && c < 160 && data[i] != '\n') {
      c++;
      i++;
    }
    if (i < length && data[i] == '\n') {
      i++;
      c++;
    }
    ascii_print(e, (const char *) &data[i - c], c);
    fprintf (e, "\"");
    if (i < length) {
      fprintf (e, "\n");
    }
  }

  if (i == 0) {
    indent (e, 2);
    fprintf (e, "\"\"");
  }
  if (has_next) {
    fprintf (e, ",");
  }
  fprintf (e, "\n");
  if (hasblock) {
    fprintf (e, "END\n");
  }
}

static void
write_unicode_datablock(FILE *e, rc_uint_type length, const bfd_byte *data,
                        int has_next, int hasblock)
{
  rc_uint_type i = 0;

  while (i < length) {
    rc_uint_type c = 0;
    const unichar *u = (const unichar *) &data[i];

    indent (e, 2);
    fprintf (e, "L\"");

    while (i < length && c < 160 && u[c] != '\n') {
      c++;
      i += 2;
    }
    if (i < length && u[c] == '\n') {
      i += 2;
      c++;
    }
    unicode_print (e, u, c);
    fprintf (e, "\"");
    if (i < length) {
      fprintf (e, "\n");
    }
  }

  if (i == 0) {
    indent (e, 2);
    fprintf (e, "L\"\"");
  }
  if (has_next) {
    fprintf (e, ",");
  }
  fprintf (e, "\n");
  if (hasblock) {
    fprintf (e, "END\n");
  }
}

static void
write_binary_datablock(FILE *e, rc_uint_type length, const bfd_byte *data,
                       int has_next, int show_comment)
{
  if (length == 0) {
    return;
  }

  rc_uint_type max_row = (show_comment ? 4 : 8);
  rc_uint_type i = 0;
  int first = 1;

  indent (e, 2);
  
  while (i + 3 < length) {
    rc_uint_type comment_start = i;

    if (!first) {
      indent (e, 2);
    }

    for (rc_uint_type k = 0; k < max_row && i + 3 < length; k++, i += 4) {
      int plen = print_32bit_value(e, data + i, length - i, k == 0);
      
      if (has_next || (i + 4) < length) {
        if (plen > 0 && plen < 11) {
          indent (e, 11 - plen);
        }
        fprintf (e, ",");
      }
    }
    
    if (show_comment) {
      fprintf (e, "\t/* ");
      ascii_print (e, (const char *) &data[comment_start], i - comment_start);
      fprintf (e, ".  */");
    }
    fprintf (e, "\n");
    first = 0;
  }

  write_remaining_bytes(e, data, length, &i, has_next, show_comment, &first);
}

static int
print_32bit_value(FILE *e, const bfd_byte *data, rc_uint_type remaining,
                  int is_first)
{
  if (is_first) {
    return fprintf (e, "0x%lxL",
                   (unsigned long) target_get_32 (data, remaining));
  } else {
    return fprintf (e, " 0x%lxL",
                   (unsigned long) target_get_32 (data, remaining)) - 1;
  }
}

static void
write_remaining_bytes(FILE *e, const bfd_byte *data, rc_uint_type length,
                      rc_uint_type *i, int has_next, int show_comment, int *first)
{
  if (*i + 1 < length) {
    if (!*first) {
      indent (e, 2);
    }
    int plen = fprintf (e, "0x%x",
                       (int) target_get_16 (data + *i, length - *i));
    if (has_next || *i + 2 < length) {
      if (plen > 0 && plen < 11) {
        indent (e, 11 - plen);
      }
      fprintf (e, ",");
    }
    if (show_comment) {
      fprintf (e, "\t/* ");
      ascii_print (e, (const char *) &data[*i], 2);
      fprintf (e, ".  */");
    }
    fprintf (e, "\n");
    *i += 2;
    *first = 0;
  }

  if (*i < length) {
    if (!*first) {
      indent (e, 2);
    }
    fprintf (e, "\"");
    ascii_print (e, (const char *) &data[*i], 1);
    fprintf (e, "\"");
    if (has_next) {
      fprintf (e, ",");
    }
    fprintf (e, "\n");
  }
}

/* Write out an rcdata resource.  This is also used for other types of
   resources that need to print arbitrary data.  */

static void
write_rc_rcdata (FILE *e, const rc_rcdata_item *rcdata, int ind)
{
  const rc_rcdata_item *ri;

  if (!e || !rcdata) {
    return;
  }

  indent (e, ind);
  fprintf (e, "BEGIN\n");

  for (ri = rcdata; ri != NULL; ri = ri->next)
    {
      if (ri->type == RCDATA_BUFFER && ri->u.buffer.length == 0)
	continue;

      switch (ri->type)
	{
	case RCDATA_WORD:
	  indent (e, ind + 2);
	  fprintf (e, "%ld", (long) (ri->u.word & 0xffff));
	  break;

	case RCDATA_DWORD:
	  indent (e, ind + 2);
	  fprintf (e, "%luL", (unsigned long) ri->u.dword);
	  break;

	case RCDATA_STRING:
	  indent (e, ind + 2);
	  fprintf (e, "\"");
	  ascii_print (e, ri->u.string.s, ri->u.string.length);
	  fprintf (e, "\"");
	  break;

	case RCDATA_WSTRING:
	  indent (e, ind + 2);
	  fprintf (e, "L\"");
	  unicode_print (e, ri->u.wstring.w, ri->u.wstring.length);
	  fprintf (e, "\"");
	  break;

	case RCDATA_BUFFER:
	  write_rc_datablock (e, (rc_uint_type) ri->u.buffer.length,
			      (const bfd_byte *) ri->u.buffer.data,
			      ri->next != NULL, 0, -1);
	  break;

	default:
	  return;
	}

      if (ri->type != RCDATA_BUFFER)
	{
	  if (ri->next != NULL)
	    fprintf (e, ",");
	  fprintf (e, "\n");
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
  rc_uint_type offset;
  int i;

  if (e == NULL || stringtable == NULL)
    return;

  if (name != NULL && ! name->named)
    offset = (name->u.id - 1) << 4;
  else
    {
      fprintf (e, "/* %s string table name.  */\n",
	       name == NULL ? "Missing" : "Invalid");
      offset = 0;
    }

  fprintf (e, "BEGIN\n");

  for (i = 0; i < 16; i++)
    {
      if (stringtable->strings[i].length != 0)
	{
	  fprintf (e, "  %lu, ", (unsigned long) (offset + i));
	  unicode_print_quoted (e, stringtable->strings[i].string,
				stringtable->strings[i].length);
	  fprintf (e, "\n");
	}
    }

  fprintf (e, "END\n");
}

/* Write out a versioninfo resource.  */

static void
write_rc_versioninfo (FILE *e, const rc_versioninfo *versioninfo)
{
  const rc_fixed_versioninfo *f;
  const rc_ver_info *vi;

  if (!e || !versioninfo || !versioninfo->fixed) {
    return;
  }

  f = versioninfo->fixed;
  
  if (f->file_version_ms != 0 || f->file_version_ls != 0) {
    fprintf (e, " FILEVERSION %u, %u, %u, %u\n",
             (unsigned int) ((f->file_version_ms >> 16) & 0xffff),
             (unsigned int) (f->file_version_ms & 0xffff),
             (unsigned int) ((f->file_version_ls >> 16) & 0xffff),
             (unsigned int) (f->file_version_ls & 0xffff));
  }
  
  if (f->product_version_ms != 0 || f->product_version_ls != 0) {
    fprintf (e, " PRODUCTVERSION %u, %u, %u, %u\n",
             (unsigned int) ((f->product_version_ms >> 16) & 0xffff),
             (unsigned int) (f->product_version_ms & 0xffff),
             (unsigned int) ((f->product_version_ls >> 16) & 0xffff),
             (unsigned int) (f->product_version_ls & 0xffff));
  }
  
  if (f->file_flags_mask != 0) {
    fprintf (e, " FILEFLAGSMASK 0x%x\n", (unsigned int) f->file_flags_mask);
  }
  
  if (f->file_flags != 0) {
    fprintf (e, " FILEFLAGS 0x%x\n", (unsigned int) f->file_flags);
  }
  
  if (f->file_os != 0) {
    fprintf (e, " FILEOS 0x%x\n", (unsigned int) f->file_os);
  }
  
  if (f->file_type != 0) {
    fprintf (e, " FILETYPE 0x%x\n", (unsigned int) f->file_type);
  }
  
  if (f->file_subtype != 0) {
    fprintf (e, " FILESUBTYPE 0x%x\n", (unsigned int) f->file_subtype);
  }
  
  if (f->file_date_ms != 0 || f->file_date_ls != 0) {
    fprintf (e, "/* Date: %u, %u.  */\n",
             (unsigned int) f->file_date_ms, (unsigned int) f->file_date_ls);
  }

  fprintf (e, "BEGIN\n");

  for (vi = versioninfo->var; vi != NULL; vi = vi->next) {
    if (vi->type == VERINFO_STRING) {
      const rc_ver_stringtable *vst;
      const rc_ver_stringinfo *vs;

      fprintf (e, "  BLOCK \"StringFileInfo\"\n");
      fprintf (e, "  BEGIN\n");

      for (vst = vi->u.string.stringtables; vst != NULL; vst = vst->next) {
        fprintf (e, "    BLOCK ");
        unicode_print_quoted (e, vst->language, -1);
        fprintf (e, "\n");
        fprintf (e, "    BEGIN\n");

        for (vs = vst->strings; vs != NULL; vs = vs->next) {
          fprintf (e, "      VALUE ");
          unicode_print_quoted (e, vs->key, -1);
          fprintf (e, ", ");
          unicode_print_quoted (e, vs->value, -1);
          fprintf (e, "\n");
        }

        fprintf (e, "    END\n");
      }
      fprintf (e, "  END\n");
    } else if (vi->type == VERINFO_VAR) {
      const rc_ver_varinfo *vv;

      fprintf (e, "  BLOCK \"VarFileInfo\"\n");
      fprintf (e, "  BEGIN\n");
      fprintf (e, "    VALUE ");
      unicode_print_quoted (e, vi->u.var.key, -1);

      for (vv = vi->u.var.var; vv != NULL; vv = vv->next) {
        fprintf (e, ", 0x%x, %d", (unsigned int) vv->language, (int) vv->charset);
      }

      fprintf (e, "\n  END\n");
    }
  }

  fprintf (e, "END\n");
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
      if (dst && src->u.string.length && src->u.string.s)
        memcpy (dst, src->u.string.s, src->u.string.length);
      return (rc_uint_type) src->u.string.length;

    case RCDATA_WSTRING:
      if (dst && src->u.wstring.length && src->u.wstring.w)
        memcpy (dst, src->u.wstring.w, src->u.wstring.length * sizeof (unichar));
      return (rc_uint_type) (src->u.wstring.length * sizeof (unichar));

    case RCDATA_BUFFER:
      if (dst && src->u.buffer.length && src->u.buffer.data)
        memcpy (dst, src->u.buffer.data, src->u.buffer.length);
      return (rc_uint_type) src->u.buffer.length;

    default:
      return 0;
    }
}
