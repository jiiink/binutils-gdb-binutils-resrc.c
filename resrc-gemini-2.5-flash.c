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

static char**
parse_cmd_args(char *cmd_str)
{
    int capacity = 8; // Initial capacity for argv
    char **argv = xmalloc(sizeof(char *) * capacity);
    int argc = 0;
    char *s = cmd_str;
    char *token_start;
    char quote_char; // Stores the quote char (' or ") if inside a quoted string

    while (1)
    {
        // Skip leading whitespace
        while (*s == ' ')
            s++;

        if (*s == '\0')
            break; // End of command string

        // Check if we need to resize argv. +2 for the current argument and the final NULL.
        if (argc + 2 > capacity)
        {
            capacity *= 2;
            argv = xrealloc(argv, sizeof(char *) * capacity);
            // xrealloc is assumed to call fatal on failure, so no need for explicit NULL check here.
        }

        quote_char = 0; // Reset quote state for new argument
        if (*s == '\'' || *s == '"')
        {
            quote_char = *s;
            s++; // Move past the opening quote
        }
        token_start = s; // This is where the actual argument content starts

        // Find the end of the argument
        if (quote_char)
        {
            // Inside a quoted string, search for the matching closing quote
            while (*s != '\0' && *s != quote_char)
                s++;
        }
        else
        {
            // Unquoted argument, search for space or end of string
            while (*s != '\0' && *s != ' ')
                s++;
        }

        // Null-terminate the argument and move past the separator (if not end of string)
        if (*s != '\0')
        {
            *s = '\0';
            s++; // Move past the separator (quote or space)
        }

        argv[argc++] = token_start;
    }

    argv[argc] = NULL; // NULL-terminate the argument list
    return argv;
}

static int
run_cmd (char *cmd, const char *redir)
{
  char **argv = NULL;
  int redir_handle = -1;
  int stdout_save = -1;
  char *temp_base = NULL;
  char *errmsg_fmt = NULL, *errmsg_arg = NULL;
  int retcode = 1; // Assume failure by default

  // Parse command arguments, modifying 'cmd' in place as per original functionality.
  argv = parse_cmd_args(cmd);
  // parse_cmd_args uses xmalloc/xrealloc, which are assumed to call fatal on failure.

  // --- Setup Redirection ---
  fflush(stdout);
  fflush(stderr);

  redir_handle = open(redir, O_WRONLY | O_TRUNC | O_CREAT, 0666);
  if (redir_handle == -1)
  {
    fatal(_("can't open temporary file `%s': %s"), redir, strerror(errno));
    goto cleanup;
  }

  stdout_save = dup(STDOUT_FILENO);
  if (stdout_save == -1)
  {
    fatal(_("can't duplicate stdout file descriptor for `%s': %s"), redir, strerror(errno));
    goto cleanup;
  }

  if (dup2(redir_handle, STDOUT_FILENO) == -1)
  {
      fatal(_("can't redirect stdout to file `%s': %s"), redir, strerror(errno));
      goto cleanup;
  }

  // --- Create Temporary File Base ---
  temp_base = make_temp_file(NULL);
  if (temp_base == NULL)
  {
      // make_temp_file is expected to call fatal on failure or return NULL.
      // If it returns NULL, we fatal.
      fatal(_("failed to create temporary file base: %s"), strerror(errno));
      goto cleanup;
  }

  // --- Execute Command ---
  int pid = pexecute(argv[0], (char * const *) argv, program_name, temp_base,
                     &errmsg_fmt, &errmsg_arg, PEXECUTE_ONE | PEXECUTE_SEARCH);

  if (pid == -1)
  {
      // Assuming pexecute provides safe strings, or fatal handles format strings securely.
      fatal("%s %s: %s", (errmsg_fmt ? errmsg_fmt : "unknown error"), (errmsg_arg ? errmsg_arg : ""), strerror(errno));
      // retcode is 1
      goto cleanup;
  }

  // --- Wait for Command Completion ---
  int wait_status;
  int wait_pid = pwait(pid, &wait_status, 0);

  if (wait_pid == -1)
  {
    fatal(_("wait failed: %s"), strerror(errno));
    // retcode is 1
  }
  else if (WIFSIGNALED(wait_status))
  {
    fatal(_("subprocess got fatal signal %d"), WTERMSIG(wait_status));
    // retcode is 1
  }
  else if (WIFEXITED(wait_status))
  {
    if (WEXITSTATUS(wait_status) != 0)
    {
      fatal(_("command `%s` exited with status %d"), cmd, WEXITSTATUS(wait_status));
      // retcode is 1
    }
    else
    {
      retcode = 0; // Success
    }
  }
  else
  {
    // Unhandled termination status (e.g., WIFSTOPPED, WIFCONTINUED)
    // or other unexpected wait_status values. Treat as failure.
    // retcode is 1
  }

cleanup:
  // --- Resource Cleanup ---

  // Restore stdout to its previous setting.
  // This must be attempted even if earlier steps failed to ensure terminal output is restored.
  if (stdout_save != -1)
  {
    // The original code did not check the return value of dup2 for restoration.
    // For "without altering external functionality", we maintain that behavior.
    dup2(stdout_save, STDOUT_FILENO);
    close(stdout_save);
  }

  // Close the redirection file handle.
  if (redir_handle != -1)
  {
    close(redir_handle);
  }

  // Free dynamically allocated memory.
  free(argv); // Frees the array of pointers, not the strings pointed to (they are in 'cmd')
  free(temp_base);

  // The contract for errmsg_fmt/errmsg_arg from pexecute is unclear regarding ownership.
  // The original code does not free them. To avoid altering external functionality
  // (e.g., if pexecute returns static strings or if they are pointers into temp_base),
  // they are not explicitly freed here. This matches the original code's behavior.

  return retcode;
}

static FILE *
open_input_stream (char *cmd)
{
  if (istream_type == ISTREAM_FILE)
    {
      char *fileprefix = NULL;
      size_t needed_len;

      fileprefix = make_temp_file (NULL);
      if (fileprefix == NULL)
        fatal (_("can't create temporary file prefix"));

      needed_len = strlen (fileprefix) + strlen (".irc") + 1;
      cpp_temp_file = (char *) xmalloc (needed_len);
      snprintf (cpp_temp_file, needed_len, "%s.irc", fileprefix);
      free (fileprefix);

      xatexit (close_input_stream);

      if (run_cmd (cmd, cpp_temp_file))
	fatal (_("can't execute `%s': %s"), cmd, strerror (errno));

      cpp_pipe = fopen (cpp_temp_file, FOPEN_RT);
      if (cpp_pipe == NULL)
	fatal (_("can't open temporary file `%s': %s"),
	       cpp_temp_file, strerror (errno));

      if (verbose)
	fprintf (stderr,
		 _("Using temporary file `%s' to read preprocessor output\n"),
		 cpp_temp_file);
    }
  else
    {
      cpp_pipe = popen (cmd, FOPEN_RT);
      if (cpp_pipe == NULL)
	fatal (_("can't popen `%s': %s"), cmd, strerror (errno));

      xatexit (close_input_stream);

      if (verbose)
	fprintf (stderr, _("Using popen to read preprocessor output\n"));
    }

  return cpp_pipe;
}

/* Determine if FILENAME contains special characters that
   can cause problems unless the entire filename is quoted.  */

static int
filename_need_quotes (const char *filename)
{
  if (filename == NULL)
    {
      return 0;
    }

  if (filename[0] == '-' && filename[1] == '\0')
    {
      return 0;
    }

  while (*filename != '\0')
    {
      switch (*filename)
        {
        case '&':
        case ' ':
        case '<':
        case '>':
        case '|':
        case '%':
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
  int found;
  struct stat s;
  const char *fnquotes = (filename_need_quotes (filename) ? "\"" : "");

  memcpy (cmd, prefix, end_prefix);
  char *current_cmd_end = stpcpy (cmd + end_prefix, DEFAULT_PREPROCESSOR_CMD);

  if (
#if defined (__DJGPP__) || defined (__CYGWIN__) || defined (_WIN32)
      strchr (cmd, '\\') ||
#endif
      strchr (cmd, '/'))
    {
      found = (stat (cmd, &s) == 0);

#ifdef HAVE_EXECUTABLE_SUFFIX
      if (!found)
        {
          char *suffix_start_pos = current_cmd_end;
          current_cmd_end = stpcpy(current_cmd_end, EXECUTABLE_SUFFIX);

          found = (stat (cmd, &s) == 0);
        }
#endif

      if (! found)
	{
	  if (verbose)
	    fprintf (stderr, _("Tried `%s'\n"), cmd);
	  return NULL;
	}
    }

  if (filename_need_quotes (cmd))
    {
      size_t current_len = strlen(cmd);
      memmove (cmd + 1, cmd, current_len + 1);
      
      cmd[0] = '"';
      cmd[current_len + 1] = '"';
      cmd[current_len + 2] = '\0';
      current_cmd_end = cmd + current_len + 2;
    }

  sprintf (current_cmd_end, " %s %s %s%s%s",
	   DEFAULT_PREPROCESSOR_ARGS, preprocargs, fnquotes, filename, fnquotes);

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
  Istream *cpp_pipe = NULL;

  const char *actual_filename = (filename == NULL) ? "-" : filename;

  if (filename != NULL && (strchr (filename, '/') != NULL || strchr (filename, '\\') != NULL))
    {
      size_t filename_len = strlen(filename);
      int is_absolute = (filename_len > 0 && (filename[0] == '/' || filename[0] == '\\')) ||
                        (filename_len > 1 && filename[1] == ':');

      // Allocate enough space: '.' + '/' (if relative) + filename + NULL terminator
      size_t buffer_len = filename_len + (is_absolute ? 1 : 3);
      char *path_buffer = xmalloc(buffer_len);

      char *current = path_buffer;
      if (!is_absolute) {
          *current++ = '.';
          *current++ = '/';
      }
      stpcpy(current, filename); // Copy filename into the buffer, current now points to null terminator

      // Find the last directory separator
      char *dir_separator = NULL;
      char *p;
      for (p = path_buffer; *p != '\0'; ++p) {
          if (*p == '/' || *p == '\\') {
              dir_separator = p;
          }
      }

      // Cut off the filename part, keeping the directory.
      if (dir_separator != NULL) {
          *dir_separator = '\0'; // Truncate at the last separator
      } else if (!is_absolute) {
          // If relative path and no separator (e.g., "file.rc"), the directory is "."
          // The buffer already contains "./filename.rc"
          // Truncate after the "./" part.
          path_buffer[2] = '\0'; // Result: "./\0"
      }
      // If absolute path with no separator (e.g., "C:file.rc"), leave as is.

      // Convert all backslashes to forward slashes
      for (char *q = path_buffer; *q != '\0'; ++q) {
          if (*q == '\\') {
              *q = '/';
          }
      }

      windres_add_include_dir(path_buffer);
      free(path_buffer);
    }

  istream_type = (use_temp_file) ? ISTREAM_FILE : ISTREAM_PIPE;

  const char *effective_preprocargs = (preprocargs == NULL) ? "" : preprocargs;
  const char *fnquotes = (filename_need_quotes (actual_filename) ? "\"" : "");

  if (preprocessor)
    {
      size_t cmd_len = strlen (preprocessor)
                       + strlen (effective_preprocargs)
                       + strlen (actual_filename)
                       + strlen (fnquotes) * 2
                       + 4; // Extra for two spaces, null terminator
      cmd = xmalloc (cmd_len);
      snprintf (cmd, cmd_len, "%s %s %s%s%s", preprocessor, effective_preprocargs,
                fnquotes, actual_filename, fnquotes);

      cpp_pipe = open_input_stream (cmd);
    }
  else
    {
      // Calculate max possible cmd length for default preprocessor.
      // This includes components that look_for_default might use to build the command.
      size_t cmd_len = strlen (program_name)
                       + strlen (DEFAULT_PREPROCESSOR_CMD)
                       + strlen (DEFAULT_PREPROCESSOR_ARGS)
                       + strlen (effective_preprocargs)
                       + strlen (actual_filename)
#ifdef HAVE_EXECUTABLE_SUFFIX
                       + strlen (EXECUTABLE_SUFFIX)
#endif
                       + strlen (fnquotes) * 2 // look_for_default might use quotes
                       + 10; // Extra padding for spaces, and null terminator
      cmd = xmalloc (cmd_len);

      char *dash = NULL;
      char *slash = NULL;
      const char *cp;

      // Find last dash and last slash/colon in program_name
      for (cp = program_name; *cp; cp++) {
          if (*cp == '-') {
              dash = (char *)cp;
          }
          if (
#if defined (__DJGPP__) || defined (__CYGWIN__) || defined(_WIN32)
              *cp == ':' || *cp == '\\' ||
#endif
              *cp == '/') {
              slash = (char *)cp;
              dash = NULL; // Reset dash if a directory separator is found
          }
      }

      // Try different paths for the default preprocessor
      if (dash) {
          cpp_pipe = look_for_default(cmd, program_name, dash - program_name + 1,
                                     effective_preprocargs, actual_filename);
      }

      if (slash && !cpp_pipe) {
          cpp_pipe = look_for_default(cmd, program_name, slash - program_name + 1,
                                     effective_preprocargs, actual_filename);
      }

      if (!cpp_pipe) {
          cpp_pipe = look_for_default(cmd, "", 0, effective_preprocargs, actual_filename);
      }
    }

  free (cmd); // cmd buffer is no longer needed after stream is opened

  rc_filename = xstrdup (actual_filename);
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
  if (istream_type == ISTREAM_FILE)
    {
      if (cpp_pipe != NULL)
        {
          fclose (cpp_pipe);
        }

      if (cpp_temp_file != NULL)
        {
          int errno_save = errno;
          unlink (cpp_temp_file);
          errno = errno_save;
          free (cpp_temp_file);
          cpp_temp_file = NULL;
        }
    }
  else
    {
      if (cpp_pipe != NULL)
        {
          int err;
          err = pclose (cpp_pipe);
          if (err != 0 || errno == ECHILD)
            {
              cpp_pipe = NULL;
              cpp_temp_file = NULL;
              fatal (_("preprocessing failed."));
            }
        }
    }

  cpp_pipe = NULL;
  cpp_temp_file = NULL;
}

/* Report an error while reading an rc file.  */

#include <stdio.h>
#include <stdlib.h>

void
yyerror (const char *msg)
{
  fprintf(stderr, "%s:%d: %s\n", rc_filename, rc_lineno, msg);
  exit(EXIT_FAILURE);
}

/* Issue a warning while reading an rc file.  */

void
rcparse_warning (const char *filename, int lineno, const char *msg)
{
  const char *safe_filename = (filename != NULL) ? filename : "(unknown file)";
  const char *safe_msg = (msg != NULL) ? msg : "(null message)";

  fprintf (stderr, "%s:%d: %s\n", safe_filename, lineno, safe_msg);
}

/* Die if we get an unexpected end of file.  */

static const char * const UNEXPECTED_EOF_FORMAT = "%s: unexpected EOF";

static void
unexpected_eof (const char *msg)
{
  fatal (_(UNEXPECTED_EOF_FORMAT), msg);
}

/* Read a 16 bit word from a file.  The data is assumed to be little
   endian.  */

static int
get_word (FILE *e, const char *msg)
{
  int byte1_val = getc(e);
  if (byte1_val == EOF) {
    unexpected_eof(msg);
  }

  int byte2_val = getc(e);
  if (byte2_val == EOF) {
    unexpected_eof(msg);
  }

  unsigned char byte1 = (unsigned char)byte1_val;
  unsigned char byte2 = (unsigned char)byte2_val;

  return ((int)byte2 << 8) | (int)byte1;
}

/* Read a 32 bit word from a file.  The data is assumed to be little
   endian.  */

static unsigned long
get_long (FILE *e, const char *msg)
{
  int bytes[4];
  unsigned long result = 0;
  int i;

  for (i = 0; i < 4; ++i) {
    bytes[i] = getc(e);
  }

  if (feof (e)) {
    unexpected_eof (msg);
  }

  for (i = 3; i >= 0; --i) {
    result = (result << 8) | (unsigned long)(bytes[i] & 0xff);
  }

  return result;
}

/* Read data from a file.  This is a wrapper to do error checking.  */

static void
get_data (FILE *e, bfd_byte *p, rc_uint_type c, const char *msg)
{
  size_t got_bytes;

  got_bytes = fread (p, 1, (size_t)c, e);

  if (got_bytes == (size_t)c)
    return;

  if (ferror (e))
    {
      fatal (_("%s: I/O error during read. Expected %lu bytes, but only read %lu. Error: %s"),
             msg, (unsigned long) c, (unsigned long) got_bytes, strerror(errno));
    }
  else if (feof (e))
    {
      fatal (_("%s: unexpected end of file. Expected %lu bytes, but only read %lu bytes before EOF."),
             msg, (unsigned long) c, (unsigned long) got_bytes);
    }
  else
    {
      fatal (_("%s: partial read. Expected %lu bytes, but only read %lu bytes."),
             msg, (unsigned long) c, (unsigned long) got_bytes);
    }
}

static rc_uint_type
target_get_16 (const void *p, size_t len)
{
  if (len < 2)
    return (rc_uint_type)-1;
  return windres_get_16 (&wrtarget, p);
}

static rc_uint_type
target_get_32 (const void *p, size_t len)
{
  if (len < sizeof (rc_uint_type))
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

#include <stdio.h>
#include <stdlib.h>
#include <sys/stat.h>
#include <errno.h>
#include <string.h>
#include <stdarg.h>

// Placeholder definitions for external types, functions, and globals.
// These are assumed to be defined elsewhere in the project.
typedef unsigned int rc_uint_type;
typedef void* bfd_byte;
typedef int rc_res_id;

typedef struct {
    int language;
} rc_res_res_info;

typedef enum {
    RES_TYPE_BITMAP
} RES_TYPE;

typedef struct {
    size_t length;
    bfd_byte data;
} rc_u_data;

typedef struct {
    RES_TYPE type;
    rc_u_data u;
    rc_res_res_info res_info;
} rc_res_resource;

extern FILE *open_file_search(const char *filename, const char *mode, const char *context, char **real_filename_ptr);
extern void fatal(const char *fmt, ...) __attribute__((noreturn));
extern const char *_(_(const char *msgid)); // Placeholder for gettext or similar localization function
extern void *res_alloc(size_t size);
extern void get_data(FILE *e, bfd_byte *data, size_t length, const char *filename);
extern rc_res_resource *define_standard_resource(void *resources_ptr, int type, rc_res_id id, int language, int flags);

extern void *resources;
extern const int FOPEN_RB;
extern const int RT_BITMAP;
extern const int BITMAP_SKIP;

// Static variables to store the formatted error message and a flag.
// This allows for centralizing cleanup via `goto` while preserving
// the exact error message provided by `fatal` on program exit.
// For single-threaded applications, this is an acceptable pattern in legacy code refactoring.
#define BITMAP_FATAL_ERROR_MSG_MAX_LEN 512
static char s_bitmap_fatal_error_msg[BITMAP_FATAL_ERROR_MSG_MAX_LEN];
static int s_bitmap_error_occurred = 0;

// Helper function to format and store an error message.
// This function prepares the message that `fatal` will use,
// and sets a flag indicating that an error has occurred.
static void store_and_set_fatal_error(const char *fmt, ...) {
    va_list args;
    va_start(args, fmt);
    vsnprintf(s_bitmap_fatal_error_msg, BITMAP_FATAL_ERROR_MSG_MAX_LEN, fmt, args);
    va_end(args);
    s_bitmap_error_occurred = 1;
}

void
define_bitmap (rc_res_id id, const rc_res_res_info *resinfo,
	       const char *filename)
{
  FILE *e = NULL;
  char *real_filename = NULL;
  struct stat s;
  bfd_byte *data = NULL; // 'data' is allocated by res_alloc and its ownership is transferred to 'r'.
  size_t data_length;
  rc_res_resource *r;

  // Reset error state for this function call to ensure isolation between calls.
  s_bitmap_error_occurred = 0;
  s_bitmap_fatal_error_msg[0] = '\0';

  // 1. File opening and path resolution.
  // Assuming `open_file_search` either succeeds (returning valid `FILE*` and allocated `char*`)
  // or calls `fatal` internally, exiting the program directly.
  e = open_file_search (filename, FOPEN_RB, "bitmap file", &real_filename);
  // At this point, if `open_file_search` returned without calling `fatal`,
  // `e` is an open file handle and `real_filename` points to allocated memory.
  // These resources must be properly closed/freed on any subsequent error.

  // 2. Stat check: Get file information.
  if (stat (real_filename, &s) < 0) {
    store_and_set_fatal_error (_("stat failed on bitmap file `%s': %s"), real_filename, strerror (errno));
    goto cleanup;
  }

  // 3. Validate file size and calculate the data length to read.
  // Ensure `s.st_size` is non-negative (covered by successful `stat` check)
  // and is large enough to account for `BITMAP_SKIP`.
  if (s.st_size < (off_t)BITMAP_SKIP) {
      store_and_set_fatal_error(_("bitmap file `%s' is too small (size %lld, minimum %d)"),
            real_filename, (long long)s.st_size, BITMAP_SKIP);
      goto cleanup;
  }
  data_length = (size_t)(s.st_size - BITMAP_SKIP);

  // 4. Data allocation.
  // `res_alloc` is assumed to either succeed (return valid memory) or call `fatal` internally.
  data = (bfd_byte *) res_alloc (data_length);

  // 5. Skip initial bytes using `fseek` for efficiency and clarity.
  if (fseek (e, BITMAP_SKIP, SEEK_SET) != 0) {
      store_and_set_fatal_error (_("failed to seek in bitmap file `%s': %s"), real_filename, strerror(errno));
      goto cleanup;
  }

  // 6. Read the remaining data into the allocated buffer.
  // `get_data` is assumed to either succeed or call `fatal` internally.
  get_data (e, data, data_length, real_filename);

  // 7. Define the standard resource.
  // `define_standard_resource` is assumed to either succeed or call `fatal` internally.
  r = define_standard_resource (&resources, RT_BITMAP, id,
				resinfo->language, 0);

  // 8. Assign resource data and info.
  r->type = RES_TYPE_BITMAP;
  r->u.data.length = data_length;
  r->u.data.data = data; // Ownership of 'data' is transferred to 'r'.
                         // 'data' does not need to be freed directly by define_bitmap.
  r->res_info = *resinfo;

cleanup:
  // Centralized cleanup for resources managed by `define_bitmap`.
  if (e != NULL) {
    // The original code did not check the return value of `fclose`.
    // Maintaining this behavior to adhere to "without altering its external functionality".
    fclose (e);
  }
  if (real_filename != NULL) {
    free (real_filename);
  }

  // If an error was recorded, call `fatal` with the stored message.
  // This ensures program exit with the specific error message, while also ensuring resources are freed.
  if (s_bitmap_error_occurred) {
    fatal ("%s", s_bitmap_fatal_error_msg);
  }
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

  static const int CURSOR_FILE_DATA_TYPE = 2;

  e = open_file_search (filename, FOPEN_RB, "cursor file", &real_filename);
  if (!e) {
      /* open_file_search is assumed to call fatal or handle its own errors.
         If it could return NULL without calling fatal,
         this block would need to handle cleanup or propagate error. */
      goto cleanup_real_filename;
  }

  get_word (e, real_filename); /* Ignored word */
  type = get_word (e, real_filename);
  count = get_word (e, real_filename);

  if (type != CURSOR_FILE_DATA_TYPE)
    fatal (_("cursor file `%s' does not contain cursor data"), real_filename);

  icondirs = xmalloc (count * sizeof (*icondirs));
  if (!icondirs) {
      /* xmalloc is assumed to call fatal or exit on failure.
         If it could return NULL, this block would need error handling. */
      goto cleanup_file;
  }

  for (i = 0; i < count; i++)
    {
      icondirs[i].width = getc (e);
      icondirs[i].height = getc (e);
      icondirs[i].colorcount = getc (e);
      getc (e); /* Skip reserved byte */
      icondirs[i].u.cursor.xhotspot = get_word (e, real_filename);
      icondirs[i].u.cursor.yhotspot = get_word (e, real_filename);
      icondirs[i].bytes = get_long (e, real_filename);
      icondirs[i].offset = get_long (e, real_filename);

      if (feof (e))
	unexpected_eof (real_filename);
    }

  first_cursor = cursors;

  for (i = 0; i < count; i++)
    {
      bfd_byte *data;
      rc_res_id name;
      rc_cursor *c;

      if (fseek (e, icondirs[i].offset, SEEK_SET) != 0)
	fatal (_("%s: fseek to %lu failed: %s"), real_filename,
	       (unsigned long)icondirs[i].offset, strerror (errno));

      data = res_alloc (icondirs[i].bytes);
      if (!data) {
          /* res_alloc is assumed to call fatal or exit on failure. */
          goto cleanup_icondirs;
      }

      get_data (e, data, icondirs[i].bytes, real_filename);

      c = res_alloc (sizeof (rc_cursor));
      if (!c) {
          /* res_alloc is assumed to call fatal or exit on failure. */
          goto cleanup_icondirs;
      }
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

cleanup_file:
  if (e)
    fclose (e);
cleanup_real_filename:
  if (real_filename)
    free (real_filename);

  first = NULL;
  pp = &first;
  for (i = 0; i < count; i++)
    {
      rc_group_cursor *cg;

      cg = res_alloc (sizeof (rc_group_cursor));
      if (!cg) {
          /* res_alloc is assumed to call fatal or exit on failure. */
          goto cleanup_icondirs;
      }
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

cleanup_icondirs:
  if (icondirs)
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
  rc_dialog *copy = NULL;
  rc_res_resource *r = NULL;

  if (resinfo == NULL || dialog == NULL)
    {
      return;
    }

  copy = (rc_dialog *) res_alloc (sizeof *copy);
  if (copy == NULL)
    {
      return;
    }

  *copy = *dialog;

  r = define_standard_resource (&resources, RT_DIALOG, id,
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
  rc_dialog_control *n = (rc_dialog_control *) res_alloc (sizeof (rc_dialog_control));

  if (n == NULL)
    {
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
    {
      return NULL;
    }

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

#define FONT_HEADER_STATIC_LEN 56
#define DEVICE_OFFSET_POSITION 44
#define FACE_OFFSET_POSITION 48

static uint32_t
read_uint32_le_from_buffer(const bfd_byte *buffer, size_t buffer_size, size_t offset)
{
  if (offset + 4 > buffer_size)
    {
      return 0;
    }
  return ((uint32_t)buffer[offset + 3] << 24)
       | ((uint32_t)buffer[offset + 2] << 16)
       | ((uint32_t)buffer[offset + 1] << 8)
       | ((uint32_t)buffer[offset + 0]);
}

void
define_font (rc_res_id id, const rc_res_res_info *resinfo,
	     const char *filename)
{
  FILE *e;
  char *real_filename;
  struct stat s;
  bfd_byte *data;
  rc_res_resource *r;
  uint32_t device_offset;
  uint32_t face_offset;
  size_t device_len;
  const char *device_src;
  size_t face_len;
  const char *face_src;
  long fontdatalength;
  bfd_byte *fontdata;
  rc_fontdir *fd;
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

  device_offset = read_uint32_le_from_buffer(data, s.st_size, DEVICE_OFFSET_POSITION);
  face_offset = read_uint32_le_from_buffer(data, s.st_size, FACE_OFFSET_POSITION);

  device_src = "";
  device_len = 0;
  if (device_offset > 0 && device_offset < s.st_size)
    {
      device_src = (const char *)data + device_offset;
      device_len = strnlen(device_src, s.st_size - device_offset);
    }

  face_src = "";
  face_len = 0;
  if (face_offset > 0 && face_offset < s.st_size)
    {
      face_src = (const char *)data + face_offset;
      face_len = strnlen(face_src, s.st_size - face_offset);
    }

  ++fonts;

  fontdatalength = FONT_HEADER_STATIC_LEN + (device_len + 1) + (face_len + 1);
  fontdata = (bfd_byte *)res_alloc(fontdatalength);

  memcpy(fontdata, data, FONT_HEADER_STATIC_LEN);

  memcpy((char *)fontdata + FONT_HEADER_STATIC_LEN, device_src, device_len);
  *((char *)fontdata + FONT_HEADER_STATIC_LEN + device_len) = '\0';

  memcpy((char *)fontdata + FONT_HEADER_STATIC_LEN + device_len + 1, face_src, face_len);
  *((char *)fontdata + FONT_HEADER_STATIC_LEN + device_len + 1 + face_len) = '\0';

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
define_font_rcdata (rc_res_id id,const rc_res_res_info *resinfo,
		    rc_rcdata_item *data)
{
  rc_res_resource *r;
  rc_uint_type len_data;
  bfd_byte *pb_data;

  /* Validate input parameters to prevent NULL pointer dereferences. */
  if (resinfo == NULL) {
    /* Critical error: Cannot define resource without valid resource info. */
    /* In a production environment, this might log an error or assert. */
    return;
  }

  if (data == NULL) {
    /* Critical error: Cannot render font data from a NULL data item. */
    /* In a production environment, this might log an error or assert. */
    return;
  }

  r = define_standard_resource (&resources, RT_FONT, id,
				resinfo->language, 0);
  if (r == NULL) {
    /* Critical error: Failed to allocate or define the standard resource. */
    /* This prevents a NULL pointer dereference on subsequent accesses to 'r'. */
    /* In a production environment, this might log an error or assert. */
    return;
  }

  pb_data = rcdata_render_as_buffer (data, &len_data);

  /* The resource 'r' has been created. Populate its fields. */
  /* If rcdata_render_as_buffer failed (pb_data is NULL), the resource will */
  /* be defined with a NULL data pointer and (presumably) zero length. */
  /* This ensures the resource structure itself is valid, even if the data is missing. */
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

  id.named = 0;
  id.u.id = 1;

  r = define_standard_resource (&resources, RT_FONTDIR, id, 0x409, 0);

  if (r == NULL)
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
  const rc_rcdata_item *d;
  bfd_byte *ret = NULL;
  bfd_byte *write_ptr;
  rc_uint_type len = 0;

  for (d = data; d != NULL; d = d->next)
    len += rcdata_copy (d, NULL);

  if (len != 0)
    {
      ret = (bfd_byte *) res_alloc (len);
      if (ret == NULL)
        {
          if (plen)
            *plen = len;
          return NULL;
        }
      
      write_ptr = ret;
      for (d = data; d != NULL; d = d->next)
	    write_ptr += rcdata_copy (d, write_ptr);
    }

  if (plen)
    *plen = len;

  return ret;
}

#include <string.h>

static void
free_fontdir_list (rc_fontdir *list)
{
  rc_fontdir *current = list;
  while (current != NULL)
    {
      rc_fontdir *next = current->next;
      res_free(current);
      current = next;
    }
}

static void
define_fontdir_rcdata (rc_res_id id,const rc_res_res_info *resinfo,
		       rc_rcdata_item *data)
{
  rc_res_resource *r = NULL;
  rc_fontdir *fd_first = NULL;
  rc_fontdir *fd_current = NULL;
  rc_uint_type len_data;
  bfd_byte *pb_data = NULL;
  rc_uint_type item_count;
  rc_uint_type current_offset;

#define FONTDIR_LANGUAGE_ID 0x409
#define FONTDIR_COUNT_SIZE 2
#define FONTDIR_ITEM_INDEX_SIZE 2
#define FONTDIR_ITEM_FIXED_OTHER_SIZE 54
#define FONTDIR_ITEM_FIXED_TOTAL_SIZE (FONTDIR_ITEM_INDEX_SIZE + FONTDIR_ITEM_FIXED_OTHER_SIZE)

  r = define_standard_resource(&resources, RT_FONTDIR, id, FONTDIR_LANGUAGE_ID, 0);
  if (r == NULL)
    {
      return;
    }

  pb_data = rcdata_render_as_buffer(data, &len_data);

  if (pb_data == NULL || len_data < FONTDIR_COUNT_SIZE)
    {
      r->type = RES_TYPE_FONTDIR;
      r->u.fontdir = NULL;
      r->res_info = *resinfo;
      return;
    }

  item_count = target_get_16(pb_data, len_data);
  current_offset = FONTDIR_COUNT_SIZE;

  for (; item_count > 0; item_count--)
    {
      rc_uint_type item_start_offset = current_offset;
      rc_fontdir *fd = NULL;
      const bfd_byte *str_ptr = NULL;
      const bfd_byte *str_end = NULL;
      size_t str_len;

      if (current_offset + FONTDIR_ITEM_FIXED_TOTAL_SIZE > len_data)
        {
          free_fontdir_list(fd_first);
          fd_first = NULL;
          break;
        }

      fd = (rc_fontdir *)res_alloc(sizeof(rc_fontdir));
      if (fd == NULL)
        {
          free_fontdir_list(fd_first);
          fd_first = NULL;
          break;
        }
      fd->next = NULL;

      fd->index = target_get_16(pb_data + current_offset, len_data - current_offset);
      current_offset += FONTDIR_ITEM_INDEX_SIZE;

      current_offset += FONTDIR_ITEM_FIXED_OTHER_SIZE;

      fd->data = pb_data + item_start_offset;

      str_ptr = pb_data + current_offset;
      if (str_ptr >= pb_data + len_data)
        {
          res_free(fd);
          free_fontdir_list(fd_first);
          fd_first = NULL;
          break;
        }
      str_end = memchr(str_ptr, '\0', len_data - current_offset);
      if (str_end == NULL)
        {
          res_free(fd);
          free_fontdir_list(fd_first);
          fd_first = NULL;
          break;
        }
      str_len = (size_t)(str_end - str_ptr) + 1;
      current_offset += (rc_uint_type)str_len;

      if (current_offset > len_data)
        {
          res_free(fd);
          free_fontdir_list(fd_first);
          fd_first = NULL;
          break;
        }

      str_ptr = pb_data + current_offset;
      if (str_ptr >= pb_data + len_data)
        {
          res_free(fd);
          free_fontdir_list(fd_first);
          fd_first = NULL;
          break;
        }
      str_end = memchr(str_ptr, '\0', len_data - current_offset);
      if (str_end == NULL)
        {
          res_free(fd);
          free_fontdir_list(fd_first);
          fd_first = NULL;
          break;
        }
      str_len = (size_t)(str_end - str_ptr) + 1;
      current_offset += (rc_uint_type)str_len;

      if (current_offset > len_data)
        {
          res_free(fd);
          free_fontdir_list(fd_first);
          fd_first = NULL;
          break;
        }

      fd->length = (current_offset - item_start_offset);

      if (fd_first == NULL)
        {
          fd_first = fd;
        }
      else
        {
          fd_current->next = fd;
        }
      fd_current = fd;
    }

  r->type = RES_TYPE_FONTDIR;
  r->u.fontdir = fd_first;
  r->res_info = *resinfo;

#undef FONTDIR_LANGUAGE_ID
#undef FONTDIR_COUNT_SIZE
#undef FONTDIR_ITEM_INDEX_SIZE
#undef FONTDIR_ITEM_FIXED_OTHER_SIZE
#undef FONTDIR_ITEM_FIXED_TOTAL_SIZE
}

static void define_messagetable_rcdata (rc_res_id id, const rc_res_res_info *resinfo,
					rc_rcdata_item *data)
{
  rc_res_resource *r = NULL;
  rc_uint_type len_data = 0;
  bfd_byte *pb_data = NULL;

  // Attempt to define the standard resource.
  // Check for NULL return to ensure resource allocation/retrieval succeeded.
  r = define_standard_resource (&resources, RT_MESSAGETABLE, id, resinfo->language, 0);
  if (r == NULL) {
    // Resource definition failed.
    // As this is a void function, we cannot return an error code.
    // Returning here prevents a NULL pointer dereference for 'r'.
    return;
  }

  // Render the data into a buffer.
  // Check for NULL return to ensure buffer allocation succeeded.
  pb_data = rcdata_render_as_buffer (data, &len_data);
  if (pb_data == NULL) {
    // Data rendering to buffer failed.
    // If 'define_standard_resource' implicitly registers 'r' with 'resources',
    // this would leave 'r' in a partially initialized state within the system.
    // Without altering the function's external signature (void return type)
    // or making assumptions about 'resources' internal cleanup mechanisms,
    // the safest action here is to prevent further processing with invalid data.
    return;
  }

  // Assign the rendered data and information to the resource.
  // These assignments are only performed if both 'r' and 'pb_data' are valid.
  r->type = RES_TYPE_MESSAGETABLE;
  r->u.data.length = len_data;
  r->u.data.data = pb_data; // 'r' now takes ownership of 'pb_data'
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
  FILE *e = NULL;
  char *real_filename = NULL;
  int type, count, i;
  struct icondir *icondirs = NULL;
  int first_icon;
  rc_res_resource *r;
  rc_group_icon *first = NULL;
  rc_group_icon **pp;

  e = open_file_search (filename, FOPEN_RB, "icon file", &real_filename);

  (void) get_word (e, real_filename);
  type = get_word (e, real_filename);
  count = get_word (e, real_filename);
  if (type != 1)
    fatal (_("icon file `%s' does not contain icon data"), real_filename);

  icondirs = xmalloc (count * sizeof (*icondirs));

  for (i = 0; i < count; i++)
    {
      int c;

      if ((c = getc (e)) == EOF) unexpected_eof (real_filename);
      icondirs[i].width = (unsigned char)c;

      if ((c = getc (e)) == EOF) unexpected_eof (real_filename);
      icondirs[i].height = (unsigned char)c;

      if ((c = getc (e)) == EOF) unexpected_eof (real_filename);
      icondirs[i].colorcount = (unsigned char)c;

      if ((c = getc (e)) == EOF) unexpected_eof (real_filename);

      icondirs[i].u.icon.planes = get_word (e, real_filename);
      icondirs[i].u.icon.bits = get_word (e, real_filename);
      icondirs[i].bytes = get_long (e, real_filename);
      icondirs[i].offset = get_long (e, real_filename);
    }

  first_icon = icons;

  for (i = 0; i < count; i++)
    {
      bfd_byte *data;
      rc_res_id name;

      if (fseek (e, icondirs[i].offset, SEEK_SET) != 0)
	fatal (_("%s: fseek to %lu failed: %s"), real_filename,
	       (unsigned long)icondirs[i].offset, strerror (errno));

      data = res_alloc (icondirs[i].bytes);

      get_data (e, data, icondirs[i].bytes, real_filename);

      ++icons;

      name = (rc_res_id){ .named = 0, .u.id = icons };

      r = define_standard_resource (&resources, RT_ICON, name,
				    resinfo->language, 0);
      r->type = RES_TYPE_ICON;
      r->u.data.length = icondirs[i].bytes;
      r->u.data.data = data;
      r->res_info = *resinfo;
    }

  fclose (e);
  free (real_filename);

  first = NULL;
  pp = &first;
  for (i = 0; i < count; i++)
    {
      rc_group_icon *cg;

      cg = res_alloc (sizeof (rc_group_icon));
      cg->next = NULL;
      cg->width = icondirs[i].width;
      cg->height = icondirs[i].height;
      cg->colors = icondirs[i].colorcount;

      unsigned int current_planes = icondirs[i].u.icon.planes;
      cg->planes = (current_planes == 0) ? 1 : current_planes;

      unsigned int current_bits = icondirs[i].u.icon.bits;
      if (current_bits == 0)
	{
	  unsigned int temp_bits = 0;
	  while ((1U << temp_bits) < cg->colors && temp_bits < (sizeof(unsigned int) * 8))
	    ++temp_bits;
	  cg->bits = temp_bits;
	}
      else
	{
	  cg->bits = current_bits;
	}

      cg->bytes = icondirs[i].bytes;
      cg->index = first_icon + i + 1;

      *pp = cg;
      pp = &cg->next;
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
  rc_group_icon *first_icon = NULL;
  rc_group_icon *current_icon = NULL;
  bfd_byte *original_buffer_start;
  bfd_byte *read_ptr;
  rc_uint_type remaining_len;

  const unsigned int GROUP_ICON_HEADER_SIZE = 6;
  const unsigned short GROUP_ICON_TYPE_EXPECTED = 1;
  const unsigned int GROUP_ICON_ENTRY_SIZE = 14;

  original_buffer_start = rcdata_render_as_buffer (data, &remaining_len);
  read_ptr = original_buffer_start;

  if (read_ptr == NULL)
    fatal (_("Failed to render group icon rcdata: buffer is NULL."));

  while (remaining_len >= GROUP_ICON_HEADER_SIZE)
    {
      unsigned short type;
      int icon_count;
      rc_uint_type current_header_offset = (rc_uint_type)(read_ptr - original_buffer_start);

      type = target_get_16 (read_ptr + 2, remaining_len - 2);
      if (type != GROUP_ICON_TYPE_EXPECTED)
	fatal (_("Unexpected group icon type %d at offset %u. Expected %d."),
               type, current_header_offset + 2, GROUP_ICON_TYPE_EXPECTED);

      icon_count = target_get_16 (read_ptr + 4, remaining_len - 4);
      if (icon_count < 0)
        fatal (_("Invalid group icon count %d detected at offset %u."), icon_count, current_header_offset + 4);

      read_ptr += GROUP_ICON_HEADER_SIZE;
      remaining_len -= GROUP_ICON_HEADER_SIZE;

      rc_uint_type required_entries_bytes;
      if (__builtin_mul_overflow((rc_uint_type)icon_count, GROUP_ICON_ENTRY_SIZE, &required_entries_bytes))
        fatal (_("Integer overflow calculating required bytes for %d group icon entries at offset %u."),
               icon_count, current_header_offset);

      if (remaining_len < required_entries_bytes)
	fatal (_("Group icon rcdata too small for %d entries at offset %u. Expected at least %u bytes, got %u."),
               icon_count, current_header_offset + GROUP_ICON_HEADER_SIZE, required_entries_bytes, remaining_len);

      for (int i = 0; i < icon_count; i++)
	{
          rc_uint_type entry_offset = (rc_uint_type)(read_ptr - original_buffer_start);

          if (remaining_len < GROUP_ICON_ENTRY_SIZE)
            fatal (_("Insufficient data for group icon entry %d at offset %u. Expected %u bytes, got %u."),
                   i, entry_offset, GROUP_ICON_ENTRY_SIZE, remaining_len);

	  rc_group_icon *new_icon = (rc_group_icon *) res_alloc (sizeof (rc_group_icon));
          if (!new_icon)
            fatal (_("Memory allocation failed for group icon entry %d at offset %u."), i, entry_offset);

	  new_icon->next = NULL;
	  new_icon->width = read_ptr[0];
	  new_icon->height = read_ptr[1];
	  new_icon->colors = read_ptr[2];
	  new_icon->planes = target_get_16 (read_ptr + 4, remaining_len - 4);
	  new_icon->bits = target_get_16 (read_ptr + 6, remaining_len - 6);
	  new_icon->bytes = target_get_32 (read_ptr + 8, remaining_len - 8);
	  new_icon->index = target_get_16 (read_ptr + 12, remaining_len - 12);

	  if (! first_icon)
	    first_icon = new_icon;
	  else
	    current_icon->next = new_icon;
	  current_icon = new_icon;

	  read_ptr += GROUP_ICON_ENTRY_SIZE;
	  remaining_len -= GROUP_ICON_ENTRY_SIZE;
	}
    }

  r = define_standard_resource (&resources, RT_GROUP_ICON, id,
				resinfo->language, 0);
  if (!r)
    fatal (_("Failed to define standard resource (type: RT_GROUP_ICON, ID: %d, lang: %d)."),
           (int)id, (int)resinfo->language);

  r->type = RES_TYPE_GROUP_ICON;
  r->u.group_icon = first_icon;
  r->res_info = *resinfo;
}

static void
define_group_cursor_rcdata (rc_res_id id, const rc_res_res_info *resinfo,
			    rc_rcdata_item *data)
{
  rc_res_resource *r;
  rc_group_cursor *first_cursor = NULL;
  rc_group_cursor *current_cursor = NULL;
  rc_uint_type total_data_len;
  const bfd_byte *raw_data_buffer;

  raw_data_buffer = rcdata_render_as_buffer (data, &total_data_len);
  const bfd_byte *read_ptr = raw_data_buffer;
  rc_uint_type bytes_remaining = total_data_len;

  const unsigned int GROUP_CURSOR_HEADER_SIZE    = 6;
  const unsigned int GROUP_CURSOR_TYPE_OFFSET    = 2;
  const unsigned int GROUP_CURSOR_COUNT_OFFSET   = 4;

  const unsigned int INDIVIDUAL_CURSOR_ENTRY_SIZE       = 14;
  const unsigned int INDIVIDUAL_CURSOR_WIDTH_OFFSET      = 0;
  const unsigned int INDIVIDUAL_CURSOR_HEIGHT_OFFSET     = 2;
  const unsigned int INDIVIDUAL_CURSOR_PLANES_OFFSET     = 4;
  const unsigned int INDIVIDUAL_CURSOR_BITS_OFFSET       = 6;
  const unsigned int INDIVIDUAL_CURSOR_BYTES_OFFSET      = 8;
  const unsigned int INDIVIDUAL_CURSOR_INDEX_OFFSET     = 12;

  while (bytes_remaining >= GROUP_CURSOR_HEADER_SIZE)
    {
      unsigned short group_type;
      int cursor_count;

      group_type = target_get_16 (read_ptr + GROUP_CURSOR_TYPE_OFFSET, bytes_remaining - GROUP_CURSOR_TYPE_OFFSET);
      if (group_type != 2)
	fatal (_("unexpected group cursor type %d"), group_type);

      cursor_count = target_get_16 (read_ptr + GROUP_CURSOR_COUNT_OFFSET, bytes_remaining - GROUP_CURSOR_COUNT_OFFSET);
      if (cursor_count < 0)
	fatal ("invalid cursor count in group cursor rcdata header");

      read_ptr += GROUP_CURSOR_HEADER_SIZE;
      bytes_remaining -= GROUP_CURSOR_HEADER_SIZE;

      for (int i = 0; i < cursor_count; ++i)
	{
	  if (bytes_remaining < INDIVIDUAL_CURSOR_ENTRY_SIZE)
	    fatal ("too small group cursor rcdata: insufficient data for cursor entry");

	  rc_group_cursor *new_cursor = (rc_group_cursor *) res_alloc (sizeof (rc_group_cursor));
	  new_cursor->next = NULL;

	  new_cursor->width  = target_get_16 (read_ptr + INDIVIDUAL_CURSOR_WIDTH_OFFSET,  bytes_remaining - INDIVIDUAL_CURSOR_WIDTH_OFFSET);
	  new_cursor->height = target_get_16 (read_ptr + INDIVIDUAL_CURSOR_HEIGHT_OFFSET, bytes_remaining - INDIVIDUAL_CURSOR_HEIGHT_OFFSET);
	  new_cursor->planes = target_get_16 (read_ptr + INDIVIDUAL_CURSOR_PLANES_OFFSET, bytes_remaining - INDIVIDUAL_CURSOR_PLANES_OFFSET);
	  new_cursor->bits   = target_get_16 (read_ptr + INDIVIDUAL_CURSOR_BITS_OFFSET,   bytes_remaining - INDIVIDUAL_CURSOR_BITS_OFFSET);
	  new_cursor->bytes  = target_get_32 (read_ptr + INDIVIDUAL_CURSOR_BYTES_OFFSET,  bytes_remaining - INDIVIDUAL_CURSOR_BYTES_OFFSET);
	  new_cursor->index  = target_get_16 (read_ptr + INDIVIDUAL_CURSOR_INDEX_OFFSET,  bytes_remaining - INDIVIDUAL_CURSOR_INDEX_OFFSET);

	  if (!first_cursor)
	    {
	      first_cursor = new_cursor;
	    }
	  else
	    {
	      current_cursor->next = new_cursor;
	    }
	  current_cursor = new_cursor;

	  read_ptr += INDIVIDUAL_CURSOR_ENTRY_SIZE;
	  bytes_remaining -= INDIVIDUAL_CURSOR_ENTRY_SIZE;
	}
    }

  r = define_standard_resource (&resources, RT_GROUP_ICON, id,
				resinfo->language, 0);
  r->type = RES_TYPE_GROUP_CURSOR;
  r->u.group_cursor = first_cursor;
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

  pb_data = rcdata_render_as_buffer (data, &len_data);

  if (pb_data == NULL)
    {
      return;
    }

  if (len_data < BIN_CURSOR_SIZE)
    {
      return;
    }

  c = res_alloc (sizeof (rc_cursor));
  c->xhotspot = target_get_16 (pb_data, len_data);
  c->yhotspot = target_get_16 (pb_data + 2, len_data - 2);
  c->length = len_data - BIN_CURSOR_SIZE;
  c->data = (const bfd_byte *) (pb_data + BIN_CURSOR_SIZE);

  r = define_standard_resource (&resources, RT_CURSOR, id, resinfo->language, 0);
  r->type = RES_TYPE_CURSOR;
  r->u.cursor = c;
  r->res_info = *resinfo;
}

static void
define_bitmap_rcdata (rc_res_id id, const rc_res_res_info *resinfo,
		      rc_rcdata_item *data)
{
  rc_res_resource *r = NULL;
  rc_uint_type len_data = 0;
  bfd_byte *pb_data = NULL;

  pb_data = rcdata_render_as_buffer (data, &len_data);

  /* If pb_data is NULL but len_data indicates content was expected,
   * it's an error (e.g., memory allocation failure).
   * If len_data is 0, pb_data being NULL is a valid representation
   * of an empty resource, and we proceed. */
  if (pb_data == NULL && len_data > 0)
    {
      /* Error handling: Cannot render data with non-zero length.
       * As this is a void function, we return early. */
      return;
    }

  r = define_standard_resource (&resources, RT_BITMAP, id, resinfo->language, 0);
  if (r == NULL)
    {
      /* Resource creation failed. We must free pb_data if it was allocated
       * by rcdata_render_as_buffer to prevent a memory leak.
       * If pb_data is NULL (either due to error already handled or valid empty data),
       * free(NULL) is typically a no-op, but guarding it is good practice. */
      if (pb_data != NULL)
        {
          free (pb_data);
        }
      return;
    }

  r->type = RES_TYPE_BITMAP;
  r->u.data.length = len_data;
  r->u.data.data = pb_data; /* Ownership of pb_data is transferred to 'r'. */
  r->res_info = *resinfo;
}

static void
define_icon_rcdata (rc_res_id id, const rc_res_res_info *resinfo,
		    rc_rcdata_item *data)
{
  rc_res_resource *r = NULL;
  rc_uint_type len_data = 0;
  bfd_byte *pb_data = NULL;

  pb_data = rcdata_render_as_buffer (data, &len_data);

  if (pb_data == NULL)
    {
      return;
    }

  r = define_standard_resource (&resources, RT_ICON, id, resinfo->language, 0);

  if (r == NULL)
    {
      free (pb_data);
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
  rc_menu *m = NULL;
  rc_res_resource *r = NULL;

  if (resinfo == NULL) {
    return;
  }

  m = res_alloc(sizeof(rc_menu));
  if (m == NULL) {
    return;
  }

  m->items = menuitems;
  m->help = 0;

  r = define_standard_resource(&resources, RT_MENU, id, resinfo->language, 0);

  if (r == NULL) {
    res_free(m);
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
  unichar *duplicated_text = NULL;

  mi = res_alloc (sizeof (rc_menuitem));
  if (mi == NULL)
    {
      return NULL;
    }

  if (text != NULL)
    {
      duplicated_text = unichar_dup (text);
      if (duplicated_text == NULL)
	{
	  res_free (mi);
	  return NULL;
	}
    }

  mi->next = NULL;
  mi->type = type;
  mi->state = state;
  mi->id = menuid;
  mi->text = duplicated_text;
  mi->help = help;
  mi->popup = menuitems;

  return mi;
}

/* Define a messagetable resource.  */

void
define_messagetable (rc_res_id id, const rc_res_res_info *resinfo,
                     const char *filename)
{
  FILE *file_handle = NULL;
  char *real_file_path = NULL;
  bfd_byte *file_content_data = NULL;
  rc_res_resource *resource_obj = NULL;

  // 1. Open file and retrieve its real path.
  // It is assumed that 'open_file_search' handles its own errors internally,
  // potentially by calling 'fatal' and exiting the program, or by guaranteeing
  // valid non-NULL 'file_handle' and 'real_file_path' upon successful return.
  file_handle = open_file_search(filename, "rb", "messagetable file", &real_file_path);

  // 2. Obtain file status to get its size.
  struct stat file_status;
  if (stat(real_file_path, &file_status) < 0) {
    int saved_errno = errno; // Capture errno before other calls may change it.
    char *path_for_fatal = strdup(real_file_path); // Copy path for the error message.
    // If strdup fails, path_for_fatal will be NULL. In such an extreme case,
    // the original 'real_file_path' will be used directly by 'fatal', accepting a minor risk of
    // Use-After-Free if `real_file_path` were freed beforehand, or a leak if it isn't.

    // Clean up resources acquired before this point, as 'fatal' will exit the program.
    free(real_file_path);
    fclose(file_handle);

    fatal(_("stat failed on messagetable file `%s': %s"),
          (path_for_fatal != NULL ? path_for_fatal : "unknown file"),
          strerror(saved_errno));
    // Note: 'fatal' is assumed to exit the program. 'path_for_fatal' cannot be freed here.
  }

  // 3. Allocate memory to store the file's content.
  // 'res_alloc' is assumed to handle allocation failures internally,
  // typically by calling 'fatal' and exiting the program.
  file_content_data = (bfd_byte *) res_alloc(file_status.st_size);

  // 4. Read the file's content into the allocated memory.
  // 'get_data' is assumed to handle read errors internally,
  // potentially by calling 'fatal' and exiting.
  get_data(file_handle, file_content_data, file_status.st_size, real_file_path);

  // The file handle and path string are no longer needed after data is read.
  // Close the file and free its path early to release resources efficiently.
  fclose(file_handle);
  file_handle = NULL; // Mark as closed.
  free(real_file_path);
  real_file_path = NULL; // Mark as freed.

  // 5. Define the standard resource object that will hold the message table.
  // 'define_standard_resource' is assumed to handle allocation failures internally,
  // typically by calling 'fatal' and exiting.
  resource_obj = define_standard_resource(&resources, RT_MESSAGETABLE, id,
                                          resinfo->language, 0);

  // 6. Populate the newly created resource object with the loaded data and information.
  resource_obj->type = RES_TYPE_MESSAGETABLE;
  resource_obj->u.data.length = file_status.st_size;
  resource_obj->u.data.data = file_content_data; // Ownership of 'file_content_data' is transferred to 'resource_obj'.
  file_content_data = NULL; // Mark as transferred to prevent double-free or incorrect cleanup.
  resource_obj->res_info = *resinfo;

  // All resources are either cleaned up or their ownership transferred to the resource management system.
  // The function implicitly returns here upon successful completion.
}

/* Define an rcdata resource.  */

void
define_rcdata (rc_res_id id, const rc_res_res_info *resinfo,
	       rc_rcdata_item *data)
{
  rc_res_resource *r;

  if (resinfo == NULL)
    {
      return;
    }

  r = define_standard_resource (&resources, RT_RCDATA, id,
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
  rc_rcdata_item *ri = NULL;
  char *s = NULL;

  ri = res_alloc (sizeof (rc_rcdata_item));
  if (ri == NULL) {
    return NULL;
  }

  s = res_alloc (len);
  if (s == NULL) {
    res_free(ri);
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
  rc_rcdata_item *ri = NULL;
  unichar *s = NULL;
  size_t byte_length;

  if (len > 0 && string == NULL) {
    return NULL;
  }

  if (len > 0 && (SIZE_MAX / sizeof(unichar) < (size_t)len)) {
    return NULL;
  }
  byte_length = (size_t)len * sizeof(unichar);

  ri = res_alloc (sizeof (rc_rcdata_item));
  if (ri == NULL) {
    return NULL;
  }

  s = res_alloc (byte_length);
  if (s == NULL) {
    res_free(ri);
    return NULL;
  }

  memcpy (s, string, byte_length);

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
  rc_rcdata_item *ri = res_alloc(sizeof(rc_rcdata_item));

  if (ri == NULL) {
    return NULL;
  }

  ri->next = NULL;

  if (dword) {
    ri->type = RCDATA_DWORD;
    ri->u.dword = (unsigned long)val;
  } else {
    ri->type = RCDATA_WORD;
    ri->u.word = (unsigned short)val;
  }

  return ri;
}

/* Define a stringtable resource.  This is called for each string
   which appears in a STRINGTABLE statement.  */

#define STRINGTABLE_COUNT 16

void
define_stringtable (const rc_res_res_info *resinfo,
		    rc_uint_type stringid, const unichar *string, int len)
{
  rc_res_id id;
  rc_res_resource *r;
  unichar *h;
  int string_index = stringid & (STRINGTABLE_COUNT - 1);

  id.named = 0;
  id.u.id = (stringid >> 4) + 1;

  r = define_standard_resource (&resources, RT_STRING, id,
				resinfo->language, 1);

  if (r->type == RES_TYPE_UNINITIALIZED)
    {
      r->type = RES_TYPE_STRINGTABLE;
      r->u.stringtable = (rc_stringtable *) res_alloc (sizeof (rc_stringtable));

      if (r->u.stringtable == NULL)
        {
          return;
        }

      for (int i = 0; i < STRINGTABLE_COUNT; i++)
	{
	  r->u.stringtable->strings[i].length = 0;
	  r->u.stringtable->strings[i].string = NULL;
	}

      r->res_info = *resinfo;
    }

  if (r->u.stringtable == NULL)
    {
      return;
    }

  h = (unichar *) res_alloc ((len + 1) * sizeof (unichar));

  if (h == NULL)
    {
      r->u.stringtable->strings[string_index].length = 0;
      r->u.stringtable->strings[string_index].string = NULL;
      return;
    }

  memcpy (h, string, len * sizeof (unichar));
  h[len] = 0;
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

  t = (rc_toolbar *) res_alloc (sizeof (rc_toolbar));
  if (t == NULL)
    {
      return;
    }

  t->button_width = width;
  t->button_height = height;
  t->nitems = 0;
  t->items = items;

  current_item = items;
  while (current_item != NULL)
    {
      t->nitems++;
      current_item = current_item->next;
    }

  r = define_standard_resource (&resources, RT_TOOLBAR, id, resinfo->language, 0);
  if (r == NULL)
    {
      res_free (t);
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
  rc_res_resource *r = 0;
  rc_rcdata_item *userdata_item = 0;
  bfd_byte *pb_data = 0;
  rc_uint_type len_data = 0;

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
  if (r == 0)
    {
      return;
    }

  r->type = RES_TYPE_USERDATA;

  userdata_item = (rc_rcdata_item *) res_alloc (sizeof (rc_rcdata_item));
  if (userdata_item == 0)
    {
      return;
    }
  r->u.userdata = userdata_item;

  userdata_item->next = 0;
  userdata_item->type = RCDATA_BUFFER;

  pb_data = rcdata_render_as_buffer (data, &len_data);

  if (pb_data == 0 && len_data > 0)
    {
      goto error_cleanup;
    }

  userdata_item->u.buffer.length = len_data;
  userdata_item->u.buffer.data = pb_data;

  r->res_info = *resinfo;
  return;

error_cleanup:
  if (pb_data != 0)
    {
      res_free (pb_data);
      pb_data = 0;
    }
  if (userdata_item != 0)
    {
      res_free (userdata_item);
      userdata_item = 0;
      if (r != 0) {
        r->u.userdata = 0;
      }
    }
  return;
}

void
define_rcdata_file (rc_res_id id, const rc_res_res_info *resinfo,
		    const char *filename)
{
  rc_rcdata_item *ri = NULL;
  FILE *e = NULL;
  char *real_filename = NULL;
  struct stat s;
  bfd_byte *data = NULL;
  int error_code = 0;

  e = open_file_search (filename, FOPEN_RB, "file", &real_filename);

  if (e == NULL)
    {
      error_code = 1;
      goto cleanup;
    }

  if (stat (real_filename, &s) < 0)
    {
      error_code = 2;
      goto cleanup;
    }

  data = res_alloc (s.st_size);

  get_data (e, data, s.st_size, real_filename);

  ri = res_alloc (sizeof (rc_rcdata_item));
  ri->next = NULL;
  ri->type = RCDATA_BUFFER;
  ri->u.buffer.length = s.st_size;
  ri->u.buffer.data = data;

  define_rcdata (id, resinfo, ri);

cleanup:
  if (e != NULL)
    {
      fclose (e);
    }
  if (real_filename != NULL)
    {
      free (real_filename);
    }

  if (error_code == 1)
    {
      fatal (_("Failed to open file: %s"), filename);
    }
  else if (error_code == 2)
    {
      fatal (_("stat failed on file `%s': %s"), real_filename,
	     strerror (errno));
    }
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
  rc_res_resource *r = NULL;
  rc_rcdata_item *userdata_item = NULL;

  // Attempt to open the file and retrieve its canonical path.
  // The `open_file_search` function is expected to call `fatal()` internally
  // if it encounters a critical failure (e.g., file not found, permissions).
  // If it returns NULL, it indicates an unexpected error, which we handle as fatal.
  e = open_file_search (filename, FOPEN_RB, "file", &real_filename);
  if (e == NULL)
    {
      // If `open_file_search` returned NULL, `real_filename` might or might not
      // have been allocated/set. Safely free it if it was.
      if (real_filename != NULL)
        free (real_filename);
      fatal (_("Failed to open or locate file '%s'"), filename);
    }

  // Retrieve file status to get its size.
  if (stat (real_filename, &s) < 0)
    {
      fclose (e);
      free (real_filename);
      fatal (_("stat failed on file '%s': %s"), real_filename, strerror (errno));
    }

  // Allocate memory to hold the file's content.
  // `res_alloc(0)` for a 0-byte file might return NULL or a valid pointer;
  // `get_data` and subsequent logic should handle a 0-byte buffer correctly.
  data = (bfd_byte *) res_alloc (s.st_size);
  if (data == NULL && s.st_size > 0)
    {
      // Fail if allocation for a non-zero size failed.
      fclose (e);
      free (real_filename);
      fatal (_("Failed to allocate memory for file data (%ld bytes)"), (long)s.st_size);
    }

  // Read the file's content into the allocated buffer.
  // `get_data` is assumed to handle its own errors (e.g., calling `fatal()` on read failure).
  get_data (e, data, s.st_size, real_filename);

  // Close the file handle and free the dynamically allocated `real_filename`.
  fclose (e);
  e = NULL; // Mark as closed
  free (real_filename);
  real_filename = NULL; // Mark as freed

  // Prepare the array of resource IDs.
  ids[0] = type;
  ids[1] = id;
  ids[2].named = 0; // Explicitly set named flag to 0 for an ID type.
  ids[2].u.id = resinfo->language;

  // Define the primary resource structure.
  // If `define_resource` fails to create and register the resource,
  // the `data` buffer (if allocated) must be freed to prevent memory leaks.
  r = define_resource (&resources, 3, ids, 0);
  if (r == NULL)
    {
      if (data != NULL)
        res_free (data); // Free the data buffer as its ownership transfer failed.
      fatal (_("Failed to define resource for user file '%s'"), filename);
    }

  r->type = RES_TYPE_USERDATA;

  // Allocate memory for the `rc_rcdata_item` structure that will hold the buffer details.
  // If this allocation fails, both the `data` buffer and the resource `r` itself
  // are in an inconsistent state. `data` must be freed.
  // Cleanup for `r` (e.g., `undefine_resource`) is not exposed by the provided context;
  // relying on `fatal` to terminate the program, thus preventing further inconsistent state.
  userdata_item = (rc_rcdata_item *) res_alloc (sizeof (rc_rcdata_item));
  if (userdata_item == NULL)
    {
      if (data != NULL)
        res_free (data); // Free the data buffer, as its ownership transfer failed.
      fatal (_("Failed to allocate user data item for resource '%s'"), filename);
    }

  // Assign the allocated user data item and populate its fields.
  r->u.userdata = userdata_item;
  r->u.userdata->next = NULL;
  r->u.userdata->type = RCDATA_BUFFER;
  r->u.userdata->u.buffer.length = s.st_size;
  r->u.userdata->u.buffer.data = data; // Ownership of `data` buffer is now transferred.

  // Copy the resource information.
  r->res_info = *resinfo;
}

/* Define a versioninfo resource.  */

void
define_versioninfo (rc_res_id id, rc_uint_type language,
		    rc_fixed_versioninfo *fixedverinfo,
		    rc_ver_info *verinfo)
{
  rc_res_resource *r;
  rc_versioninfo *version_info_data;

  r = define_standard_resource (&resources, RT_VERSION, id, language, 0);
  if (r == NULL)
    {
      return;
    }

  r->type = RES_TYPE_VERSIONINFO;

  version_info_data = (rc_versioninfo *) res_alloc (sizeof (rc_versioninfo));
  if (version_info_data == NULL)
    {
      return;
    }

  r->u.versioninfo = version_info_data;
  r->u.versioninfo->fixed = fixedverinfo;
  r->u.versioninfo->var = verinfo;
  r->res_info.language = language;
}

/* Add string version info to a list of version information.  */

rc_ver_info *
append_ver_stringfileinfo (rc_ver_info *verinfo,
			   rc_ver_stringtable *stringtables)
{
  rc_ver_info *new_node;
  rc_ver_info **current_ptr;

  new_node = (rc_ver_info *) res_alloc (sizeof (rc_ver_info));
  if (new_node == NULL)
    {
      return NULL;
    }

  new_node->next = NULL;
  new_node->type = VERINFO_STRING;
  new_node->u.string.stringtables = stringtables;

  for (current_ptr = &verinfo; *current_ptr != NULL; current_ptr = &(*current_ptr)->next)
    ;
  *current_ptr = new_node;

  return verinfo;
}

rc_ver_stringtable *
append_ver_stringtable (rc_ver_stringtable *stringtable,
			const char *language,
			rc_ver_stringinfo *strings)
{
  rc_ver_stringtable *new_node;
  rc_ver_stringtable **current_ptr;

  new_node = res_alloc(sizeof(*new_node));
  if (new_node == NULL)
    {
      return NULL; /* CWE-399: Allocation failure, return NULL to signal error. */
    }

  new_node->next = NULL;

  if (language == NULL)
    {
      /* CWE-476: NULL Pointer Dereference. Prevent crash in unicode_from_ascii. */
      /* Free the newly allocated node to prevent a memory leak before returning. */
      res_free(new_node); /* Assuming res_free is the counterpart to res_alloc. */
      return NULL;
    }

  /*
   * Assumption: unicode_from_ascii allocates memory for new_node->language
   * and handles its own errors or is guaranteed not to fail in a way
   * detectable by this function's return value. The original code does not
   * check for failure of unicode_from_ascii, so we maintain this behavior
   * to avoid altering external functionality.
   */
  unicode_from_ascii((rc_uint_type *)NULL, &new_node->language, language);

  new_node->strings = strings;

  /* Traverse the linked list to find the last node and append the new node. */
  for (current_ptr = &stringtable; *current_ptr != NULL; current_ptr = &(*current_ptr)->next)
    ;
  *current_ptr = new_node;

  return stringtable;
}

/* Add variable version info to a list of version information.  */

rc_ver_info *
append_ver_varfileinfo (rc_ver_info *verinfo, const unichar *key,
			rc_ver_varinfo *var)
{
  rc_ver_info *new_node;
  rc_ver_info **pp;

  new_node = res_alloc (sizeof *new_node);
  if (new_node == NULL)
    {
      return NULL; /* Allocation failed */
    }

  new_node->next = NULL;
  new_node->type = VERINFO_VAR;
  new_node->u.var.var = var;

  new_node->u.var.key = unichar_dup (key);
  if (new_node->u.var.key == NULL)
    {
      res_free (new_node); /* Clean up allocated node if key duplication fails */
      return NULL;
    }

  for (pp = &verinfo; *pp != NULL; pp = &(*pp)->next)
    ;
  *pp = new_node;

  return verinfo;
}

/* Append version string information to a list.  */

rc_ver_stringinfo *
append_verval (rc_ver_stringinfo *strings, const unichar *key,
	       const unichar *value)
{
  rc_ver_stringinfo *new_node;
  rc_ver_stringinfo **current_ptr_to_next;

  if (key == NULL || value == NULL) {
    return NULL; 
  }

  new_node = (rc_ver_stringinfo *) res_alloc (sizeof (rc_ver_stringinfo));
  if (new_node == NULL) {
    return NULL;
  }

  new_node->key = unichar_dup (key);
  if (new_node->key == NULL) {
    res_free(new_node);
    return NULL;
  }

  new_node->value = unichar_dup (value);
  if (new_node->value == NULL) {
    res_free(new_node->key);
    res_free(new_node);
    return NULL;
  }

  new_node->next = NULL;

  current_ptr_to_next = &strings;
  while (*current_ptr_to_next != NULL) {
    current_ptr_to_next = &(*current_ptr_to_next)->next;
  }
  *current_ptr_to_next = new_node;

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
    {
      /*
       * Memory allocation failed.
       * Return the original list head without modification.
       * This ensures the list remains in its prior state and signals failure
       * to the caller (no new element was added).
       */
      return var;
    }

  vv->next = NULL;
  vv->language = language;
  vv->charset = charset;

  for (pp = &var; *pp != NULL; pp = &(*pp)->next)
    ;
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

static int
indent (FILE *e, int c)
{
  int i;
  int written_count = 0;

  if (e == NULL) {
    return EOF;
  }

  if (c < 0) {
    c = 0;
  }

  for (i = 0; i < c; i++) {
    if (putc (' ', e) == EOF) {
      return EOF;
    }
    written_count++;
  }

  return written_count;
}

/* Dump the resources we have read in the format of an rc file.

   Reasoned by the fact, that some resources need to be stored into file and
   refer to that file, we use the user-data model for that to express it binary
   without the need to store it somewhere externally.  */

bool
write_rc_file (const char *filename, const rc_res_directory *res_dir)
{
  FILE *e = NULL;
  bool opened_file = false;
  bool result = false;
  rc_uint_type language;

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
	  goto cleanup;
	}
      opened_file = true;
    }

  language = (rc_uint_type) ((bfd_signed_vma) -1);

  if (!write_rc_directory (e, res_dir, (const rc_res_id *) NULL,
                           (const rc_res_id *) NULL, &language, 1))
    {
      goto cleanup;
    }

  result = true;

cleanup:
  if (opened_file && e != NULL)
    {
      if (fclose (e) != 0)
        {
          non_fatal (_("error closing file `%s': %s"), filename, strerror (errno));
          result = false;
        }
    }
  return result;
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

  /* Print out some COFF information that rc files can't represent.  */
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

  for (re = rd->entries;  re != NULL; re = re->next)
    {
      switch (level)
	{
	case 1:
	  /* If we're at level 1, the key of this resource is the
	     type.  This normally duplicates the information we have
	     stored with the resource itself, but we need to remember
	     the type if this is a user define resource type.  */
	  type = &re->id;
	  break;

	case 2:
	  /* If we're at level 2, the key of this resource is the name
	     we are going to use in the rc printout.  */
	  name = &re->id;
	  break;

	case 3:
	  /* If we're at level 3, then this key represents a language.
	     Use it to update the current language.  */
	  if (! re->id.named
	      && re->id.u.id != (unsigned long) (unsigned int) *language
	      && (re->id.u.id & 0xffff) == re->id.u.id)
	    {
	      wr_print (e, "LANGUAGE %u, %u\n",
		       re->id.u.id & ((1 << SUBLANG_SHIFT) - 1),
		       (re->id.u.id >> SUBLANG_SHIFT) & 0xff);
	      *language = re->id.u.id;
	    }
	  break;

	default:
	  break;
	}

      if (re->subdir)
	write_rc_subdir (e, re, type, name, language, level);
      else
	{
	  if (level == 3)
	    {
	      /* This is the normal case: the three levels are
		 TYPE/NAME/LANGUAGE.  NAME will have been set at level
		 2, and represents the name to use.  We probably just
		 set LANGUAGE, and it will probably match what the
		 resource itself records if anything.  */
	      write_rc_resource (e, type, name, re->u.res, language);
	    }
	  else
	    {
	      wr_printcomment (e, "Resource at unexpected level %d", level);
	      write_rc_resource (e, type, (rc_res_id *) NULL, re->u.res,
				 language);
	    }
	}
    }
  
  /* Ensure output buffer is flushed after processing all entries,
   * or if there were no entries to begin with. The original logic
   * only flushed if rd->entries was NULL, which is likely incorrect. */
  wr_print_flush (e);
}

/* Write out a subdirectory entry.  E is the file to write to.  RE is
   the subdirectory entry.  TYPE and NAME are pointers to higher level
   IDs, or NULL.  LANGUAGE is a pointer to the current language.
   LEVEL is the level in the tree.  */

static const char*
get_resource_type_string_for_id(unsigned int id)
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
      wr_printcomment (e, "Type: ");
      if (re->id.named)
	{
	  res_id_print (e, re->id, 1);
	}
      else
	{
	  const char *s = get_resource_type_string_for_id(re->id.u.id);
	  if (s != NULL)
	    {
	      fprintf (e, "%s", s);
	    }
	  else
	    {
	      res_id_print (e, re->id, 1);
	    }
	}
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

static void print_rc_resource_type_id(FILE *e, const rc_res_id *type_id) {
    if (type_id == NULL) {
        fprintf(e, "??Unknown-Type??");
        return;
    }

    if (type_id->named) {
        res_id_print(e, *type_id, 1);
    } else {
        switch (type_id->u.id) {
            case RT_MANIFEST: fprintf(e, "%u /* RT_MANIFEST */", (unsigned int)RT_MANIFEST); break;
            case RT_ANICURSOR: fprintf(e, "%u /* RT_ANICURSOR */", (unsigned int)RT_ANICURSOR); break;
            case RT_ANIICON: fprintf(e, "%u /* RT_ANIICON */", (unsigned int)RT_ANIICON); break;
            case RT_RCDATA: fprintf(e, "%u /* RT_RCDATA */", (unsigned int)RT_RCDATA); break;
            case RT_ICON: fprintf(e, "%u /* RT_ICON */", (unsigned int)RT_ICON); break;
            case RT_CURSOR: fprintf(e, "%u /* RT_CURSOR */", (unsigned int)RT_CURSOR); break;
            case RT_BITMAP: fprintf(e, "%u /* RT_BITMAP */", (unsigned int)RT_BITMAP); break;
            case RT_PLUGPLAY: fprintf(e, "%u /* RT_PLUGPLAY */", (unsigned int)RT_PLUGPLAY); break;
            case RT_VXD: fprintf(e, "%u /* RT_VXD */", (unsigned int)RT_VXD); break;
            case RT_FONT: fprintf(e, "%u /* RT_FONT */", (unsigned int)RT_FONT); break;
            case RT_FONTDIR: fprintf(e, "%u /* RT_FONTDIR */", (unsigned int)RT_FONTDIR); break;
            case RT_HTML: fprintf(e, "%u /* RT_HTML */", (unsigned int)RT_HTML); break;
            case RT_MESSAGETABLE: fprintf(e, "%u /* RT_MESSAGETABLE */", (unsigned int)RT_MESSAGETABLE); break;
            case RT_DLGINCLUDE: fprintf(e, "%u /* RT_DLGINCLUDE */", (unsigned int)RT_DLGINCLUDE); break;
            case RT_DLGINIT: fprintf(e, "%u /* RT_DLGINIT */", (unsigned int)RT_DLGINIT); break;
            default: res_id_print(e, *type_id, 0); break;
        }
    }
}

static void
write_rc_resource (FILE *e, const rc_res_id *type,
		   const rc_res_id *name, const rc_res_resource *res,
		   rc_uint_type *language)
{
  const char *resource_type_str = NULL;
  int resource_type_id = 0;
  int is_menuex = 0;

  switch (res->type)
    {
    case RES_TYPE_ACCELERATOR:
      resource_type_str = "ACCELERATORS";
      resource_type_id = RT_ACCELERATOR;
      break;

    case RES_TYPE_BITMAP:
      resource_type_str = "2 /* RT_BITMAP */";
      resource_type_id = RT_BITMAP;
      break;

    case RES_TYPE_CURSOR:
      resource_type_str = "1 /* RT_CURSOR */";
      resource_type_id = RT_CURSOR;
      break;

    case RES_TYPE_GROUP_CURSOR:
      resource_type_str = "12 /* RT_GROUP_CURSOR */";
      resource_type_id = RT_GROUP_CURSOR;
      break;

    case RES_TYPE_DIALOG:
      if (extended_dialog (res->u.dialog))
	resource_type_str = "DIALOGEX";
      else
	resource_type_str = "DIALOG";
      resource_type_id = RT_DIALOG;
      break;

    case RES_TYPE_FONT:
      resource_type_str = "8 /* RT_FONT */";
      resource_type_id = RT_FONT;
      break;

    case RES_TYPE_FONTDIR:
      resource_type_str = "7 /* RT_FONTDIR */";
      resource_type_id = RT_FONTDIR;
      break;

    case RES_TYPE_ICON:
      resource_type_str = "3 /* RT_ICON */";
      resource_type_id = RT_ICON;
      break;

    case RES_TYPE_GROUP_ICON:
      resource_type_str = "14 /* RT_GROUP_ICON */";
      resource_type_id = RT_GROUP_ICON;
      break;

    case RES_TYPE_MENU:
      if (extended_menu (res->u.menu))
	{
	  resource_type_str = "MENUEX";
	  is_menuex = 1;
	}
      else
	{
	  resource_type_str = "MENU";
	  is_menuex = 0;
	}
      resource_type_id = RT_MENU;
      break;

    case RES_TYPE_MESSAGETABLE:
      resource_type_str = "11 /* RT_MESSAGETABLE */";
      resource_type_id = RT_MESSAGETABLE;
      break;

    case RES_TYPE_RCDATA:
      resource_type_str = "RCDATA";
      resource_type_id = RT_RCDATA;
      break;

    case RES_TYPE_STRINGTABLE:
      resource_type_str = "STRINGTABLE";
      resource_type_id = RT_STRING;
      break;

    case RES_TYPE_USERDATA:
      resource_type_str = NULL;
      resource_type_id = 0;
      break;

    case RES_TYPE_VERSIONINFO:
      resource_type_str = "VERSIONINFO";
      resource_type_id = RT_VERSION;
      break;

    case RES_TYPE_TOOLBAR:
      resource_type_str = "TOOLBAR";
      resource_type_id = RT_TOOLBAR;
      break;

    default:
      abort (); 
    }

  if (resource_type_id != 0
      && type != NULL
      && (type->named || type->u.id != (unsigned long) resource_type_id))
    {
      wr_printcomment (e, "Unexpected resource type mismatch: ");
      res_id_print (e, *type, 1);
      fprintf (e, " != %d", resource_type_id);
    }

  if (res->coff_info.codepage != 0)
    wr_printcomment (e, "Code page: %u", res->coff_info.codepage);
  if (res->coff_info.reserved != 0)
    wr_printcomment (e, "COFF reserved value: %u", res->coff_info.reserved);

  wr_print (e, "\n");
  if (resource_type_id != RT_STRING)
    {
      if (name != NULL)
	res_id_print (e, *name, 1);
      else
	fprintf (e, "??Unknown-Name??");
      fprintf (e, " ");
    }

  if (resource_type_str != NULL)
    fprintf (e, "%s", resource_type_str);
  else
    {
      print_rc_resource_type_id(e, type);
    }

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
      int modifiers_enabled = 0;

      switch (res->type)
	{
	case RES_TYPE_ACCELERATOR:
	case RES_TYPE_DIALOG:
	case RES_TYPE_MENU:
	case RES_TYPE_RCDATA:
	case RES_TYPE_STRINGTABLE:
	  modifiers_enabled = 1;
	  break;

	default:
	  /* modifiers_enabled remains 0 */
	  break;
	}

      const char *comment_prefix = modifiers_enabled ? "// " : "";

      if (res->res_info.language != 0 && res->res_info.language != *language)
	fprintf (e, "%sLANGUAGE %d, %d\n",
		 comment_prefix,
		 (int) res->res_info.language & ((1<<SUBLANG_SHIFT)-1),
		 (int) (res->res_info.language >> SUBLANG_SHIFT) & 0xff);
      if (res->res_info.characteristics != 0)
	fprintf (e, "%sCHARACTERISTICS %u\n",
		 comment_prefix,
		 (unsigned int) res->res_info.characteristics);
      if (res->res_info.version != 0)
	fprintf (e, "%sVERSION %u\n",
		 comment_prefix,
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
      write_rc_menu (e, res->u.menu, is_menuex);
      break;

    case RES_TYPE_RCDATA:
    case RES_TYPE_USERDATA:
      write_rc_rcdata (e, res->u.rcdata, 0);
      break;

    case RES_TYPE_STRINGTABLE:
      write_rc_stringtable (e, name, res->u.stringtable);
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
      abort ();
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

  (void) fprintf (e, "BEGIN\n");

  for (acc = accelerators; acc != NULL; acc = acc->next)
    {
      (void) fprintf (e, "  ");

      const int key_value = (int) acc->key;

      const int is_7bit_ascii_range = (key_value >= 0 && key_value <= 127);
      const int is_printable_ascii_char = is_7bit_ascii_range && ISPRINT((unsigned char)key_value);
      const int is_not_virtual_key_flag = ((acc->flags & ACC_VIRTKEY) == 0);

      const int use_char_representation = is_printable_ascii_char && is_not_virtual_key_flag;

      if (use_char_representation)
        {
          (void) fprintf (e, "\"%c\"", (char) key_value);
        }
      else
        {
          (void) fprintf (e, "%d", key_value);
        }

      (void) fprintf (e, ", %d", (int) acc->id);

      if (!use_char_representation)
        {
          if ((acc->flags & ACC_VIRTKEY) != 0)
            {
              (void) fprintf (e, ", VIRTKEY");
            }
          else
            {
              (void) fprintf (e, ", ASCII");
            }
        }

      if ((acc->flags & ACC_SHIFT) != 0)
        {
          (void) fprintf (e, ", SHIFT");
        }
      if ((acc->flags & ACC_CONTROL) != 0)
        {
          (void) fprintf (e, ", CONTROL");
        }
      if ((acc->flags & ACC_ALT) != 0)
        {
          (void) fprintf (e, ", ALT");
        }

      (void) fprintf (e, "\n");
    }

  (void) fprintf (e, "END\n");
}

/* Write out cursor information.  This would normally be in a separate
   file, which the rc file would include.  */

static int
write_rc_cursor (FILE *e, const rc_cursor *cursor)
{
  if (e == NULL || cursor == NULL)
    {
      return -1;
    }

  if (fprintf (e, "BEGIN\n") < 0)
    {
      return -1;
    }

  indent (e, 2);

  if (fprintf (e, " 0x%x, 0x%x,\t/* Hotspot x: %d, y: %d.  */\n",
               (unsigned int) cursor->xhotspot, (unsigned int) cursor->yhotspot,
               (int) cursor->xhotspot, (int) cursor->yhotspot) < 0)
    {
      return -1;
    }

  if (write_rc_datablock (e, (rc_uint_type) cursor->length,
                          (const bfd_byte *) cursor->data,
                          0, 0, 0) != 0)
    {
      return -1;
    }

  if (fprintf (e, "END\n") < 0)
    {
      return -1;
    }

  return 0;
}

/* Write out group cursor data.  This would normally be built from the
   cursor data.  */

static void
write_rc_group_cursor (FILE *e, const rc_group_cursor *group_cursor)
{
  if (e == NULL) {
    return;
  }

  const rc_group_cursor *gc_ptr;
  int item_count = 0;

  for (gc_ptr = group_cursor; gc_ptr != NULL; gc_ptr = gc_ptr->next) {
    item_count++;
  }

  fprintf(e, "BEGIN\n");

  indent(e, 2);
  fprintf(e, "0, 2, %d%s\t /* Having %d items.  */\n", item_count, (item_count != 0 ? "," : ""), item_count);

  indent(e, 4);
  fprintf(e, "/* width, height, planes, bits, bytes, index.  */\n");

  int current_item_index = 0;
  for (gc_ptr = group_cursor; gc_ptr != NULL; gc_ptr = gc_ptr->next) {
    current_item_index++;
    indent(e, 4);
    fprintf(e, "%d, %d, %d, %d, 0x%x, %d%s /* Element %d. */\n",
            (int) gc_ptr->width, (int) gc_ptr->height, (int) gc_ptr->planes, (int) gc_ptr->bits,
            (unsigned int) gc_ptr->bytes, (int) gc_ptr->index,
            (gc_ptr->next != NULL ? "," : ""), current_item_index);
  }

  fprintf(e, "END\n");
}

/* Write dialog data.  */

#include <stdio.h>
#include <stdbool.h>

static bool is_res_id_present(const res_id *id)
{
  if (id == NULL)
    return false;
  return (id->named && id->u.n.length > 0) || id->u.id != 0;
}

static void
write_rc_dialog (FILE *e, const rc_dialog *dialog)
{
  const rc_dialog_control *control;

  if (e == NULL || dialog == NULL)
    {
      return;
    }

  fprintf (e, "STYLE 0x%x\n", dialog->style);

  if (dialog->exstyle != 0)
    fprintf (e, "EXSTYLE 0x%x\n", (unsigned int) dialog->exstyle);

  if (is_res_id_present(&dialog->class))
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

  if (is_res_id_present(&dialog->menu))
    {
      fprintf (e, "MENU ");
      res_id_print (e, dialog->menu, 0);
      fprintf (e, "\n");
    }

  if (dialog->font != NULL)
    {
      fprintf (e, "FONT %d, ", (int) dialog->pointsize);
      unicode_print_quoted (e, dialog->font, -1);

      const bool has_extra_font_params = (dialog->ex != NULL &&
                                          (dialog->ex->weight != 0 ||
                                           dialog->ex->italic != 0 ||
                                           dialog->ex->charset != 1));
      if (has_extra_font_params)
        {
          fprintf (e, ", %d, %d, %d",
                   (int) dialog->ex->weight,
                   (int) dialog->ex->italic,
                   (int) dialog->ex->charset);
        }
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

static const struct control_info *
get_control_info_entry(const rc_dialog_control *control)
{
  if (control->class.named)
    return NULL;

  for (const struct control_info *ci_iter = control_info; ci_iter->name != NULL; ++ci_iter)
  {
    if (ci_iter->class == control->class.u.id &&
        (ci_iter->style == (unsigned long) -1 || ci_iter->style == (control->style & 0xff)))
    {
      return ci_iter;
    }
  }
  return NULL;
}

static bool
is_text_suppressed_for_class(const struct control_info *ci)
{
  if (ci == NULL)
    return false;

  return ci->class == CTL_EDIT ||
         ci->class == CTL_COMBOBOX ||
         ci->class == CTL_LISTBOX ||
         ci->class == CTL_SCROLLBAR;
}

static void
write_rc_dialog_control (FILE *e, const rc_dialog_control *control)
{
  const struct control_info *resolved_ci = NULL;

  if (!control->class.named)
  {
    resolved_ci = get_control_info_entry(control);
  }

  fprintf (e, "  ");

  if (resolved_ci != NULL && resolved_ci->name != NULL)
  {
    fprintf (e, "%s", resolved_ci->name);
  }
  else
  {
    fprintf (e, "CONTROL");
    resolved_ci = NULL; // Explicitly nullify if it was not identified as a known type
  }

  if ((control->text.named || control->text.u.id != 0) &&
      !is_text_suppressed_for_class(resolved_ci))
    {
      fprintf (e, " ");
      res_id_print (e, control->text, 1);
      fprintf (e, ",");
    }

  fprintf (e, " %d, ", (int) control->id);

  if (resolved_ci == NULL)
    {
      if (control->class.named)
	fprintf (e, "\"");
      res_id_print (e, control->class, 0);
      if (control->class.named)
	fprintf (e, "\"");
      fprintf (e, ", 0x%x, ", (unsigned int) control->style);
    }

  fprintf (e, "%d, %d", (int) control->x, (int) control->y);

  if (control->style != SS_ICON ||
      control->exstyle != 0 ||
      control->width != 0 ||
      control->height != 0 ||
      control->help != 0)
    {
      fprintf (e, ", %d, %d", (int) control->width, (int) control->height);

      if (resolved_ci != NULL)
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
  if (e == NULL) {
    return;
  }

  const rc_fontdir *current_fontdir_entry;
  int element_count;

  const int fontdir_data_header_size = 4;
  const int fontdir_length_trailer_size = 2;

  for (element_count = 0, current_fontdir_entry = fontdir;
       current_fontdir_entry != NULL;
       current_fontdir_entry = current_fontdir_entry->next, element_count++)
    ;

  if (fprintf (e, "BEGIN\n") < 0) {
    return;
  }
  indent (e, 2);
  if (fprintf (e, "%d%s\t /* Has %d elements.  */\n", element_count, (element_count != 0 ? "," : ""), element_count) < 0) {
    return;
  }

  int entry_number = 1;
  for (current_fontdir_entry = fontdir;
       current_fontdir_entry != NULL;
       current_fontdir_entry = current_fontdir_entry->next, entry_number++)
    {
      indent (e, 4);
      if (fprintf (e, "%d,\t/* Font no %d with index %d.  */\n",
                   (int) current_fontdir_entry->index, entry_number, (int) current_fontdir_entry->index) < 0) {
        return;
      }

      rc_uint_type data_block_length = 0;
      if (current_fontdir_entry->length > fontdir_length_trailer_size) {
          data_block_length = current_fontdir_entry->length - fontdir_length_trailer_size;
      }

      const bfd_byte *data_block_ptr = NULL;
      if (current_fontdir_entry->data != NULL) {
          data_block_ptr = (const bfd_byte *) current_fontdir_entry->data + fontdir_data_header_size;
      }

      write_rc_datablock (e, data_block_length,
                          data_block_ptr,
                          current_fontdir_entry->next != NULL,
                          0, 0);
    }

  if (fprintf (e, "END\n") < 0) {
    return;
  }
}

/* Write out group icon data.  This would normally be built from the
   icon data.  */

#define RC_GROUP_ICON_DEFAULT_PAD 0

static void
write_rc_group_icon (FILE *e, const rc_group_icon *group_icon)
{
  if (e == NULL)
    {
      return;
    }

  const rc_group_icon *gi_current;
  int count;

  count = 0;
  for (gi_current = group_icon; gi_current != NULL; gi_current = gi_current->next)
    {
      count++;
    }

  fprintf (e, "BEGIN\n");
  indent (e, 2);
  fprintf (e, " 0, 1, %d%s\t /* Has %d elements.  */\n", count, (count != 0 ? "," : ""), count);

  indent (e, 4);
  fprintf (e, "/* \"width height colors pad\", planes, bits, bytes, index.  */\n");

  int element_num = 1;
  for (gi_current = group_icon; gi_current != NULL; gi_current = gi_current->next)
    {
      indent (e, 4);
      fprintf (e, "\"\\%03o\\%03o\\%03o\\%03o\", %d, %d, 0x%xL, %d%s\t/* Element no %d.  */\n",
	       gi_current->width,
	       gi_current->height,
	       gi_current->colors,
	       RC_GROUP_ICON_DEFAULT_PAD,
	       (int) gi_current->planes,
	       (int) gi_current->bits,
	       (unsigned int) gi_current->bytes,
	       (int) gi_current->index,
	       (gi_current->next != NULL ? "," : ""),
	       element_num);
      element_num++;
    }
  fprintf (e, "END\n");
}

/* Write out a menu resource.  */

static void
write_rc_menu (FILE *e, const rc_menu *menu, int menuex)
{
  if (e == NULL || menu == NULL) {
    return;
  }

  if (menu->help != 0) {
    if (fprintf (e, "// Help ID: %u\n", (unsigned int) menu->help) < 0) {
      return;
    }
  }

  write_rc_menuitems (e, menu->items, menuex, 0);
}

static int
write_rc_toolbar (FILE *e, const rc_toolbar *tb)
{
  if (e == NULL || tb == NULL) {
    return -1; // Indicate error for null input pointers
  }

  rc_toolbar_item *it;

  if (indent (e, 0) < 0) {
    return -1; // Propagate error from indent
  }
  if (fprintf (e, "BEGIN\n") < 0) {
    return -1; // Propagate error from fprintf
  }

  it = tb->items;
  while(it != NULL)
  {
    if (indent (e, 2) < 0) {
      return -1; // Propagate error from indent
    }
    if (it->id.u.id == 0) {
      if (fprintf (e, "SEPARATOR\n") < 0) {
        return -1; // Propagate error from fprintf
      }
    } else {
      if (fprintf (e, "BUTTON %d\n", (int) it->id.u.id) < 0) {
        return -1; // Propagate error from fprintf
      }
    }
    it = it->next;
  }

  if (indent (e, 0) < 0) {
    return -1; // Propagate error from indent
  }
  if (fprintf (e, "END\n") < 0) {
    return -1; // Propagate error from fprintf
  }

  return 0; // Indicate success
}

/* Write out menuitems.  */

static void
write_rc_menuitems (FILE *e, const rc_menuitem *menuitems, int menuex,
		    int ind)
{
  const rc_menuitem *mi;
  const int current_indent = ind + 2;

  indent (e, ind);
  fprintf (e, "BEGIN\n");

  for (mi = menuitems; mi != NULL; mi = mi->next)
    {
      indent (e, current_indent);

      const char *item_keyword = (mi->popup == NULL) ? "MENUITEM" : "POPUP";
      fprintf (e, "%s", item_keyword);

      int is_separator = (!menuex
                          && mi->popup == NULL
                          && mi->text == NULL
                          && mi->type == 0
                          && mi->id == 0);

      if (is_separator)
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
	  /*
	   * For 'menuex' mode, parameters (id, type, state, help) are printed
	   * if they are non-zero, OR if any subsequent parameter is non-zero.
	   * This ensures leading zeros are printed if a later parameter is
	   * present and non-zero, but trailing zeros are omitted.
	   */
	  int has_type_or_subsequent  = (mi->type != 0 || mi->state != 0 || mi->help != 0);
	  int has_state_or_subsequent = (mi->state != 0 || mi->help != 0);
	  int has_help_param          = (mi->help != 0);

	  if (mi->id != 0 || has_type_or_subsequent)
	    {
	      fprintf (e, ", %d", (int) mi->id);
	      if (mi->type != 0 || has_state_or_subsequent)
		{
		  fprintf (e, ", %u", (unsigned int) mi->type);
		  if (mi->state != 0 || has_help_param)
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
	write_rc_menuitems (e, mi->popup, menuex, current_indent);
    }

  indent (e, ind);
  fprintf (e, "END\n");
}

#include <stdbool.h>

static bool
test_rc_datablock_unicode (rc_uint_type length, const bfd_byte *data)
{
  if ((length & 1) != 0)
    return false;

  for (rc_uint_type i = 0; i < length; i += 2)
    {
      const bfd_byte current_byte1 = data[i];
      const bfd_byte current_byte2 = data[i + 1];

      if (current_byte1 == 0xff && current_byte2 == 0xff)
        return false;

      if (current_byte1 == 0x00 && current_byte2 == 0x00 && (i + 2) < length)
        return false;
    }
  return true;
}

static int is_acceptable_byte_in_block(const bfd_byte *data, rc_uint_type current_index, rc_uint_type total_length);

static int
test_rc_datablock_text (rc_uint_type length, const bfd_byte *data)
{
  if (length <= 1)
    return 0;

  rc_uint_type undesirable_char_count = 0;
  int has_newline = 0;
  rc_uint_type i;

  for (i = 0; i < length; ++i)
    {
      if (!is_acceptable_byte_in_block(data, i, length))
        {
          if (data[i] > 0 && data[i] <= 7)
            return 0;
          undesirable_char_count++;
        }
      else if (data[i] == '\n')
        {
          has_newline++;
        }
    }

  const rc_uint_type MAX_LINE_LENGTH_WITHOUT_NL = 80;
  const rc_uint_type UNDESIRABLE_CHAR_THRESHOLD = 150;
  const rc_uint_type RATIO_MULTIPLIER = 10000;
  const rc_uint_type LENGTH_SCALER = 100;

  if (length > MAX_LINE_LENGTH_WITHOUT_NL && !has_newline)
    return 0;

  rc_uint_type ratio_numerator_term1 = undesirable_char_count * RATIO_MULTIPLIER;
  rc_uint_type ratio_numerator_term2 = length / LENGTH_SCALER;
  rc_uint_type ratio_numerator;

  ratio_numerator = ratio_numerator_term1 + ratio_numerator_term2;
  ratio_numerator -= 1; 

  rc_uint_type ratio_val = ratio_numerator / length;

  if (ratio_val >= UNDESIRABLE_CHAR_THRESHOLD)
    return 0;

  return 1;
}

static int
is_acceptable_byte_in_block(const bfd_byte *data, rc_uint_type current_index, rc_uint_type total_length)
{
  const bfd_byte current_char = data[current_index];

  if (ISPRINT(current_char))
    return 1;

  if (current_char == '\n')
    return 1;

  if (current_char == '\t')
    return 1;

  if (current_char == '\r' && (current_index + 1) < total_length && data[current_index + 1] == '\n')
    return 1;

  if (current_char == 0 && (current_index + 1) == total_length)
    return 1;

  return 0;
}

static void
write_rc_messagetable (FILE *e, rc_uint_type length, const bfd_byte *data)
{
  fprintf (e, "BEGIN\n");
  write_rc_datablock (e, length, data, 0, 0, 0);
  fprintf (e, "\n");
  wr_printcomment (e, "MC syntax dump");

  // Initial validation: data must be at least the size of the message table header.
  if (length < BIN_MESSAGETABLE_SIZE)
    goto error_exit;

  // Cast `data` to the message table structure.
  const struct bin_messagetable *mt = (const struct bin_messagetable *) data;

  // Read the count of message blocks.
  rc_uint_type m = target_get_32 (mt->cblocks, length);

  // Validate the total expected size for all message blocks to prevent buffer overflows.
  // We need BIN_MESSAGETABLE_SIZE + m * BIN_MESSAGETABLE_BLOCK_SIZE <= length.
  // This is equivalent to m * BIN_MESSAGETABLE_BLOCK_SIZE <= length - BIN_MESSAGETABLE_SIZE.

  // First, calculate the maximum space available for message blocks after the header.
  // This check also implicitly handles `length < BIN_MESSAGETABLE_SIZE` again defensively.
  rc_uint_type remaining_length_for_blocks;
  if (length < BIN_MESSAGETABLE_SIZE)
    goto error_exit;
  remaining_length_for_blocks = length - BIN_MESSAGETABLE_SIZE;

  // Check for multiplication overflow and if `m * BIN_MESSAGETABLE_BLOCK_SIZE`
  // would exceed the `remaining_length_for_blocks`.
  // Assumes BIN_MESSAGETABLE_BLOCK_SIZE is a positive constant.
  if (BIN_MESSAGETABLE_BLOCK_SIZE > 0 && m > remaining_length_for_blocks / BIN_MESSAGETABLE_BLOCK_SIZE)
    goto error_exit;

  // The total `BIN_MESSAGETABLE_SIZE + m * BIN_MESSAGETABLE_BLOCK_SIZE` is now guaranteed
  // to not overflow and be less than or equal to `length`.

  // Iterate through each message block.
  for (rc_uint_type i = 0; i < m; i++)
    {
      // Access message item fields. These reads are implicitly covered by the previous total length check.
      rc_uint_type low = windres_get_32 (&wrtarget, mt->items[i].lowid);
      rc_uint_type high = windres_get_32 (&wrtarget, mt->items[i].highid);
      rc_uint_type offset = windres_get_32 (&wrtarget, mt->items[i].offset);

      // Iterate through messages within the current block (from low to high IDs).
      while (low <= high)
        {
          const struct bin_messagetable_item *mti;
          rc_uint_type elen, flags;

          // Validate that the message item header itself is within bounds.
          // Check for `offset` being out of bounds, and then if `offset + BIN_MESSAGETABLE_ITEM_SIZE` fits.
          if (offset >= length)
            goto error_exit;
          if (BIN_MESSAGETABLE_ITEM_SIZE > length - offset) // Checks for (offset + BIN_MESSAGETABLE_ITEM_SIZE) overflow AND bounds
            goto error_exit;

          mti = (const struct bin_messagetable_item *) &data[offset];

          // Safely read element length and flags. These reads are covered by the previous `BIN_MESSAGETABLE_ITEM_SIZE` check.
          elen = windres_get_16 (&wrtarget, mti->length);
          flags = windres_get_16 (&wrtarget, mti->flags);

          // Validate that the full message item (header + data) is within bounds.
          // `elen` must be at least the size of the header, otherwise `data_len` would be invalid.
          // Check for `elen` itself being excessively large or `offset + elen` overflow/bounds.
          if (elen < BIN_MESSAGETABLE_ITEM_SIZE || elen > length) // `elen > length` check ensures `length - offset` is safe below.
            goto error_exit;
          if (elen > length - offset) // Checks for (offset + elen) overflow AND bounds
            goto error_exit;

          wr_printcomment (e, "MessageId = 0x%x", low);
          wr_printcomment (e, "");

          rc_uint_type data_len = elen - BIN_MESSAGETABLE_ITEM_SIZE;

          if ((flags & MESSAGE_RESOURCE_UNICODE) == MESSAGE_RESOURCE_UNICODE)
            {
              // Replicate original `elen > BIN_MESSAGETABLE_ITEM_SIZE * 2` behavior,
              // which translates to `data_len > BIN_MESSAGETABLE_ITEM_SIZE`.
              // Also ensure `data_len` is even for Unicode characters.
              if (data_len > BIN_MESSAGETABLE_ITEM_SIZE && (data_len % 2 == 0))
                unicode_print (e, (const unichar *) mti->data, data_len / 2);
            }
          else
            {
              // Replicate original `elen > BIN_MESSAGETABLE_ITEM_SIZE` behavior,
              // which translates to `data_len > 0`.
              if (data_len > 0)
                ascii_print (e, (const char *) mti->data, data_len);
            }

          wr_printcomment (e, "");
          ++low;       // Move to the next message ID.
          offset += elen; // Advance `offset` by the current message item's total length.
        }
    }

  // Normal successful exit path.
  wr_print_flush (e);
  fprintf (e, "END\n");
  return;

error_exit:
  // Error handling path: print "Illegal data" and then flush and print "END".
  wr_printcomment (e, "Illegal data");
  wr_print_flush (e);
  fprintf (e, "END\n");
}

#include <stdio.h> // For FILE, fprintf
// Assume rc_uint_type, bfd_byte, unichar are defined globally or in an appropriate header.
// Assume indent, test_rc_datablock_text, test_rc_datablock_unicode,
// ascii_print, unicode_print, target_get_32, target_get_16 are declared elsewhere.

#ifndef HEX_FIELD_MAX_WIDTH
#define HEX_FIELD_MAX_WIDTH 11 // Max width for "0xDEADBEEFL" or similar hex representations
#endif
#ifndef MAX_STRING_LINE_CHARS
#define MAX_STRING_LINE_CHARS 160 // Maximum characters per line for string output
#endif
#ifndef BYTES_PER_DWORD
#define BYTES_PER_DWORD 4 // Size of a double-word in bytes
#endif
#ifndef BYTES_PER_WORD
#define BYTES_PER_WORD 2 // Size of a word in bytes
#endif
#ifndef BYTES_PER_BYTE
#define BYTES_PER_BYTE 1 // Size of a byte in bytes
#endif
#ifndef HEX_VALUES_PER_ROW_WITH_COMMENT
#define HEX_VALUES_PER_ROW_WITH_COMMENT 4 // Number of hex values per row when comments are shown
#endif
#ifndef HEX_VALUES_PER_ROW_WITHOUT_COMMENT
#define HEX_VALUES_PER_ROW_WITHOUT_COMMENT 8 // Number of hex values per row when no comments
#endif

// Helper function to print string data (either ASCII or Unicode) line by line.
// Returns 1 if data was printed as string, 0 otherwise (though in this context it always returns 1).
static int
print_string_lines(FILE *e, rc_uint_type length, const bfd_byte *data,
                   int char_byte_size, // 1 for ASCII, 2 for Unicode
                   void (*printer_func)(FILE *, const void *, rc_uint_type),
                   const char *string_prefix) // e.g., "" for ASCII, "L" for Unicode
{
  // Handle empty string case
  if (length == 0)
    {
      indent(e, 2);
      fprintf(e, "%s\"\"", string_prefix ? string_prefix : "");
      return 1;
    }

  rc_uint_type current_data_offset = 0;
  while (current_data_offset < length)
    {
      indent(e, 2);
      fprintf(e, "%s\"", string_prefix ? string_prefix : "");

      rc_uint_type line_segment_start_offset = current_data_offset;
      rc_uint_type chars_in_segment = 0;
      const void *segment_ptr = &data[line_segment_start_offset];

      // Loop to find end of line or max chars for this segment
      while (current_data_offset < length && chars_in_segment < MAX_STRING_LINE_CHARS)
        {
          if (char_byte_size == BYTES_PER_BYTE) // ASCII
            {
              if (data[current_data_offset] == '\n')
                {
                  current_data_offset += char_byte_size;
                  chars_in_segment++; // Include newline character in count
                  break; // End of line
                }
            }
          else if (char_byte_size == BYTES_PER_WORD) // Unicode
            {
              const unichar *u_ptr = (const unichar *)segment_ptr;
              if (u_ptr[chars_in_segment] == (unichar)'\n')
                {
                  current_data_offset += char_byte_size;
                  chars_in_segment++; // Include newline character in count
                  break; // End of line
                }
            }
          current_data_offset += char_byte_size;
          chars_in_segment++;
        }

      printer_func(e, segment_ptr, chars_in_segment);
      fprintf(e, "\"");
      if (current_data_offset < length) // If there are more characters in the overall data, print a newline for this string segment
        fprintf(e, "\n");
    }
  return 1;
}

static void
write_rc_datablock (FILE *e, rc_uint_type length, const bfd_byte *data,
		    int has_next, int hasblock, int show_comment)
{
  // Basic error handling: if file pointer is invalid, do nothing.
  if (e == NULL)
    return;

  if (hasblock)
    fprintf (e, "BEGIN\n");

  // Attempt to print data as string (ASCII or Unicode) if show_comment == -1
  if (show_comment == -1)
    {
      int printed_as_string = 0;

      if (test_rc_datablock_text(length, data))
	{
	  printed_as_string = print_string_lines(e, length, data, BYTES_PER_BYTE,
						 (void (*)(FILE *, const void *, rc_uint_type))ascii_print,
						 ""); // No prefix for ASCII string segments
	}
      else if (test_rc_datablock_unicode(length, data))
	{
	  printed_as_string = print_string_lines(e, length, data, BYTES_PER_WORD,
						 (void (*)(FILE *, const void *, rc_uint_type))unicode_print,
						 "L"); // "L" prefix for wide string segments
	}

      if (printed_as_string)
	{
	  if (has_next)
	    fprintf (e, ",");
	  fprintf (e, "\n");
	  if (hasblock)
	    fprintf (e, "END\n");
	  return;
	}

      // If not printed as string, fallback to raw data printing
      show_comment = 0;
    }

  // Handle raw data printing (hex values)
  if (length != 0)
    {
      rc_uint_type current_offset = 0;
      int is_first_line_of_block = 1;

      const rc_uint_type hex_values_per_row = (show_comment ? HEX_VALUES_PER_ROW_WITH_COMMENT : HEX_VALUES_PER_ROW_WITHOUT_COMMENT);

      // Process 4-byte (DWORD) data units
      while (current_offset + BYTES_PER_DWORD <= length)
	{
	  if (!is_first_line_of_block)
	    indent (e, 2);

	  rc_uint_type comment_start_offset = current_offset;
	  rc_uint_type values_printed_on_row = 0;

	  for (; values_printed_on_row < hex_values_per_row && current_offset + BYTES_PER_DWORD <= length;
	       values_printed_on_row++, current_offset += BYTES_PER_DWORD)
	    {
	      int printed_len;
	      if (values_printed_on_row == 0)
		printed_len = fprintf (e, "0x%lxL",
				       (unsigned long) target_get_32 (data + current_offset,
								      length - current_offset));
	      else
		printed_len = fprintf (e, " 0x%lxL",
				       (unsigned long) target_get_32 (data + current_offset,
								      length - current_offset)) - 1; // Subtract 1 for the leading space

	      // Print comma and pad if there are more items on this row, or more data in general
	      if (has_next || (current_offset + BYTES_PER_DWORD < length) || (values_printed_on_row + 1 < hex_values_per_row))
		{
		  if (printed_len > 0 && printed_len < HEX_FIELD_MAX_WIDTH)
		    indent (e, HEX_FIELD_MAX_WIDTH - printed_len);
		  fprintf (e, ",");
		}
	    }

	  if (show_comment)
	    {
	      fprintf (e, "\t/* ");
	      ascii_print (e, (const char *) &data[comment_start_offset],
			   current_offset - comment_start_offset); // Comment for bytes processed in this row
	      fprintf (e, ".  */");
	    }
	  fprintf (e, "\n");
	  is_first_line_of_block = 0;
	}

      // Handle remaining 2-byte (WORD) data unit (if any)
      if (current_offset + BYTES_PER_WORD <= length)
	{
	  if (!is_first_line_of_block)
	    indent (e, 2);
	  int printed_len = fprintf (e, "0x%x",
				     (int) target_get_16 (data + current_offset,
							  length - current_offset));
	  if (has_next || (current_offset + BYTES_PER_WORD < length))
	    {
	      if (printed_len > 0 && printed_len < HEX_FIELD_MAX_WIDTH)
		indent (e, HEX_FIELD_MAX_WIDTH - printed_len);
	      fprintf (e, ",");
	    }
	  if (show_comment)
	    {
	      fprintf (e, "\t/* ");
	      ascii_print (e, (const char *) &data[current_offset], BYTES_PER_WORD);
	      fprintf (e, ".  */");
	    }
	  fprintf (e, "\n");
	  current_offset += BYTES_PER_WORD;
	  is_first_line_of_block = 0;
	}

      // Handle remaining 1-byte data unit (if any)
      if (current_offset < length)
	{
	  if (!is_first_line_of_block)
	    indent (e, 2);
	  fprintf (e, "\"");
	  ascii_print (e, (const char *) &data[current_offset], BYTES_PER_BYTE);
	  fprintf (e, "\"");
	  if (has_next) // This is the very last data unit, so only has_next dictates a trailing comma
	    fprintf (e, ",");
	  fprintf (e, "\n");
	  current_offset += BYTES_PER_BYTE;
	}
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

  /* Check for NULL file pointer to prevent dereferencing issues. */
  if (e == NULL)
    {
      return;
    }

  indent (e, ind);
  /* Check fprintf return value for critical framing output. */
  if (fprintf (e, "BEGIN\n") < 0)
    {
      return;
    }

  for (ri = rcdata; ri != NULL; ri = ri->next)
    {
      /* Skip empty buffers as per original logic. */
      if (ri->type == RCDATA_BUFFER && ri->u.buffer.length == 0)
	continue;

      switch (ri->type)
	{
	default:
	  /* Retain original behavior for unhandled types. */
	  abort ();

	case RCDATA_WORD:
	  indent (e, ind + 2);
	  /* fprintf failures for intermediate items are not explicitly handled
	     with a return here to maintain the void function's original external
	     error handling (or lack thereof, relying on ferror for caller). */
	  fprintf (e, "%ld", (long) (ri->u.word & 0xffff));
	  break;

	case RCDATA_DWORD:
	  indent (e, ind + 2);
	  fprintf (e, "%luL", (unsigned long) ri->u.dword);
	  break;

	case RCDATA_STRING:
	  indent (e, ind + 2);
	  fprintf (e, "\"");
	  /* Assume ascii_print handles its own errors or is guaranteed not to fail. */
	  ascii_print (e, ri->u.string.s, ri->u.string.length);
	  fprintf (e, "\"");
	  break;

	case RCDATA_WSTRING:
	  indent (e, ind + 2);
	  fprintf (e, "L\"");
	  /* Assume unicode_print handles its own errors or is guaranteed not to fail. */
	  unicode_print (e, ri->u.wstring.w, ri->u.wstring.length);
	  fprintf (e, "\"");
	  break;

	case RCDATA_BUFFER:
	  /* Assume write_rc_datablock handles its own output formatting and errors. */
	  write_rc_datablock (e, (rc_uint_type) ri->u.buffer.length,
			      (const bfd_byte *) ri->u.buffer.data,
			      ri->next != NULL, 0, -1);
	  break;
	}

      /* Apply comma and newline formatting for non-buffer types. */
      if (ri->type != RCDATA_BUFFER)
	{
	  if (ri->next != NULL)
	    fprintf (e, ",");
	  fprintf (e, "\n");
	}
    }

  indent (e, ind);
  /* Check fprintf return value for critical framing output. */
  if (fprintf (e, "END\n") < 0)
    {
      return;
    }
}

/* Write out a stringtable resource.  */

static void
write_rc_stringtable (FILE *e, const rc_res_id *name,
		      const rc_stringtable *stringtable)
{
  rc_uint_type offset;
  const char *comment_message = NULL;

  if (name != NULL && !name->named)
    {
      offset = (name->u.id - 1) << 4;
    }
  else
    {
      comment_message = (name == NULL) ? "Missing" : "Invalid";
      offset = 0;
    }

  if (comment_message != NULL)
    {
      fprintf (e, "/* %s string table name.  */\n", comment_message);
    }

  fprintf (e, "BEGIN\n");

  for (int i = 0; i < 16; i++)
    {
      if (stringtable->strings[i].length != 0)
	{
	  const rc_string_entry *current_entry = &stringtable->strings[i];
	  fprintf (e, "  %lu, ", (unsigned long)(offset + i));
	  unicode_print_quoted (e, current_entry->string,
				current_entry->length);
	  fprintf (e, "\n");
	}
    }

  fprintf (e, "END\n");
}

/* Write out a versioninfo resource.  */

static void
print_version_quad (FILE *e, const char *label, unsigned int ms, unsigned int ls)
{
  if (ms != 0 || ls != 0)
    {
      fprintf (e, " %s %u, %u, %u, %u\n", label,
               (unsigned int) ((ms >> 16) & 0xffff),
               (unsigned int) (ms & 0xffff),
               (unsigned int) ((ls >> 16) & 0xffff),
               (unsigned int) (ls & 0xffff));
    }
}

static void
print_hex_field (FILE *e, const char *label, unsigned int value)
{
  if (value != 0)
    {
      fprintf (e, " %s 0x%x\n", label, value);
    }
}

static void
write_string_file_info_block (FILE *e, const rc_ver_stringtable *stringtables)
{
  fprintf (e, "  BLOCK \"StringFileInfo\"\n");
  fprintf (e, "  BEGIN\n");

  for (const rc_ver_stringtable *vst = stringtables; vst != NULL; vst = vst->next)
    {
      fprintf (e, "    BLOCK ");
      unicode_print_quoted (e, vst->language, -1);
      fprintf (e, "\n");
      fprintf (e, "    BEGIN\n");

      for (const rc_ver_stringinfo *vs = vst->strings; vs != NULL; vs = vs->next)
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
write_var_file_info_block (FILE *e, const WCHAR *key, const rc_ver_varinfo *vars)
{
  fprintf (e, "  BLOCK \"VarFileInfo\"\n");
  fprintf (e, "  BEGIN\n");
  fprintf (e, "    VALUE ");
  unicode_print_quoted (e, key, -1);

  for (const rc_ver_varinfo *vv = vars; vv != NULL; vv = vv->next)
    {
      fprintf (e, ", 0x%x, %d", (unsigned int) vv->language, (int) vv->charset);
    }
  fprintf (e, "\n  END\n");
}

static void
write_rc_versioninfo (FILE *e, const rc_versioninfo *versioninfo)
{
  const rc_fixed_versioninfo *f = versioninfo->fixed;

  print_version_quad (e, "FILEVERSION", f->file_version_ms, f->file_version_ls);
  print_version_quad (e, "PRODUCTVERSION", f->product_version_ms, f->product_version_ls);

  print_hex_field (e, "FILEFLAGSMASK", f->file_flags_mask);
  print_hex_field (e, "FILEFLAGS", f->file_flags);
  print_hex_field (e, "FILEOS", f->file_os);
  print_hex_field (e, "FILETYPE", f->file_type);
  print_hex_field (e, "FILESUBTYPE", f->file_subtype);

  if (f->file_date_ms != 0 || f->file_date_ls != 0)
    {
      fprintf (e, "/* Date: %u, %u.  */\n",
               (unsigned int) f->file_date_ms, (unsigned int) f->file_date_ls);
    }

  fprintf (e, "BEGIN\n");

  for (const rc_ver_info *vi = versioninfo->var; vi != NULL; vi = vi->next)
    {
      switch (vi->type)
        {
        case VERINFO_STRING:
          write_string_file_info_block (e, vi->u.string.stringtables);
          break;
        case VERINFO_VAR:
          write_var_file_info_block (e, vi->u.var.key, vi->u.var.var);
          break;
        }
    }

  fprintf (e, "END\n");
}

static rc_uint_type
rcdata_copy (const rc_rcdata_item *src, bfd_byte *dst)
{
  rc_uint_type size = 0;

  if (!src)
    return 0;

  switch (src->type)
    {
    case RCDATA_WORD:
      size = 2;
      if (dst)
	windres_put_16 (&wrtarget, dst, (rc_uint_type) src->u.word);
      break;
    case RCDATA_DWORD:
      size = 4;
      if (dst)
	windres_put_32 (&wrtarget, dst, (rc_uint_type) src->u.dword);
      break;
    case RCDATA_STRING:
      size = (rc_uint_type) src->u.string.length;
      if (dst && size > 0)
	memcpy (dst, src->u.string.s, size);
      break;
    case RCDATA_WSTRING:
      size = (rc_uint_type) (src->u.wstring.length * sizeof (unichar));
      if (dst && size > 0)
	memcpy (dst, src->u.wstring.w, size);
      break;
    case RCDATA_BUFFER:
      size = (rc_uint_type) src->u.buffer.length;
      if (dst && size > 0)
	memcpy (dst, src->u.buffer.data, size);
      break;
    default:
      abort ();
    }
  return size;
}
