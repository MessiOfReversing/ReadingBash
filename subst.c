localhost:~/bash# cat subst.c
/* subst.c -- The part of the shell that does parameter, command, arithmetic,
   and globbing substitutions. */

/* ``Have a little faith, there's magic in the night.  You ain't a
     beauty, but, hey, you're alright.'' */

/* Copyright (C) 1987-2025 Free Software Foundation, Inc.

   This file is part of GNU Bash, the Bourne Again SHell.

   Bash is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   Bash is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with Bash.  If not, see <http://www.gnu.org/licenses/>.
*/

#include "config.h"

#include "bashtypes.h"
#include <stdio.h>
#include "chartypes.h"
#if defined (HAVE_PWD_H)
#  include <pwd.h>
#endif
#include <signal.h>
#include <errno.h>

#if defined (HAVE_UNISTD_H)
#  include <unistd.h>
#endif

#define NEED_FPURGE_DECL

#include "bashansi.h"
#include "posixstat.h"
#include "bashintl.h"

#ifdef __CYGWIN__
#  define NEED_SH_SETLINEBUF_DECL
#endif

#include "shell.h"
#include "parser.h"
#include "redir.h"
#include "flags.h"
#include "jobs.h"
#include "execute_cmd.h"
#include "builtins.h"
#include "filecntl.h"
#include "trap.h"
#include "pathexp.h"
#include "mailcheck.h"

#include "shmbutil.h"
#if defined (HAVE_MBSTR_H) && defined (HAVE_MBSCHR)
#  include <mbstr.h>            /* mbschr */
#endif
#include "typemax.h"

#include "builtins/getopt.h"
#include "builtins/common.h"

#include "builtins/builtext.h"

#include <tilde/tilde.h>
#include <glob/strmatch.h>

#if !defined (errno)
extern int errno;
#endif /* !errno */

/* The size that strings change by. */
#define DEFAULT_INITIAL_ARRAY_SIZE 112
#define DEFAULT_ARRAY_SIZE 128

/* Variable types. */
#define VT_VARIABLE     0
#define VT_POSPARMS     1
#define VT_ARRAYVAR     2
#define VT_ARRAYMEMBER  3
#define VT_ASSOCVAR     4

#define VT_STARSUB      128     /* $* or ${array[*]} -- used to split */

/* Flags for quoted_strchr */
#define ST_BACKSL       0x01
#define ST_CTLESC       0x02
#define ST_SQUOTE       0x04    /* unused yet */
#define ST_DQUOTE       0x08    /* unused yet */

/* These defs make it easier to use the editor. */
#define LBRACE          '{'
#define RBRACE          '}'
#define LPAREN          '('
#define RPAREN          ')'
#define LBRACK          '['
#define RBRACK          ']'

#if defined (HANDLE_MULTIBYTE)
#define WLPAREN         L'('
#define WRPAREN         L')'
#endif

#define DOLLAR_AT_STAR(c)       ((c) == '@' || (c) == '*')
#define STR_DOLLAR_AT_STAR(s)   (DOLLAR_AT_STAR ((s)[0]) && (s)[1] == '\0')

/* Evaluates to 1 if C is one of the shell's special parameters whose length
   can be taken, but is also one of the special expansion characters. */
#define VALID_SPECIAL_LENGTH_PARAM(c) \
  ((c) == '-' || (c) == '?' || (c) == '#' || (c) == '@')

/* Evaluates to 1 if C is one of the shell's special parameters for which an
   indirect variable reference may be made. */
#define VALID_INDIR_PARAM(c) \
  ((posixly_correct == 0 && (c) == '#') || (posixly_correct == 0 && (c) == '?') || (c) == '@' || (c) == '*')

/* Evaluates to 1 if C is one of the OP characters that follows the parameter
   in ${parameter[:]OPword}. */
#define VALID_PARAM_EXPAND_CHAR(c) (sh_syntaxtab[(unsigned char)c] & CSUBSTOP)
/* Evaluates to 1 if this is one of the shell's special variables. */
#define SPECIAL_VAR(name, wi) \
 (*name && ((DIGIT (*name) && all_digits (name)) || \
      (name[1] == '\0' && (sh_syntaxtab[(unsigned char)*name] & CSPECVAR)) || \
      (wi && name[2] == '\0' && VALID_INDIR_PARAM (name[1]))))

/* This can be used by all of the *_extract_* functions that have a similar
   structure.  It can't just be wrapped in a do...while(0) loop because of
   the embedded `break'. The dangling else accommodates a trailing semicolon;
   we could also put in a do ; while (0) */

#define CHECK_STRING_OVERRUN(oind, ind, len, ch) \
  if (ind >= len) \
    { \
      oind = len; \
      ch = 0; \
      break; \
    } \
  else \

/* An expansion function that takes a string and a quoted flag and returns
   a WORD_LIST *.  Used as the type of the third argument to
   expand_string_if_necessary(). */
typedef WORD_LIST *EXPFUNC (const char *, int);

/* Process ID of the last command executed within command substitution. */
pid_t last_command_subst_pid = NO_PID;
pid_t current_command_subst_pid = NO_PID;
int last_command_subst_status = 0;

/* Variables used to keep track of the characters in IFS. */
SHELL_VAR *ifs_var;
char *ifs_value;
unsigned char ifs_cmap[UCHAR_MAX + 1];
int ifs_is_set, ifs_is_null;

#if defined (HANDLE_MULTIBYTE)
unsigned char ifs_firstc[MB_LEN_MAX];
size_t ifs_firstc_len;
#else
unsigned char ifs_firstc;
#endif

/* If non-zero, command substitution inherits the value of errexit option */
int inherit_errexit = 0;

/* Sentinel to tell when we are performing variable assignments preceding a
   command name and putting them into the environment.  Used to make sure
   we use the temporary environment when looking up variable values. */
int assigning_in_environment;

/* Used to hold a list of variable assignments preceding a command.  Global
   so the SIGCHLD handler in jobs.c can unwind-protect it when it runs a
   SIGCHLD trap and so it can be saved and restored by the trap handlers. */
WORD_LIST *subst_assign_varlist = (WORD_LIST *)NULL;

/* Tell the expansion functions to not longjmp back to top_level on fatal
   errors.  Enabled when doing completion and prompt string expansion. */
int no_longjmp_on_fatal_error = 0;

/* Non-zero means to allow unmatched globbed filenames to expand to
   a null file. */
int allow_null_glob_expansion;

/* Non-zero means to throw an error when globbing fails to match anything. */
int fail_glob_expansion;

/* If non-zero, perform `&' substitution on the replacement string in the
   pattern substitution word expansion. */
int patsub_replacement = PATSUB_REPLACE_DEFAULT;

/* Are we executing a ${ command; } nofork comsub? */
int executing_funsub = 0;

/* Extern functions and variables from different files. */
extern struct fd_bitmap *current_fds_to_close;
extern int wordexp_only;
extern int singlequote_translations;
extern int extended_quote;

extern REDIRECT *exec_redirection_undo_list, *redirection_undo_list;

#if !defined (HAVE_WCSDUP) && defined (HANDLE_MULTIBYTE)
extern wchar_t *wcsdup (const wchar_t *);
#endif

#if 0
/* Variables to keep track of which words in an expanded word list (the
   output of expand_word_list_internal) are the result of globbing
   expansions.  GLOB_ARGV_FLAGS is used by execute_cmd.c.
   (CURRENTLY UNUSED). */
char *glob_argv_flags;
static int glob_argv_flags_size;
#endif

static WORD_LIST *cached_quoted_dollar_at = 0;

/* Distinguished error values to return from expansion functions */
static WORD_LIST expand_word_error, expand_word_fatal;
static WORD_DESC expand_wdesc_error, expand_wdesc_fatal;
static char expand_param_error, expand_param_fatal, expand_param_unset;
static char extract_string_error, extract_string_fatal;

/* Set by expand_word_unsplit and several of the expand_string_XXX functions;
   used to inhibit splitting and re-joining $* on $IFS, primarily when doing
   assignment statements.  The idea is that if we're in a context where this
   is set, we're not going to be performing word splitting, so we use the same
   rules to expand $* as we would if it appeared within double quotes. */
static int expand_no_split_dollar_star = 0;

/* A WORD_LIST of words to be expanded by expand_word_list_internal,
   without any leading variable assignments. */
static WORD_LIST *garglist = (WORD_LIST *)NULL;

static char *quoted_substring (char *, int, int);
static int quoted_strlen (char *);
static char *quoted_strchr (char *, int, int);

static char *expand_string_if_necessary (char *, int, EXPFUNC *);
static inline char *expand_string_to_string_internal (char *, int, EXPFUNC *);
static WORD_LIST *call_expand_word_internal (WORD_DESC *, int, int, int *, int *);
static WORD_LIST *expand_string_internal (const char *, int);
static WORD_LIST *expand_string_leave_quoted (const char *, int);
static WORD_LIST *expand_string_for_rhs (const char *, int, int, int, int *, int *);
static WORD_LIST *expand_string_for_pat (const char *, int, int *, int *);

static char *quote_escapes_internal (const char *, int);

static char *quote_ifs (const char *);
static WORD_LIST *list_quote_ifs (WORD_LIST *);

static WORD_LIST *list_quote_escapes (WORD_LIST *);
static WORD_LIST *list_dequote_escapes (WORD_LIST *);

static char *make_quoted_char (int);
static WORD_LIST *quote_list (WORD_LIST *);

static int unquoted_substring (const char *, const char *);
static int unquoted_member (int, const char *);

#if defined (ARRAY_VARS)
static SHELL_VAR *do_compound_assignment (const char *, char *, int);
#endif
static int do_assignment_internal (const WORD_DESC *, int);

static char *string_extract_verbatim (const char *, size_t, size_t *, char *, int);
static char *string_extract (const char *, size_t *, const char *, int);
static char *string_extract_double_quoted (const char *, size_t *, int);
static inline char *string_extract_single_quoted (const char *, size_t *, int);
static inline size_t skip_single_quoted (const char *, size_t, size_t, int);static int skip_double_quoted (const char *, size_t, size_t, int);
static char *extract_delimited_string (const char *, size_t *, char *, char *, char *, int);
static char *extract_heredoc_dolbrace_string (const char *, size_t *, int, int);
static int skip_matched_pair (const char *, int, int, int, int);

static char *pos_params (const char *, int, int, int, int);

static unsigned char *mb_getcharlens (const char *, int);

static char *remove_upattern (char *, char *, int);
#if defined (HANDLE_MULTIBYTE) 
static wchar_t *remove_wpattern (wchar_t *, size_t, wchar_t *, int);
#endif
static char *remove_pattern (char *, char *, int);

static int match_upattern (char *, char *, int, char **, char **);
#if defined (HANDLE_MULTIBYTE)
static int match_wpattern (wchar_t *, char **, size_t, wchar_t *, int, char **, char **);
#endif
static int match_pattern (char *, char *, int, char **, char **);
static int getpatspec (int, const char *);
static char *getpattern (char *, int, int);
static char *variable_remove_pattern (char *, char *, int, int);
static char *list_remove_pattern (WORD_LIST *, char *, int, int, int);
static char *parameter_list_remove_pattern (int, char *, int, int);
#ifdef ARRAY_VARS
static char *array_remove_pattern (SHELL_VAR *, char *, int, int, int);
#endif
static char *parameter_brace_remove_pattern (char *, char *, array_eltstate_t *, char *, int, int, int);

static char *string_var_assignment (SHELL_VAR *, char *);
#if defined (ARRAY_VARS)
static char *array_var_assignment (SHELL_VAR *, int, int, int);
#endif
static char *pos_params_assignment (WORD_LIST *, int, int);
static char *string_transform (int, SHELL_VAR *, char *);
static char *list_transform (int, SHELL_VAR *, WORD_LIST *, int, int);
static char *parameter_list_transform (int, int, int);
#if defined ARRAY_VARS
static char *array_transform (int, SHELL_VAR *, int, int);
#endif
static char *parameter_brace_transform (char *, char *, array_eltstate_t *, char *, int, int, int, int);
static int valid_parameter_transform (const char *);

static char *process_substitute (char *, int);

static char *optimize_cat_file (REDIRECT *, int, int, int *);
static char *read_comsub (int, int, int, int *);

#ifdef ARRAY_VARS
static arrayind_t array_length_reference (const char *);
#endif

static int valid_brace_expansion_word (const char *, int);
static int chk_atstar (const char *, int, int, int *, int *);
static int chk_arithsub (const char *, int);

static WORD_DESC *parameter_brace_expand_word (char *, int, int, int, array_eltstate_t *);
static char *parameter_brace_find_indir (char *, int, int, int);
static WORD_DESC *parameter_brace_expand_indir (char *, int, int, int, int *, int *);
static WORD_DESC *parameter_brace_expand_rhs (char *, char *, int, int, int, int *, int *);
static void parameter_brace_expand_error (char *, char *, int);

static int valid_length_expression (const char *);
static intmax_t parameter_brace_expand_length (char *);

static char *skiparith (char *, int);
static int verify_substring_values (SHELL_VAR *, char *, char *, int, intmax_t *, intmax_t *);
static int get_var_and_type (char *, char *, array_eltstate_t *, int, int, SHELL_VAR **, char **);
static char *mb_subfstring (const char *, int, int);
static char *parameter_brace_substring (char *, char *, array_eltstate_t *, char *, int, int, int);

static int shouldexp_replacement (const char *);

static char *pos_params_pat_subst (char *, char *, char *, int);

static char *expand_string_for_patsub (char *, int);
static char *parameter_brace_patsub (char *, char *, array_eltstate_t *, char *, int, int, int);

static char *pos_params_casemod (char *, char *, int, int);
static char *parameter_brace_casemod (char *, char *, array_eltstate_t *, int, char *, int, int, int);

static WORD_DESC *parameter_brace_expand (char *, size_t *, int, int, int *, int *);
static WORD_DESC *param_expand (char *, size_t *, int, int *, int *, int *, int *, int);

static WORD_LIST *expand_word_internal (WORD_DESC *, int, int, int *, int *);

static WORD_LIST *word_list_split (WORD_LIST *);

static void exp_jump_to_top_level (int);

static WORD_LIST *separate_out_assignments (WORD_LIST *);
static WORD_LIST *glob_expand_word_list (WORD_LIST *, int);
#ifdef BRACE_EXPANSION
static WORD_LIST *brace_expand_word_list (WORD_LIST *, int);
#endif
#if defined (ARRAY_VARS)
static int make_internal_declare (const char *, const char *, const char *, const char *);
static void expand_compound_assignment_word (WORD_LIST *, int);
static WORD_LIST *expand_declaration_argument (WORD_LIST *, WORD_LIST *);
#endif
static WORD_LIST *shell_expand_word_list (WORD_LIST *, int);
static WORD_LIST *expand_word_list_internal (WORD_LIST *, int);

static inline void posix_variable_assignment_error (int);
static inline void bash_variable_assignment_error (int);

static int do_assignment_statements (WORD_LIST *, char *, int);

/* **************************************************************** */
/*                                                                  */
/*                      Utility Functions                           */
/*                                                                  */
/* **************************************************************** */

#if defined (DEBUG)
void
dump_word_flags (int flags)
{
  int f;

  f = flags;
  fprintf (stderr, "%d -> ", f);
  if (f & W_ARRAYIND)
    {
      f &= ~W_ARRAYIND;
      fprintf (stderr, "W_ARRAYIND%s", f ? "|" : "");
    }
  if (f & W_ASSIGNASSOC)
    {
      f &= ~W_ASSIGNASSOC;
      fprintf (stderr, "W_ASSIGNASSOC%s", f ? "|" : "");
    }
  if (f & W_ASSIGNARRAY)
    {
      f &= ~W_ASSIGNARRAY;
      fprintf (stderr, "W_ASSIGNARRAY%s", f ? "|" : "");
    }
  if (f & W_SAWQUOTEDNULL)
    {
      f &= ~W_SAWQUOTEDNULL;
      fprintf (stderr, "W_SAWQUOTEDNULL%s", f ? "|" : "");
    }
  if (f & W_NOPROCSUB)
    {
      f &= ~W_NOPROCSUB;
      fprintf (stderr, "W_NOPROCSUB%s", f ? "|" : "");
    }
  if (f & W_DQUOTE)
    {
      f &= ~W_DQUOTE;
      fprintf (stderr, "W_DQUOTE%s", f ? "|" : "");
    }
  if (f & W_HASQUOTEDNULL)
    {
      f &= ~W_HASQUOTEDNULL;
      fprintf (stderr, "W_HASQUOTEDNULL%s", f ? "|" : "");
    }
  if (f & W_ASSIGNARG)
    {
      f &= ~W_ASSIGNARG;
      fprintf (stderr, "W_ASSIGNARG%s", f ? "|" : "");   }
  if (f & W_ASSNBLTIN)
    {
      f &= ~W_ASSNBLTIN;
      fprintf (stderr, "W_ASSNBLTIN%s", f ? "|" : "");
    }
  if (f & W_ASSNGLOBAL)
    {
      f &= ~W_ASSNGLOBAL;
      fprintf (stderr, "W_ASSNGLOBAL%s", f ? "|" : "");
    }
  if (f & W_COMPASSIGN)
    {
      f &= ~W_COMPASSIGN;
      fprintf (stderr, "W_COMPASSIGN%s", f ? "|" : "");
    }
  if (f & W_EXPANDRHS)
    {
      f &= ~W_EXPANDRHS;
      fprintf (stderr, "W_EXPANDRHS%s", f ? "|" : "");
    }
  if (f & W_NOTILDE)
    {
      f &= ~W_NOTILDE;
      fprintf (stderr, "W_NOTILDE%s", f ? "|" : "");
    }
  if (f & W_ASSIGNRHS)
    {
      f &= ~W_ASSIGNRHS;
      fprintf (stderr, "W_ASSIGNRHS%s", f ? "|" : "");
    }
  if (f & W_NOASSNTILDE)
    {
      f &= ~W_NOASSNTILDE;
      fprintf (stderr, "W_NOASSNTILDE%s", f ? "|" : "");
    }
  if (f & W_NOCOMSUB)
    {
      f &= ~W_NOCOMSUB;
      fprintf (stderr, "W_NOCOMSUB%s", f ? "|" : "");
    }
  if (f & W_ARRAYREF)
    {
      f &= ~W_ARRAYREF;
      fprintf (stderr, "W_ARRAYREF%s", f ? "|" : "");
    }
  if (f & W_DOLLARAT)
    {
      f &= ~W_DOLLARAT;
      fprintf (stderr, "W_DOLLARAT%s", f ? "|" : "");
    }
  if (f & W_TILDEEXP)
    {
      f &= ~W_TILDEEXP;
      fprintf (stderr, "W_TILDEEXP%s", f ? "|" : "");
    }
  if (f & W_NOSPLIT2)
    {
      f &= ~W_NOSPLIT2;
      fprintf (stderr, "W_NOSPLIT2%s", f ? "|" : "");
    }
  if (f & W_NOSPLIT)
    {
      f &= ~W_NOSPLIT;
      fprintf (stderr, "W_NOSPLIT%s", f ? "|" : "");
    }
  if (f & W_NOBRACE)
    {
      f &= ~W_NOBRACE;
      fprintf (stderr, "W_NOBRACE%s", f ? "|" : "");
    }
  if (f & W_NOGLOB)
    {
      f &= ~W_NOGLOB;
      fprintf (stderr, "W_NOGLOB%s", f ? "|" : "");
    }
  if (f & W_SPLITSPACE)
    {
      f &= ~W_SPLITSPACE;
      fprintf (stderr, "W_SPLITSPACE%s", f ? "|" : "");
    }
  if (f & W_ASSIGNMENT)
    {
      f &= ~W_ASSIGNMENT;
      fprintf (stderr, "W_ASSIGNMENT%s", f ? "|" : "");
    }
  if (f & W_QUOTED)
    {
      f &= ~W_QUOTED;
      fprintf (stderr, "W_QUOTED%s", f ? "|" : "");
    }
  if (f & W_HASDOLLAR)
    {
      f &= ~W_HASDOLLAR;
      fprintf (stderr, "W_HASDOLLAR%s", f ? "|" : "");
    }
  if (f & W_COMPLETE)
    {
      f &= ~W_COMPLETE;
      fprintf (stderr, "W_COMPLETE%s", f ? "|" : "");
    }
  if (f & W_CHKLOCAL)
    {
      f &= ~W_CHKLOCAL;
      fprintf (stderr, "W_CHKLOCAL%s", f ? "|" : "");
    }
  if (f & W_FORCELOCAL)
    {
      f &= ~W_FORCELOCAL;
      fprintf (stderr, "W_FORCELOCAL%s", f ? "|" : "");
    }

  fprintf (stderr, "\n");
  fflush (stderr);
}
#endif#ifdef INCLUDE_UNUSED
static char *
quoted_substring (char *string, int start, int end)
{
  register int len, l;
  register char *result, *s, *r;

  len = end - start;

  /* Move to string[start], skipping quoted characters. */
  for (s = string, l = 0; *s && l < start; )
    {
      if (*s == CTLESC)
        {
          s++;
          continue;
        }
      l++;
      if (*s == 0)
        break;
    }

  r = result = (char *)xmalloc (2*len + 1);      /* save room for quotes */

  /* Copy LEN characters, including quote characters. */
  s = string + l;
  for (l = 0; l < len; s++)
    {
      if (*s == CTLESC)
        *r++ = *s++;
      *r++ = *s;
      l++;
      if (*s == 0)
        break;
    }
  *r = '\0';
  return result;
}
#endif

#ifdef INCLUDE_UNUSED
/* Return the length of S, skipping over quoted characters */
static int
quoted_strlen (char *s)
{
  register char *p;
  int i;

  i = 0;
  for (p = s; *p; p++)
    {
      if (*p == CTLESC)
        {
          p++;
          if (*p == 0)
            return (i + 1);
        }
      i++;
    }

  return i;
}
#endif

#ifdef INCLUDE_UNUSED
/* Find the first occurrence of character C in string S, obeying shell
   quoting rules.  If (FLAGS & ST_BACKSL) is non-zero, backslash-escaped
   characters are skipped.  If (FLAGS & ST_CTLESC) is non-zero, characters
   escaped with CTLESC are skipped. */
static char *
quoted_strchr (char *s, int c, int flags)
{
  register char *p;

  for (p = s; *p; p++)
    {
      if (((flags & ST_BACKSL) && *p == '\\')
            || ((flags & ST_CTLESC) && *p == CTLESC))
        {
          p++;
          if (*p == '\0')
            return ((char *)NULL);
          continue;
        }
      else if (*p == c)
        return p;
    }
  return ((char *)NULL);
}

/* Return 1 if CHARACTER appears in an unquoted portion of
   STRING.  Return 0 otherwise.  CHARACTER must be a single-byte character. */
static int
unquoted_member (int character, const char *string)
{
  size_t slen, sindex;
  int c;
  DECLARE_MBSTATE;

  slen = strlen (string);
  sindex = 0;
  while (c = string[sindex])
    {
      if (c == character)
        return (1);

      switch (c)
        {
        default:
          ADVANCE_CHAR (string, slen, sindex);
          break;

        case '\\':
          sindex++;
          if (string[sindex])
            ADVANCE_CHAR (string, slen, sindex);
          break;

        case '\'':
          sindex = skip_single_quoted (string, slen, ++sindex, 0);
          break;

        case '"':
          sindex = skip_double_quoted (string, slen, ++sindex, 0);
          break;
        }
    }
  return (0);
}

/* Return 1 if SUBSTR appears in an unquoted portion of STRING. */
static int
unquoted_substring (const char *substr, const char *string)
{
  size_t sindex, slen, sublen;
  int c;
  DECLARE_MBSTATE;

  if (substr == 0 || *substr == '\0')
    return (0);

  slen = strlen (string);
  sublen = strlen (substr);
  for (sindex = 0; c = string[sindex]; )
    {
      if (STREQN (string + sindex, substr, sublen))
        return (1);

      switch (c)
        {
        case '\\':
          sindex++;
          if (string[sindex])
            ADVANCE_CHAR (string, slen, sindex);
          break;

        case '\'':
          sindex = skip_single_quoted (string, slen, ++sindex, 0);
          break;

        case '"':
          sindex = skip_double_quoted (string, slen, ++sindex, 0);
          break;

        default:
          ADVANCE_CHAR (string, slen, sindex);
          break;
        }
    }
  return (0);
}
#endif

/* Most of the substitutions must be done in parallel.  In order
   to avoid using tons of unclear goto's, I have some functions
   for manipulating malloc'ed strings.  They all take INDX, a
   pointer to an integer which is the offset into the string
   where manipulation is taking place.  They also take SIZE, a
   pointer to an integer which is the current length of the
   character array for this string. *//* Append SOURCE to TARGET at INDEX.  SIZE is the current amount
   of space allocated to TARGET.  SOURCE can be NULL, in which
   case nothing happens.  Gets rid of SOURCE by freeing it.
   Returns TARGET in case the location has changed. */
INLINE char *
sub_append_string (char *source, char *target, size_t *indx, size_t *size)
{
  if (source)
    {
      size_t n, srclen;

      srclen = STRLEN (source);
      if ((srclen + *indx) >= *size)
        {
          n = srclen + *indx;
          n = (n + DEFAULT_ARRAY_SIZE) - (n % DEFAULT_ARRAY_SIZE);
          target = (char *)xrealloc (target, (*size = n));
        }

      FASTCOPY (source, target + *indx, srclen);
      *indx += srclen;
      target[*indx] = '\0';

      free (source);
    }
  return (target);
}

#if 0
/* UNUSED */
/* Append the textual representation of NUMBER to TARGET.
   INDX and SIZE are as in SUB_APPEND_STRING. */
char *
sub_append_number (intmax_t number, char *target, size_t *indx, size_t *size)
{
  char *temp;

  temp = itos (number);
  return (sub_append_string (temp, target, indx, size));
}
#endif

/* Extract a substring from STRING, starting at SINDEX and ending with
   one of the characters in CHARLIST.  Don't make the ending character
   part of the string.  Leave SINDEX pointing at the ending character.
   Understand about backslashes in the string.  If (flags & SX_VARNAME)
   is non-zero, and array variables have been compiled into the shell,
   everything between a `[' and a corresponding `]' is skipped over.
   If (flags & SX_NOALLOC) is non-zero, don't return the substring, just
   update SINDEX.  If (flags & SX_REQMATCH) is non-zero, the string must
   contain a closing character from CHARLIST. */
static char *
string_extract (const char *string, size_t *sindex, const char *charlist, int flags)
{
  int c;
  int found;
  size_t i, slen;
  char *temp;
  DECLARE_MBSTATE;

  slen = (locale_mb_cur_max > 1) ? strlen (string + *sindex) + *sindex : 0;
  i = *sindex;
  found = 0;
  while (c = string[i])
    {
      if (c == '\\')
        {
          if (string[i + 1])
            i++;
          else
            break;
        }
#if defined (ARRAY_VARS)
      else if ((flags & SX_VARNAME) && c == LBRACK)
        {
          int ni;
          /* If this is an array subscript, skip over it and continue. */
          ni = skipsubscript (string, i, 0);
          if (string[ni] == RBRACK)
            i = ni;
        }
#endif
      else if (MEMBER (c, charlist))
        {
          found = 1;
          break;
        }

      ADVANCE_CHAR (string, slen, i);
    }

  /* If we had to have a matching delimiter and didn't find one, return an
     error and let the caller deal with it. */
  if ((flags & SX_REQMATCH) && found == 0)
    {
      *sindex = i;
      return (&extract_string_error);
    }
  
  temp = (flags & SX_NOALLOC) ? (char *)NULL : substring (string, *sindex, i);
  *sindex = i;
  
  return (temp);
}

/* Extract the contents of STRING as if it is enclosed in double quotes.
   SINDEX, when passed in, is the offset of the character immediately
   following the opening double quote; on exit, SINDEX is left pointing after
   the closing double quote.  If STRIPDQ is non-zero, unquoted double
   quotes are stripped and the string is terminated by a null byte.
   Backslashes between the embedded double quotes are processed.  If STRIPDQ
   is zero, an unquoted `"' terminates the string. */
static char *
string_extract_double_quoted (const char *string, size_t *sindex, int flags)
{
  size_t i, j, t, si, slen;
  const char *send;
  unsigned char c;
  char *temp, *ret;             /* The new string we return. */
  int pass_next, backquote;     /* State variables for the machine. */
  int dquote;
  int stripdq;
  DECLARE_MBSTATE;

  slen = strlen (string + *sindex) + *sindex;
  send = string + slen;

  stripdq = (flags & SX_STRIPDQ);

  pass_next = backquote = dquote = 0;
  temp = (char *)xmalloc (1 + slen - *sindex);j = 0;
  i = *sindex;
  while (c = string[i])
    {
      /* Process a character that was quoted by a backslash. */
      if (pass_next)
        {
          /* XXX - take another look at this in light of Interp 221 */
          /* Posix.2 sez:

             ``The backslash shall retain its special meaning as an escape
             character only when followed by one of the characters:
                $       `       "       \       <newline>''.

             If STRIPDQ is zero, we handle the double quotes here and let
             expand_word_internal handle the rest.  If STRIPDQ is non-zero,
             we have already been through one round of backslash stripping,
             and want to strip these backslashes only if DQUOTE is non-zero,
             indicating that we are inside an embedded double-quoted string. */

          /* If we are in an embedded quoted string, then don't strip
             backslashes before characters for which the backslash
             retains its special meaning, but remove backslashes in
             front of other characters.  If we are not in an
             embedded quoted string, don't strip backslashes at all.
             This mess is necessary because the string was already
             surrounded by double quotes (and sh has some really weird
             quoting rules).
             The returned string will be run through expansion as if
             it were double-quoted. */
          if ((stripdq == 0 && c != '"') ||
              (stripdq && ((dquote && (sh_syntaxtab[c] & CBSDQUOTE)) || dquote == 0)))
            temp[j++] = '\\';
          pass_next = 0;

add_one_character:
          COPY_CHAR_I (temp, j, string, send, i);
          continue;
        }

      /* A backslash protects the next character.  The code just above
         handles preserving the backslash in front of any character but
         a double quote. */
      if (c == '\\')
        {
          pass_next++;
          i++;
          continue;
        }

      /* Inside backquotes, ``the portion of the quoted string from the
         initial backquote and the characters up to the next backquote
         that is not preceded by a backslash, having escape characters
         removed, defines that command''. */
      if (backquote)
        {
          if (c == '`')
            backquote = 0;
          temp[j++] = c;        /* COPY_CHAR_I? */
          i++;
          continue;
        }

      if (c == '`')
        {
          temp[j++] = c;
          backquote++;
          i++;
          continue;
        }

      /* Pass everything between `$(' and the matching `)' or a quoted
         ${ ... } pair through according to the Posix.2 specification. */
      if (c == '$' && ((string[i + 1] == LPAREN) || (string[i + 1] == LBRACE)))
        {
          int free_ret = 1;

          si = i + 2;
          if (string[i + 1] == LPAREN)
            ret = extract_command_subst (string, &si, (flags & SX_COMPLETE));
          else if (string[i + 1] == LBRACE && FUNSUB_CHAR (string[si]))
            ret = extract_function_subst (string, &si, Q_DOUBLE_QUOTES, (flags & SX_COMPLETE));
          else
            ret = extract_dollar_brace_string (string, &si, Q_DOUBLE_QUOTES, 0);

          temp[j++] = '$';
          temp[j++] = string[i + 1];

          /* Just paranoia; ret will not be 0 unless no_longjmp_on_fatal_error
             is set. */
          if (ret == 0 && no_longjmp_on_fatal_error)
            {
              free_ret = 0;
              ret = (char *)string + i + 2;
            }

          /* XXX - CHECK_STRING_OVERRUN here? */
          for (t = 0; ret[t]; t++, j++)
            temp[j] = ret[t];
          temp[j] = string[si];

          if (si < i + 2)       /* we went back? */
            i += 2;
          else if (string[si])
            {
              j++;
              i = si + 1;
            }
          else
            i = si;

          if (free_ret)
            free (ret);
          continue;
        }

      /* Add any character but a double quote to the quoted string we're
         accumulating. */
      if (c != '"')
        goto add_one_character;

      /* c == '"' */
      if (stripdq)
        {
          dquote ^= 1;
          i++;
          continue;
        }

      break;
    }
  temp[j] = '\0';

  /* Point to after the closing quote. */
  if (c)
    i++;
  *sindex = i;

  return (temp);
}

/* This should really be another option to string_extract_double_quoted. */
static int
skip_double_quoted (const char *string, size_t slen, size_t sind, int flags)
{
  int c;
  size_t i, si;
  char *ret;
  int pass_next, backquote;
  DECLARE_MBSTATE;

  pass_next = backquote = 0;
  i = sind;
  while (c = string[i])
    {
      if (pass_next)
        {
          pass_next = 0;
          ADVANCE_CHAR (string, slen, i);
          continue;
        }
      else if (c == '\\')   {
          pass_next++;
          i++;
          continue;
        }
      else if (backquote)
        {
          if (c == '`')
            backquote = 0;
          ADVANCE_CHAR (string, slen, i);
          continue;
        }
      else if (c == '`')
        {
          backquote++;
          i++;
          continue;
        }
      else if (c == '$' && ((string[i + 1] == LPAREN) || (string[i + 1] == LBRACE)))
        {
          si = i + 2;
          if (string[i + 1] == LPAREN)
            ret = extract_command_subst (string, &si, SX_NOALLOC|(flags&SX_COMPLETE));
          else if (string[i + 1] == LBRACE && FUNSUB_CHAR (string[si]))
            ret = extract_function_subst (string, &si, Q_DOUBLE_QUOTES, SX_NOALLOC|(flags & SX_COMPLETE));
          else
            ret = extract_dollar_brace_string (string, &si, Q_DOUBLE_QUOTES, SX_NOALLOC|(flags&SX_COMPLETE));

          /* These can consume the entire string if they are unterminated */
          CHECK_STRING_OVERRUN (i, si, slen, c);

          i = si + 1;
          continue;
        }
      else if (c != '"')
        {
          ADVANCE_CHAR (string, slen, i);
          continue;
        }
      else
        break;
    }

  if (c)
    i++;

  return (i);
}

/* Extract the contents of STRING as if it is enclosed in single quotes.
   SINDEX, when passed in, is the offset of the character immediately
   following the opening single quote; on exit, SINDEX is left pointing after
   the closing single quote. ALLOWESC allows the single quote to be quoted by
   a backslash; it's not used yet. */
static inline char *
string_extract_single_quoted (const char *string, size_t *sindex, int allowesc)
{
  size_t i, slen;
  char *t;
  int pass_next;
  DECLARE_MBSTATE;

  /* Don't need slen for ADVANCE_CHAR unless multibyte chars possible. */
  slen = (locale_mb_cur_max > 1) ? strlen (string + *sindex) + *sindex : 0;
  i = *sindex;
  pass_next = 0;
  while (string[i])
    {
      if (pass_next)
        {
          pass_next = 0;
          ADVANCE_CHAR (string, slen, i);
          continue;
        }
      if (allowesc && string[i] == '\\')
        pass_next++;
      else if (string[i] == '\'')
        break;
      ADVANCE_CHAR (string, slen, i);
    }

  t = substring (string, *sindex, i);

  if (string[i])
    i++;
  *sindex = i;

  return (t);
}

/* Skip over a single-quoted string.  We overload the SX_COMPLETE flag to mean
   that we are splitting out words for completion and have encountered a $'...'
   string, which allows backslash-escaped single quotes. */
static inline size_t
skip_single_quoted (const char *string, size_t slen, size_t sind, int flags)
{
  size_t si;
  DECLARE_MBSTATE;

  si = sind;
  while (string[si] && string[si] != '\'')
    {
      if ((flags & SX_COMPLETE) && string[si] == '\\' && string[si+1] == '\'' && string[si+2])
        ADVANCE_CHAR (string, slen, si);
      ADVANCE_CHAR (string, slen, si);
    }

  if (string[si])
    si++;
  return si;
}

/* Just like string_extract, but doesn't hack backslashes or any of
   that other stuff.  Obeys CTLESC quoting.  Used to do splitting on $IFS. */
static char *
string_extract_verbatim (const char *string, size_t slen, size_t *sindex, char *charlist, int flags)
{
  size_t i, c;
#if defined (HANDLE_MULTIBYTE)
  wchar_t *wcharlist;
  mbstate_t mbstmp;
#endif
  char *temp;
  DECLARE_MBSTATE;

  if ((flags & SX_NOCTLESC) && charlist[0] == '\'' && charlist[1] == '\0')
    {
      temp = string_extract_single_quoted (string, sindex, 0);
      --*sindex;        /* leave *sindex at separator character */
      return temp;
    }

  /* This can never be called with charlist == NULL. If *charlist == NULL,
     we can skip the loop and just return a copy of the string, updating
     *sindex */
  if (*charlist == 0)
    {
      const char *xtemp;
      xtemp = string + *sindex;
      c = (*sindex == 0) ? slen : STRLEN (xtemp);
      temp = savestring (xtemp);
      *sindex += c;
      return temp;
    }

  i = *sindex;
#if defined (HANDLE_MULTIBYTE)
  wcharlist = 0;
#endif
  while (c = string[i])
    {
#if defined (HANDLE_MULTIBYTE)
      size_t mblength;
#endif
      if ((flags & SX_NOCTLESC) == 0 && c == CTLESC)
        {
          i++;
          CHECK_STRING_OVERRUN (i, i, slen, c);
          ADVANCE_CHAR (string, slen, i);       /* CTLESC can quote mbchars */
          CHECK_STRING_OVERRUN (i, i, slen, c);
          continue;
        }
      /* Even if flags contains SX_NOCTLESC, we let CTLESC quoting CTLNUL
         through, to protect the CTLNULs from later calls to
         remove_quoted_nulls. */
      else if ((flags & SX_NOESCCTLNUL) == 0 && c == CTLESC && string[i+1] == CTLNUL)
        {
          i += 2;
          CHECK_STRING_OVERRUN (i, i, slen, c);
          continue;
        }

#if defined (HANDLE_MULTIBYTE)
      if (locale_utf8locale && slen > i && UTF8_SINGLEBYTE (string[i]))
        mblength = (string[i] != 0) ? 1 : 0;
      else
        {
          mbstmp = state;
          mblength = MBRLEN (string + i, slen - i, &mbstmp);
        }
      if (mblength > 1)
        {
          wchar_t wc;
          mbstmp = state;
          mblength = mbrtowc (&wc, string + i, slen - i, &mbstmp);
          if (MB_INVALIDCH (mblength))
            {
              if (MEMBER (c, charlist))
                break;
            }
          else
            {
              if (wcharlist == 0)
                {
                  size_t len;
                  len = mbstowcs (wcharlist, charlist, 0);
                  if (len == -1)
                    len = 0;
                  wcharlist = (wchar_t *)xmalloc (sizeof (wchar_t) * (len + 1));
                  mbstowcs (wcharlist, charlist, len + 1);
                }

              if (wcschr (wcharlist, wc))
                break;
            }
        }
      else#endif
      if (MEMBER (c, charlist))
        break;

      ADVANCE_CHAR (string, slen, i);
    }

#if defined (HANDLE_MULTIBYTE)
  FREE (wcharlist);
#endif

  temp = substring (string, *sindex, i);
  *sindex = i;

  return (temp);
}

/* Extract the $( construct in STRING, and return a new string.
   Start extracting at (SINDEX) as if we had just seen "$(".
   Make (SINDEX) get the position of the matching ")". )
   XFLAGS is additional flags to pass to other extraction functions. */
char *
extract_command_subst (const char *string, size_t *sindex, int xflags)
{
  char *ret;
  char *xstr;

  if (string[*sindex] == LPAREN || (xflags & SX_COMPLETE))
    return (extract_delimited_string (string, sindex, "$(", "(", ")", xflags|SX_COMMAND)); /*)*/
  else
    {
      xflags |= (no_longjmp_on_fatal_error ? SX_NOLONGJMP : 0);
      xstr = (char *)string + *sindex;
      ret = xparse_dolparen (string, xstr, sindex, xflags);
      return ret;
    }
}

/* Take a ${Ccommand} where C is a character that introduces a function
   substitution and extract the string. */
char *
extract_function_subst (const char *string, size_t *sindex, int quoted, int xflags)
{
  char *ret;
  char *xstr;

  if (string[*sindex] == LBRACE || (xflags & SX_COMPLETE))
    return (extract_dollar_brace_string (string, sindex, quoted, xflags|SX_COMMAND));
  else
    {
      xflags |= (no_longjmp_on_fatal_error ? SX_NOLONGJMP : 0);
      xstr = (char *)string + *sindex;
      ret = xparse_dolparen (string, xstr, sindex, xflags|SX_FUNSUB);
      return ret;
    }
}

/* Extract the $[ construct in STRING, and return a new string. (])
   Start extracting at (SINDEX) as if we had just seen "$[".
   Make (SINDEX) get the position of the matching "]". */
char *
extract_arithmetic_subst (const char *string, size_t *sindex)
{
  return (extract_delimited_string (string, sindex, "$[", "[", "]", 0)); /*]*/
}

#if defined (PROCESS_SUBSTITUTION)
/* Extract the <( or >( construct in STRING, and return a new string.
   Start extracting at (SINDEX) as if we had just seen "<(".
   Make (SINDEX) get the position of the matching ")". */ /*))*/
char *
extract_process_subst (const char *string, char *starter, size_t *sindex, int xflags)
{
  char *ret;
  char *xstr;
#if 0
  /* XXX - check xflags&SX_COMPLETE here? */
  if (flags & SX_COMPLETE)
    return (extract_delimited_string (string, sindex, starter, "(", ")", SX_COMMAND));
  else
#else
    {
      xflags |= (no_longjmp_on_fatal_error ? SX_NOLONGJMP : 0);
      xstr = (char *)string + *sindex;
      ret = xparse_dolparen (string, xstr, sindex, xflags);
      return ret;
    }
#endif
}
#endif /* PROCESS_SUBSTITUTION */

#if defined (ARRAY_VARS)
/* This can be fooled by unquoted right parens in the passed string. If
   each caller verifies that the last character in STRING is a right paren,
   we don't even need to call extract_delimited_string. */
char *
extract_array_assignment_list (const char *string, size_t *sindex)
{
  size_t slen;
  char *ret;

  slen = strlen (string);
  if (string[slen - 1] == RPAREN)
   {
      ret = substring (string, *sindex, slen - 1);
      *sindex = slen - 1;
      return ret;
    }
  return 0;  
}
#endif

/* Extract and create a new string from the contents of STRING, a
   character string delimited with OPENER and CLOSER.  SINDEX is
   the address of an int describing the current offset in STRING;
   it should point to just after the first OPENER found.  On exit,
   SINDEX gets the position of the last character of the matching CLOSER.
   If OPENER is more than a single character, ALT_OPENER, if non-null,
   contains a character string that can also match CLOSER and thus
   needs to be skipped. */
static char *
extract_delimited_string (const char *string, size_t *sindex, char *opener, char *alt_opener, char *closer, int flags)
{
  int c, xflags;
  size_t i, si, slen;
  char *t, *result;
  int pass_character, nesting_level, in_comment;
  size_t len_closer, len_opener, len_alt_opener;
  DECLARE_MBSTATE;

  slen = strlen (string + *sindex) + *sindex;
  len_opener = STRLEN (opener);
  len_alt_opener = STRLEN (alt_opener);
  len_closer = STRLEN (closer);

  pass_character = in_comment = 0;

  nesting_level = 1;
  i = *sindex;

  while (nesting_level)
    {
      c = string[i];

      /* If a recursive call or a call to ADVANCE_CHAR leaves the index beyond
         the end of the string, catch it and cut the loop. */
      if (i > slen)
        {
          c = string[i = slen];
          break;
        }

      if (c == 0)
        break;

      if (in_comment)
        {
          if (c == '\n')
            in_comment = 0;
          ADVANCE_CHAR (string, slen, i);
          continue;
        }

      if (pass_character)       /* previous char was backslash */
        {
          pass_character = 0;
          ADVANCE_CHAR (string, slen, i);
          continue;
        }

      /* Not exactly right yet; should handle shell metacharacters and
         multibyte characters, too.  See COMMENT_BEGIN define in parse.y */
      if ((flags & SX_COMMAND) && c == '#' && (i == 0 || string[i - 1] == '\n' || shellblank (string[i - 1])))
        {
          in_comment = 1;
          ADVANCE_CHAR (string, slen, i);
          continue;
        }
        
      if (c == CTLESC || c == '\\')
        {
          pass_character++;
          i++;
          continue;
        }

      /* Process a nested command substitution, but only if we're parsing an
         arithmetic substitution. */
      if ((flags & SX_COMMAND) && string[i] == '$' && string[i+1] == LPAREN) {
          si = i + 2;
          t = extract_command_subst (string, &si, flags|SX_NOALLOC);
          CHECK_STRING_OVERRUN (i, si, slen, c);
          i = si + 1;
          continue;
        }

      /* Process alternate form of nested command substitution. */
      if ((flags & SX_COMMAND) && string[i] == '$' && string[i+1] == LBRACE && FUNSUB_CHAR (string[i+2]))
        {
          si = i + 2;
          t = extract_function_subst (string, &si, 0, flags|SX_NOALLOC);
          CHECK_STRING_OVERRUN (i, si, slen, c);
          i = si + 1;
          continue;
        }

      /* Process a nested OPENER. */
      if (STREQN (string + i, opener, len_opener))
        {
          si = i + len_opener;
          t = extract_delimited_string (string, &si, opener, alt_opener, closer, flags|SX_NOALLOC);
          CHECK_STRING_OVERRUN (i, si, slen, c);
          i = si + 1;
          continue;
        }

      /* Process a nested ALT_OPENER */
      if (len_alt_opener && STREQN (string + i, alt_opener, len_alt_opener))
        {
          si = i + len_alt_opener;
          t = extract_delimited_string (string, &si, alt_opener, alt_opener, closer, flags|SX_NOALLOC);
          CHECK_STRING_OVERRUN (i, si, slen, c);
          i = si + 1;
          continue;
        }

      /* If the current substring terminates the delimited string, decrement
         the nesting level. */
      if (STREQN (string + i, closer, len_closer))
        {
          i += len_closer - 1;  /* move to last byte of the closer */
          nesting_level--;
          if (nesting_level == 0)
            break;
        }

      /* Pass old-style command substitution through verbatim. */
      if (c == '`')
        {
          si = i + 1;
          t = string_extract (string, &si, "`", flags|SX_NOALLOC);
          CHECK_STRING_OVERRUN (i, si, slen, c);
          i = si + 1;
          continue;
        }

      /* Pass single-quoted and double-quoted strings through verbatim. */
      if (c == '\'' || c == '"')
        {
          si = i + 1;
          i = (c == '\'') ? skip_single_quoted (string, slen, si, flags)
                          : skip_double_quoted (string, slen, si, flags);
          continue;
        }

      /* move past this character, which was not special. */
      ADVANCE_CHAR (string, slen, i);
    }

  if (c == 0 && nesting_level)
    {
      if (no_longjmp_on_fatal_error == 0)
        {
          last_command_exit_value = EXECUTION_FAILURE;
          report_error (_("bad substitution: no closing `%s' in %s"), closer, string);
          exp_jump_to_top_level (DISCARD);
        }
      else
        {
          *sindex = i;
          return (char *)NULL;
        }
    }

  si = i - *sindex - len_closer + 1;
  if (flags & SX_NOALLOC)
    result = (char *)NULL;
  else    {
      result = (char *)xmalloc (1 + si);
      strncpy (result, string + *sindex, si);
      result[si] = '\0';
    }
  *sindex = i;

  return (result);
}

/* A simplified version of extract_dollar_brace_string that exists to handle
   $'...' and $"..." quoting in here-documents, since the here-document read
   path doesn't. It's separate because we don't want to mess with the fast
   common path. We already know we're going to allocate and return a new
   string and quoted == Q_HERE_DOCUMENT. We might be able to cut it down
   some more, but extracting strings and adding them as we go adds complexity.
   This needs to match the logic in parse.y:parse_matched_pair so we get
   consistent behavior between here-documents and double-quoted strings. */
static char *
extract_heredoc_dolbrace_string (const char *string, size_t *sindex, int quoted, int flags)
{
  register int c;
  size_t i, si, slen, tlen, result_index, result_size;
  int pass_character, nesting_level, dolbrace_state;
  char *result, *t;
  const char *send;
  DECLARE_MBSTATE;

  pass_character = 0;
  nesting_level = 1;
  slen = strlen (string + *sindex) + *sindex;
  send = string + slen;

  result_size = slen;
  result_index = 0;
  result = xmalloc (result_size + 1);

  /* This function isn't called if this condition is not true initially. */
  dolbrace_state = DOLBRACE_QUOTE;

  i = *sindex;
  while (c = string[i])
    {
      if (pass_character)
        {
          pass_character = 0;
          RESIZE_MALLOCED_BUFFER (result, result_index, locale_mb_cur_max + 1, result_size, 64);
          COPY_CHAR_I (result, result_index, string, send, i);
          continue;
        }

      /* CTLESCs and backslashes quote the next character. */
      if (c == CTLESC || c == '\\')
        {
          pass_character++;
          RESIZE_MALLOCED_BUFFER (result, result_index, 2, result_size, 64);
          result[result_index++] = c;
          i++;
          continue;
        }

      /* The entire reason we have this separate function right here. */
      if (c == '$' && string[i+1] == '\'')
        {
          char *ttrans;
          size_t ttranslen;

          if ((posixly_correct || extended_quote == 0) && dolbrace_state != DOLBRACE_QUOTE && dolbrace_state != DOLBRACE_QUOTE2)
            {
              RESIZE_MALLOCED_BUFFER (result, result_index, 3, result_size, 64);
              result[result_index++] = '$';
              result[result_index++] = '\'';
              i += 2;
              continue;
            }

          si = i + 2;
          t = string_extract_single_quoted (string, &si, 1);    /* XXX */
          CHECK_STRING_OVERRUN (i, si, slen, c);

          tlen = si - i - 2;    /* -2 since si is one after the close quote */
          ttrans = ansiexpand (t, 0, tlen, &ttranslen);
          free (t);

          /* needed to correctly quote any embedded single quotes. */
          if (dolbrace_state == DOLBRACE_QUOTE || dolbrace_state == DOLBRACE_QUOTE2)
            {
              t = sh_single_quote (ttrans);
              tlen = strlen (t);
              free (ttrans);
            }
          else if (extended_quote) /* dolbrace_state == DOLBRACE_PARAM */
            {
              /* This matches what parse.y:parse_matched_pair() does */
              t = ttrans;
              tlen = strlen (t);
            }

          RESIZE_MALLOCED_BUFFER (result, result_index, tlen + 1, result_size, 64);
          strncpy (result + result_index, t, tlen);
          result_index += tlen;
          free (t);
          i = si;
          continue;
        }

#if defined (TRANSLATABLE_STRINGS)
      if (c == '$' && string[i+1] == '"')
        {
          char *ttrans;
          size_t ttranslen;

          si = i + 2;
          t = string_extract_double_quoted (string, &si, flags);        /* XXX */
          CHECK_STRING_OVERRUN (i, si, slen, c);

          tlen = si - i - 2;    /* -2 since si is one after the close quote */
          ttrans = locale_expand (t, 0, tlen, line_number, &ttranslen);
          free (t);

          t = singlequote_translations ? sh_single_quote (ttrans) : sh_mkdoublequoted (ttrans, ttranslen, 0);
          tlen = strlen (t);
          free (ttrans);

          RESIZE_MALLOCED_BUFFER (result, result_index, tlen + 1, result_size, 64);
          strncpy (result + result_index, t, tlen);
          result_index += tlen;
          free (t); i = si;
          continue;
        }
#endif /* TRANSLATABLE_STRINGS */

      if (c == '$' && string[i+1] == LBRACE)
        {
          nesting_level++;
          RESIZE_MALLOCED_BUFFER (result, result_index, 3, result_size, 64);
          result[result_index++] = c;
          result[result_index++] = string[i+1];
          i += 2;
          if (dolbrace_state == DOLBRACE_QUOTE || dolbrace_state == DOLBRACE_QUOTE2 || dolbrace_state == DOLBRACE_WORD)
            dolbrace_state = DOLBRACE_PARAM;
          continue;
        }

      if (c == RBRACE)
        {
          nesting_level--;
          if (nesting_level == 0)
            break;
          RESIZE_MALLOCED_BUFFER (result, result_index, 2, result_size, 64);
          result[result_index++] = c;
          i++;
          continue;
        }

      /* Pass the contents of old-style command substitutions through
         verbatim. */
      if (c == '`')
        {
          si = i + 1;
          t = string_extract (string, &si, "`", flags); /* already know (flags & SX_NOALLOC) == 0) */
          CHECK_STRING_OVERRUN (i, si, slen, c);

          tlen = si - i - 1;
          RESIZE_MALLOCED_BUFFER (result, result_index, tlen + 3, result_size, 64);
          result[result_index++] = c;
          strncpy (result + result_index, t, tlen);
          result_index += tlen;
          result[result_index++] = string[si];
          free (t);
          i = si + 1;
          continue;
        }

      /* Pass the contents of new-style command substitutions and
         arithmetic substitutions through verbatim. */
      if (string[i] == '$' && (string[i+1] == LPAREN || (string[i+1] == LBRACE && FUNSUB_CHAR (string[i+2]))))
        {
          int open;

          si = i + 2;
          open = string[i+1];
          if (open == LPAREN)
            t = extract_command_subst (string, &si, flags);
          else
            t = extract_function_subst (string, &si, quoted, flags);
          CHECK_STRING_OVERRUN (i, si, slen, c);

          tlen = si - i - 2;
          RESIZE_MALLOCED_BUFFER (result, result_index, tlen + 4, result_size, 64);
          result[result_index++] = c;
          result[result_index++] = open;
          strncpy (result + result_index, t, tlen);
          result_index += tlen;
          result[result_index++] = string[si];
          free (t);
          i = si + 1;
          continue;
        }

#if defined (PROCESS_SUBSTITUTION)
      /* Technically this should only work at the start of a word */
      if ((string[i] == '<' || string[i] == '>') && string[i+1] == LPAREN)
        {
          si = i + 2;
          t = extract_process_subst (string, (string[i] == '<' ? "<(" : ">)"), &si, flags);
          CHECK_STRING_OVERRUN (i, si, slen, c);

          tlen = si - i - 2;
          RESIZE_MALLOCED_BUFFER (result, result_index, tlen + 4, result_size, 64);
          result[result_index++] = c;
          result[result_index++] = LPAREN;
          strncpy (result + result_index, t, tlen);
          result_index += tlen;
          result[result_index++] = string[si];
          free (t);
          i = si + 1;
          continue;
        }
#endif

      if (c == '\'' && posixly_correct && shell_compatibility_level > 42 && dolbrace_state != DOLBRACE_QUOTE)
        {
          COPY_CHAR_I (result, result_index, string, send, i);
          continue;
        }

      /* Pass the contents of single and double-quoted strings through verbatim. */
      if (c == '"' || c == '\'')
        {
          si = i + 1;
          if (c == '"')
            t = string_extract_double_quoted (string, &si, flags);
          else
            t = string_extract_single_quoted (string, &si, 0);
          CHECK_STRING_OVERRUN (i, si, slen, c);

          tlen = si - i - 2;    /* -2 since si is one after the close quote */
          RESIZE_MALLOCED_BUFFER (result, result_index, tlen + 3, result_size, 64);
          result[result_index++] = c;
          strncpy (result + result_index, t, tlen);
          result_index += tlen;
          result[result_index++] = string[si - 1];
          free (t);
          i = si;
          continue;
        }

      /* copy this character, which was not special. */
      COPY_CHAR_I (result, result_index, string, send, i);

      /* This logic must agree with parse.y:parse_matched_pair, since they
         share the same defines. */
      if (dolbrace_state == DOLBRACE_PARAM && c == '%' && (i - *sindex) > 1)
        dolbrace_state = DOLBRACE_QUOTE;
      else if (dolbrace_state == DOLBRACE_PARAM && c == '#' && (i - *sindex) > 1)
        dolbrace_state = DOLBRACE_QUOTE;
      else if (dolbrace_state == DOLBRACE_PARAM && c == '/' && (i - *sindex) > 1)
        dolbrace_state = DOLBRACE_QUOTE2;       /* XXX */
      else if (dolbrace_state == DOLBRACE_PARAM && c == '^' && (i - *sindex) > 1)
        dolbrace_state = DOLBRACE_QUOTE;
      else if (dolbrace_state == DOLBRACE_PARAM && c == ',' && (i - *sindex) > 1)
        dolbrace_state = DOLBRACE_QUOTE;
      /* This is intended to handle all of the [:]op expansions and the substring/
         length/pattern removal/pattern substitution expansions. */
      else if (dolbrace_state == DOLBRACE_PARAM && strchr ("#%^,~:-=?+/", c) != 0)
        dolbrace_state = DOLBRACE_OP;
      else if (dolbrace_state == DOLBRACE_OP && strchr ("#%^,~:-=?+/", c) == 0)
        dolbrace_state = DOLBRACE_WORD;
    }

  if (c == 0 && nesting_level)
    {
      free (result);
      if (no_longjmp_on_fatal_error == 0)
        {                       /* { */
          last_command_exit_value = EXECUTION_FAILURE;
          report_error (_("bad substitution: no closing `%s' in %s"), "}", string);
          exp_jump_to_top_level (DISCARD);
        }
      else
        {
          *sindex = i;
          return ((char *)NULL);
        }
    }

  *sindex = i;
  result[result_index] = '\0';

  return (result);
}

#define PARAMEXPNEST_MAX        32      // for now
static int dbstate[PARAMEXPNEST_MAX];

/* Extract a parameter expansion expression within ${ and } from STRING.
   Obey the Posix.2 rules for finding the ending `}': count braces while
   skipping over enclosed quoted strings and command substitutions.
   SINDEX is the address of an int describing the current offset in STRING;
   it should point to just after the first `{' found.  On exit, SINDEX
   gets the position of the matching `}'.  QUOTED is non-zero if this
   occurs inside double quotes. */
/* XXX -- this is very similar to extract_delimited_string -- XXX */
char *
extract_dollar_brace_string (const char *string, size_t *sindex, int quoted, int flags)
{
  register int i, c;
  size_t si, slen;
  int pass_character, nesting_level, dolbrace_state;
  char *result, *t;
  DECLARE_MBSTATE;

  /* The handling of dolbrace_state needs to agree with the code in parse.y:
     parse_matched_pair().  The different initial value is to handle the
     case where this function is called to parse the word in
     ${param op word} (SX_WORD). */
  dolbrace_state = (flags & SX_WORD) ? DOLBRACE_WORD : DOLBRACE_PARAM;
  if ((quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)) && (flags & SX_POSIXEXP))
    dolbrace_state = DOLBRACE_QUOTE;

  if (quoted == Q_HERE_DOCUMENT && dolbrace_state == DOLBRACE_QUOTE && (flags & SX_NOALLOC) == 0)
    return (extract_heredoc_dolbrace_string (string, sindex, quoted, flags));

  dbstate[0] = dolbrace_state;

  pass_character = 0;
  nesting_level = 1;
  slen = strlen (string + *sindex) + *sindex;

  i = *sindex;
  while (c = string[i])
    {
      if (pass_character)
        {
          pass_character = 0;
          ADVANCE_CHAR (string, slen, i);
          continue;
        }

      /* CTLESCs and backslashes quote the next character. */
      if (c == CTLESC || c == '\\') {
          pass_character++;
          i++;
          continue;
        }

      if (string[i] == '$' && string[i+1] == LBRACE)
        {
          if (nesting_level < PARAMEXPNEST_MAX)
            dbstate[nesting_level] = dolbrace_state;
          nesting_level++;
          i += 2;
          if (dolbrace_state == DOLBRACE_QUOTE || dolbrace_state == DOLBRACE_WORD)
            dolbrace_state = DOLBRACE_PARAM;
          continue;
        }

      if (c == RBRACE)
        {
          nesting_level--;
          if (nesting_level == 0)
            break;
          dolbrace_state = (nesting_level < PARAMEXPNEST_MAX) ? dbstate[nesting_level] : dbstate[0];    /* Guess using initial state */
          i++;
          continue;
        }

      /* Pass the contents of old-style command substitutions through
         verbatim. */
      if (c == '`')
        {
          si = i + 1;
          t = string_extract (string, &si, "`", flags|SX_NOALLOC);

          CHECK_STRING_OVERRUN (i, si, slen, c);

          i = si + 1;
          continue;
        }

      /* Pass the contents of new-style command substitutions and
         arithmetic substitutions through verbatim. */
      if (string[i] == '$' && string[i+1] == LPAREN)
        {
          si = i + 2;
          t = extract_command_subst (string, &si, flags|SX_NOALLOC);

          CHECK_STRING_OVERRUN (i, si, slen, c);

          i = si + 1;
          continue;
        }

      /* Pass the contents of foreground command substitutions (funsub/valsub)
         through verbatim. */
      if (string[i] == '$' && string[i+1] == LBRACE && FUNSUB_CHAR (string[i+2]))
        {
          si = i + 2;
          t = extract_function_subst (string, &si, quoted, flags|SX_NOALLOC);

          CHECK_STRING_OVERRUN (i, si, slen, c);

          i = si + 1;
          continue;
        }

#if defined (PROCESS_SUBSTITUTION)
      /* Technically this should only work at the start of a word */
      if ((string[i] == '<' || string[i] == '>') && string[i+1] == LPAREN)
        {
          si = i + 2;
          t = extract_process_subst (string, (string[i] == '<' ? "<(" : ">)"), &si, flags|SX_NOALLOC);

          CHECK_STRING_OVERRUN (i, si, slen, c);

          i = si + 1;
          continue;
        }
#endif

      /* Pass the contents of double-quoted strings through verbatim. */
      if (c == '"')
        {
          si = i + 1;
          i = skip_double_quoted (string, slen, si, 0);
          /* skip_XXX_quoted leaves index one past close quote */
          continue;
        }

      if (c == '\'')
        {
/*itrace("extract_dollar_brace_string: c == single quote flags = %d quoted = %d dolbrace_state = %d", flags, quoted, dolbrace_state);*/
          if (posixly_correct && shell_compatibility_level > 42 && dolbrace_state != DOLBRACE_QUOTE && (quoted & (Q_HERE_DOCUMENT|Q_DOUBLE_QUOTES)))
            ADVANCE_CHAR (string, slen, i);
          else
            {
              si = i + 1;
              i = skip_single_quoted (string, slen, si, 0);
            }

          continue;
        }

#if defined (ARRAY_VARS)
      if (c == LBRACK && dolbrace_state == DOLBRACE_PARAM)
        {
          si = skipsubscript (string, i, 0);
          CHECK_STRING_OVERRUN (i, si, slen, c);
          if (string[si] == RBRACK)
            c = string[i = si];
        }
#endif

      /* move past this character, which was not special. */
      ADVANCE_CHAR (string, slen, i);

      /* This logic must agree with parse.y:parse_matched_pair, since they
         share the same defines. */
      if (dolbrace_state == DOLBRACE_PARAM && c == '%' && (i - *sindex) > 1)
        dolbrace_state = DOLBRACE_QUOTE;
      else if (dolbrace_state == DOLBRACE_PARAM && c == '#' && (i - *sindex) > 1)
        dolbrace_state = DOLBRACE_QUOTE;
      else if (dolbrace_state == DOLBRACE_PARAM && c == '/' && (i - *sindex) > 1)
        dolbrace_state = DOLBRACE_QUOTE2;       /* XXX */
      else if (dolbrace_state == DOLBRACE_PARAM && c == '^' && (i - *sindex) > 1)
        dolbrace_state = DOLBRACE_QUOTE;
      else if (dolbrace_state == DOLBRACE_PARAM && c == ',' && (i - *sindex) > 1)
        dolbrace_state = DOLBRACE_QUOTE;
      /* This is intended to handle all of the [:]op expansions and the substring/
         length/pattern removal/pattern substitution expansions. */
      else if (dolbrace_state == DOLBRACE_PARAM && strchr ("#%^,~:-=?+/", c) != 0)
        dolbrace_state = DOLBRACE_OP;
      else if (dolbrace_state == DOLBRACE_OP && strchr ("#%^,~:-=?+/", c) == 0)
        dolbrace_state = DOLBRACE_WORD;
    }

  if (c == 0 && nesting_level)
    {
      if (no_longjmp_on_fatal_error == 0)
        {                       /* { */
          last_command_exit_value = EXECUTION_FAILURE;
          report_error (_("bad substitution: no closing `%s' in %s"), "}", string);
          exp_jump_to_top_level (DISCARD);
        }
      else
        {
          *sindex = i;
          return ((char *)NULL);
        }
    }

  result = (flags & SX_NOALLOC) ? (char *)NULL : substring (string, *sindex, i);
  *sindex = i;

  return (result);
}

/* Remove backslashes which are quoting backquotes from STRING.  Modifies
   STRING, and returns a pointer to it. */
char *
de_backslash (char *string, int qflags)
{
  register size_t slen;
  register size_t i, j, prev_i;
  DECLARE_MBSTATE;

  slen = strlen (string);
  i = j = 0;

  /* Loop copying string[i] to string[j], i >= j. */
  while (i < slen)
    {
      if (string[i] == '\\' && (string[i + 1] == '`' || string[i + 1] == '\\' ||
                              string[i + 1] == '$'))
        i++;
      else if (posixly_correct && (qflags & Q_HERE_DOCUMENT) && string[i] == '\\' && string[i + 1] == '"')
        i++;
      prev_i = i;
      ADVANCE_CHAR (string, slen, i);
      if (j < prev_i)
        do string[j++] = string[prev_i++]; while (prev_i < i);
      else
        j = i;
    }
  string[j] = '\0';

  return (string);
}

#if 0
/*UNUSED*/
/* Replace instances of \! in a string with !. */
void
unquote_bang (char *string)
{
  register int i, j;
  register char *temp;

  temp = (char *)xmalloc (1 + strlen (string));

  for (i = 0, j = 0; (temp[j] = string[i]); i++, j++)
    {
      if (string[i] == '\\' && string[i + 1] == '!')
        {
          temp[j] = '!';
          i++;
        }
    }
  strcpy (string, temp);
  free (temp);
}
#endif

#define CQ_RETURN(x) do { no_longjmp_on_fatal_error = oldjmp; return (x); } while (0)

/* When FLAGS & 2 == 0, this function assumes STRING[I] == OPEN; when
   FLAGS & 2 != 0, it assumes STRING[I] points to one character past OPEN;
   returns with STRING[RET] == close; used to parse array subscripts.
   FLAGS & 1 means not to attempt to skip over matched pairs of quotes or
   backquotes, or skip word expansions; it is intended to be used after
   expansion has been performed and during final assignment parsing (see
   arrayfunc.c:assign_compound_array_list()) or during execution by a builtin
   which has already undergone word expansion. */
static int
skip_matched_pair (const char *string, int start, int open, int close, int flags)
{
  int pass_next, backq, c, count, oldjmp;
  size_t i, si, slen;
  char *temp;
  DECLARE_MBSTATE;

  slen = strlen (string + start) + start;
  oldjmp = no_longjmp_on_fatal_error;
  no_longjmp_on_fatal_error = 1;

  /* Move to the first character after a leading OPEN. If FLAGS&2, we assume
    that START already points to that character. If not, we need to skip over
    it here. */
  i = (flags & 2) ? start : start + 1;
  count = 1;
  pass_next = backq = 0;
  while (c = string[i])
    {
      if (pass_next)
        {
          pass_next = 0;
          if (c == 0)
            CQ_RETURN(i);
          ADVANCE_CHAR (string, slen, i);
          continue;
        }
      else if ((flags & 1) == 0 && c == '\\')
        {
          pass_next = 1;
          i++;
          continue;
        }
      else if (backq)
        {
          if (c == '`')
            backq = 0;
          ADVANCE_CHAR (string, slen, i);
          continue;
        }
      else if ((flags & 1) == 0 && c == '`')
