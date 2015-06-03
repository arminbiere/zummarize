#include <stdio.h>
#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <ctype.h>
#include <dirent.h>

typedef struct Entry {
  char * name;
  struct Zummary * zummary;
  struct Entry * next;
  double time, wall, mb;
  char timeout, memout;
  int res;
} Entry;

typedef struct Zummary {
  char * path;
  Entry * first, * last;
  int count, sat, unsat, unknown, memout, timeout;
  double time, wall, mb, timelimit, spacelimit;
} Zummary;

static int verbose;

static Zummary ** zummaries;
static int nzummaries, sizezummaries;
static int loaded, written, updated;

static char * token;
static int ntoken, sizetoken;

static char ** tokens;
static int ntokens, sizetokens;

static void die (const char * fmt, ...) {
  va_list ap;
  fputs ("*** zummarize: ", stderr);
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

static void msg (int level, const char * fmt, ...) {
  va_list ap;
  if (verbose < level) return;
  fflush (stderr);
  fputs ("[zummarize] ", stderr);
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  fflush (stderr);
}

static const char * USAGE =
"usage: zummarize [-h|-v] [ <dir> ... ]\n"
;

static void usage () {
  fputs (USAGE, stdout);
  exit (0);
}

static int isdir (const char * path) {
  struct stat buf;
  return !stat (path, &buf) && S_ISDIR (buf.st_mode);
}

static int isfile (const char * path) {
  struct stat buf;
  return !stat (path, &buf) && S_ISREG (buf.st_mode);
}

static void stripleadingslash (char * str) {
  int i = strlen (str);
  while (i > 0 && str[i-1] == '/')
    str[--i] = 0;
}

static Zummary * newzummary (const char * path) {
  Zummary * res = malloc (sizeof *res);
  memset (res, 0, sizeof *res);
  res->path = strdup (path);
  res->timelimit = res->spacelimit = -1;
  stripleadingslash (res->path);
  if (sizezummaries == nzummaries) {
    int newsize = sizezummaries ? 2*sizezummaries : 1;
    zummaries = realloc (zummaries, newsize * sizeof *zummaries);
    sizezummaries = newsize;
  }
  zummaries[nzummaries++] = res;
  return res;
}

static char * appendstr (const char * a, const char * b) {
  int i = strlen (a), j = strlen (b);
  char * res = malloc (i + j + 1);
  strcpy (res, a);
  strcpy (res + i, b);
  return res;
}

static char * appendtopath (const char * prefix, const char * name) {
  char * res = malloc (strlen (prefix) + strlen (name) + 2);
  strcpy (res, prefix);
  stripleadingslash (res);
  strcat (res, "/");
  strcat (res, name);
  return res;
}

static void pushtoken () {
  char * res = malloc (ntoken + 1);
  int i;
  for (i = 0; i < ntoken; i++) res[i] = token[i];
  res[i] = 0;
  if (sizetokens == ntokens) {
    int newsizetokens = sizetokens ? 2*sizetokens : 1;
    tokens = realloc (tokens, newsizetokens * sizeof *tokens);
    sizetokens = newsizetokens;
  }
  tokens[ntokens++] = res;
  ntoken = 0;
}

static int parseline (FILE * file) {
  while (ntokens > 0) free (tokens[--ntokens]);
  ntoken = 0;
  for (;;) {
    int ch = getc (file);
    if (ch == EOF || ch == '\n') break;
    if (ch == ' ' || ch  == '\t' || ch == '\r') {
      if (ntoken) pushtoken ();
      continue;
    }
    if (ntoken == sizetoken) {
      int newsizetoken = sizetoken ? 2*sizetoken : 1;
      token = realloc (token, newsizetoken);
      sizetoken = newsizetoken;
    }
    token[ntoken++] = ch;
  }
  if (ntoken) pushtoken ();
  return ntokens;
}

static int loadzummary (Zummary * z, const char * path) {
  FILE * file = fopen (path, "r");
  msg (1, "trying to load zummary '%s'", path);
  if (!file) {
    msg (1, "could not open zummary '%s'", path);
    return 0;
  }
  while (parseline (file))
    ;
  loaded++;
  return 0;
}

static int zummaryneedsupdate (Zummary * z, const char * path) {
  return 1;
}

#if 0
static int hasuffix (const char * str, const char * suffix) {
  int i = strlen (str), j = strlen (suffix);
  if (i < j) return 0;
  return !strcmp (str + i - j, suffix);
}
#endif

static char * stripsuffix (const char * str, const char * suffix) {
  int i = strlen (str), j = strlen (suffix), k;
  char * res;
  if (i < j) return 0;
  k = i - j;
  if (strcmp (str + k, suffix)) return 0;
  res = malloc (k + 1);
  res[k] = 0;
  while (k-- > 0) res[k] = str[k];
  return res;
}

static Entry * newentry (Zummary * z, const char * name) {
  Entry * res = malloc (sizeof *res);
  memset (res, 0, sizeof *res);
  res->zummary = z;
  res->name = strdup (name);
  return res;
}

static void updatezummary (Zummary * z) {
  struct dirent * dirent;
  DIR * dir;
  msg (1, "updating zummary for directory '%s'", z->path);
  if (!(dir = opendir (z->path)))
    die ("can not open directory '%s'", z->path);
  z->count = 0;
  while ((dirent = readdir (dir))) {
    char * base, * logname, * logpath;
    const char * errname = dirent->d_name;
    msg (3, "checking '%s'", errname);
    if (!(base = stripsuffix (errname, ".err"))) {
      msg (3, "skipping '%s'", errname);
      continue;
    }
    logname = appendstr (base, ".log");
    logpath = appendtopath (z->path, logname);
    if (isfile (logpath)) {
      char * errpath = appendtopath (z->path, errname);
      Entry * e = newentry (z, base);
      assert (isfile (errpath));
      z->count++;
      if (z->last) z->last->next = e;
      else z->first = e;
      z->last = e;
      z->unknown++;
      free (errpath);
    } else msg (3, "missing '%s'", logpath);
    free (logpath);
    free (logname);
    free (base);
  }
  (void) closedir (dir);
  msg (1, "found %d entries in '%s'", z->count, z->path);
  updated++;
}

static void writezummary (Zummary * z, const char * path) {
  msg (1, "writing zummary '%s'", path);
  written++;
}

static void zummarize (const char * path) {
  char * pathtozummary;
  int update;
  Zummary * z;
  assert (isdir (path));
  z = newzummary (path);
  msg (1, "zummarizing directory %s", path);
  pathtozummary = appendtopath (path, "zummary");
  update = 1;
  if (!isfile (pathtozummary))
    msg (1, "zummary file '%s' not found", pathtozummary);
  else if (!loadzummary (z, pathtozummary))
    msg (1, "failed to load zummary '%s'", pathtozummary);
  else if (zummaryneedsupdate (z, pathtozummary))
    msg (1, "zummary '%s' needs update", pathtozummary);
  else update = 0;
  if (update) updatezummary (z), writezummary (z, pathtozummary);
  free (pathtozummary);
}

static void reset () {
  int i;
  for (i = 0; i < nzummaries; i++) {
    Zummary * z = zummaries[i];
    Entry * e, * n;
    for (e = z->first; e; e = n) {
      n = e->next;
      free (e->name);
      free (e);
    }
    free (z->path);
    free (z);
  }
  free (zummaries);
  for (i = 0; i < ntokens; i++) free (tokens[i]);
  free (tokens);
  free (token);
}

int main (int argc, char ** argv) {
  int i, count = 0;
  for (i = 1; i < argc; i++) {
    if (!strcmp (argv[i], "-h")) usage ();
    else if (!strcmp (argv[i], "-v")) verbose++;
    else if (argv[i][0] == '-') die ("invalid option '%s'", argv[i]);
    else if (!isdir (argv[i]))
      die ("argument '%s' not a directory", argv[i]);
    else count++;
  }
  if (!count) die ("no directory specified");
  for (i = 1; i < argc; i++)
    if (argv[i][0] != '-')
      zummarize (argv[i]);
  reset ();
  msg (1, "%d loaded, %d updated, %d written", loaded, updated, written);
  return 0;
}
