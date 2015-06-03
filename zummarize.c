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
#include <limits.h>

typedef struct Entry {
  char * name;
  struct Zummary * zummary;
  struct Entry * next;
  double time, real, space;
  char timeout, memout, unknown;
  int res;
} Entry;

typedef struct Zummary {
  char * path;
  Entry * first, * last;
  int count, sat, unsat, memout, timeout, unknown;
  double time, real, space, tlim, rlim, slim;
} Zummary;

static int verbose, force;

static Zummary ** zummaries;
static int nzummaries, sizezummaries;
static int loaded, written, updated;

static char * token;
static int ntoken, sizetoken;
static int lineno;

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
"usage: zummarize [-h|-v|-f] [ <dir> ... ]\n"
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
  if (!res) die ("out of memory allocating zummary object");
  memset (res, 0, sizeof *res);
  res->path = strdup (path);
  if (!res->path) die ("out of memory copy zummary path");
  res->tlim = res->rlim = res->slim = -1;
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
  if (!res) die ("out of memory appending string");
  strcpy (res, a);
  strcpy (res + i, b);
  return res;
}

static char * appenpath (const char * prefix, const char * name) {
  char * res = malloc (strlen (prefix) + strlen (name) + 2);
  if (!res) die ("out of memory appending path");
  strcpy (res, prefix);
  stripleadingslash (res);
  strcat (res, "/");
  strcat (res, name);
  return res;
}

static void pushtokens () {
  char * res;
  int i;
  res = malloc (ntoken + 1);
  if (!res) die ("out of memory copying token");
  for (i = 0; i < ntoken; i++) res[i] = token[i];
  res[i] = 0;
  if (sizetokens == ntokens) {
    int newsizetokens = sizetokens ? 2*sizetokens : 1;
    tokens = realloc (tokens, newsizetokens * sizeof *tokens);
    if (!tokens) die ("out of memory reallocating token stack");
    sizetokens = newsizetokens;
  }
  if (ntokens == INT_MAX) die ("token stack overflow");
  tokens[ntokens++] = res;
  ntoken = 0;
}

static void pushtoken (int ch) {
  if (ntoken == sizetoken) {
    int newsizetoken = sizetoken ? 2*sizetoken : 1;
    token = realloc (token, newsizetoken);
    if (!token) die ("out of memory reallocating token buffer");
    sizetoken = newsizetoken;
  }
  if (ntoken == INT_MAX) die ("token buffer overflow");
  token[ntoken++] = ch;
}

static int parseline (FILE * file, int maxtokens) {
  int i, newline = 0;
  while (ntokens > 0) free (tokens[--ntokens]);
  ntoken = 0;
  for (;;) {
    int ch = getc (file);
    if (ch == EOF) break;
    if (ch == '\n') { newline = 1; break; }
    if (ch == ' ' || ch  == '\t' || ch == '\r') {
      assert (ntokens < maxtokens || !ntoken);
      if (ntoken) pushtokens ();
      continue;
    }
    if (ntokens < maxtokens) pushtoken (ch);
    else assert (!ntoken);
  }
  assert (ntokens < maxtokens || !ntoken);
  if (ntoken) pushtokens ();
  if (verbose > 2)
    for (i = 0; i < ntokens; i++)
      msg (3, "token[%d,%d] %s", lineno, i, tokens[i]);
  if (newline) lineno++;
  return ntokens;
}

static int loadzummary (Zummary * z, const char * path) {
  FILE * file = fopen (path, "r");
  msg (1, "trying to load zummary '%s'", path);
  if (!file) {
    msg (1, "could not open zummary '%s'", path);
    return 0;
  }
  lineno = 1;
  while (parseline (file, INT_MAX))
    ;
  loaded++;
  return 0;
}

static int zummaryneedsupdate (Zummary * z, const char * path) {
  return 1;
}

static char * stripsuffix (const char * str, const char * suffix) {
  int i = strlen (str), j = strlen (suffix), k;
  char * res;
  if (i < j) return 0;
  k = i - j;
  if (strcmp (str + k, suffix)) return 0;
  res = malloc (k + 1);
  if (!res) die ("out of memory stripping suffix");
  res[k] = 0;
  while (k-- > 0) res[k] = str[k];
  return res;
}

static Entry * newentry (Zummary * z, const char * name) {
  Entry * res = malloc (sizeof *res);
  if (!res) die ("out of memory allocating entry object");
  memset (res, 0, sizeof *res);
  res->zummary = z;
  res->name = strdup (name);
  if (!res->name) die ("out of memory copying entry name");
  return res;
}

enum {
  TLIM   = 0,
  RLIM   = 1,
  SLIM   = 2,
  STATUS = 3,
  RESULT = 4,
  TIME   = 5,
  REAL   = 6,
  SPACE  = 7,
  MAX    = 8,
};

#define FOUND(FIELD,STR) \
do { \
  checked++; \
  if (found[FIELD]) break; \
  msg (1, \
    "error file '%s' is missing '%s' line", \
    errpath, STR); \
  res = 0; \
} while (0)

static int parserrfile (Entry * e, const char * errpath) {
  FILE * file;
  int found[MAX], i, checked, res = 1;
  msg (2, "parsing error file '%s'", errpath);
  file = fopen (errpath, "r");
  if (!file) die ("can not read '%s'", errpath);
  for (i = 0; i < MAX; i++) found[i] = 0;
  lineno = 1;
  while (parseline (file, 5)) {
    if (!ntokens) continue;
    if (strcmp (tokens[0], "[runlim]") &&
        strcmp (tokens[0], "[run]"))
      continue;
    if (ntokens > 3 &&
       !strcmp (tokens[1], "time") &&
       !strcmp (tokens[2], "limit:")) {
      double tlim = atof (tokens[3]);
      msg (2, "found time limit '%.0f' in '%s'", tlim, errpath);
      if (found[TLIM]) {
	msg (1,
	  "error file '%s' contains two 'time limit:' lines",
	  errpath);
	res = 0;
      } else {
	found[TLIM] = 1;
	if (tlim <= 0) {
	  msg (1,
	    "error file '%s' with invalid time limit '%.0f'",
	    errpath, tlim);
	  res = 0;
	} else if (e->zummary->tlim < 0) {
	  msg (1, "assuming time limit '%.0f'", tlim);
	  e->zummary->tlim = tlim;
	} else if (e->zummary->tlim != tlim) {
	  msg (1,
	    "error file '%s' with different time limit '%.0f'",
	    errpath, tlim);
	  res = 0;
	}
      }
    } else if (ntokens > 4 &&
	       !strcmp (tokens[1], "real") &&
	       !strcmp (tokens[2], "time") &&
	       !strcmp (tokens[3], "limit:")) {
      double rlim = atof (tokens[4]);
      msg (2, "found real time limit '%.0f' in '%s'", rlim, errpath);
      if (found[RLIM]) {
	msg (1,
	  "error file '%s' contains two 'real time limit:' lines",
	  errpath);
	res = 0;
      } else {
	found[RLIM] = 1;
	if (rlim <= 0) {
	  msg (1,
	    "error file '%s' with invalid real time limit '%.0f'",
	    errpath, rlim);
	  res = 0;
	} else if (e->zummary->rlim < 0) {
	  msg (1, "assuming real time limit '%.0f'", rlim);
	  e->zummary->rlim = rlim;
	} else if (e->zummary->rlim != rlim) {
	  msg (1,
	    "error file '%s' with different real time limit '%.0f'",
	    errpath, rlim);
	  res = 0;
	}
      }
    } else if (ntokens > 3 &&
	       !strcmp (tokens[1], "space") &&
	       !strcmp (tokens[2], "limit:")) {
      double slim = atof (tokens[3]);
      msg (2, "found space limit '%.0f' in '%s'", slim, errpath);
      if (found[SLIM]) {
	msg (1,
	  "error file '%s' contains two 'space limit:' lines",
	  errpath);
	res = 0;
      } else {
	found[SLIM] = 1;
	if (slim <= 0) {
	  msg (1,
	    "error file '%s' with invalid space limit '%.0f'",
	    errpath, slim);
	  res = 0;
	} else if (e->zummary->slim < 0) {
	  msg (1, "assuming space limit '%.0f'", slim);
	  e->zummary->slim = slim;
	} else if (e->zummary->slim != slim) {
	  msg (1,
	    "error file '%s' with different space limit '%.0f'",
	    errpath, slim);
	  res = 0;
	}
      }
    } else if (ntokens > 2 &&
	      !strcmp (tokens[1], "status:")) {
      if (found[STATUS]) {
	msg (1, "error file '%s' contains two 'status:' lines", errpath);
	res = 0;
      } else if (!strcmp (tokens[2], "ok")) {
	msg (2, "found 'ok' status in '%s'", errpath);
	found[STATUS] = 1;
      } else if (ntokens > 4 &&
		 !strcmp (tokens[2], "out") &&
		 !strcmp (tokens[3], "of") &&
		 !strcmp (tokens[4], "time")) {
	msg (2, "found 'out of time' status in '%s'", errpath);
	found[STATUS] = 1;
	e->timeout = 1;
	res = 0;
      } else if (ntokens > 4 &&
		 !strcmp (tokens[2], "out") &&
		 !strcmp (tokens[3], "of") &&
		 !strcmp (tokens[4], "memory")) {
	msg (2, "found 'out of memory' status in '%s'", errpath);
	found[STATUS] = 1;
	e->memout = 1;
	res = 0;
      } else {
	msg (1, "invalid status line in '%s'", errpath);
	found[STATUS] = 1;
	res = 0;
      }
    } else if (ntokens > 2 &&
	       !strcmp (tokens[1], "result:")) {
      if (found[RESULT]) {
	msg (1, "error file '%s' contains two 'result:' lines", errpath);
	res = 0;
      } else {
	int result = atoi (tokens[2]);
	found[RESULT] = 1;
	if (!result) {
	  msg (2, "found '0' result in '%s'", errpath);
	  e->res = 0;
	} else if (result == 10) {
	  msg (2, "found '10' (SAT) result in '%s'", errpath);
	  e->res = 10;
	} else if (result == 20) {
	  msg (2, "found '20' (UNSAT) result in '%s'", errpath);
	  e->res = 20;
	} else {
	  msg (2, "found invalid '%d' result in '%s'", result, errpath);
	  res = 0;
	}
      }
    } else if (ntokens > 2 &&
               !strcmp (tokens[1], "time:")) {
      double time = atof (tokens[2]);
      msg (2, "found time '%.2f' in '%s'", time, errpath);
      if (found[TIME]) {
	msg (1, "error file '%s' contains two 'time:' lines", errpath);
	res = 0;
      } else {
	found[TIME] = 1;
	if (time < 0) {
	  msg (1, "invalid time '%.2f' in '%s'", time, errpath);
	  res = 0;
	} else e->time = time;
      }
    } else if (ntokens > 2 &&
               !strcmp (tokens[1], "real:")) {
      double real = atof (tokens[2]);
      msg (2, "found real time '%.2f' in '%s'", real, errpath);
      if (found[REAL]) {
	msg (1, "error file '%s' contains two 'real:' lines", errpath);
	res = 0;
      } else {
	found[REAL] = 1;
	if (real < 0) {
	  msg (1, "invalid real time '%.2f' in '%s'", real, errpath);
	  res = 0;
	} else e->real = real;
      }
    } else if (ntokens > 2 &&
               !strcmp (tokens[1], "space:")) {
      double space = atof (tokens[2]);
      msg (2, "found space '%.1f' in '%s'", space, errpath);
      if (found[SPACE]) {
	msg (1, "error file '%s' contains two 'space:' lines", errpath);
	res = 0;
      } else {
	found[SPACE] = 1;
	if (space < 0) {
	  msg (1, "invalid space '%.1f' in '%s'", space, errpath);
	  res = 0;
	} else e->space = space;
      }
    }
  }
  fclose (file);
  checked = 0;
  FOUND (TLIM,   "time limit:");
  FOUND (RLIM,   "real time limit:");
  FOUND (SLIM,   "space limit:");
  FOUND (STATUS, "status:");
  FOUND (RESULT, "result:");
  FOUND (TIME,   "time:");
  FOUND (REAL,   "real:");
  FOUND (SPACE,  "space:");
  assert (checked == MAX);
  if (!res) {
    if (e->res) e->res = 0;
    if (!e->timeout && !e->memout && !e->unknown) e->unknown = 1;
  }
  return res;
}

static int cmpentry4qsort (const void * p, const void * q) {
  Entry * d = *(Entry**) p, * e = *(Entry**) q;
  return strcmp (d->name, e->name);
}

static void sortzummary (Zummary * z) {
  Entry ** entries, * p;
  int i;
  if (!z->count) return;
  entries = malloc (z->count * sizeof *entries);
  if (!entries) die ("out of memory allocating sorting array");
  i = 0;
  for (p = z->first; p; p = p->next)
    assert (i < z->count), entries[i++] = p;
  assert (i == z->count);
  qsort (entries, z->count, sizeof *entries, cmpentry4qsort);
  z->first = entries[0];
  for (i = 0; i < z->count - 1; i++)
    entries[i]->next = entries[i+1];
  (z->last = entries[i])->next = 0;
  free (entries);
}

static void parselogfile (Entry * e, const char * logpath) {
  const char * other = 0;
  int found, res;
  FILE * file;
  assert (!e->res);
  assert (!e->timeout), assert (!e->memout), assert (!e->unknown);
  msg (2, "parsing log file '%s'", logpath);
  file = fopen (logpath, "r");
  if (!file) die ("can not read log file '%s'", logpath);
  res = found = 0;
  while (parseline (file, 2)) {
    if (ntokens == 1) {
      if (!strcmp (tokens[0], "sat")) {
	msg (2, "found 'sat' line in '%s'", logpath);
	if (found)
	  die ("two results '%s' and 'sat' in '%s'",
	       other, logpath);
	other = "sat";
	found = 1;
	res = 10;
      } else if (!strcmp (tokens[0], "unsat")) {
	msg (2, "found 'unsat' line in '%s'", logpath);
	if (found)
	  die ("two results '%s' and 'unsat' in '%s'",
	       other, logpath);
	other = "unsat";
	found = 1;
	res = 20;
      } else if (!strcmp (tokens[0], "1")) {
	msg (2, "found '1' line in '%s'", logpath);
	if (found)
	  die ("two results '%s' and '1' in '%s'",
	       other, logpath);
	other = "1";
	found = 1;
	res = 10;
      } else if (!strcmp (tokens[0], "0")) {
	msg (2, "found '0' line in '%s'", logpath);
	if (found)
	  die ("two results '%s' and '0' in '%s'",
	       other, logpath);
	other = "0";
	found = 1;
	res = 10;
      }
    } else if (ntokens == 2 && !strcmp (tokens[0], "s")) {
      if (!strcmp (tokens[1], "SATISFIABLE")) {
	msg (2, "found 's SATISFIABLE' line in '%s'", logpath);
	if (found)
	  die ("two results '%s' and 's SATISFIABLE' in '%s'",
	       other, logpath);
	other = "s SATISFIABLE";
	found = 1;
	res = 10;
      } else if (!strcmp (tokens[1], "UNSATISFIABLE")) {
	msg (2, "found 's UNSATISFIABLE' line in '%s'", logpath);
	if (found)
	  die ("two results '%s' and 's UNSATISFIABLE' in '%s'",
	       other, logpath);
	other = "s UNSATISFIABLE";
	found = 1;
	res = 20;
      }
    }
  }
  fclose (file);
  assert (found <= 1);
  assert (!e->res);
  if (found) {
    assert (res == 10 || res == 20);
    e->res = res;
  } else {
    msg (2, "no proper sat/unsat line found in '%s'", logpath);
    assert (!res);
  }
}

static void updatezummary (Zummary * z) {
  struct dirent * dirent;
  DIR * dir;
  Entry * e;
  msg (1, "updating zummary for directory '%s'", z->path);
  if (!(dir = opendir (z->path)))
    die ("can not open directory '%s'", z->path);
  z->count = 0;
  while ((dirent = readdir (dir))) {
    char * base, * logname, * logpath;
    const char * errname = dirent->d_name;
    msg (2, "checking '%s'", errname);
    if (!(base = stripsuffix (errname, ".err"))) {
      msg (2, "skipping '%s'", errname);
      continue;
    }
    logname = appendstr (base, ".log");
    logpath = appenpath (z->path, logname);
    if (isfile (logpath)) {
      char * errpath = appenpath (z->path, errname);
      e = newentry (z, base);
      assert (isfile (errpath));
      z->count++;
      if (z->last) z->last->next = e;
      else z->first = e;
      z->last = e;
      if (!parserrfile (e, errpath)) assert (!e->res);
      else if (!e->res) parselogfile (e, logpath);
      else assert (e->res == 10 || e->res == 20);
      free (errpath);
      assert (!e->res || e->res == 10 || e->res == 20);
      assert (!e->timeout || !e->res);
      assert (!e->memout || !e->res);
      assert (!e->unknown || !e->res);
    } else msg (1, "missing '%s'", logpath);
    free (logpath);
    free (logname);
    free (base);
  }
  (void) closedir (dir);
  msg (1, "found %d entries in '%s'", z->count, z->path);
  if (z->tlim < 0) die ("no time limit in '%s'", z->path);
  if (z->rlim < 0) die ("no real time limit in '%s'", z->path);
  if (z->slim < 0) die ("no space limit in '%s'", z->path);
  if (nzummaries > 1) {
    if (z->tlim != zummaries[0]->tlim)
      die ("different time limit '%.0f' in '%s'", z->tlim, z->path);
    if (z->rlim != zummaries[0]->rlim)
      die ("different real time limit '%.0f' in '%s'", z->rlim, z->path);
    if (z->slim != zummaries[0]->slim)
      die ("different space limit '%.0f' in '%s'", z->slim, z->path);
  }
  for (e = z->first; e; e = e->next) {
    if (e->res < 10) continue;
    assert (e->res == 10 || e->res == 20);
    assert (!e->timeout), assert (!e->memout), assert (!e->unknown);
    if (e->time > z->tlim) {
      msg (1,
        "error file '%s/%s.err' actually exceeds time limit",
	z->path, e->name);
      e->timeout = 1;
      e->res = 0;
    } else if (e->real > z->rlim) {
      msg (1,
        "error file '%s/%s.err' actually exceeds real time limit",
	z->path, e->name);
      e->timeout = 1;
      e->res = 0;
    } else if (e->space > z->slim) {
      msg (1,
        "error file '%s/%s.err' actually exceeds space limit",
	z->path, e->name);
      e->memout = 1;
      e->res = 0;
    }
  }
  for (e = z->first; e; e = e->next) {
#ifndef NDEBUG
    if (e->res)
      assert (e->res == 10 || e->res == 20),
      assert (!e->memout), assert (!e->unknown), assert (!e->unknown);
    assert (!e->timeout || !e->memout);
    assert (!e->timeout || !e->unknown);
    assert (!e->memout || !e->unknown);
#endif
         if (e->res == 10) z->sat++;
    else if (e->res == 20) z->unsat++;
    else if (e->timeout) assert (!e->res), e->res = 1, z->timeout++;
    else if (e->memout) assert (!e->res), e->res = 2, z->memout++;
    else assert (e->unknown), assert (!e->res), e->res = 3, z->unknown++;

    if (e->res == 10 || e->res == 20) z->time += e->time, z->real += e->real;
    z->space += e->space;
  }
  assert (z->count == z->sat + z->unsat + z->timeout + z->memout + z->unknown);
  sortzummary (z);
  updated++;
}

static void writezummary (Zummary * z, const char * path) {
  FILE * file;
  Entry * e;
  file = fopen ("/tmp/zummary", "w");		// TODO set this to path
  if (!file) die ("can not write '%s'", path);
  for (e = z->first; e; e = e->next)
    fprintf (file,
      "%s %d %.2f %.2f %.1f\n",
      e->name, e->res, e->time, e->real, e->space);
  fclose (file);
  msg (1, "written %d entries to zummary '%s'", z->count, path);
  written++;
}

static void zummarize (const char * path) {
  char * pathtozummary;
  int update;
  Zummary * z;
  assert (isdir (path));
  z = newzummary (path);
  msg (1, "zummarizing directory %s", path);
  pathtozummary = appenpath (path, "zummary");
  update = 1;
  if (!isfile (pathtozummary))
    msg (1, "zummary file '%s' not found", pathtozummary);
  else if (force)
    msg (1, "forcing update of '%s' (through '-f' option)", pathtozummary);
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
    else if (!strcmp (argv[i], "-f")) force++;
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
