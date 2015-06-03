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

typedef struct Symbol {
  char * name;
  struct Entry * first, * last;
  struct Symbol * next;
} Symbol;

typedef struct Entry {
  const char * name;
  struct Zummary * zummary;
  struct Entry * next, * chain;
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

static int verbose, force, nowrite;

static Zummary ** zummaries;
static int nzummaries, sizezummaries;
static int loaded, written, updated;

static char * token;
static int ntoken, sizetoken;
static int lineno;

static char ** tokens;
static int ntokens, sizetokens;

static Symbol ** symtab;
static unsigned nsyms, sizesymtab;
static unsigned long long searches, collisions;

static int usereal;

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
"usage: zummarize [-h|-v|-f|--no-write] [ <dir> ... ]\n"
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

static void striptrailingslash (char * str) {
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
  striptrailingslash (res->path);
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

static char * appendpath (const char * prefix, const char * name) {
  char * res = malloc (strlen (prefix) + strlen (name) + 2);
  if (!res) die ("out of memory appending path");
  strcpy (res, prefix);
  striptrailingslash (res);
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

static unsigned primes[] = { 111111113, 222222227, 333333349, 444444457 };

#define NPRIMES (sizeof primes/sizeof primes[0])

static unsigned hashstr (const char * name) {
  unsigned res = 0, i = 0;
  const char * p;
  char ch;
  for (p = name; (ch = *p); p++) {
    res += primes[i++] * (unsigned) ch;
    if (i == NPRIMES) i = 0;
  }
  return res;
}

static void enlarge () {
  unsigned newsizesymtab = sizesymtab ? 2*sizesymtab : 1;
  Symbol *s, *n, ** newsymtab;
  unsigned h, i;
  size_t bytes = newsizesymtab * sizeof *newsymtab;
  newsymtab = malloc (bytes);
  if (!newsymtab) die ("out of memory reallocating symbol table");
  memset (newsymtab, 0, bytes);
  for (i = 0; i < sizesymtab; i++) {
    for (s = symtab[i]; s; s = n) {
      n = s->next;
      h = hashstr (s->name) & (newsizesymtab - 1);
      s->next = newsymtab[h];
      newsymtab[h] = s;
    }
  }
  free (symtab);
  symtab = newsymtab;
  sizesymtab = newsizesymtab;
}

static Entry * newentry (Zummary * z, const char * name) {
  Entry * res = malloc (sizeof *res);
  Symbol * s, ** p;
  unsigned h;
  if (!res) die ("out of memory allocating entry object");
  memset (res, 0, sizeof *res);
  res->zummary = z;
  if (nsyms == sizesymtab) enlarge ();
  h = hashstr (name) & (sizesymtab - 1);
  searches++;
  for (p = symtab + h; (s = *p) && strcmp (s->name, name); p = &s->next)
    collisions++;
  if (!s) {
    s = malloc (sizeof *s);
    if (!s) die ("out of memory allocating symbol object");
    memset (s, 0, sizeof *s);
    s->name = strdup (name);
    if (!s->name) die ("out of memory copying symbol name");
    nsyms++;
    *p = s;
  }
  res->name = s->name;
  if (s->last) s->last->chain = res;
  else s->first = res;
  s->last = res;
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
    logpath = appendpath (z->path, logname);
    if (isfile (logpath)) {
      char * errpath = appendpath (z->path, errname);
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
  fputs (" result time real space\n", file);
  for (e = z->first; e; e = e->next)
    fprintf (file,
      "%s %d %.2f %.2f %.1f\n",
      e->name, e->res, e->time, e->real, e->space);
  fclose (file);
  msg (1, "written %d entries to zummary '%s'", z->count, path);
  written++;
}

static void zummarizeone (const char * path) {
  char * pathtozummary;
  int update;
  Zummary * z;
  assert (isdir (path));
  z = newzummary (path);
  msg (1, "zummarizing directory %s", path);
  pathtozummary = appendpath (path, "zummary");
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
  if (update) {
    updatezummary (z);
    if (!nowrite) writezummary (z, pathtozummary);
  }
  free (pathtozummary);
}

static int cmpsyms4qsort (const void * p, const void * q) {
  Symbol * s = * (Symbol**) p, * t = *(Symbol **) q;
  return strcmp (s->name, t->name);
}

static void sortsymbols () {
  Symbol * p = 0, * s, * n;
  int i;
  for (i = 0; i < sizesymtab; i++)
    for (s = symtab[i]; s; s = n)
      n = s->next, s->next = p, p = s;
  for (i = 0; p; p = p->next)
    symtab[i++] = p;
  assert (i == nsyms);
  qsort (symtab, nsyms, sizeof *symtab, cmpsyms4qsort);
  msg (2, "sorted %d symbols", nsyms);
}

static void discrepancies () {
  int i;
  for (i = 0; i < nsyms; i++) {
    Symbol * s = symtab[i];
    int sat = 0, unsat = 0;
    Entry * e;
    for (e = s->first; e; e = e->chain) {
      assert (e->name == s->name);
      if (e->res == 10) sat++;
      if (e->res == 20) unsat++;
    }
    if (!sat) continue;
    if (!unsat) continue;
    fflush (stdout);
    fprintf (stderr,
      "*** zummarize: discrepancy on '%s' with %d SAT and %d UNSAT\n",
      s->name, sat, unsat);
    for (e = s->first; e; e = e->chain) {
      if (e->res < 10) continue;
      assert (e->res == 10 || e->res == 20);
      fprintf (stderr,
        "*** zummarize: '%s/%s' %s\n",
	e->zummary->path, s->name, 
	(e->res == 10 ? "SAT" : "UNSAT"));
    }
    fflush (stderr);
    exit (1);
  }
  msg (1, "no discrepancies found");
}

static void checklimits () {
  Zummary * y, * z;
  int i;
  if (nzummaries <= 1) return;
  y = zummaries[0];
  for (i = 1; i < nzummaries; i++) {
    z = zummaries[i];
    if (y->tlim != z->tlim)
      die ("different time limit in '%s' and '%s'", y->path, z->path);
    if (y->rlim != z->rlim)
      die ("different real time limit in '%s' and '%s'", y->path, z->path);
    if (y->slim != z->slim)
      die ("different space limit in '%s' and '%s'", y->path, z->path);
  }
  msg (1, "all zummaries have the same time and space limits");
  if (y->tlim >= y->rlim) {
    msg (1, "zummarizing over real time (not process time)");
    usereal = 1;
  } else {
    msg (1, "zummarizing over process time (not real time)");
    usereal = 0;
  }
}

static int cmpdouble (double a, double b) {
  if (a < b) return -1;
  if (b < a) return 1;
  return 0;
}

static int cmpzummaries4qsort (const void * p, const void * q) {
  Zummary * y = * (Zummary**) p, * z = * (Zummary**) q;
  int a = y->sat + y->unsat, b = z->sat + z->unsat;
  int res = b - a;
  if (res) return res;
  if (usereal) {
    if ((res = cmpdouble (y->real, z->real))) return res;
    if ((res = cmpdouble (y->time, z->time))) return res;
  } else {
    if ((res = cmpdouble (y->time, z->time))) return res;
    if ((res = cmpdouble (y->real, z->real))) return res;
  }
  if ((res = cmpdouble (y->space, z->space))) return res;
  return strcmp (y->path, z->path);
}

static void sortzummaries () {
  qsort (zummaries, nzummaries, sizeof *zummaries, cmpzummaries4qsort);
  msg (2, "sorted all zummaries");
}

static void printsummaries () {
  char fmt[20];
  int len = 0, i;
  for (i = 0; i < nzummaries; i++) {
    Zummary * z = zummaries[i];
    int tmp = strlen (z->path);
    if (tmp > len) len = tmp;
  }
  sprintf (fmt, "%%%ds", len);
  printf (fmt, "");
  printf (" %5s %5s %5s %5s %5s %3s %3s %3s %7s %7s %7s\n",
    "count", "solve", "sat", "unsat", "fail", "to", "mo", "uo",
    "time", "real", "space");
  for (i = 0; i < nzummaries; i++) {
    Zummary * z = zummaries[i];
    int solved = z->sat + z->unsat;
    int failed = z->timeout + z->memout + z->unknown;
    assert (solved + failed == z->count);
    printf (fmt, z->path);
    printf (" %5d %5d %5d %5d %5d %3d %3d %3d %7.0f %7.0f %7.0f\n",
      z->count,
      solved, z->sat, z->unsat,
      failed, z->timeout, z->memout, z->unknown,
      z->time, z->real, z->space);
  }
}

static void zummarizeall () {
  msg (2,
    "%u benchmarks (%llu searched, %llu collisions %.2f on average)",
    nsyms, searches, collisions,
    searches ? collisions/(double)searches : 1.0);
  sortsymbols ();
  discrepancies ();
  checklimits ();
  sortzummaries ();
  printsummaries ();
}

static void reset () {
  int i;
  for (i = 0; i < nzummaries; i++) {
    Zummary * z = zummaries[i];
    Entry * e, * n;
    for (e = z->first; e; e = n) {
      n = e->next;
      free (e);
    }
    free (z->path);
    free (z);
  }
  free (zummaries);
  for (i = 0; i < ntokens; i++) free (tokens[i]);
  free (tokens);
  free (token);
  for (i = 0; i < nsyms; i++) {
    Symbol * s = symtab[i];
    free (s->name);
    free (s);
  }
  free (symtab);
}

int main (int argc, char ** argv) {
  int i, count = 0;
  for (i = 1; i < argc; i++) {
    if (!strcmp (argv[i], "-h")) usage ();
    else if (!strcmp (argv[i], "-v")) verbose++;
    else if (!strcmp (argv[i], "-f")) force++;
    else if (!strcmp (argv[i], "--no-write")) nowrite = 1;
    else if (argv[i][0] == '-') die ("invalid option '%s'", argv[i]);
    else if (!isdir (argv[i]))
      die ("argument '%s' not a directory", argv[i]);
    else count++;
  }
  if (!count) die ("no directory specified");
  for (i = 1; i < argc; i++)
    if (argv[i][0] != '-')
      zummarizeone (argv[i]);
  zummarizeall ();
  reset ();
  msg (1, "%d loaded, %d updated, %d written", loaded, updated, written);
  return 0;
}
