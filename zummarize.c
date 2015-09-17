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
#ifndef NMMAP
#include <sys/mman.h>
#include <fcntl.h>
#endif

typedef struct Symbol {
  char * name;
  struct Entry * first, * last;
  struct Symbol * next;
} Symbol;

typedef struct Entry {
  const char * name;
  struct Zummary * zummary;
  struct Entry * next, * chain;
  char tio, meo, unk, dis, s11, si6;
  double tim, wll, mem;
  int res, bnd, maxubnd, minsbnd;
} Entry;

typedef struct Zummary {
  char * path, dirty;
  Entry * first, * last;
  int cnt, sol, sat, uns, dis, fld, tio, meo, s11, si6, unk, bnd;
  double tim, wll, mem, max, tlim, rlim, slim;
} Zummary;

static int verbose, force, nowrite, nobounds;

static Zummary ** zummaries;
static int nzummaries, sizezummaries;
static int loaded, written, updated;

static char * token;
static int stoken, ntoken, sizetoken;
static int lineno;

static const char ** tokens;
static int ntokens, sizetokens;

static Symbol ** symtab;
static unsigned nsyms, sizesymtab;
static unsigned long long searches, collisions;

static int usereal;

static void die (const char * fmt, ...) {
  va_list ap;
  fputs ("*** zummarize error: ", stdout);
  va_start (ap, fmt);
  vfprintf (stdout, fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  exit (1);
}

static void wrn (const char * fmt, ...) {
  va_list ap;
  fputs ("*** zummarize warning: ", stdout);
  va_start (ap, fmt);
  vfprintf (stdout, fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
}

static void msg (int level, const char * fmt, ...) {
  va_list ap;
  if (verbose < level) return;
  fputs ("[zummarize] ", stdout);
  va_start (ap, fmt);
  vfprintf (stdout, fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

#ifndef NMMAP

static struct { int opened; int fd; char * start, * top, * end; } input;

static size_t file_size (const char * path) {
  struct stat buf;
  if (stat (path, &buf)) die ("failed to determine size of '%s'", path);
  return buf.st_size;
}

static void open_input (const char * path) {
  size_t bytes;
  assert (!input.opened);
  bytes = file_size (path);
  input.fd = open (path, O_RDONLY);
  if (input.fd == -1) die ("failed to open '%s'", path);
  input.start =
    mmap (0, bytes, PROT_READ, MAP_PRIVATE | MAP_POPULATE, input.fd, 0);
  if (!input.start) die ("failed to map '%s' to memory", path);
  msg (2, "memory mapped '%s' of size %ld", path, (long) bytes);
  input.top = input.start;
  input.end = input.start + bytes;
  input.opened = 1;
}

static int nextch () {
  assert (input.opened);
  assert (input.top <= input.end);
  if (input.top == input.end) return EOF;
  return *input.top++;
}

static void close_input () {
  size_t bytes;
  assert (input.opened);
  bytes = input.end - input.start;
  if (munmap (input.start, bytes))
    wrn ("failed to unmap file from memory");
  if (close (input.fd))
    wrn ("failed to close file");
  input.opened = 0;
}

#else

static FILE * input;

static void open_input (const char * path) {
  assert (!input);
  if (!(input = fopen (path, "r")))
    die ("failed to open '%s'", path);
}

static int nextch () {
  assert (input);
#ifndef NGETCUNLOCKED
  return getc_unlocked (input);
#else
  return getc (input);
#endif
}

static void close_input () {
  assert (input);
  fclose (input);
  input = 0;
}

#endif

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
    if (!zummaries) die ("out of memory reaallocating zummaries stack");
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

static void pushtoken (int ch) {
  if (ntoken == sizetoken) {
    int newsizetoken = sizetoken ? 2*sizetoken : 1;
    char * oldtoken = token;
    long delta;
    token = realloc (token, newsizetoken);
    if (!token) die ("out of memory reallocating token buffer");
    sizetoken = newsizetoken;
    if ((delta = token - oldtoken)) {
      int i;
      for (i = 0; i < ntokens; i++)
	tokens[i] += delta;
    }
  }
  if (ntoken == INT_MAX) die ("token buffer overflow");
  token[ntoken++] = ch;
}

static int pusherrtokens () {
  const char * res;
  int skip;
  pushtoken (0);
  res = token + stoken;
  if (!ntokens &&
      strcmp (res, "[run]")&&
      strcmp (res, "[runlim]")) {
    msg (3, "skipping line starting with '%s'", res);
    skip = 1;
  } else if (ntokens == 1 &&
             !strcmp (res, "sample:")) {
    msg (3, "skipping sample line");
    skip = 1;
  } else skip = 0;
  if (skip) {
    int ch;
    while ((ch = nextch ()) != '\n')
      if (ch == EOF) break;
    if (ch == '\n') lineno++;
    ntokens = ntoken = stoken = 0;
    return 0;
  }
  if (sizetokens == ntokens) {
    int newsizetokens = sizetokens ? 2*sizetokens : 1;
    tokens = realloc (tokens, newsizetokens * sizeof *tokens);
    if (!tokens) die ("out of memory reallocating token stack");
    sizetokens = newsizetokens;
  }
  if (ntokens == INT_MAX) die ("token stack overflow");
  tokens[ntokens++] = res;
  stoken = ntoken;
  return 1;
}

static int parserrline () {
  int i, newline = 0, res = 1;
  stoken = ntoken = ntokens = 0;
  for (;;) {
    int ch = nextch ();
    if (ch == EOF) { res = 0; break; }
    if (ch == '\n') { newline = 1; break; }
    if (ch == ' ' || ch  == '\t' || ch == '\r') {
      assert (ntokens < 5 || ntoken == stoken);
      if (stoken < ntoken && !pusherrtokens ()) break;
      continue;
    }
    if (ntokens < 5) pushtoken (ch);
    else assert (stoken == ntoken);
  }
  assert (ntokens < 5 || stoken == ntoken);
  if (stoken < ntoken) (void) pusherrtokens ();
  if (verbose > 2)
    for (i = 0; i < ntokens; i++)
      msg (3, "token[%d,%d] %s", lineno, i, tokens[i]);
  if (newline) lineno++;
  return res;
}

static void pushzummarytokens () {
  const char * res;
  pushtoken (0);
  res = token + stoken;
  if (sizetokens == ntokens) {
    int newsizetokens = sizetokens ? 2*sizetokens : 1;
    tokens = realloc (tokens, newsizetokens * sizeof *tokens);
    if (!tokens) die ("out of memory reallocating token stack");
    sizetokens = newsizetokens;
  }
  if (ntokens == INT_MAX) die ("token stack overflow");
  tokens[ntokens++] = res;
  stoken = ntoken;
}

static int parsezummaryline () {
  int i, newline = 0;
  stoken = ntoken = ntokens = 0;
  for (;;) {
    int ch = nextch ();
    if (ch == EOF) break;
    if (ch == '\n') { newline = 1; break; }
    if (ch == ' ' || ch  == '\t' || ch == '\r') {
      if (stoken < ntoken) pushzummarytokens ();
      continue;
    }
    pushtoken (ch);
  }
  if (stoken < ntoken) pushzummarytokens ();
  if (verbose > 2)
    for (i = 0; i < ntokens; i++)
      msg (3, "token[%d,%d] %s", lineno, i, tokens[i]);
  if (newline) lineno++;
  return ntokens;
}

static int getmtime (const char * path, double * timeptr) {
  struct stat buf;
  if (stat (path, &buf)) {
    msg (1, "can not get modification time of '%s'", path);
    return 0;
  }
  msg (2, "modification time %.0f of '%s'", (double) buf.st_mtime, path);
  *timeptr = buf.st_mtime;
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

static int zummaryneedsupdate (Zummary * z, const char * path) {
  struct dirent * dirent;
  double ztime;
  int res = 0;
  DIR * dir;
  if (!getmtime (path, &ztime)) return 1;
  if (!(dir = opendir (z->path)))
    die ("can not open directory '%s' for checking times", z->path);
  while (!res && (dirent = readdir (dir))) {
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
      double etime;
      if (getmtime (errpath, &etime)) {
	if (etime <= ztime) {
	  double ltime;
	  if (getmtime (logpath, &ltime)) {
	    if (ltime > ztime) {
	      msg (1, "log file '%s' more recently modified", logpath);
	      res = 1;
	    }
	  } else res = 1;
	} else {
	  msg (1, "error file '%s' more recently modified", errpath);
	  res = 1;
	}
      } else res = 1;
    } else msg (1, "missing '%s'", logpath);
    free (logpath);
    free (logname);
    free (base);
  }
  (void) closedir (dir);
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

static void enlargesymtab () {
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
  res->bnd = res->maxubnd = res->minsbnd = -1;
  if (nsyms == sizesymtab) enlargesymtab ();
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
  z->cnt++;
  if (z->last) z->last->next = res;
  else z->first = res;
  z->last = res;
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
  int found[MAX], i, checked, res = 1;
  msg (2, "parsing error file '%s'", errpath);
  open_input (errpath);
  for (i = 0; i < MAX; i++) found[i] = 0;
  lineno = 1;
  while (parserrline ()) {
    if (!ntokens) continue;
    assert (!strcmp (tokens[0], "[run]") || !strcmp (tokens[0], "[runlim]"));
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
      } else if (!strcmp (tokens[2], "signal(11)")) {
	msg (2, "found 'ok' status in '%s'", errpath);
	found[STATUS] = 1;
	e->s11 = 1;
      } else if (!strcmp (tokens[2], "signal(6)")) {
	msg (2, "found 'ok' status in '%s'", errpath);
	found[STATUS] = 1;
	e->si6 = 1;
      } else if (ntokens > 4 &&
		 !strcmp (tokens[2], "out") &&
		 !strcmp (tokens[3], "of") &&
		 !strcmp (tokens[4], "time")) {
	msg (2, "found 'out of time' status in '%s'", errpath);
	found[STATUS] = 1;
	e->tio = 1;
	res = 0;
      } else if (ntokens > 4 &&
		 !strcmp (tokens[2], "out") &&
		 !strcmp (tokens[3], "of") &&
		 !strcmp (tokens[4], "memory")) {
	msg (2, "found 'out of memory' status in '%s'", errpath);
	found[STATUS] = 1;
	e->meo = 1;
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
	} else e->tim = time;
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
	} else e->wll = real;
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
	} else e->mem = space;
      }
    }
  }
  close_input ();
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
    if (!e->tio && !e->meo && !e->unk) e->unk = 1;
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
  if (!z->cnt) return;
  entries = malloc (z->cnt * sizeof *entries);
  if (!entries) die ("out of memory allocating sorting array");
  i = 0;
  for (p = z->first; p; p = p->next)
    assert (i < z->cnt), entries[i++] = p;
  assert (i == z->cnt);
  qsort (entries, z->cnt, sizeof *entries, cmpentry4qsort);
  z->first = entries[0];
  for (i = 0; i < z->cnt - 1; i++)
    entries[i]->next = entries[i+1];
  (z->last = entries[i])->next = 0;
  free (entries);
}

static int getposnum (int ch) {
  int res, digit;
  assert (isdigit (ch));
  res = ch - '0';
  while (isdigit (ch = nextch ())) {
    if (INT_MAX/10 < res) return -1;
    res *= 10;
    digit = (ch - '0');
    if (INT_MAX - digit < res) return -1;
    res += digit;
  }
  if (ch != '\n') return -1;
  return res;
}

static void parselogfile (Entry * e, const char * logpath) {
  const char * other = 0, * this = 0;
  int found, res, ch, bnd;
  assert (!e->res);
  assert (!e->tio), assert (!e->meo), assert (!e->unk);
  msg (2, "parsing log file '%s'", logpath);
  open_input (logpath);
  res = found = 0;
START:
  ch = nextch ();
  if (ch == EOF) goto DONE;
  if (ch == '\n' || ch == '\r') goto START;
  if (ch == '1') goto SEEN_1;
  if (ch == '0') goto SEEN_0;
  if (ch == 's') goto SEEN_S;
  if (ch == 'u') goto SEEN_U;
WAIT:
  ch = nextch ();
  if (ch == EOF) goto DONE;
  if (ch == '\n') goto START;
  goto WAIT;
SEEN_0:
  ch = nextch ();
  if (ch != '\n') goto WAIT;
  this = "0";
UNSAT:
  assert (ch == '\n');
  res = 20;
RESULT:
  msg (2, "found '%s' line in '%s'", this, logpath);
  if (other) {
    if (strcmp (other, this))
      die ("two different results '%s' and '%s' in '%s'",
        other, this, logpath);
    else
      wrn ("two (identical) results '%s' and '%s' in '%s'",
        other, this, logpath);
  }
  other = this;
  goto START;
SEEN_1:
  ch = nextch ();
  if (ch != '\n') goto WAIT;
  this = "1";
SAT:
  assert (ch == '\n');
  res = 10;
  goto RESULT;
SEEN_S:
  assert (ch == 's');
  ch = nextch ();
  if (isdigit (ch)) {
    bnd = getposnum (ch);
    if (bnd < 0) goto WAIT;
    msg (2, "found 's%d' line", bnd);
    if (e->minsbnd < 0 || e->minsbnd > bnd)
      e->minsbnd = bnd;
    goto START;
  }
  if (ch == '\n') goto START;
  if (ch == 'a') goto SEEN_SA;
  if (ch != ' ') goto WAIT;
  ch = nextch ();
  if (ch == 'S') goto SEEN_S_S;
  if (ch == 'U') goto SEEN_S_U;
  if (ch == '\n') goto START;
  goto WAIT;
SEEN_U:
  assert (ch == 'u');
  ch = nextch ();
  if (isdigit (ch)) {
    bnd = getposnum (ch);
    if (bnd < 0) goto WAIT;
    msg (2, "found 'u%d' line", bnd);
    if (e->maxubnd < 0 || e->maxubnd < bnd)
      e->maxubnd = bnd;
    goto START;
  }
  if (ch == '\n') goto START;
  if (ch != 'n') goto WAIT;
  ch = nextch ();
  if (ch == '\n') goto START;
  if (ch != 's') goto WAIT;
  ch = nextch ();
  if (ch == '\n') goto START;
  if (ch != 'a') goto WAIT;
  ch = nextch ();
  if (ch == '\n') goto START;
  if (ch != 't') goto WAIT;
  ch = nextch ();
  if (ch != '\n') goto WAIT;
  this = "unsat";
  goto UNSAT;
SEEN_SA:
  assert (ch == 'a');
  ch = nextch ();
  if (ch == '\n') goto START;
  if (ch != 't') goto WAIT;
  ch = nextch ();
  if (ch != '\n') goto WAIT;
  this = "sat";
  goto SAT;
SEEN_S_S:
  ch = nextch ();
  if (ch == '\n') goto START;
  if (ch != 'A') goto WAIT;
  ch = nextch ();
  if (ch == '\n') goto START;
  if (ch != 'T') goto WAIT;
  ch = nextch ();
  if (ch == '\n') goto START;
  if (ch != 'I') goto WAIT;
  ch = nextch ();
  if (ch == '\n') goto START;
  if (ch != 'S') goto WAIT;
  ch = nextch ();
  if (ch == '\n') goto START;
  if (ch != 'F') goto WAIT;
  ch = nextch ();
  if (ch == '\n') goto START;
  if (ch != 'I') goto WAIT;
  ch = nextch ();
  if (ch == '\n') goto START;
  if (ch != 'A') goto WAIT;
  ch = nextch ();
  if (ch == '\n') goto START;
  if (ch != 'B') goto WAIT;
  ch = nextch ();
  if (ch == '\n') goto START;
  if (ch != 'L') goto WAIT;
  ch = nextch ();
  if (ch == '\n') goto START;
  if (ch != 'E') goto WAIT;
  ch = nextch ();
  if (ch != '\n') goto WAIT;
  this = "s SATISFIABLE";
  goto SAT;
SEEN_S_U:
  ch = nextch ();
  if (ch == '\n') goto START;
  if (ch != 'N') goto WAIT;
  ch = nextch ();
  if (ch == '\n') goto START;
  if (ch != 'S') goto WAIT;
  ch = nextch ();
  if (ch == '\n') goto START;
  if (ch != 'A') goto WAIT;
  ch = nextch ();
  if (ch == '\n') goto START;
  if (ch != 'T') goto WAIT;
  ch = nextch ();
  if (ch == '\n') goto START;
  if (ch != 'I') goto WAIT;
  ch = nextch ();
  if (ch == '\n') goto START;
  if (ch != 'S') goto WAIT;
  ch = nextch ();
  if (ch == '\n') goto START;
  if (ch != 'F') goto WAIT;
  ch = nextch ();
  if (ch == '\n') goto START;
  if (ch != 'I') goto WAIT;
  ch = nextch ();
  if (ch == '\n') goto START;
  if (ch != 'A') goto WAIT;
  ch = nextch ();
  if (ch == '\n') goto START;
  if (ch != 'B') goto WAIT;
  ch = nextch ();
  if (ch == '\n') goto START;
  if (ch != 'L') goto WAIT;
  ch = nextch ();
  if (ch == '\n') goto START;
  if (ch != 'E') goto WAIT;
  ch = nextch ();
  if (ch != '\n') goto WAIT;
  this = "s UNSATISFIABLE";
  goto UNSAT;
DONE:
  close_input ();
  assert (found <= 1);
  assert (!e->res);
  if (other) {
    assert (res == 10 || res == 20);
    e->res = res;
  } else {
    msg (2, "no proper sat/unsat line found in '%s'", logpath);
    assert (!res);
  }
  if (e->minsbnd >= 0)
    msg (2, "found minimum sat-bound 's%d' in '%s'", e->minsbnd, logpath);
  if (e->maxubnd >= 0)
    msg (2, "found maximum unsat-bound 'u%d'", e->maxubnd, logpath);

  if (e->minsbnd >= 0 && e->minsbnd <= e->maxubnd)
    die ("minimum sat-bound %d <= maximum usat-bound %d in '%s'",
      e->minsbnd, e->maxubnd, logpath);

  if (e->minsbnd >= 0 && res == 20)
    die ("minimum sat-bound %d and with unsat result line in '%s'",
      e->minsbnd, logpath);

  if (e->minsbnd >= 0 && res != 10) {
    assert (!res);
    wrn ("minimum sat-bound %d and no result line found in '%s' (forcing sat)",
      e->minsbnd, logpath);
    e->res = 10;
  }

  if (e->minsbnd >= 0) {
    assert (e->res == 10);
    e->bnd = e->minsbnd;
  } else if (e->maxubnd >= 0) {
    if (e->res) assert (e->res == 20);
    else e->bnd = e->maxubnd;
  }
}

static void fixzummary (Zummary * z) {
  Entry * e;
  z->sat = z->uns = z->tio = z->meo = z->unk = z->dis = 0;
  z->tim = z->wll = z->mem = z->max = 0;
  z->s11 = z->si6 = z->bnd = 0;
  for (e = z->first; e; e = e->next) {
    if (e->res < 10) continue;
    assert (e->res == 10 || e->res == 20);
    assert (!e->tio), assert (!e->meo), assert (!e->unk);
    if (e->tim > z->tlim) {
      msg (1,
        "error file '%s/%s.err' actually exceeds time limit",
	z->path, e->name);
      e->tio = 1;
      e->res = 0;
    } else if (e->wll > z->rlim) {
      msg (1,
        "error file '%s/%s.err' actually exceeds real time limit",
	z->path, e->name);
      e->tio = 1;
      e->res = 0;
    } else if (e->mem > z->slim) {
      msg (1,
        "error file '%s/%s.err' actually exceeds space limit",
	z->path, e->name);
      e->meo = 1;
      e->res = 0;
    }
  }
  for (e = z->first; e; e = e->next) {
    if (e->res < 10) {
           if (e->res == 1) e->tio = 1;
      else if (e->res == 2) e->meo = 1;
      else if (e->res == 3) e->unk = 1;
      else if (e->res == 4) e->dis = 1;
      else if (e->res == 5) e->s11 = 1;
      else if (e->res == 6) e->si6 = 1;
      e->res = 0;
    } else
      assert (e->res == 10 || e->res == 20),
      assert (!e->meo), assert (!e->tio), assert (!e->unk);
    assert (!e->tio + !e->meo + !e->unk >= 2);
         if (e->dis) e->res = 4, z->dis++;
    else if (e->s11) e->res = 5, z->s11++;
    else if (e->si6) e->res = 6, z->si6++;
    else if (e->res == 10) z->sat++;
    else if (e->res == 20) z->uns++;
    else if (e->tio) e->res = 1, z->tio++;
    else if (e->meo) e->res = 2, z->meo++;
    else e->res = 3, e->unk = 1, z->unk++;
    assert (e->res);

    if (e->res == 10 || e->res == 20) {
      z->tim += e->tim, z->wll += e->wll, z->mem += e->mem;
      if (e->mem > z->max) z->max = e->mem;
    }
    if (e->bnd >= 0 && e->res != 4) z->bnd++;
  }
  z->sol = z->sat + z->uns;
  z->fld = z->tio + z->meo + z->s11 + z->si6 + z->unk;
  assert (z->cnt == z->sol + z->fld);
}

static int mystrcmp (const char * a, const char * b) {
  return strcmp (a, b);
}

static void loadzummary (Zummary * z, const char * path) {
  int first = 1;
  assert (!z->cnt);
  msg (1, "trying to load zummary '%s'", path);
  open_input (path);
  lineno = 1;
  while (parsezummaryline ()) {
    if (!first) {
      double tlim, rlim, slim;
      Entry * e;
      if (ntokens < 8 || ntokens > 9)
	die ("invalid line in '%s'", path);
      e = newentry (z, tokens[0]);
      e->res = atoi (tokens[1]);
      e->tim = atof (tokens[2]);
      e->wll = atof (tokens[3]);
      e->mem = atof (tokens[4]);
      tlim = atof (tokens[5]);
      if (tlim <= 0)
	die ("invalid time limit %.0f in '%s'", tlim, path);
      if (z->tlim < 0) {
	msg (1, "setting time limit of '%s' to %.0f", z->path, tlim);
	z->tlim = tlim;
      } else if (z->tlim != tlim)
        die ("different time limit %.0f in '%s'", tlim, path);
      rlim = atof (tokens[6]);
      if (rlim <= 0)
	die ("invalid real time limit %.0f in '%s'", rlim, path);
      if (z->rlim < 0) {
	msg (1, "setting real time limit of '%s' to %.0f", z->path, rlim);
	z->rlim = rlim;
      } else if (z->rlim != rlim)
        die ("different space limit %.0f in '%s'", rlim, path);
      slim = atof (tokens[7]);
      if (slim <= 0)
	die ("invalid space limit %.0f in '%s'", slim, path);
      if (z->slim < 0) {
	msg (1, "setting space limit of '%s' to %.0f", z->path, slim);
	z->slim = slim;
      } else if (z->slim != slim)
        die ("different space limit %.0f in '%s'", slim, path);
      if (ntokens < 9 || (e->bnd = atof (tokens[8])) < 0)
	e->bnd = -1;
      if (ntokens == 9)
	msg (2,
	  "loaded %s %d %.2f %.2f %.1f %.2f %.2f %.1f %d",
	  e->name, e->res, e->tim, e->wll, e->mem, tlim, rlim, slim, e->bnd);
      else
	msg (2,
	  "loaded %s %d %.2f %.2f %.1f %.2f %.2f %.1f",
	  e->name, e->res, e->tim, e->wll, e->mem, tlim, rlim, slim);

      if (e->res != 10 && e->res != 20) {
	     if (e->res == 1) e->tio = 1;
	     if (e->res == 2) e->meo = 1;
	else if (e->res == 3) e->unk = 1;
	else if (e->res == 4) e->dis = 1;
	else if (e->res == 5) e->s11 = 1;
	else if (e->res == 6) e->si6 = 1;
	e->res = 0;
      }
    } else if (ntokens < 7 ||
               ntokens > 8 ||
               mystrcmp (tokens[0], "result") ||
               mystrcmp (tokens[1], "time") ||
               mystrcmp (tokens[2], "real") ||
               mystrcmp (tokens[3], "space") ||
               mystrcmp (tokens[4], "tlim") ||
               mystrcmp (tokens[5], "rlim") ||
               mystrcmp (tokens[6], "slim") ||
	       (ntokens == 8 && mystrcmp (tokens[7], "bound")))
      die ("invalid header in '%s'", path);
    else first = 0;
  } msg (1, "loaded %d entries from '%s'", z->cnt, path);
  close_input ();
  fixzummary (z);
  sortzummary (z);
  loaded++;
}

static void updatezummary (Zummary * z) {
  struct dirent * dirent;
  DIR * dir;
  Entry * e;
  msg (1, "updating zummary for directory '%s'", z->path);
  if (!(dir = opendir (z->path)))
    die ("can not open directory '%s' for updating", z->path);
  z->cnt = 0;
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
      if (!parserrfile (e, errpath)) assert (!e->res);
      else if (!e->res) parselogfile (e, logpath);
      else assert (e->res == 10 || e->res == 20);
      free (errpath);
      assert (!e->res || e->res == 10 || e->res == 20);
      assert (!e->tio || !e->res);
      assert (!e->meo || !e->res);
      assert (!e->unk || !e->res);
    } else msg (1, "missing '%s'", logpath);
    free (logpath);
    free (logname);
    free (base);
  }
  (void) closedir (dir);
  msg (1, "found %d entries in '%s'", z->cnt, z->path);
  if (z->cnt) {
    if (z->tlim < 0) die ("no time limit in '%s'", z->path);
    if (z->rlim < 0) die ("no real time limit in '%s'", z->path);
    if (z->slim < 0) die ("no space limit in '%s'", z->path);
    if (nzummaries > 1 && z->cnt) {
      if (z->tlim != zummaries[0]->tlim)
	die ("different time limit '%.0f' in '%s'", z->tlim, z->path);
      if (z->rlim != zummaries[0]->rlim)
	die ("different real time limit '%.0f' in '%s'", z->rlim, z->path);
      if (z->slim != zummaries[0]->slim)
	die ("different space limit '%.0f' in '%s'", z->slim, z->path);
    }
  }
  fixzummary (z);
  sortzummary (z);
  updated++;
}

static void writezummary (Zummary * z, const char * path) {
  FILE * file;
  Entry * e;
  file = fopen (path, "w");
  if (!file) die ("can not write '%s'", path);
  fputs (" result time real space tlim rlim slim", file);
  if (!nobounds && z->bnd > 0) fputs (" bound", file);
  fputc ('\n', file);
  for (e = z->first; e; e = e->next) {
    fprintf (file,
      "%s %d %.2f %.2f %.1f %.0f %.0f %.0f",
      e->name, e->res, e->tim, e->wll, e->mem, z->tlim, z->rlim, z->slim);
    if (!nobounds && e->bnd >= 0) fprintf (file, " %d", e->bnd);
    fputc ('\n', file);
  }
  fclose (file);
  msg (1, "written %d entries to zummary '%s'", z->cnt, path);
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
  else if (zummaryneedsupdate (z, pathtozummary))
    msg (1, "zummary '%s' needs update", pathtozummary);
  else {
    loadzummary (z, pathtozummary);
    update = 0;
  }
  if (update) {
    updatezummary (z);
    if (!nowrite && z->cnt) writezummary (z, pathtozummary);
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
  int i, count = 0;;
  for (i = 0; i < nsyms; i++) {
    Symbol * s = symtab[i];
    int sat = 0, unsat = 0, expected;
    char cmp;
    Entry * e;
    for (e = s->first; e; e = e->chain) {
      assert (e->name == s->name);
      if (e->res == 10) sat++;
      if (e->res == 20) unsat++;
    }
    if (!sat) continue;
    if (!unsat) continue;
    if (sat > unsat) expected = 10, cmp = '>';
    else if (sat < unsat) expected = 20, cmp = '<';
    else expected = 0, cmp = '=';
    fprintf (stdout,
      "*** zummarize: DISCREPANCY on '%s' with %d SAT %c %d UNSAT\n",
      s->name, sat, cmp, unsat);
    for (e = s->first; e; e = e->chain) {
      if (e->res < 10) continue;
      assert (e->res == 10 || e->res == 20);
      fprintf (stdout,
        "*** zummarize: %s '%s/%s' %s",
        (e->res == expected) ? " " : "!",
	e->zummary->path, s->name, 
	(e->res == 10 ? "SAT" : "UNSAT"));
      if (!expected)
	fprintf (stdout, " (unclear status so assumed wrong)");
      if (expected && e->res != expected)
	fprintf (stdout, " (probably wrong)");
      if (e->res != expected)
	e->dis = 1, e->zummary->dirty = 1;
      fputc ('\n', stdout);
    }
    fflush (stdout);
    count++;
  }
  if (count) {
    msg (1, "found %d discrepancies", count);
    count = 0;
    for (i = 0; i < nzummaries; i++) {
      Zummary * z = zummaries[i];
      if (!z->dirty) continue;
      fixzummary (z);
      count++;
    }
    msg (1, "fixed %d zummaries", count);
  } else msg (1, "no discrepancies found");
}

static void checklimits () {
  Zummary * x, * y, * z;
  int i;
  y = 0;
  for (i = 0; !y && i < nzummaries; i++)
    if ((x = zummaries[i])->cnt) y = x;
  if (!y) return;
  while (i < nzummaries) {
    z = zummaries[i++];
    if (!z->cnt) continue;
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
  int a = y->sat + y->uns, b = z->sat + z->uns;
  int res = b - a;
  if (res) return res;
  if (usereal) {
    if ((res = cmpdouble (y->wll, z->wll))) return res;
    if ((res = cmpdouble (y->tim, z->tim))) return res;
  } else {
    if ((res = cmpdouble (y->tim, z->tim))) return res;
    if ((res = cmpdouble (y->wll, z->wll))) return res;
  }
  if ((res = cmpdouble (y->mem, z->mem))) return res;
  return strcmp (y->path, z->path);
}

static void sortzummaries () {
  qsort (zummaries, nzummaries, sizeof *zummaries, cmpzummaries4qsort);
  msg (2, "sorted all zummaries");
}

static int ilen (int n) {
  int res, tmp;
  assert (n >= 0);
  for (res = 1, tmp = 10; res < 10; res++, tmp *= 10)
    if (n < tmp) return res;
  return res;
}

static int dlen (double d) {
  double tmp;
  int res;
  assert (d >= 0);
  for (res = 1, tmp = 10; res < 20; res++, tmp *= 10)
    if (d < tmp) return res;
  return res;
}

static void printzummaries () {
  int nam, cnt, sol, sat, uns, dis, fld, tio, meo, s11, si6, unk, tim, wll, mem, max;
  int i, j, skip;

  nam = cnt = sol = sat = uns = dis = fld = tio = meo = s11 = si6 = unk = tim = wll = mem = max = 0;

  skip = nzummaries ? strlen (zummaries[0]->path) : 0;
  for (i = 1; i < nzummaries; i++) {
    for (j = 0; j < skip; j++)
      if (zummaries[i]->path[j] != zummaries[0]->path[j])
	break;
    skip = j;
    assert (skip <= strlen (zummaries[i]->path));
  }
  for (i = 0; i < nzummaries; i++) {
    Zummary * z = zummaries[i];

#define UPDATEIFLARGERAUX(OLDLEN,NEWLEN) \
  do { \
    int TMPAUX = (NEWLEN); \
    if (TMPAUX > OLDLEN) OLDLEN = TMPAUX; \
  } while (0)
#define UPDATEIFLARGERLEN(OLDLEN,LEN,DATA) \
  do { \
    int TMPLEN = (DATA); \
    if (!TMPLEN) break; \
    UPDATEIFLARGERAUX(OLDLEN,LEN(TMPLEN)); \
  } while (0)

    UPDATEIFLARGERAUX (nam, strlen (z->path + skip));
    UPDATEIFLARGERLEN (cnt, ilen, z->cnt);
    UPDATEIFLARGERLEN (sol, ilen, z->sat + z->uns);
    UPDATEIFLARGERLEN (sat, ilen, z->sat);
    UPDATEIFLARGERLEN (uns, ilen, z->uns);
    UPDATEIFLARGERLEN (dis, ilen, z->dis);
    UPDATEIFLARGERLEN (fld, ilen, z->tio + z->meo + z->unk);
    UPDATEIFLARGERLEN (tio, ilen, z->tio);
    UPDATEIFLARGERLEN (meo, ilen, z->meo);
    UPDATEIFLARGERLEN (s11, ilen, z->s11);
    UPDATEIFLARGERLEN (si6, ilen, z->si6);
    UPDATEIFLARGERLEN (unk, ilen, z->unk);
    UPDATEIFLARGERLEN (tim, dlen, z->tim);
    UPDATEIFLARGERLEN (wll, dlen, z->wll);
    UPDATEIFLARGERLEN (mem, dlen, z->mem);
    UPDATEIFLARGERLEN (max, dlen, z->max);
  }

#define PRINTHEADER(CHARS,HEADER) \
do { \
  int LEN, I; \
  if (!CHARS) break; \
  LEN = strlen (HEADER); \
  if (CHARS < LEN) CHARS = LEN; \
  if (&CHARS != &nam) fputc (' ', stdout); \
  for (I = 0; I < CHARS - LEN; I++) fputc (' ', stdout); \
  fputs (HEADER, stdout); \
} while (0)


  PRINTHEADER (nam, "");
  PRINTHEADER (cnt, "cnt");
  PRINTHEADER (sol, "ok");
  PRINTHEADER (sat, "sat");
  PRINTHEADER (uns, "uns");
  PRINTHEADER (dis, "d");
  PRINTHEADER (fld, "fld");
  PRINTHEADER (tio, "to");
  PRINTHEADER (meo, "mo");
  PRINTHEADER (s11, "s11");
  PRINTHEADER (si6, "s6");
  PRINTHEADER (unk, "x");
  PRINTHEADER (tim, "time");
  PRINTHEADER (wll, "real");
  PRINTHEADER (mem, "mem");
  PRINTHEADER (max, "max");
  putc ('\n', stdout);

  for (i = 0; i < nzummaries; i++) {
    Zummary * z = zummaries[i];
    j = nam - strlen (z->path + skip);
    assert (j >= 0);
    while (j-- > 0) fputc (' ', stdout);
    fputs (z->path + skip, stdout);
#define IPRINTZUMMARY(NAME) \
do { \
  char fmt[20]; \
  if (!NAME) break; \
  sprintf (fmt, " %%%dd", NAME); \
  printf (fmt, z->NAME); \
} while (0)

#define FPRINTZUMMARY(NAME) \
do { \
  char fmt[20]; \
  if (!NAME) break; \
  sprintf (fmt, " %%%d.0f", NAME); \
  printf (fmt, z->NAME); \
} while (0)
    IPRINTZUMMARY (cnt);
    IPRINTZUMMARY (sol);
    IPRINTZUMMARY (sat);
    IPRINTZUMMARY (uns);
    IPRINTZUMMARY (dis);
    IPRINTZUMMARY (fld);
    IPRINTZUMMARY (tio);
    IPRINTZUMMARY (meo);
    IPRINTZUMMARY (s11);
    IPRINTZUMMARY (si6);
    IPRINTZUMMARY (unk);
    FPRINTZUMMARY (tim);
    FPRINTZUMMARY (wll);
    FPRINTZUMMARY (mem);
    FPRINTZUMMARY (max);
    fputc ('\n', stdout);
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
  printzummaries ();
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
    else if (!strcmp (argv[i], "--no-bounds")) nobounds = 1;
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
