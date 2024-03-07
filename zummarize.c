#include <assert.h>
#include <ctype.h>
#include <dirent.h>
#include <limits.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
#ifndef NMMAP
#include <fcntl.h>
#include <sys/mman.h>
#endif

typedef struct Symbol {
  char *name;
  struct Entry *first, *last;
  struct Symbol *next;
  int sat, uns;
} Symbol;

typedef struct Entry {
  Symbol *symbol;
  const char *name;
  struct Zummary *zummary;
  struct Entry *next, *chain, *best;
  char tio, meo, unk, dis, s11, si6;
  double wll, tim, mem;
  int res, bnd, maxubnd, minsbnd;
  long obnd;
} Entry;

typedef struct Zummary {
  char *path;
  Entry *first, *last;
  int cnt, sol, sat, uns, dis, fld, tio, meo, s11, si6, unk, bnd, bst, unq;
  double wll, tim, par, mem, max, tlim, rlim, slim, deep;
  int only_use_for_reporting_and_do_not_write;
  char ubndbroken, obndbroken;
} Zummary;

typedef struct Order {
  char *name;
  int order;
} Order;

static int verbose, force, ignore, printall, nowrite, nobounds, par;
static int nowarnings, satonly, unsatonly, deeponly, just, center;
static int solved, unsolved, cmp, filter, nounknown;
static int plotting, cactus, cdf;

static int xmin = -1, xmax = -1, ymin = -1, ymax = -1;
static int limit = -1;

static const char *patch;

static const char *title, *outputpath;

static Zummary **zummaries;
static int nzummaries, sizezummaries;
static int loaded, written, updated;

static char *token;
static int stoken, ntoken, sizetoken;
static int lineno;

static const char **tokens;
static int ntokens, sizetokens;

static Symbol **symtab;
static unsigned nsyms, sizesymtab;
static unsigned long long searches, collisions;

static const char *orderpath;
static Order *order;
static int norder;

static int usereal;

static int capped = 1000;
static int logy;
static int merge;
static int rank;

static void die(const char *fmt, ...) {
  va_list ap;
  fputs("*** zummarize error: ", stdout);
  va_start(ap, fmt);
  vfprintf(stdout, fmt, ap);
  va_end(ap);
  fputc('\n', stdout);
  exit(1);
}

static void wrn(const char *fmt, ...) {
  va_list ap;
  if (nowarnings)
    return;
  fputs("*** zummarize warning: ", stdout);
  va_start(ap, fmt);
  vfprintf(stdout, fmt, ap);
  va_end(ap);
  fputc('\n', stdout);
}

static void msg(int level, const char *fmt, ...) {
  va_list ap;
  if (verbose < level)
    return;
  fputs("[zummarize] ", stdout);
  va_start(ap, fmt);
  vfprintf(stdout, fmt, ap);
  va_end(ap);
  fputc('\n', stdout);
  fflush(stdout);
}

#ifndef NMMAP

static struct {
  int opened;
  int fd;
  char *start, *top, *end;
} input;

static size_t file_size(const char *path) {
  struct stat buf;
  if (stat(path, &buf))
    die("failed to determine size of '%s'", path);
  return buf.st_size;
}

static void open_input(const char *path) {
  size_t bytes;
  assert(!input.opened);
  bytes = file_size(path);
  input.fd = open(path, O_RDONLY);
  if (input.fd == -1)
    die("failed to open '%s'", path);
  input.start =
      mmap(0, bytes, PROT_READ, MAP_PRIVATE | MAP_POPULATE, input.fd, 0);
  if (!input.start)
    die("failed to map '%s' to memory", path);
  msg(2, "memory mapped '%s' of size %ld", path, (long)bytes);
  input.top = input.start;
  input.end = input.start + bytes;
  input.opened = 1;
}

static int reallynextch() {
  assert(input.opened);
  assert(input.top <= input.end);
  if (input.top == input.end)
    return EOF;
  return *input.top++;
}

static void close_input(const char *path) {
  size_t bytes;
  assert(input.opened);
  bytes = input.end - input.start;
  if (munmap(input.start, bytes) && verbose)
    wrn("failed to unmap '%s' from memory", path);
  if (close(input.fd))
    wrn("failed to close file '%s'", path);
  input.opened = 0;
}

#else

static FILE *input;

static void open_input(const char *path) {
  assert(!input);
  if (!(input = fopen(path, "r")))
    die("failed to open '%s'", path);
}

static int reallynextch() {
  assert(input);
#ifndef NGETCUNLOCKED
  return getc_unlocked(input);
#else
  return getc(input);
#endif
}

static void close_input(const char *path) {
  assert(input);
  if (fclose(input))
    wrn("failed to close file '%s'", path);
  input = 0;
}

#endif

static int savedch = EOF, savedchvalid;

static int nextch() {
  int res;
  if (savedchvalid)
    res = savedch, savedchvalid = 0;
  else
    res = reallynextch();
  return res;
}

static void savech(int ch) {
  assert(!savedchvalid);
  savedchvalid = 1;
  savedch = ch;
}

static const char *USAGE =
    "usage: zummarize [ <option> ... ] <dir> ... \n"
    "\n"
    "where <option> is one of the following:\n"
    "\n"
    "-h             print this command line option zummary\n"
    "-v             increase verbose level (maximum 3, default 0)\n"
    "-f|--force     recompute zummaries (do not read '<dir>/zummary' files)\n"
    "-i|--ignore    ignore mismatching limits and bounds\n"
    "-j|--just      assume terminated are just solved (unsat)\n"
    "\n"
    "-n|--no-warnings\n"
    "\n"
    "-a|--all       report all column and rows (even with zero entries)\n"
    "-s|--sat       report goes over satisfiable instances only\n"
    "-u|--unsat     report goes over unsatisfiable instances only\n"
    "-d|--deep      report goes over unsolved instances only (sorted by deep)\n"
    "-c|--plot      print plot (default is 'CDF' not 'cactus')\n"
    "--cactus       generate classical SAT competition cactus plot\n"
    "--cdf          generate cumulative distribution function\n"
    "--center       center legend vertically\n"
    "-m|--merge     merge zummaries by benchmark\n"
    "-r|--rank      print number of times benchmark has been solved\n"
    "--unsolved     print unsolved (never solved) instances\n"
    "--solved       print all at least once solved instances\n"
    "--filter       filter out solved in comparison\n"
    "--cmp          compare two runs\n"
    "\n"
    "--ymin <y>     minimum Y value\n"
    "--xmin <x>     minimum X value\n"
    "--ymax <y>     maximum Y value\n"
    "--xmax <x>     maximum X value\n"
    "--limit <y>    limit line\n"
    "--patch <file> add these commands after 'plot'\n"
    "\n"
    "--par<x>       use PAR<X> score\n"
    "\n"
    "  -l|--log\n"
    "  -o <output>\n"
    "  -t <title>|--title <title>\n"
    "  --order <orderpath>\n"
    "\n"
    "--no-write     do not write generated zummaries\n"
    "--no-bounds    do not print bounds\n"
    "\n"
    "The directory arguments are considered to have '.err' files generated\n"
    "by the 'runlim' tool and '.log' files which adhere loosly to the output\n"
    "file requirements used in the SAT, SMT and HWMCC competitions.  The tool\n"
    "will by default write '<dir>/zummary' file unless there are already such\n"
    "zummaries available, which will then be used for caching results.\n";

static void usage() {
  fputs(USAGE, stdout);
  exit(0);
}

static int isdir(const char *path) {
  struct stat buf;
  return !stat(path, &buf) && S_ISDIR(buf.st_mode);
}

static int isfile(const char *path) {
  struct stat buf;
  return !stat(path, &buf) && S_ISREG(buf.st_mode);
}

static void striptrailingslash(char *str) {
  int i = strlen(str);
  while (i > 0 && str[i - 1] == '/')
    str[--i] = 0;
}

static Zummary *newzummary(const char *path) {
  Zummary *res = malloc(sizeof *res);
  if (!res)
    die("out of memory allocating zummary object");
  memset(res, 0, sizeof *res);
  res->path = strdup(path);
  if (!res->path)
    die("out of memory copy zummary path");
  res->tlim = res->rlim = res->slim = -1;
  striptrailingslash(res->path);
  if (sizezummaries == nzummaries) {
    int newsize = sizezummaries ? 2 * sizezummaries : 1;
    zummaries = realloc(zummaries, newsize * sizeof *zummaries);
    if (!zummaries)
      die("out of memory reaallocating zummaries stack");
    sizezummaries = newsize;
  }
  zummaries[nzummaries++] = res;
  return res;
}

static char *appendstr(const char *a, const char *b) {
  int i = strlen(a), j = strlen(b);
  char *res = malloc(i + j + 1);
  if (!res)
    die("out of memory appending string");
  strcpy(res, a);
  strcpy(res + i, b);
  return res;
}

static char *appendpath(const char *prefix, const char *name) {
  char *res = malloc(strlen(prefix) + strlen(name) + 2);
  if (!res)
    die("out of memory appending path");
  strcpy(res, prefix);
  striptrailingslash(res);
  strcat(res, "/");
  strcat(res, name);
  return res;
}

static void pushtoken(int ch) {
  if (ntoken == sizetoken) {
    int newsizetoken = sizetoken ? 2 * sizetoken : 1;
    char *oldtoken = token;
    long delta;
    token = realloc(token, newsizetoken);
    if (!token)
      die("out of memory reallocating token buffer");
    sizetoken = newsizetoken;
    if ((delta = token - oldtoken)) {
      int i;
      for (i = 0; i < ntokens; i++)
	tokens[i] += delta;
    }
  }
  if (ntoken == INT_MAX)
    die("token buffer overflow");
  token[ntoken++] = ch;
}

static int pusherrtokens() {
  const char *res;
  int skip;
  pushtoken(0);
  res = token + stoken;
  if (!ntokens && strcmp(res, "[run]") && strcmp(res, "[runlim]")) {
    msg(3, "skipping line starting with '%s'", res);
    skip = 1;
  } else if (ntokens == 1 && !strcmp(res, "sample:")) {
    msg(3, "skipping sample line");
    skip = 1;
  } else
    skip = 0;
  if (skip) {
    int ch;
    while ((ch = nextch()) != '\n')
      if (ch == EOF)
	break;
    if (ch == '\n')
      lineno++;
    ntokens = ntoken = stoken = 0;
    return 0;
  }
  if (sizetokens == ntokens) {
    int newsizetokens = sizetokens ? 2 * sizetokens : 1;
    tokens = realloc(tokens, newsizetokens * sizeof *tokens);
    if (!tokens)
      die("out of memory reallocating token stack");
    sizetokens = newsizetokens;
  }
  if (ntokens == INT_MAX)
    die("token stack overflow");
  tokens[ntokens++] = res;
  stoken = ntoken;
  return 1;
}

static int parserrline() {
  int i, newline = 0, res = 1;
  stoken = ntoken = ntokens = 0;
  for (;;) {
    int ch = nextch();
    if (ch == EOF) {
      res = 0;
      break;
    }
    if (ch == '\n') {
      newline = 1;
      break;
    }
    if (ch == ' ' || ch == '\t' || ch == '\r') {
      assert(ntokens < 5 || ntoken == stoken);
      if (stoken < ntoken && !pusherrtokens())
	break;
      continue;
    }
    if (ntokens < 5)
      pushtoken(ch);
    else
      assert(stoken == ntoken);
  }
  assert(ntokens < 5 || stoken == ntoken);
  if (stoken < ntoken)
    (void)pusherrtokens();
  if (verbose > 2)
    for (i = 0; i < ntokens; i++)
      msg(3, "token[%d,%d] %s", lineno, i, tokens[i]);
  if (newline)
    lineno++;
  return res;
}

static void pushzummarytokens() {
  const char *res;
  pushtoken(0);
  res = token + stoken;
  if (sizetokens == ntokens) {
    int newsizetokens = sizetokens ? 2 * sizetokens : 1;
    tokens = realloc(tokens, newsizetokens * sizeof *tokens);
    if (!tokens)
      die("out of memory reallocating token stack");
    sizetokens = newsizetokens;
  }
  if (ntokens == INT_MAX)
    die("token stack overflow");
  tokens[ntokens++] = res;
  stoken = ntoken;
}

static int parsezummaryline() {
  int i, newline = 0;
  stoken = ntoken = ntokens = 0;
  for (;;) {
    int ch = nextch();
    if (ch == EOF)
      break;
    if (ch == '\n') {
      newline = 1;
      break;
    }
    if (ch == ' ' || ch == '\t' || ch == '\r') {
      if (stoken < ntoken)
	pushzummarytokens();
      continue;
    }
    pushtoken(ch);
  }
  if (stoken < ntoken)
    pushzummarytokens();
  if (verbose > 2)
    for (i = 0; i < ntokens; i++)
      msg(3, "token[%d,%d] %s", lineno, i, tokens[i]);
  if (newline)
    lineno++;
  return ntokens;
}

static int parseorderline() {
  ntoken = 0;
  for (;;) {
    int ch = nextch();
    if (ch == EOF)
      return 0;
    if (ch == '\n')
      break;
    pushtoken(ch);
  }
  pushtoken(0);
  return 1;
}

static void insertorder(const char *name) {
  Order *o;
  int i;
  for (i = 0; i < norder; i++)
    if (!strcmp(name, order[i].name))
      return;
  order = realloc(order, (norder + 1) * sizeof *order);
  o = order + norder++;
  o->name = strdup(name);
  if (norder > 1) {
    o->order = (o - 1)->order + 1;
    if (o->order == 7 || o->order == 15)
      o->order++;
  } else
    o->order = 1;
}

static void parseorder() {
  assert(plotting);
  assert(orderpath);
  open_input(orderpath);
  while (parseorderline())
    insertorder(token);
  close_input(orderpath);
}

static int getmtime(const char *path, double *timeptr) {
  struct stat buf;
  if (stat(path, &buf)) {
    msg(1, "can not get modification time of '%s'", path);
    return 0;
  }
  msg(2, "modification time %.0f of '%s'", (double)buf.st_mtime, path);
  *timeptr = buf.st_mtime;
  return 1;
}

static char *stripsuffix(const char *str, const char *suffix) {
  int i = strlen(str), j = strlen(suffix), k;
  char *res;
  if (i < j)
    return 0;
  k = i - j;
  if (strcmp(str + k, suffix))
    return 0;
  res = malloc(k + 1);
  if (!res)
    die("out of memory stripping suffix");
  res[k] = 0;
  while (k-- > 0)
    res[k] = str[k];
  return res;
}

static int zummaryneedsupdate(Zummary *z, const char *path) {
  struct dirent *dirent;
  double ztime;
  int res = 0;
  DIR *dir;
  if (!getmtime(path, &ztime))
    return 1;
  if (!(dir = opendir(z->path)))
    die("can not open directory '%s' for checking times", z->path);
  while (!res && (dirent = readdir(dir))) {
    char *base, *logname, *logpath;
    const char *errname = dirent->d_name;
    msg(2, "checking '%s'", errname);
    if (!(base = stripsuffix(errname, ".err"))) {
      msg(2, "skipping '%s'", errname);
      continue;
    }
    logname = appendstr(base, ".log");
    logpath = appendpath(z->path, logname);
    if (isfile(logpath)) {
      char *errpath = appendpath(z->path, errname);
      double etime;
      if (getmtime(errpath, &etime)) {
	if (etime <= ztime) {
	  double ltime;
	  if (getmtime(logpath, &ltime)) {
	    if (ltime > ztime) {
	      msg(1, "log file '%s' more recently modified", logpath);
	      res = 1;
	    }
	  } else
	    res = 1;
	} else {
	  msg(1, "error file '%s' more recently modified", errpath);
	  res = 1;
	}
      } else
	res = 1;
    } else
      msg(1, "missing '%s'", logpath);
    free(logpath);
    free(logname);
    free(base);
  }
  (void)closedir(dir);
  return res;
}

static unsigned primes[] = {111111113, 222222227, 333333349, 444444457};

#define NPRIMES (sizeof primes / sizeof primes[0])

static unsigned hashstr(const char *name) {
  unsigned res = 0, i = 0;
  const char *p;
  char ch;
  for (p = name; (ch = *p); p++) {
    res += primes[i++] * (unsigned)ch;
    if (i == NPRIMES)
      i = 0;
  }
  return res;
}

static void enlargesymtab() {
  unsigned newsizesymtab = sizesymtab ? 2 * sizesymtab : 1;
  Symbol *s, *n, **newsymtab;
  unsigned h, i;
  size_t bytes = newsizesymtab * sizeof *newsymtab;
  newsymtab = malloc(bytes);
  if (!newsymtab)
    die("out of memory reallocating symbol table");
  memset(newsymtab, 0, bytes);
  for (i = 0; i < sizesymtab; i++) {
    for (s = symtab[i]; s; s = n) {
      n = s->next;
      h = hashstr(s->name) & (newsizesymtab - 1);
      s->next = newsymtab[h];
      newsymtab[h] = s;
    }
  }
  free(symtab);
  symtab = newsymtab;
  sizesymtab = newsizesymtab;
}

static Entry *newentry(Zummary *z, const char *name) {
  Entry *res = malloc(sizeof *res);
  Symbol *s, **p;
  unsigned h;
  if (!res)
    die("out of memory allocating entry object");
  memset(res, 0, sizeof *res);
  res->zummary = z;
  res->bnd = res->maxubnd = res->minsbnd = -1;
  res->obnd = -1;
  if (nsyms == sizesymtab)
    enlargesymtab();
  h = hashstr(name) & (sizesymtab - 1);
  searches++;
  for (p = symtab + h; (s = *p) && strcmp(s->name, name); p = &s->next)
    collisions++;
  if (!s) {
    s = malloc(sizeof *s);
    if (!s)
      die("out of memory allocating symbol object");
    memset(s, 0, sizeof *s);
    s->name = strdup(name);
    if (!s->name)
      die("out of memory copying symbol name");
    nsyms++;
    *p = s;
  }
  res->name = s->name;
  res->symbol = s;
  if (s->last)
    s->last->chain = res;
  else
    s->first = res;
  s->last = res;
  z->cnt++;
  if (z->last)
    z->last->next = res;
  else
    z->first = res;
  z->last = res;
  return res;
}

enum {
  TLIM = 0,
  RLIM = 1,
  SLIM = 2,
  STATUS = 3,
  RESULT = 4,
  TIME = 5,
  REAL = 6,
  SPACE = 7,
  MAX = 8,
};

#define FOUND(FIELD, STR)                                                      \
  do {                                                                         \
    checked++;                                                                 \
    if (found[FIELD])                                                          \
      break;                                                                   \
    msg(1, "error file '%s' is missing '%s' line", errpath, STR);              \
    res = 0;                                                                   \
  } while (0)

static int parserrfile(Entry *e, const char *errpath) {
  int found[MAX], i, checked, res = 1;
  msg(2, "parsing error file '%s'", errpath);
  open_input(errpath);
  for (i = 0; i < MAX; i++)
    found[i] = 0;
  lineno = 1;
  while (parserrline()) {
    if (!ntokens)
      continue;
    assert(!strcmp(tokens[0], "[run]") || !strcmp(tokens[0], "[runlim]"));
    if (ntokens > 3 && !strcmp(tokens[1], "time") &&
	!strcmp(tokens[2], "limit:")) {
      double tlim = atof(tokens[3]);
      msg(2, "found time limit '%.0f' in '%s'", tlim, errpath);
      if (found[TLIM]) {
	msg(1, "error file '%s' contains two 'time limit:' lines", errpath);
	res = 0;
      } else {
	found[TLIM] = 1;
	if (tlim <= 0) {
	  msg(1, "error file '%s' with invalid time limit '%.0f'", errpath,
	      tlim);
	  res = 0;
	} else if (e->zummary->tlim < 0) {
	  msg(1, "assuming time limit '%.0f'", tlim);
	  e->zummary->tlim = tlim;
	} else if (e->zummary->tlim != tlim) {
	  msg(1, "error file '%s' with different time limit '%.0f'", errpath,
	      tlim);
	  res = 0;
	}
      }
    } else if (ntokens > 4 && !strcmp(tokens[1], "real") &&
	       !strcmp(tokens[2], "time") && !strcmp(tokens[3], "limit:")) {
      double rlim = atof(tokens[4]);
      msg(2, "found real time limit '%.0f' in '%s'", rlim, errpath);
      if (found[RLIM]) {
	msg(1, "error file '%s' contains two 'real time limit:' lines",
	    errpath);
	res = 0;
      } else {
	found[RLIM] = 1;
	if (rlim <= 0) {
	  msg(1, "error file '%s' with invalid real time limit '%.0f'", errpath,
	      rlim);
	  res = 0;
	} else if (e->zummary->rlim < 0) {
	  msg(1, "assuming real time limit '%.0f'", rlim);
	  e->zummary->rlim = rlim;
	} else if (e->zummary->rlim != rlim) {
	  msg(1, "error file '%s' with different real time limit '%.0f'",
	      errpath, rlim);
	  res = 0;
	}
      }
    } else if (ntokens > 3 && !strcmp(tokens[1], "space") &&
	       !strcmp(tokens[2], "limit:")) {
      double slim = atof(tokens[3]);
      msg(2, "found space limit '%.0f' in '%s'", slim, errpath);
      if (found[SLIM]) {
	msg(1, "error file '%s' contains two 'space limit:' lines", errpath);
	res = 0;
      } else {
	found[SLIM] = 1;
	if (slim <= 0) {
	  msg(1, "error file '%s' with invalid space limit '%.0f'", errpath,
	      slim);
	  res = 0;
	} else if (e->zummary->slim < 0) {
	  msg(1, "assuming space limit '%.0f'", slim);
	  e->zummary->slim = slim;
	} else if (e->zummary->slim != slim) {
	  msg(1, "error file '%s' with different space limit '%.0f'", errpath,
	      slim);
	  if (e->zummary->slim < slim) {
	    msg(1, "increasing space limit to '%.0f'", slim);
	    e->zummary->slim = slim;
	  }
	}
      }
    } else if (ntokens > 2 && !strcmp(tokens[1], "status:")) {
      if (found[STATUS]) {
	msg(1, "error file '%s' contains two 'status:' lines", errpath);
	res = 0;
      } else if (!strcmp(tokens[2], "ok")) {
	msg(2, "found 'ok' status in '%s'", errpath);
	found[STATUS] = 1;
      } else if (!strcmp(tokens[2], "signal(11)") ||
		 (ntokens > 3 && !strcmp(tokens[2], "segmentation") &&
		  !strcmp(tokens[3], "fault"))) {
	msg(2, "found 'ok' status in '%s'", errpath);
	found[STATUS] = 1;
	e->s11 = 1;
      } else if (!strcmp(tokens[2], "signal(6)")) {
	msg(2, "found 'ok' status in '%s'", errpath);
	found[STATUS] = 1;
	e->si6 = 1;
      } else if (ntokens > 4 && !strcmp(tokens[2], "out") &&
		 !strcmp(tokens[3], "of") && !strcmp(tokens[4], "time")) {
	msg(2, "found 'out of time' status in '%s'", errpath);
	found[STATUS] = 1;
	e->tio = 1;
      } else if (ntokens > 4 && !strcmp(tokens[2], "out") &&
		 !strcmp(tokens[3], "of") && !strcmp(tokens[4], "memory")) {
	msg(2, "found 'out of memory' status in '%s'", errpath);
	found[STATUS] = 1;
	e->meo = 1;
      } else {
	msg(1, "invalid status line in '%s'", errpath);
	found[STATUS] = 1;
      }
    } else if (ntokens > 2 && !strcmp(tokens[1], "result:")) {
      if (found[RESULT]) {
	msg(1, "error file '%s' contains two 'result:' lines", errpath);
	res = 0;
      } else {
	int result = atoi(tokens[2]);
	found[RESULT] = 1;
	if (!result) {
	  msg(2, "found '0' result in '%s'", errpath);
	} else if (result == 10) {
	  msg(2, "found '10' (SAT) result in '%s'", errpath);
	} else if (result == 20) {
	  msg(2, "found '20' (UNSAT) result in '%s'", errpath);
	} else {
	  msg(2, "found invalid '%d' result in '%s'", result, errpath);
	}
      }
    } else if (ntokens > 2 && !strcmp(tokens[1], "time:")) {
      double time = atof(tokens[2]);
      msg(2, "found time '%.2f' in '%s'", time, errpath);
      if (found[TIME]) {
	msg(1, "error file '%s' contains two 'time:' lines", errpath);
	res = 0;
      } else {
	found[TIME] = 1;
	if (time < 0) {
	  msg(1, "invalid time '%.2f' in '%s'", time, errpath);
	  res = 0;
	} else
	  e->tim = time;
      }
    } else if (ntokens > 2 && !strcmp(tokens[1], "real:")) {
      double real = atof(tokens[2]);
      msg(2, "found real time '%.2f' in '%s'", real, errpath);
      if (found[REAL]) {
	msg(1, "error file '%s' contains two 'real:' lines", errpath);
	res = 0;
      } else {
	found[REAL] = 1;
	if (real < 0) {
	  msg(1, "invalid real time '%.2f' in '%s'", real, errpath);
	  res = 0;
	} else
	  e->wll = real;
      }
    } else if (ntokens > 2 && !strcmp(tokens[1], "space:")) {
      double space = atof(tokens[2]);
      msg(2, "found space '%.1f' in '%s'", space, errpath);
      if (found[SPACE]) {
	msg(1, "error file '%s' contains two 'space:' lines", errpath);
	res = 0;
      } else {
	found[SPACE] = 1;
	if (space < 0) {
	  msg(1, "invalid space '%.1f' in '%s'", space, errpath);
	  res = 0;
	} else
	  e->mem = space;
      }
    }
  }
  close_input(errpath);
  checked = 0;
  FOUND(TLIM, "time limit:");
  FOUND(RLIM, "real time limit:");
  FOUND(SLIM, "space limit:");
  FOUND(STATUS, "status:");
  FOUND(RESULT, "result:");
  FOUND(TIME, "time:");
  FOUND(REAL, "real:");
  FOUND(SPACE, "space:");
  assert(checked == MAX);
  if (!res && !e->tio && !e->meo && !e->unk)
    e->unk = 1;
  return res;
}

static int cmpentry4qsort(const void *p, const void *q) {
  Entry *d = *(Entry **)p, *e = *(Entry **)q;
  return strcmp(d->name, e->name);
}

static void sortzummary(Zummary *z) {
  Entry **entries, *p;
  int i;
  if (!z->cnt)
    return;
  entries = malloc(z->cnt * sizeof *entries);
  if (!entries)
    die("out of memory allocating sorting array");
  i = 0;
  for (p = z->first; p; p = p->next)
    assert(i < z->cnt), entries[i++] = p;
  assert(i == z->cnt);
  qsort(entries, z->cnt, sizeof *entries, cmpentry4qsort);
  z->first = entries[0];
  for (i = 0; i < z->cnt - 1; i++)
    entries[i]->next = entries[i + 1];
  (z->last = entries[i])->next = 0;
  free(entries);
}

static int getposint(int ch) {
  int res, digit;
  assert(isdigit(ch));
  res = ch - '0';
  while (isdigit(ch = nextch())) {
    if (INT_MAX / 10 < res)
      return -1;
    res *= 10;
    digit = (ch - '0');
    if (INT_MAX - digit < res)
      return -1;
    res += digit;
  }
  if (ch != '\n')
    return -1;
  return res;
}

static long getposlong(int ch) {
  long res;
  int digit;
  assert(isdigit(ch));
  res = ch - '0';
  while (isdigit(ch = nextch())) {
    if (LONG_MAX / 10 < res)
      return -1;
    res *= 10;
    digit = (ch - '0');
    if (LONG_MAX - digit < res)
      return -1;
    res += digit;
  }
  if (ch != '\n')
    return -1;
  return res;
}

#define UBND_LOCALLY_BROKEN 1  // Actually only used for assertion
#define UBND_GLOBALLY_BROKEN 2 // checking and a proper warning below.

static void setubndbroken(Entry *e, int broken_level) {
  assert(broken_level == UBND_LOCALLY_BROKEN ||
	 broken_level == UBND_GLOBALLY_BROKEN);
  if (e->zummary->ubndbroken >= broken_level)
    return;
  wrn("assuming 'u...' lines are %s broken in '%s'",
      broken_level == UBND_GLOBALLY_BROKEN ? "globally" : "locally",
      e->zummary->path);
  e->zummary->ubndbroken = broken_level;
}

static void parselogfile(Entry *e, const char *logpath) {
  const char *other = 0, *this = 0;
  int found, ch, bnd;
  long obnd = -1;
  assert(!e->res);
  msg(2, "parsing log file '%s'", logpath);
  open_input(logpath);
  e->res = found = 0;
START:
  ch = nextch();
  if (ch == EOF)
    goto DONE;
  if (ch == '\n' || ch == '\r')
    goto START;
  if (ch == '1')
    goto SEEN_1;
  if (ch == '0')
    goto SEEN_0;
  if (ch == 's')
    goto SEEN_S;
  if (ch == 'u')
    goto SEEN_U;
  if (ch == 'o')
    goto SEEN_O;
  if (ch == 'S')
    goto SEEN_C_S;
  if (ch == 'U')
    goto SEEN_C_U;
WAIT:
  ch = nextch();
  if (ch == EOF)
    goto DONE;
  if (ch == '\n')
    goto START;
  goto WAIT;
SEEN_0:
  ch = nextch();
  if (ch != '\n')
    goto WAIT;
  this = "0";
UNSAT:
  assert(ch == '\n');
  e->res = 20;
RESULT:
  msg(2, "found '%s' line in '%s'", this, logpath);
  if (other) {
    if (strcmp(other, this))
      die("two different results '%s' and '%s' in '%s'", other, this, logpath);
    else
      wrn("two (identical) results '%s' and '%s' in '%s'", other, this,
	  logpath);
  }
  other = this;
  goto START;
SEEN_1:
  ch = nextch();
  if (ch != '\n')
    goto WAIT;
  this = "1";
START_OF_WITNESS:
  ch = nextch();
  if (ch == 'c') {
    while ((ch = nextch()) != '\n')
      if (ch == EOF)
	goto INVALID_WITNESS_SAVECH;
    goto START_OF_WITNESS;
  }
  if (ch != 'b' && ch != 'j')
    goto INVALID_WITNESS_SAVECH;
  if ((ch = nextch()) != '0')
    goto INVALID_WITNESS_SAVECH;
  if ((ch = nextch()) != '\n')
    goto INVALID_WITNESS_SAVECH;
  bnd = -2;
NEXT_TRACE_LINE:
  assert(ch == '\n');
  ch = nextch();
  if (ch == '.')
    goto END_OF_WITNESS;
  if (ch != '0' && ch != '1' && ch != 'x' && ch != '\n')
    goto INVALID_WITNESS_SAVECH;
  bnd++;
  if (ch == '\n')
    goto NEXT_TRACE_LINE;
NEXT_CHAR_IN_TRACE_LINE:
  ch = nextch();
  if (ch == '\n')
    goto NEXT_TRACE_LINE;
  if (ch != '0' && ch != '1' && ch != 'x')
    goto INVALID_WITNESS_SAVECH;
  goto NEXT_CHAR_IN_TRACE_LINE;
END_OF_WITNESS:
  assert(ch == '.');
  ch = nextch();
  if (ch != '\n') {
    wrn("no new line after '.' at end of AIGER witness in '%s'", logpath);
    goto INVALID_WITNESS_NO_SAVECH;
  }
  if (bnd < 0)
    goto INVALID_WITNESS_NO_SAVECH;
  msg(2, "found AIGER witness of length '%d'", bnd);
  if (e->minsbnd < 0 || e->minsbnd > bnd)
    e->minsbnd = bnd;
  goto SAT;
INVALID_WITNESS_SAVECH:
  savech(ch);
INVALID_WITNESS_NO_SAVECH:
  wrn("invalid AIGER witness in '%s'", logpath);
SAT:
  e->res = 10;
  goto RESULT;
SEEN_S:
  assert(ch == 's');
  ch = nextch();
  if (isdigit(ch)) {
    bnd = getposint(ch);
    if (bnd < 0)
      goto WAIT;
    msg(2, "found 's%d' line", bnd);
    if (e->minsbnd < 0 || e->minsbnd > bnd)
      e->minsbnd = bnd;
    goto START;
  }
  if (ch == '\n')
    goto START;
  if (ch == 'a')
    goto SEEN_SA;
  if (ch != ' ')
    goto WAIT;
  ch = nextch();
  if (ch == 'S')
    goto SEEN_S_S;
  if (ch == 'U')
    goto SEEN_S_U;
  if (ch == 'O')
    goto SEEN_S_O;
  if (ch == '\n')
    goto START;
  goto WAIT;
SEEN_U:
  assert(ch == 'u');
  ch = nextch();
  if (isdigit(ch)) {
    bnd = getposint(ch);
    if (bnd < 0)
      goto WAIT;
    msg(2, "found 'u%d' line", bnd);
    if (e->maxubnd < 0 || e->maxubnd < bnd)
      e->maxubnd = bnd;
    goto START;
  }
  if (ch == '\n')
    goto START;
  if (ch != 'n')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 's')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'a')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 't')
    goto WAIT;
  ch = nextch();
  if (ch != '\n')
    goto WAIT;
  this = "unsat";
  goto UNSAT;
SEEN_O:
  assert(ch == 'o');
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != ' ')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (!isdigit(ch))
    goto WAIT;
  obnd = getposlong(ch);
  if (obnd < 0)
    goto WAIT;
  msg(2, "found 'o %ld' line in '%s'", obnd, logpath);
  e->obnd = obnd;
  goto START;
SEEN_SA:
  assert(ch == 'a');
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 't')
    goto WAIT;
  ch = nextch();
  if (ch != '\n')
    goto WAIT;
  this = "sat";
  goto SAT;
SEEN_S_S:
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'A')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'T')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'I')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'S')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'F')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'I')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'A')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'B')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'L')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'E')
    goto WAIT;
  ch = nextch();
  if (ch != '\n')
    goto WAIT;
  this = "s SATISFIABLE";
  goto SAT;
SEEN_S_U:
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'N')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'S')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'A')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'T')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'I')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'S')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'F')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'I')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'A')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'B')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'L')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'E')
    goto WAIT;
  ch = nextch();
  if (ch != '\n')
    goto WAIT;
  this = "s UNSATISFIABLE";
  goto UNSAT;
SEEN_S_O:
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'P')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'T')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'I')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'M')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch == 'I') { // TODO remove ...
    ch = nextch();
    if (ch == '\n')
      goto START;
  }
  if (ch != 'U')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'M')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != ' ')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'F')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'O')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'U')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'N')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'D')
    goto WAIT;
  ch = nextch();
  if (ch != '\n')
    goto WAIT;
  this = "s OPTIMUM FOUND";
  goto SAT;
SEEN_C_S:
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'A')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'T')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'I')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'S')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'F')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'I')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'A')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'B')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'L')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'E')
    goto WAIT;
  ch = nextch();
  if (ch != '\n')
    goto WAIT;
  this = "SATISFIABLE";
  goto SAT;
SEEN_C_U:
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'N')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'S')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'A')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'T')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'I')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'S')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'F')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'I')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'A')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'B')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'L')
    goto WAIT;
  ch = nextch();
  if (ch == '\n')
    goto START;
  if (ch != 'E')
    goto WAIT;
  ch = nextch();
  if (ch != '\n')
    goto WAIT;
  this = "UNSATISFIABLE";
  goto UNSAT;
DONE:
  close_input(logpath);
  assert(found <= 1);
  if (other)
    assert(e->res == 10 || e->res == 20);
  else {
    msg(2, "no proper sat/unsat line found in '%s'", logpath);
    if (just) {
      msg(2, "'--just'' option forces UNSAT result '%s'", logpath);
      e->res = 20;
    }
    assert(!e->res);
  }
  if (e->minsbnd >= 0)
    msg(2, "found minimum sat-bound 's%d' in '%s'", e->minsbnd, logpath);
  if (e->maxubnd >= 0)
    msg(2, "found maximum unsat-bound 'u%d'", e->maxubnd, logpath);

  if (e->minsbnd >= 0 && e->minsbnd <= e->maxubnd) {
    wrn("minimum sat-bound %d <= maximum unsat-bound %d in '%s'", e->minsbnd,
	e->maxubnd, logpath);
    wrn("ignoring maximum unsat-bound %d in '%s'", e->maxubnd, logpath);
    e->maxubnd = -1;
    setubndbroken(e, UBND_LOCALLY_BROKEN);
  }

  if (e->minsbnd >= 0 && e->res == 20)
    die("minimum sat-bound %d and with unsat result line in '%s'", e->minsbnd,
	logpath);

  if (e->minsbnd >= 0 && e->res != 10) {
    assert(!e->res);
    wrn("minimum sat-bound %d and no result line found in '%s' (forcing sat)",
	e->minsbnd, logpath);
    e->res = 10;
  }

  assert(e->bnd < 0);
  if (e->minsbnd >= 0) {
    assert(e->res == 10);
    e->bnd = e->minsbnd;
  } else if (e->maxubnd >= 0) {
    if (e->res)
      assert(e->res == 10 || e->res == 20);
    else
      e->bnd = e->maxubnd;
  }
}

static int cmp_entry_better(Entry *, Entry *);

/* This is a very complex function with complex contract.  It is used when
 * writing a 'zummary' file and also after discrepancies have been checked
 * both with respect to SAT/UNSAT status as well as to bounds, and then a
 * third time after the best entry for an instance is determined.  The first
 * usage is 'local' in the sense, that the zummary just uses its own
 * information, and thus reflects exactly what the log and error files tell
 * us.  It is independent of other zummaries, and thus the information
 * gathered in this phase can also be written to the actual 'zummary' file.
 * In the second usage the status could change say from SAT to discrepancy
 * due to other zummaries having an UNSAT status.  Same for the bounds in
 * the second usage.  After a best entry is found, in the third usage,
 * certain information is skipped if 'satonly', 'unsatonly', or 'deep' is
 * set.  This projects the reported stats to these corresponding cases.  It
 * also allows to compute 'best' and 'unique' stats.  Starting with the
 * second usage the information gathered this function is used for reporting
 * only and thus afterwards a 'zummary' should not be written.
 */

#define LOCAL_ZUMMARY 0
#define GLOBAL_ZUMMARY_DO_NOT_HAVE_BEST 1
#define GLOBAL_ZUMMARY_HAVE_BEST 2

static void fixzummary(Zummary *z, int zummary_mode) {
  Entry *e;
  z->cnt = z->sol = z->sat = z->uns = z->dis = 0;
  z->fld = z->tio = z->meo = z->s11 = z->si6 = z->unk = 0;
  z->wll = z->tim = z->mem = z->max = 0;
  z->bnd = z->bst = z->unq = 0;
  for (e = z->first; e; e = e->next) {
    if (e->res < 10)
      continue;
    assert(e->res == 10 || e->res == 20);
    if (!e->tio && e->tim > z->tlim) {
      msg(1, "error file '%s/%s.err' actually exceeds time limit", z->path,
	  e->name);
      e->tio = 1;
    } else if (!e->tio && e->wll > z->rlim) {
      msg(1, "error file '%s/%s.err' actually exceeds real time limit", z->path,
	  e->name);
      e->tio = 1;
    } else if (!e->meo && e->mem > z->slim) {
      msg(1, "error file '%s/%s.err' actually exceeds space limit", z->path,
	  e->name);
      e->meo = 1;
    }
  }
  for (e = z->first; e; e = e->next) {
    if (zummary_mode == GLOBAL_ZUMMARY_HAVE_BEST) {
      if (satonly && (!e->best || e->best->res != 10))
	continue;
      if (unsatonly && (!e->best || e->best->res != 20))
	continue;
      if (deeponly) {
	if (e->best) {
	  if (e->best->res == 10)
	    continue;
	  if (e->best->res == 20)
	    continue;
	}
      }
      if (e->best == e || (e->best && !cmp_entry_better(e, e->best))) {
	assert(!e->dis);
	z->bst++;
	assert((e->symbol->sat > 0) + (e->symbol->uns > 0) < 2);
	if ((e->res == 10 && e->symbol->sat == 1) ||
	    (e->res == 20 && e->symbol->uns == 1)) {
	  msg(2, "unique (SOTA) '%s/%s'", e->zummary->path, e->name);
	  z->unq++;
	}
      }
    }
    z->cnt++;
    assert(!e->tio + !e->meo + !e->unk >= 2);
    if (e->dis)
      assert(zummary_mode != LOCAL_ZUMMARY), e->res = 4, z->dis++;
    else if (e->s11)
      e->res = 5, z->s11++;
    else if (e->si6)
      e->res = 6, z->si6++;
    else if (e->res == 10)
      z->sat++;
    else if (e->res == 20)
      z->uns++;
    else if (e->tio)
      e->res = 1, z->tio++;
    else if (e->meo)
      e->res = 2, z->meo++;
    else
      e->unk = 1, e->res = 3, z->unk++;
    assert(e->res);
    if (e->res == 10 || e->res == 20) {
      z->tim += e->tim, z->wll += e->wll, z->mem += e->mem;
      if (e->mem > z->max)
	z->max = e->mem;
    }
    if (z->ubndbroken && e->bnd >= 0 && e->res != 10) {
      if (z->ubndbroken == UBND_GLOBALLY_BROKEN)
	assert(zummary_mode != LOCAL_ZUMMARY);
      e->bnd = -1;
    }
    if (e->bnd >= 0 && e->res != 4)
      z->bnd++;
  }
  z->sol = z->sat + z->uns;
  z->fld = z->tio + z->meo + z->s11 + z->si6 + z->unk;
  assert(z->cnt == z->sol + z->fld + z->dis);
  if (par) {
    if (usereal)
      z->par = z->wll + par * z->rlim * z->fld;
    else
      z->par = z->tim + par * z->tlim * z->fld;
  }
  if (zummary_mode != LOCAL_ZUMMARY)
    z->only_use_for_reporting_and_do_not_write = 1;
}

static int mystrcmp(const char *a, const char *b) { return strcmp(a, b); }

static void loadzummary(Zummary *z, const char *path) {
  int first = 1;
  assert(!z->cnt);
  msg(1, "trying to load zummary '%s'", path);
  open_input(path);
  lineno = 1;
  while (parsezummaryline()) {
    if (!first) {
      double tlim, rlim, slim;
      Entry *e;
      if (ntokens < 8 || ntokens > 9)
	die("invalid line in '%s'", path);
      e = newentry(z, tokens[0]);
      e->res = atoi(tokens[1]);
      e->tim = atof(tokens[2]);
      e->wll = atof(tokens[3]);
      e->mem = atof(tokens[4]);
      tlim = atof(tokens[5]);
      if (tlim <= 0)
	die("invalid time limit %.0f in '%s'", tlim, path);
      if (z->tlim < 0) {
	msg(1, "setting time limit of '%s' to %.0f", z->path, tlim);
	z->tlim = tlim;
      } else if (!ignore && z->tlim != tlim)
	wrn("different time limit %.0f in '%s'", tlim, path);
      rlim = atof(tokens[6]);
      if (rlim <= 0)
	die("invalid real time limit %.0f in '%s'", rlim, path);
      if (z->rlim < 0) {
	msg(1, "setting real time limit of '%s' to %.0f", z->path, rlim);
	z->rlim = rlim;
      } else if (!ignore && z->rlim != rlim)
	wrn("different real time limit %.0f in '%s'", rlim, path);
      slim = atof(tokens[7]);
      if (slim <= 0)
	die("invalid space limit %.0f in '%s'", slim, path);
      if (z->slim < 0) {
	msg(1, "setting space limit of '%s' to %.0f", z->path, slim);
	z->slim = slim;
      } else if (!ignore && z->slim != slim)
	wrn("different space limit %.0f in '%s'", slim, path);
      if (ntokens < 9 || (e->bnd = atof(tokens[8])) < 0)
	e->bnd = -1;
      if (ntokens == 9)
	msg(2, "loaded %s %d %.2f %.2f %.1f %.2f %.2f %.1f %d", e->name, e->res,
	    e->tim, e->wll, e->mem, tlim, rlim, slim, e->bnd);
      else
	msg(2, "loaded %s %d %.2f %.2f %.1f %.2f %.2f %.1f", e->name, e->res,
	    e->tim, e->wll, e->mem, tlim, rlim, slim);

      if (e->res != 10 && e->res != 20) {
	assert(e->res != 4);
	if (e->res == 1)
	  e->tio = 1;
	if (e->res == 2)
	  e->meo = 1;
	else if (e->res == 3)
	  e->unk = 1;
	else if (e->res == 4)
	  e->dis = 1; // TODO remove?
	else if (e->res == 5)
	  e->s11 = 1;
	else if (e->res == 6)
	  e->si6 = 1;
      }

    } else if (ntokens < 7 || ntokens > 8 || mystrcmp(tokens[0], "result") ||
	       mystrcmp(tokens[1], "time") || mystrcmp(tokens[2], "real") ||
	       mystrcmp(tokens[3], "space") || mystrcmp(tokens[4], "tlim") ||
	       mystrcmp(tokens[5], "rlim") || mystrcmp(tokens[6], "slim") ||
	       (ntokens == 8 && mystrcmp(tokens[7], "bound")))
      die("invalid header in '%s'", path);
    else
      first = 0;
  }
  msg(1, "loaded %d entries from '%s'", z->cnt, path);
  close_input(path);
  sortzummary(z);
  loaded++;
}

static void updatezummary(Zummary *z) {
  struct dirent *dirent;
  DIR *dir;
  Entry *e;
  msg(1, "updating zummary for directory '%s'", z->path);
  if (!(dir = opendir(z->path)))
    die("can not open directory '%s' for updating", z->path);
  z->cnt = 0;
  while ((dirent = readdir(dir))) {
    char *base, *logname, *logpath;
    const char *errname = dirent->d_name;
    msg(2, "checking '%s'", errname);
    if (!(base = stripsuffix(errname, ".err"))) {
      msg(2, "skipping '%s'", errname);
      continue;
    }
    logname = appendstr(base, ".log");
    logpath = appendpath(z->path, logname);
    if (isfile(logpath)) {
      char *errpath = appendpath(z->path, errname);
      e = newentry(z, base);
      assert(isfile(errpath));
      if (parserrfile(e, errpath))
	parselogfile(e, logpath);
      free(errpath);
      assert(!e->res || e->res == 10 || e->res == 20);
      if (e->tio && e->res)
	wrn("result %d with time-out in '%s/%s'", e->res, z->path, base);
      if (e->meo && e->res)
	wrn("result %d with memory-out in '%s/%s'", e->res, z->path, base);
      if (e->s11 && e->res)
	wrn("result %d with 'segmentation fault' in '%s/%s'", e->res, z->path,
	    base);
      if (e->s11 && e->res)
	wrn("result %d with 'segmentation fault' (s11) in '%s/%s'", e->res,
	    z->path, base);
      if (e->si6 && e->res)
	wrn("result %d with 'abort signal' (s6) in '%s/%s'", e->res, z->path,
	    base);
      if (e->unk && e->res)
	wrn("result %d and unknown status in '%s/%s'", e->res, z->path, base);
    } else
      msg(1, "missing '%s'", logpath);
    free(logpath);
    free(logname);
    free(base);
  }
  (void)closedir(dir);
  msg(1, "found %d entries in '%s'", z->cnt, z->path);
  if (z->cnt) {
    if (z->tlim < 0)
      die("no time limit in '%s'", z->path);
    if (z->rlim < 0)
      die("no real time limit in '%s'", z->path);
    if (z->slim < 0)
      die("no space limit in '%s'", z->path);
    if (nzummaries > 1 && z->cnt) {
      if (!ignore && z->tlim != zummaries[0]->tlim)
	wrn("different time limit '%.0f' in '%s'", z->tlim, z->path);
      if (!ignore && z->rlim != zummaries[0]->rlim)
	wrn("different real time limit '%.0f' in '%s'", z->rlim, z->path);
      if (!ignore && z->slim != zummaries[0]->slim)
	wrn("different space limit '%.0f' in '%s'", z->slim, z->path);
    }
  }
  sortzummary(z);
  updated++;
}

static void writezummary(Zummary *z, const char *path) {
  int printbounds;
  FILE *file;
  Entry *e;
  assert(!z->only_use_for_reporting_and_do_not_write);
  file = fopen(path, "w");
  if (!file)
    die("can not write '%s'", path);
  fputs(" result time real space tlim rlim slim", file);
  if ((printbounds = !nobounds && z->bnd > 0))
    fputs(" bound", file);
  fputc('\n', file);
  for (e = z->first; e; e = e->next) {
    fprintf(file, "%s %d %.2f %.2f %.1f %.0f %.0f %.0f", e->name, e->res,
	    e->tim, e->wll, e->mem, z->tlim, z->rlim, z->slim);
    if (printbounds)
      fprintf(file, " %d", e->bnd);
    fputc('\n', file);
  }
  fclose(file);
  msg(1, "written %d entries to zummary '%s'", z->cnt, path);
  written++;
}

static void zummarizeone(const char *path) {
  char *pathtozummary;
  int update;
  Zummary *z;
  assert(isdir(path));
  z = newzummary(path);
  msg(1, "zummarizing directory %s", path);
  pathtozummary = appendpath(path, "zummary");
  update = 1;
  if (!isfile(pathtozummary))
    msg(1, "zummary file '%s' not found", pathtozummary);
  else if (force)
    msg(1, "forcing update of '%s' (through '-f' option)", pathtozummary);
  else if (zummaryneedsupdate(z, pathtozummary))
    msg(1, "zummary '%s' needs update", pathtozummary);
  else {
    loadzummary(z, pathtozummary);
    update = 0;
  }
  if (update) {
    updatezummary(z);
    if (!nowrite && z->cnt) {
      fixzummary(z, LOCAL_ZUMMARY);
      writezummary(z, pathtozummary);
    }
  }
  free(pathtozummary);
}

static int cmpsyms4qsort(const void *p, const void *q) {
  Symbol *s = *(Symbol **)p, *t = *(Symbol **)q;
  return strcmp(s->name, t->name);
}

static void sortsymbols() {
  Symbol *p = 0, *s, *n;
  int i;
  for (i = 0; i < sizesymtab; i++)
    for (s = symtab[i]; s; s = n)
      n = s->next, s->next = p, p = s;
  for (i = 0; p; p = p->next)
    symtab[i++] = p;
  assert(i == nsyms);
  qsort(symtab, nsyms, sizeof *symtab, cmpsyms4qsort);
  msg(2, "sorted %d symbols", nsyms);
}

static void discrepancies() {
  int i, count = 0;
  for (i = 0; i < nsyms; i++) {
    int sat = 0, unsat = 0, expected;
    Symbol *s = symtab[i];
    Entry *e;
    char cmp;
    for (e = s->first; e; e = e->chain) {
      assert(e->name == s->name);
      if (e->res == 10)
	sat++;
      if (e->res == 20)
	unsat++;
    }
    if (!sat)
      continue;
    if (!unsat)
      continue;
    if (sat > unsat)
      expected = 10, cmp = '>';
    else if (sat < unsat)
      expected = 20, cmp = '<';
    else
      expected = 0, cmp = '=';
    wrn("DISCREPANCY on '%s' with %d SAT %c %d UNSAT", s->name, sat, cmp,
	unsat);
    for (e = s->first; e; e = e->chain) {
      const char *suffix;
      if (e->res < 10)
	continue;
      assert(e->res == 10 || e->res == 20);
      if (!expected)
	suffix = " (tie so assumed wrong)";
      else if (e->res != expected)
	suffix = " (overvoted so probably wrong)";
      else
	suffix = "";
      wrn("%s %s/%s %s%s", (e->res == expected) ? " " : "!", e->zummary->path,
	  s->name, (e->res == 10 ? "SAT" : "UNSAT"), suffix);
      if (e->res != expected)
	e->dis = 1;
    }
    fflush(stdout);
    count++;
  }
  if (count)
    msg(1, "found %d result discrepancies", count);
  else
    msg(1, "no result discrepancies found");
  count = 0;
  for (i = 0; i < nsyms; i++) {
    Symbol *s = symtab[i];
    Entry *e, *w = 0, *o1 = 0, *o2 = 0;
    for (e = s->first; e; e = e->chain) {
      if (e->dis)
	continue;
      if (e->res != 10)
	continue;
      if (w && e->bnd >= 0 && w->bnd > e->bnd)
	w = e;
      if (e->obnd >= 0) {
	if (o1 && !o2 && o1->obnd != e->obnd)
	  o2 = e;
	if (!o1)
	  o1 = e;
      }
    }
    if (w) {
      for (e = s->first; e; e = e->chain) {
	if (e->dis)
	  continue;
	if (e->res == 10)
	  continue;
	assert(e->res != 20);
	if (e->bnd < w->bnd)
	  continue;
	wrn("unsat-bound %d in '%s/%s' >= witness length %d in '%s/%s'", e->bnd,
	    e->zummary->path, e->name, w->bnd, w->zummary->path, w->name);
	setubndbroken(e, UBND_GLOBALLY_BROKEN);
      }
    }
    if (o1 && o2) {
      assert(o1->obnd >= 0);
      assert(o2->obnd >= 0);
      assert(o1->obnd != o2->obnd);
      wrn("optimum %ld in '%s/%s' does not match %ld in '%s/%s'", o1->obnd,
	  o1->zummary->path, o1->name, o2->obnd, o2->zummary->path, o2->name);
      for (e = s->first; e; e = e->chain) {
	if (e->dis)
	  continue;
	if (e->res != 10)
	  continue;
	e->dis = 1;
      }
    }
  }
}

static void checklimits() {
  Zummary *x, *y, *z;
  int i;
  y = 0;
  for (i = 0; !y && i < nzummaries; i++)
    if ((x = zummaries[i])->cnt)
      y = x;
  if (!y)
    return;
  while (i < nzummaries) {
    z = zummaries[i++];
    if (!z->cnt)
      continue;
    if (!ignore && y->tlim != z->tlim)
      wrn("different time limit in '%s' and '%s'", y->path, z->path);
    if (!ignore && y->rlim != z->rlim)
      wrn("different real time limit in '%s' and '%s'", y->path, z->path);
    if (!ignore && y->slim != z->slim)
      wrn("different space limit in '%s' and '%s'", y->path, z->path);
  }
  msg(1, "all zummaries have the same time and space limits");
  if (y->tlim >= y->rlim) {
    msg(1, "zummarizing over real time (not process time)");
    usereal = 1;
  } else {
    msg(1, "zummarizing over process time (not real time)");
    usereal = 0;
  }
}

static void fixzummaries(int zummary_mode) {
  int i;
  for (i = 0; i < nzummaries; i++)
    fixzummary(zummaries[i], zummary_mode);
}

static void computedeep() {
  int i, count, unsolved;
  count = unsolved = 0;
  for (i = 0; i < nsyms; i++) {
    Symbol *s = symtab[i];
    count++;
    if (s->sat)
      continue;
    if (s->uns)
      continue;
    msg(1, "unsolved instance '%s'", s->name);
    unsolved++;
  }
  if (unsolved) {
    msg(1, "found %d unsolved instances out of %d", unsolved, count);
  } else
    msg(1, "all instances solved");
  for (i = 0; i < nzummaries; i++) {
    Zummary *z = zummaries[i];
    int aftercapping;
    Entry *e;
    if (z->ubndbroken)
      continue;
    z->deep = 0;
    for (e = z->first; e; e = e->next) {
      double inc;
      if (e->dis)
	continue;
      if ((aftercapping = e->bnd) < 0)
	continue;
      if (e->symbol->sat)
	continue;
      if (e->symbol->uns)
	continue;
      if (aftercapping > capped)
	aftercapping = capped;
      inc = 1e5 - 1e5 / (aftercapping + 2.0);
      z->deep += inc;
      msg(2, "unsat-bound %d capped to %d in '%s/%s' contributes %.0f", e->bnd,
	  aftercapping, z->path, e->name, inc);
    }
    if (unsolved > 0)
      z->deep /= (double)unsolved;
    msg(1, "deep score %.0f of '%s'", z->deep, z->path);
  }
}

static int cmpdouble(double a, double b) {
  if (a < b)
    return -1;
  if (b < a)
    return 1;
  return 0;
}

static int cmp_entry_resources(Entry *a, Entry *b) {
  int res;
  if (usereal) {
    if ((res = cmpdouble(a->wll, b->wll)))
      return res;
    if ((res = cmpdouble(a->tim, b->tim)))
      return res;
  } else {
    if ((res = cmpdouble(a->tim, b->tim)))
      return res;
    if ((res = cmpdouble(a->wll, b->wll)))
      return res;
  }
  if ((res = cmpdouble(a->mem, b->mem)))
    return res;
  return 0;
}

static int cmp_entry_bound(Entry *a, Entry *b) {
  if (a->bnd < 0 && b->bnd < 0)
    return 0;
  if (a->bnd >= 0 && b->bnd < 0)
    return -1;
  if (a->bnd < 0 && b->bnd >= 0)
    return 1;
  return a->bnd - b->bnd;
}

static int cmp_entry_better_aux(Entry *a, Entry *b) {
  int res;
  if (a && a->dis)
    a = 0;
  if (b && b->dis)
    b = 0;
  if (a && a->res < 10 && a->bnd < 0)
    a = 0;
  if (b && b->res < 10 && b->bnd < 0)
    b = 0;
  if (!a && !b)
    return 0;
  if (!a) {
    assert(b);
    assert(!b->dis);
    assert(b->res >= 10 || b->bnd >= 0);
    return 1;
  }
  if (!b) {
    assert(a);
    assert(!a->dis);
    assert(a->res >= 10 || a->bnd >= 0);
    return -1;
  }
  assert(b);
  assert(!b->dis);
  assert(b->res >= 10 || b->bnd >= 0);
  assert(a);
  assert(!a->dis);
  assert(a->res >= 10 || a->bnd >= 0);
  if (a->res == 10 && b->res == 10) {
    if ((res = cmp_entry_resources(a, b)))
      return res;
    if ((res = cmp_entry_bound(a, b)))
      return res; // shorter
    return 0;
  }
  if (a->res == 20 && b->res == 20) {
    if ((res = cmp_entry_resources(a, b)))
      return res;
    return 0;
  }
  if (a->res >= 10) {
    assert(b->res < 10);
    return -1;
  }
  if (b->res >= 10) {
    assert(a->res < 10);
    return 1;
  }
  assert(a->res < 10);
  assert(b->res < 10);
  if ((res = cmp_entry_bound(b, a)))
    return res; // longer
  return 0;
}

static int cmp_entry_better(Entry *a, Entry *b) {
  int res = cmp_entry_better_aux(a, b);
  assert(cmp_entry_better_aux(b, a) == -res);
  return res;
}

static void findbest() {
  int i;
  for (i = 0; i < nsyms; i++) {
    Symbol *s = symtab[i];
    Entry *e, *best = 0;
    for (e = s->first; e; e = e->chain) {
      if (e->dis)
	continue;
      if (cmp_entry_better(e, best) < 0)
	best = e;
      if (e->res == 10)
	s->sat++;
      if (e->res == 20)
	s->uns++;
    }
    if (best) {
      msg(2, "best result '%s/%s.log'", best->zummary->path, best->name);
      for (e = s->first; e; e = e->chain)
	e->best = best;
    } else
      msg(2, "no result for '%s'", s->name);
  }
}

static int cmpzummaries4qsort(const void *p, const void *q) {
  Zummary *y = *(Zummary **)p, *z = *(Zummary **)q;
  int res;
  if (par && (res = cmpdouble(y->par, z->par)))
    return res;
  int a = y->sat + y->uns, b = z->sat + z->uns;
  res = b - a;
  if (satonly)
    res = z->sat - y->sat;
  else if (unsatonly)
    res = z->uns - y->uns;
  else if (deeponly)
    res = cmpdouble(z->deep, y->deep);
  else
    res = (z->sat + z->uns) - (y->sat + y->uns);
  if (res)
    return res;
  if (usereal) {
    if ((res = cmpdouble(y->wll, z->wll)))
      return res;
    if ((res = cmpdouble(y->tim, z->tim)))
      return res;
  } else {
    if ((res = cmpdouble(y->tim, z->tim)))
      return res;
    if ((res = cmpdouble(y->wll, z->wll)))
      return res;
  }
  if ((res = cmpdouble(y->max, z->max)))
    return res;
  if ((res = cmpdouble(y->mem, z->mem)))
    return res;
  return strcmp(y->path, z->path);
}

static void sortzummaries() {
  qsort(zummaries, nzummaries, sizeof *zummaries, cmpzummaries4qsort);
  msg(2, "sorted all zummaries");
}

static int ilen(int n) {
  int res, tmp;
  assert(n >= 0);
  for (res = 1, tmp = 10; res < 10; res++, tmp *= 10)
    if (n < tmp)
      return res;
  return res;
}

static int dlen(double d) {
  double tmp;
  int res;
  assert(d >= 0);
  for (res = 1, tmp = 10; res < 20; res++, tmp *= 10)
    if (d < tmp)
      return res;
  return res;
}

static int skiprefixlength() {
  int res, i, j;
  if (nzummaries) {
    res = strlen(zummaries[0]->path);
    for (i = 1; i < nzummaries; i++) {
      for (j = 0; j < res; j++)
	if (zummaries[i]->path[j] != zummaries[0]->path[j])
	  break;
      res = j;
      assert(res <= strlen(zummaries[i]->path));
    }
    while (res > 0 && zummaries[0]->path[res - 1] != '/')
      res--;
  } else
    res = 0;
  return res;
}

static void printzummaries() {

  char parname[10];
  sprintf(parname, "par%d", par);

  int nam, cnt, sol, sat, uns, dis, fld, tio, meo, s11, si6, unk;
  int wll, tim, par, mem, max, bst, unq, deep;
  int i, j, skip;

  nam = cnt = sol = sat = uns = dis = fld = tio = meo = s11 = si6 = unk = 0;
  wll = tim = par = mem = max = bst = unq = deep = 0;

  skip = skiprefixlength();

  for (i = 0; i < nzummaries; i++) {
    Zummary *z = zummaries[i];

#define UPDATEIFLARGERAUX(OLDLEN, NEWLEN)                                      \
  do {                                                                         \
    int TMPAUX = (NEWLEN);                                                     \
    if (TMPAUX > OLDLEN)                                                       \
      OLDLEN = TMPAUX;                                                         \
  } while (0)

#define UPDATEIFLARGERLEN(OLDLEN, LEN, DATA)                                   \
  do {                                                                         \
    int TMPLEN = (DATA);                                                       \
    if (!TMPLEN)                                                               \
      break;                                                                   \
    UPDATEIFLARGERAUX(OLDLEN, LEN(TMPLEN));                                    \
  } while (0)

    UPDATEIFLARGERAUX(nam, strlen(z->path + skip));
    UPDATEIFLARGERLEN(cnt, ilen, z->cnt);
    UPDATEIFLARGERLEN(sol, ilen, z->sol);
    UPDATEIFLARGERLEN(sat, ilen, z->sat);
    UPDATEIFLARGERLEN(uns, ilen, z->uns);
    UPDATEIFLARGERLEN(dis, ilen, z->dis);
    UPDATEIFLARGERLEN(fld, ilen, z->fld);
    UPDATEIFLARGERLEN(tio, ilen, z->tio);
    UPDATEIFLARGERLEN(meo, ilen, z->meo);
    UPDATEIFLARGERLEN(s11, ilen, z->s11);
    UPDATEIFLARGERLEN(si6, ilen, z->si6);
    UPDATEIFLARGERLEN(unk, ilen, z->unk);
    UPDATEIFLARGERLEN(wll, dlen, z->wll);
    UPDATEIFLARGERLEN(tim, dlen, z->tim);
    UPDATEIFLARGERLEN(par, dlen, z->par);
    UPDATEIFLARGERLEN(mem, dlen, z->mem);
    UPDATEIFLARGERLEN(max, dlen, z->max);
    UPDATEIFLARGERLEN(bst, ilen, z->bst);
    UPDATEIFLARGERLEN(unq, ilen, z->unq);
    UPDATEIFLARGERLEN(deep, dlen, z->deep);
  }

#define PRINTHEADER(CHARS, HEADER)                                             \
  do {                                                                         \
    int LEN, I;                                                                \
    if (!printall && !CHARS)                                                   \
      break;                                                                   \
    LEN = strlen(HEADER);                                                      \
    if (CHARS < LEN)                                                           \
      CHARS = LEN;                                                             \
    if (&CHARS != &nam)                                                        \
      fputc(' ', stdout);                                                      \
    for (I = 0; I < CHARS - LEN; I++)                                          \
      fputc(' ', stdout);                                                      \
    fputs(HEADER, stdout);                                                     \
  } while (0)

  PRINTHEADER(nam, "");
  PRINTHEADER(cnt, "cnt");
  PRINTHEADER(sol, "ok");
  PRINTHEADER(sat, "sat");
  PRINTHEADER(uns, "uns");
  PRINTHEADER(dis, "dis");
  PRINTHEADER(fld, "fld");
  PRINTHEADER(tio, "to");
  PRINTHEADER(meo, "mo");
  PRINTHEADER(s11, "s11");
  PRINTHEADER(si6, "s6");
  PRINTHEADER(unk, "unk");
  PRINTHEADER(wll, "real");
  PRINTHEADER(tim, "time");
  PRINTHEADER(par, parname);
  PRINTHEADER(mem, "space");
  PRINTHEADER(max, "max");
  PRINTHEADER(bst, "best");
  PRINTHEADER(unq, "uniq");
  PRINTHEADER(deep, "deep");
  putc('\n', stdout);

  for (i = 0; i < nzummaries; i++) {
    Zummary *z = zummaries[i];
    if (!printall && satonly && !z->sat)
      continue;
    if (!printall && unsatonly && !z->uns)
      continue;
    if (!printall && deeponly && !z->deep)
      continue;
    j = nam - strlen(z->path + skip);
    assert(j >= 0);
    while (j-- > 0)
      fputc(' ', stdout);
    fputs(z->path + skip, stdout);

#define IPRINTZUMMARY(NAME)                                                    \
  do {                                                                         \
    char fmt[20];                                                              \
    if (!printall && !NAME)                                                    \
      break;                                                                   \
    sprintf(fmt, " %%%dd", NAME);                                              \
    printf(fmt, z->NAME);                                                      \
  } while (0)

#define FPRINTZUMMARY(NAME)                                                    \
  do {                                                                         \
    char fmt[20];                                                              \
    if (!printall && !NAME)                                                    \
      break;                                                                   \
    sprintf(fmt, " %%%d.0f", NAME);                                            \
    printf(fmt, z->NAME);                                                      \
  } while (0)

    IPRINTZUMMARY(cnt);
    IPRINTZUMMARY(sol);
    IPRINTZUMMARY(sat);
    IPRINTZUMMARY(uns);
    IPRINTZUMMARY(dis);
    IPRINTZUMMARY(fld);
    IPRINTZUMMARY(tio);
    IPRINTZUMMARY(meo);
    IPRINTZUMMARY(s11);
    IPRINTZUMMARY(si6);
    IPRINTZUMMARY(unk);
    FPRINTZUMMARY(wll);
    FPRINTZUMMARY(tim);
    FPRINTZUMMARY(par);
    FPRINTZUMMARY(mem);
    FPRINTZUMMARY(max);
    IPRINTZUMMARY(bst);
    IPRINTZUMMARY(unq);
    FPRINTZUMMARY(deep);
    fputc('\n', stdout);
  }
}

static void printdeep() {
  int i, unsolved;
  FILE *file;
  unsolved = 0;
  for (i = 0; i < nsyms; i++) {
    Symbol *s = symtab[i];
    if (s->sat)
      continue;
    if (s->uns)
      continue;
    unsolved++;
  }
  printf("\nused the following %d unsolved instances:\n\n", unsolved);
  fflush(stdout);
  file = popen("fmt", "w");
  for (i = 0; i < nsyms; i++) {
    Symbol *s = symtab[i];
    if (s->sat)
      continue;
    if (s->uns)
      continue;
    fprintf(file, "%s\n", s->name);
  }
  pclose(file);
}

static double ratio(double a, double b) {
  if (!a && !b)
    return 1;
  if (!a)
    return 0;
  if (!b)
    return 1e9;
  return a / b;
}

static int cmpcmp4qsort(const void *p1, const void *p2) {
  Symbol *s1 = *(Symbol **)p1;
  Symbol *s2 = *(Symbol **)p2;
  double r1 = ratio(s1->first->tim, s1->last->tim);
  double r2 = ratio(s2->first->tim, s2->last->tim);
  if (r1 > r2)
    return -1;
  if (r1 < r2)
    return 1;
  if (s1->first->tim > s2->first->tim)
    return -1;
  if (s1->first->tim > s2->first->tim)
    return 1;
  return strcmp(s1->name, s2->name);
}

static void compare() {
  Symbol **a = malloc(nsyms * sizeof *a);
  int i, n = 0;
  if (!a)
    die("out of memory allocating comparison table");
  for (i = 0; i < nsyms; i++) {
    Symbol *s = symtab[i];
    Entry *e1 = s->first, *e2 = s->last;
    if (!e1)
      continue;
    assert(e2);
    int r1 = (e1->res == 10 || e1->res == 20);
    int r2 = (e2->res == 10 || e2->res == 20);
    if (satonly && e1->res == 20)
      continue;
    if (satonly && e2->res == 20)
      continue;
    if (unsatonly && e1->res == 10)
      continue;
    if (unsatonly && e2->res == 10)
      continue;
    if (nounknown && e1->unk)
      continue;
    if (nounknown && e2->unk)
      continue;
    if (filter && r1 + r2 != 1)
      continue;
    if (!filter && r1 + r2 == 0)
      continue;
    a[n++] = s;
  }
  qsort(a, n, sizeof *a, cmpcmp4qsort);
  for (int i = 0; i < n; i++) {
    Symbol *s = a[i];
    Entry *e1 = s->first, *e2 = s->last;
    int r1 = (e1->res == 10 || e1->res == 20);
    int r2 = (e2->res == 10 || e2->res == 20);
    double t1, t2;
    if (usereal) {
      t1 = r1 ? e1->wll : e1->zummary->rlim;
      t2 = r2 ? e2->wll : e2->zummary->rlim;
    } else {
      t1 = r1 ? e1->tim : e1->zummary->tlim;
      t2 = r2 ? e2->tim : e2->zummary->tlim;
    }
    printf("%.2f %s %.2f %.2f\n", ratio(t1, t2), s->name, t1, t2);
  }
  free(a);
}

static void plot() {
  char prefix[80], rscriptpath[100], pdfpathbuf[100], cmd[200];
  int i, c, skip = skiprefixlength(), maxbnd, res;
  const char *pdfpath;
  FILE *rscriptfile;
  Zummary *z;
  sprintf(prefix, "/tmp/zummarize-plot-%ld", (long)getpid());
  sprintf(rscriptpath, "%s.rscript", prefix);
  if (outputpath)
    pdfpath = outputpath;
  else {
    sprintf(pdfpathbuf, "%s.pdf", prefix);
    pdfpath = pdfpathbuf;
  }
  if (!(rscriptfile = fopen(rscriptpath, "w")))
    die("can not open '%s' for writing", rscriptpath);
  if (orderpath)
    parseorder();
  fprintf(rscriptfile, "m = c(");
  c = 0;
  maxbnd = 0;
  for (i = 0; i < nzummaries; i++) {
    z = zummaries[i];
    if (satonly && !z->sat)
      continue;
    if (unsatonly && !z->uns)
      continue;
    if (deeponly && !z->deep)
      continue;
    if (c++)
      fputc(',', rscriptfile);
    if (norder) {
      int j;
      for (j = 0; j < norder; j++)
	if (!strcmp(z->path + skip, order[j].name))
	  break;
      if (j == norder)
	die("order file '%s' does not contain '%s'", orderpath, z->path + skip);
      fprintf(rscriptfile, "%d", order[j].order);
    } else
      fprintf(rscriptfile, "%d", c);
    if (z->bnd > maxbnd)
      maxbnd = z->bnd;
  }
  fprintf(rscriptfile, ")\n");
  fprintf(rscriptfile, "pdf (\"%s\",height=5,width=8)\n", pdfpath);
  c = 0;
  for (i = 0; i < nzummaries; i++) {
    z = zummaries[i];
    if (!z->cnt)
      continue;
    int printed;
    Entry *e;
    if (satonly && !z->sat)
      continue;
    if (unsatonly && !z->uns)
      continue;
    if (deeponly && !z->deep)
      continue;
    c++;
    fprintf(rscriptfile, "z%d=", c);
    printed = 0;
    for (e = z->first; e; e = e->next) {
      double t;
      if (!deeponly && e->res != 10 && e->res != 20)
	continue;
      if (unsatonly && e->res != 20)
	continue;
      if (satonly && e->res != 10)
	continue;
      if (deeponly) {
	if (e->bnd < 0)
	  continue;
	if (e->best && e->best->res == 10)
	  continue;
	if (e->best && e->best->res == 20)
	  continue;
      }
      t = usereal ? e->wll : e->tim;
      if (printed++)
	fprintf(rscriptfile, ",");
      else
	fprintf(rscriptfile, "c(");
      if (deeponly) {
	int b = e->bnd > capped ? capped : e->bnd;
#if 0
	fprintf(rscriptfile, "%d", b);
#else
	double s = capped - capped / (b + 2.0);
	fprintf(rscriptfile, "%f", s);
#endif
      } else
	fprintf(rscriptfile, "%.2f", t);
    }
    fprintf(rscriptfile, ")\n");
    fprintf(rscriptfile, "z%d = sort (z%d)\n", c, c);
    if (c == 1) {
      if (title)
	fprintf(rscriptfile, "par (mar=c(2.5,2.5,1.5,.5))\n");
      else
	fprintf(rscriptfile, "par (mar=c(2.5,2.5,.5,.5))\n");

      if (deeponly) {
	fprintf(rscriptfile,
		"plot (c(0,%d+10),c(0,%d+%d),"
		"col=0,xlab=\"\",ylab=\"\",main=\"%s\"%s)\n",
		maxbnd, capped, (int)(capped * 0.02), title ? title : "",
		logy ? ",log=\"y\"" : "");
	fprintf(rscriptfile, "abline (%d, 0,lty=3)\n", capped);
      } else if (cdf) {
	double pxmax;
	int pymax;
	if (xmax < 0)
	  pxmax = (usereal ? z->rlim : z->tlim) +
		  0.02 * (usereal ? z->rlim : z->tlim);
	else
	  pxmax = xmin;
	if (ymax < 0)
	  pymax = z->sol + 10;
	else
	  pymax = ymax;
	fprintf(rscriptfile,
		"plot ("
		"c(%d,%.2f),"
		"c(%d,%d),"
		"col=0,xlab=\"\",ylab=\"\",main=\"%s\"%s)\n",
		(xmin < 0 ? 0 : xmin), pxmax, (ymin < 0 ? 0 : ymin), pymax,
		title ? title : "", logy ? ",log=\"y\"" : "");

	if (limit >= 0)
	  fprintf(rscriptfile, "abline(h=%d,col=\"blue\")\n", limit);

	if (patch) {
	  FILE *patchfile = fopen(patch, "r");
	  int ch;
	  if (!patchfile)
	    die("can not read patch file '%s'", patch);
	  while ((ch = getc(patchfile)) != EOF)
	    fputc(ch, rscriptfile);
	  fclose(patchfile);
	}
      } else {
	fprintf(rscriptfile,
		"plot (c(0,%d+10),c(0,%.2f+%.2f),"
		"col=0,xlab=\"\",ylab=\"\",main=\"%s\"%s)\n",
		z->sol, (usereal ? z->rlim : z->tlim),
		0.02 * (usereal ? z->rlim : z->tlim), title ? title : "",
		logy ? ",log=\"y\"" : "");
	fprintf(rscriptfile, "abline (%.0f, 0,lty=3)\n",
		usereal ? z->rlim : z->tlim);
      }
    }
    if (cdf)
      fprintf(rscriptfile,
	      "points (x=z%d,y=1:length(z%d),col=m[%d],pch=m[%d],type=\"o\")\n",
	      c, c, c, c);
    else
      fprintf(rscriptfile, "points (z%d,col=m[%d],pch=m[%d],type=\"o\")\n", c,
	      c, c);
  }
  if (nzummaries) {
    z = zummaries[0];
    if (center)
      fprintf(rscriptfile, "legend (x=\"%s\",legend=c(",
	      cdf ? "right" : "left");
    else
      fprintf(rscriptfile, "legend (x=\"%s\",legend=c(",
	      cdf ? "bottomright" : "topleft");
  }
  c = 0;
  for (i = 0; i < nzummaries; i++) {
    z = zummaries[i];
    if (!z->cnt)
      continue;
    if (satonly && !z->sat)
      continue;
    if (unsatonly && !z->uns)
      continue;
    if (deeponly && !z->deep)
      continue;
    c++;
    if (c > 1)
      fputc(',', rscriptfile);
    fprintf(rscriptfile, "\"%s\"", z->path + skip);
  }
  fprintf(rscriptfile, "),col=m,pch=m,cex=0.8)\n");
  fprintf(rscriptfile, "dev.off ()\n");
  fclose(rscriptfile);
  sprintf(cmd, "Rscript %s\n", rscriptpath);
  printf("%s\n", cmd);
  fflush(stdout);
  res = system(cmd);
  if (res)
    wrn("'system (%s) returned '%d'", cmd, res);
  if (!outputpath) {
    sprintf(cmd, "evince %s\n", pdfpath);
    printf("%s\n", cmd);
    res = system(cmd);
    if (res)
      wrn("'system (%s) returned '%d'", cmd, res);
  }
}

static void printmerged() {
  int skip = skiprefixlength(), i;
  for (i = 0; i < nsyms; i++) {
    Symbol *s = symtab[i];
    Entry *e;
    if (!i) {
      printf("benchmark");
      for (e = s->first; e; e = e->chain) {
	printf(";solver");
	printf(";status");
	printf(";bound");
	printf(";real");
	printf(";time");
	printf(";mem");
      }
      printf("\n");
    }
    printf("%s", s->name);
    for (e = s->first; e; e = e->chain) {
      printf(";%s", e->zummary->path + skip);
      assert(e->res != 4);
      switch (e->res) {
      case 1:
	printf(";time");
	break;
      case 2:
	printf(";mem");
	break;
      case 5:
	printf(";s11");
	break;
      case 6:
	printf(";s6");
	break;
      case 10:
	printf(";sat");
	break;
      case 20:
	printf(";uns");
	break;
      default:
	assert(e->res == 3);
      case 3:
	printf(";unk");
	break;
      }
      printf(";%d", e->bnd);
      printf(";%.02f", e->wll);
      printf(";%.02f", e->tim);
      printf(";%.1f", e->mem);
    }
    printf("\n");
  }
}

static void printranked() {
  int i;
  for (i = 0; i < nsyms; i++) {
    Symbol *s = symtab[i];
    int c = s->sat + s->uns;
    if (solved && !c)
      continue;
    if (unsolved && c)
      continue;
    printf("%d %s\n", s->sat + s->uns, s->name);
  }
}

static void zummarizeall() {
  msg(2, "%u benchmarks (%llu searched, %llu collisions %.2f on average)",
      nsyms, searches, collisions,
      searches ? collisions / (double)searches : 1.0);
  sortsymbols();
  discrepancies();
  checklimits();
  if (merge)
    printmerged();
  else {
    fixzummaries(GLOBAL_ZUMMARY_DO_NOT_HAVE_BEST);
    findbest();
    fixzummaries(GLOBAL_ZUMMARY_HAVE_BEST);
    computedeep();
    sortzummaries();
    if (solved || unsolved || rank)
      printranked();
    else if (plotting)
      plot();
    else if (cmp)
      compare();
    else {
      printzummaries();
      if (deeponly)
	printdeep();
    }
  }
}

static void reset() {
  int i;
  for (i = 0; i < nzummaries; i++) {
    Zummary *z = zummaries[i];
    Entry *e, *n;
    for (e = z->first; e; e = n) {
      n = e->next;
      free(e);
    }
    free(z->path);
    free(z);
  }
  free(zummaries);
  free(tokens);
  free(token);
  for (i = 0; i < nsyms; i++) {
    Symbol *s = symtab[i];
    free(s->name);
    free(s);
  }
  free(symtab);
  for (i = 0; i < norder; i++)
    free(order[i].name);
  free(order);
}

int main(int argc, char **argv) {
  int i, count = 0;
  for (i = 1; i < argc; i++) {
    const char *arg = argv[i];
    if (!strcmp(arg, "-h"))
      usage();
    else if (!strcmp(arg, "-v"))
      verbose++;
    else if (!strcmp(arg, "--no-warnings") || !strcmp(arg, "-n"))
      nowarnings = 1;
    else if (!strcmp(arg, "--all") || !strcmp(arg, "-a"))
      printall = 1;
    else if (!strcmp(arg, "--sat") || !strcmp(arg, "-s"))
      satonly = 1;
    else if (!strcmp(arg, "--unsat") || !strcmp(arg, "-u"))
      unsatonly = 1;
    else if (!strcmp(arg, "--deep") || !strcmp(arg, "-d"))
      deeponly = 1;
    else if (!strcmp(arg, "--cactus"))
      plotting = cactus = 1, cdf = 0;
    else if (!strcmp(arg, "--cdf") || !strcmp(arg, "--plotting") ||
	     !strcmp(arg, "-c"))
      plotting = cdf = 1, cactus = 0;
    else if (!strcmp(arg, "--log") || !strcmp(arg, "-l"))
      logy = 1;
    else if (!strcmp(arg, "--center"))
      center = 1;
    else if (!strcmp(arg, "--merge") || !strcmp(arg, "-m"))
      merge = 1;
    else if (!strcmp(arg, "--rank") || !strcmp(arg, "-r"))
      rank = 1;
    else if (!strcmp(arg, "--force") || !strcmp(arg, "-f"))
      force = 1;
    else if (!strcmp(arg, "--ignore") || !strcmp(arg, "-i"))
      ignore = 1;
    else if (!strcmp(arg, "--just") || !strcmp(arg, "-j"))
      just = 1;
    else if (!strcmp(arg, "--solved")) {
      if (solved)
	die("'--solved' specified twice");
      if (unsolved)
	die("can not combine '--unsolved' and '--solved'");
      solved = 1;
    } else if (!strcmp(arg, "--cmp"))
      cmp = 1;
    else if (!strcmp(arg, "--ymin")) {
      if (++i == argc)
	die("argument to '%s' missing", arg);
      if ((ymin = atoi(argv[i])) < 0)
	die("invalid '%s %s'", arg, argv[i]);
    } else if (!strcmp(arg, "--xmin")) {
      if (++i == argc)
	die("argument to '%s' missing", arg);
      if ((xmin = atoi(argv[i])) < 0)
	die("invalid '%s %s'", arg, argv[i]);
    } else if (!strcmp(arg, "--ymax")) {
      if (++i == argc)
	die("argument to '%s' missing", arg);
      if ((ymax = atoi(argv[i])) < 0)
	die("invalid '%s %s'", arg, argv[i]);
    } else if (!strcmp(arg, "--xmax")) {
      if (++i == argc)
	die("argument to '%s' missing", arg);
      if ((xmax = atoi(argv[i])) < 0)
	die("invalid '%s %s'", arg, argv[i]);
    } else if (!strcmp(arg, "--limit")) {
      if (++i == argc)
	die("argument to '%s' missing", arg);
      if ((limit = atoi(argv[i])) < 0)
	die("invalid '%s %s'", arg, argv[i]);
    } else if (!strcmp(arg, "--patch")) {
      if (++i == argc)
	die("argument to '%s' missing", arg);
      patch = arg;
    } else if (!strcmp(arg, "--filter"))
      filter = 1;
    else if (!strcmp(arg, "--no-unknown"))
      nounknown = 1;
    else if (!strcmp(arg, "--unsolved")) {
      if (unsolved)
	die("'--unsolved' specified twice");
      if (solved)
	die("can not combine '--solved' and '--unsolved'");
      unsolved = 1;
    } else if (!strcmp(arg, "-o")) {
      if (outputpath)
	die("multiple output paths specified");
      if (i + 1 == argc)
	die("argument to '-o' missing");
      outputpath = argv[++i];
    } else if (!strcmp(arg, "--title") || !strcmp(arg, "-t")) {
      if (title)
	die("title multiply defined");
      if (i + 1 == argc)
	die("argument to '%s' missing", arg);
      title = argv[++i];
    } else if (!strcmp(arg, "--order")) {
      if (orderpath)
	die("multiple '--order' options");
      if (i + 1 == argc)
	die("argument to '%s' missing", arg);
      orderpath = argv[++i];
    } else if (!strcmp(arg, "--no-write"))
      nowrite = 1;
    else if (!strcmp(arg, "--no-bounds"))
      nobounds = 1;
    else if (!strcmp(arg, "--update")) {
      if (system("./update.sh"))
	die("calling './update.sh' failed");
    } else if (arg[0] == '-' && arg[1] == '-' && arg[2] == 'p' &&
	       arg[3] == 'a' && arg[4] == 'r') {
      if (!isdigit(arg[5]) || (arg[6] && !isdigit(arg[6])) ||
	  (arg[6] && arg[7]))
	die("expected one or two digits after '--par'");
      par = atoi(arg + 5);
    } else if (arg[0] == '-')
      die("invalid option '%s' (try '-h')", arg);
    else if (!isdir(arg))
      wrn("argument '%s' not a directory (try '-h')", arg);
    else
      count++;
  }
  assert(!cactus || !cdf);
  if (!count)
    die("no directory specified (try '-h')");
  if (cmp && count != 2)
    die("'--cmp' requires two directories");
  if (satonly && unsatonly)
    die("'--sat-only' and '--unsat-only'");
  if (title && !plotting)
    die("title defined without ploting");
  if (outputpath && !plotting)
    die("output file specfied without ploting");
  if (plotting && merge)
    die("can not plot and merge data");
  if (nowrite)
    msg(1, "will not write zummaries");
  else
    msg(1, "will generate or update existing zummaries");
  if (nobounds)
    msg(1, "will not write bounds");
  else
    msg(1, "will write bounds if found");
  if (satonly)
    msg(1, "will restrict report to satisfiable instances");
  if (unsatonly)
    msg(1, "will restrict report to unsatisfiable instances");
  if (par)
    msg(1, "using par%d score", par);
  if (orderpath)
    parseorder();
  for (i = 1; i < argc; i++) {
    const char *arg = argv[i];
    if (!strcmp(arg, "-t") || !strcmp(arg, "-o") || !strcmp(arg, "--title") ||
	!strcmp(arg, "--order"))
      i++;
    else if (arg[0] != '-' && isdir(arg))
      zummarizeone(argv[i]);
  }
  zummarizeall();
  reset();
  msg(1, "%d loaded, %d updated, %d written", loaded, updated, written);
  return 0;
}
