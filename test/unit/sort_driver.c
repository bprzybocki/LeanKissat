/* Differential test driver for sort.h (SORT, SORT_STACK, INSERTION_SORT),
   rank.h (RADIX_SORT) and sort.c (kissat_sort_literals).  Compiled together
   with verbatim copies of the Kissat sources (see run_sort.sh) and the stubs
   in sortstub/.  Test/Sort.lean performs exactly the same sequence.

   With argument 'bench' it instead times sorting 10^6 random unsigned
   numbers (SORT with '<', RADIX_SORT with identity rank) on stderr. */

#include "internal.h"
#include "rank.h"
#include "sort.h"

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/*------------------------------------------------------------------------*/
/* allocation (allocate.h) */

void *kissat_malloc (kissat *s, size_t b) { (void) s; return malloc (b); }
void kissat_free (kissat *s, void *p, size_t b) { (void) s, (void) b; free (p); }
void *kissat_realloc (kissat *s, void *p, size_t o, size_t b) {
  (void) s, (void) o;
  return realloc (p, b);
}

/*------------------------------------------------------------------------*/

static uint64_t state = 0x9E3779B97F4A7C15ull;

static unsigned rnd32 (void) {
  state = state * 6364136223846793005ull + 1442695040888963407ull;
  return (unsigned) (state >> 32);
}

static unsigned rndn (unsigned n) { return rnd32 () % n; }

static uint64_t mix (uint64_t h, uint64_t x) {
  return (h ^ x) * 1099511628211ull;
}
#define MIX_INIT 14695981039346656037ull

static void print_array (const char *tag, unsigned n, const unsigned *a) {
  uint64_t h = MIX_INIT;
  for (unsigned i = 0; i < n; i++)
    h = mix (h, a[i]);
  printf ("%s n=%u h=%" PRIu64, tag, n, h);
  if (n <= 64)
    for (unsigned i = 0; i < n; i++)
      printf (" %u", a[i]);
  printf ("\n");
}

/*------------------------------------------------------------------------*/

#define NGENS 8

static void generate (unsigned g, unsigned n, unsigned *a) {
  for (unsigned i = 0; i < n; i++) {
    unsigned x;
    switch (g) {
    case 0: x = rnd32 (); break;
    case 1: x = rndn (10); break;
    case 2: x = 42; break;
    case 3: x = 7 * rndn (100000) + 3; break;
    case 4: x = i; break;
    case 5: x = n - i; break;
    case 6: x = i / 3; break;
    default: x = (i < n - i ? i : n - i); break;
    }
    a[i] = x;
  }
}

static const unsigned sizes_fixed[] = {50,  63,  64,  65,   100,  127,
                                       128, 200, 255, 256,  257,  500,
                                       1000, 1999, 2000};

static unsigned nsizes (void) {
  return 41 + sizeof sizes_fixed / sizeof *sizes_fixed + 30;
}

static unsigned size_at (unsigned k) {
  const unsigned nfixed = sizeof sizes_fixed / sizeof *sizes_fixed;
  if (k <= 40)
    return k;
  if (k < 41 + nfixed)
    return sizes_fixed[k - 41];
  return rndn (2001);
}

/*------------------------------------------------------------------------*/
/* SORT */

#define LESS0(A, B) ((A) < (B))
#define LESS1(A, B) ((A) % 7 < (B) % 7)
#define LESS2(A, B) (((A) >> 4) % 5 > ((B) >> 4) % 5)

static void sort_with (kissat *solver, unsigned c, unsigned n,
                       unsigned *a) {
  switch (c) {
  case 0: SORT (unsigned, n, a, LESS0); break;
  case 1: SORT (unsigned, n, a, LESS1); break;
  default: SORT (unsigned, n, a, LESS2); break;
  }
}

typedef struct pair pair;
struct pair {
  unsigned key, id;
};

#define LESS_PAIR(A, B) ((A).key < (B).key)

static void test_sort (kissat *solver) {
  printf ("== sort\n");
  unsigned *a = malloc (2001 * sizeof *a);
  const unsigned ns = nsizes ();
  for (unsigned k = 0; k < ns; k++) {
    const unsigned n = size_at (k);
    for (unsigned g = 0; g < NGENS; g++)
      for (unsigned c = 0; c < 3; c++) {
        generate (g, n, a);
        sort_with (solver, c, n, a);
        char tag[32];
        sprintf (tag, "sort g%u c%u", g, c);
        print_array (tag, n, a);
      }
  }
  printf ("== sort range\n");
  for (unsigned k = 0; k < 300; k++) {
    const unsigned n = rndn (k < 100 ? 60 : 2001);
    const unsigned g = rndn (NGENS);
    const unsigned c = rndn (3);
    generate (g, n, a);
    const unsigned lo = rndn (n + 1);
    const unsigned hi = lo + rndn (n - lo + 1);
    sort_with (solver, c, hi - lo, a + lo);
    char tag[48];
    sprintf (tag, "range g%u c%u lo%u hi%u", g, c, lo, hi);
    print_array (tag, n, a);
  }
  printf ("== sort pairs\n");
  pair *p = malloc (2001 * sizeof *p);
  unsigned *ids = malloc (2001 * sizeof *ids);
  for (unsigned k = 0; k < 200; k++) {
    const unsigned n = rndn (k < 100 ? 70 : 2001);
    const unsigned m = 1 + rndn (20);
    for (unsigned i = 0; i < n; i++)
      p[i].key = rndn (m), p[i].id = i;
    SORT (pair, n, p, LESS_PAIR);
    for (unsigned i = 0; i < n; i++)
      ids[i] = p[i].id;
    print_array ("pairs", n, ids);
  }
  printf ("== insertion sort\n");
  for (unsigned n = 1; n <= 100; n++) {
    const unsigned g = rndn (NGENS);
    generate (g, n, a);
    INSERTION_SORT (unsigned, n, a, LESS1);
    print_array ("insertion", n, a);
  }
  free (ids);
  free (p);
  free (a);
}

/*------------------------------------------------------------------------*/
/* RADIX_SORT */

#define RANK0(A) (A)
#define RANK1(A) ((A) % 7)
#define RANK2(A) ((A) & 0xFF00FF00u)
#define RANK3(A) ((A) >> 8)
#define RANK4(A) (((A) % 3) << 24)
#define RANK5(A) ((void) (A), 0x12345678u)
#define RANK6(A) ((A) & 0xFFFFu)
#define RANK7(A) (((A) >> 16) ^ ((A) & 0xFFu))
#define NRANKS32 8

static void radix32_with (kissat *solver, unsigned r, unsigned n,
                          unsigned *a) {
  switch (r) {
  case 0: RADIX_SORT (unsigned, unsigned, n, a, RANK0); break;
  case 1: RADIX_SORT (unsigned, unsigned, n, a, RANK1); break;
  case 2: RADIX_SORT (unsigned, unsigned, n, a, RANK2); break;
  case 3: RADIX_SORT (unsigned, unsigned, n, a, RANK3); break;
  case 4: RADIX_SORT (unsigned, unsigned, n, a, RANK4); break;
  case 5: RADIX_SORT (unsigned, unsigned, n, a, RANK5); break;
  case 6: RADIX_SORT (unsigned, unsigned, n, a, RANK6); break;
  default: RADIX_SORT (unsigned, unsigned, n, a, RANK7); break;
  }
}

#define K64 0x9E3779B97F4A7C15ull
#define QRANK0(P) ((((uint64_t) (P).key) << 32) | (P).id)
#define QRANK1(P) (((uint64_t) (P).key) * K64)
#define QRANK2(P) (((uint64_t) ((P).key % 5)) << 56)
#define QRANK3(P) ((uint64_t) (P).key)
#define NRANKS64 4

static void radix64_with (kissat *solver, unsigned r, unsigned n, pair *p) {
  switch (r) {
  case 0: RADIX_SORT (pair, uint64_t, n, p, QRANK0); break;
  case 1: RADIX_SORT (pair, uint64_t, n, p, QRANK1); break;
  case 2: RADIX_SORT (pair, uint64_t, n, p, QRANK2); break;
  default: RADIX_SORT (pair, uint64_t, n, p, QRANK3); break;
  }
}

#define URANK64(A) (((uint64_t) (A)) * K64)

static void test_radix (kissat *solver) {
  printf ("== radix32\n");
  unsigned *a = malloc (2001 * sizeof *a);
  const unsigned ns = nsizes ();
  for (unsigned k = 0; k < ns; k++) {
    const unsigned n = size_at (k);
    for (unsigned g = 0; g < NGENS; g++)
      for (unsigned r = 0; r < NRANKS32; r++) {
        generate (g, n, a);
        radix32_with (solver, r, n, a);
        char tag[32];
        sprintf (tag, "radix g%u r%u", g, r);
        print_array (tag, n, a);
      }
  }
  printf ("== radix range\n");
  for (unsigned k = 0; k < 300; k++) {
    const unsigned n = rndn (k < 100 ? 60 : 2001);
    const unsigned g = rndn (NGENS);
    const unsigned r = rndn (NRANKS32);
    generate (g, n, a);
    const unsigned lo = rndn (n + 1);
    const unsigned hi = lo + rndn (n - lo + 1);
    radix32_with (solver, r, hi - lo, a + lo);
    char tag[48];
    sprintf (tag, "rrange g%u r%u lo%u hi%u", g, r, lo, hi);
    print_array (tag, n, a);
  }
  printf ("== radix u64 rank\n");
  for (unsigned k = 0; k < 100; k++) {
    const unsigned n = rndn (k < 50 ? 60 : 2001);
    const unsigned g = rndn (NGENS);
    generate (g, n, a);
    RADIX_SORT (unsigned, uint64_t, n, a, URANK64);
    print_array ("radixu64", n, a);
  }
  printf ("== radix64 pairs\n");
  pair *p = malloc (2001 * sizeof *p);
  unsigned *ids = malloc (2001 * sizeof *ids);
  for (unsigned k = 0; k < 400; k++) {
    const unsigned n = rndn (k < 200 ? 70 : 2001);
    const unsigned m = 1 + rndn (k % 2 ? 20 : 1000000);
    const unsigned r = k % NRANKS64;
    for (unsigned i = 0; i < n; i++)
      p[i].key = rndn (m), p[i].id = rndn (4);
    radix64_with (solver, r, n, p);
    for (unsigned i = 0; i < n; i++)
      ids[i] = p[i].key * 4 + p[i].id;
    char tag[32];
    sprintf (tag, "radix64 r%u", r);
    print_array (tag, n, ids);
  }
  free (ids);
  free (p);
  free (a);
}

/*------------------------------------------------------------------------*/
/* kissat_sort_literals */

static void test_sort_literals (kissat *solver) {
  printf ("== sort literals\n");
  value *values = malloc (2 * 40 * sizeof *values);
  assigned *as = malloc (40 * sizeof *as);
  unsigned vars[40];
  unsigned lits[40];
  solver->values = values;
  solver->assigned = as;
  for (unsigned k = 0; k < 3000; k++) {
    const unsigned V = 2 + rndn (30);
    for (unsigned i = 0; i < V; i++) {
      const unsigned r = rndn (3);
      const value v = (value) r - 1;
      values[2 * i] = v;
      values[2 * i + 1] = -v;
      as[i].level = rndn (10);
      vars[i] = i;
    }
    for (unsigned i = V - 1; i > 0; i--) {
      const unsigned j = rndn (i + 1);
      const unsigned t = vars[i];
      vars[i] = vars[j];
      vars[j] = t;
    }
    const unsigned size = 2 + rndn (V - 1);
    for (unsigned i = 0; i < size; i++)
      lits[i] = 2 * vars[i] + rndn (2);
    kissat_sort_literals (solver, size, lits);
    print_array ("lits", size, lits);
  }
  free (as);
  free (values);
}

/*------------------------------------------------------------------------*/

static double now (void) {
  struct timespec ts;
  clock_gettime (CLOCK_MONOTONIC, &ts);
  return ts.tv_sec + 1e-9 * ts.tv_nsec;
}

static void bench (kissat *solver) {
  const unsigned n = 1000000;
  unsigned *a = malloc (n * sizeof *a);
  for (unsigned i = 0; i < n; i++)
    a[i] = rnd32 ();
  double t = now ();
  SORT (unsigned, n, a, LESS0);
  fprintf (stderr, "C SORT 10^6 unsigned: %.3f s\n", now () - t);
  print_array ("bench sort", n, a);
  for (unsigned i = 0; i < n; i++)
    a[i] = rnd32 ();
  t = now ();
  RADIX_SORT (unsigned, unsigned, n, a, RANK0);
  fprintf (stderr, "C RADIX_SORT 10^6 unsigned: %.3f s\n", now () - t);
  print_array ("bench radix", n, a);
  free (a);
}

int main (int argc, char **argv) {
  kissat s;
  memset (&s, 0, sizeof s);
  INIT_STACK (s.sorter);
  kissat *solver = &s;
  if (argc > 1 && !strcmp (argv[1], "bench")) {
    bench (solver);
    return 0;
  }
  test_sort (solver);
  test_radix (solver);
  test_sort_literals (solver);
  free (s.sorter.begin);
  return 0;
}
