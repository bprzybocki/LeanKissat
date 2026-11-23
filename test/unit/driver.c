/* Differential unit test driver for random.h, smooth.c, averages.c,
   reluctant.c, heap.c/inlineheap.h and queue.c/inlinequeue.h.  Compiled
   together with verbatim copies of the Kissat sources (see run.sh) and the
   stubs in stub/.  Test/Unit.lean performs exactly the same sequence. */

#include "inlineheap.h"
#include "inlinequeue.h"
#include "internal.h"

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/*------------------------------------------------------------------------*/
/* allocation (allocate.h) */

void *kissat_malloc (kissat *s, size_t b) { (void) s; return malloc (b); }
void kissat_free (kissat *s, void *p, size_t b) { (void) s, (void) b; free (p); }
void *kissat_calloc (kissat *s, size_t n, size_t z) { (void) s; return calloc (n, z); }
void *kissat_nalloc (kissat *s, size_t n, size_t z) { (void) s; return malloc (n * z); }
void kissat_dealloc (kissat *s, void *p, size_t n, size_t z) {
  (void) s, (void) n, (void) z;
  free (p);
}
void *kissat_realloc (kissat *s, void *p, size_t o, size_t b) {
  (void) s, (void) o;
  return realloc (p, b);
}
void *kissat_nrealloc (kissat *s, void *p, size_t o, size_t n, size_t z) {
  (void) s, (void) o;
  return realloc (p, n * z);
}

/*------------------------------------------------------------------------*/

static uint64_t bits (double d) {
  uint64_t r;
  memcpy (&r, &d, sizeof r);
  return r;
}

static uint64_t mix (uint64_t h, uint64_t x) {
  return (h ^ x) * 1099511628211ull;
}
#define MIX_INIT 14695981039346656037ull

static generator drv = 12345;
static unsigned rnd (unsigned n) { return kissat_pick_random (&drv, 0, n); }

/*------------------------------------------------------------------------*/

static void test_random (void) {
  printf ("== random\n");
  generator rng = 42;
  for (int i = 0; i < 20; i++)
    printf ("r64 %" PRIu64 "\n", kissat_next_random64 (&rng));
  for (int i = 0; i < 20; i++)
    printf ("r32 %u\n", kissat_next_random32 (&rng));
  for (int i = 0; i < 200; i++) {
    unsigned a = kissat_next_random32 (&rng);
    unsigned b = kissat_next_random32 (&rng);
    if (i % 3 == 0)
      b = a + (b & 255);
    if (b < a) {
      unsigned t = a;
      a = b, b = t;
    }
    if (i % 10 == 0)
      b = a;
    printf ("pick %u %u %u\n", a, b, kissat_pick_random (&rng, a, b));
  }
  printf ("pickfull %u\n", kissat_pick_random (&rng, 0, UINT_MAX));
  for (int i = 0; i < 40; i++)
    printf ("bool %d\n", (int) kissat_pick_bool (&rng));
  for (int i = 0; i < 40; i++)
    printf ("double %016" PRIx64 "\n", bits (kissat_pick_double (&rng)));
}

/*------------------------------------------------------------------------*/

static void print_smooth (const char *n, smooth *s) {
  printf ("%s %016" PRIx64 " %016" PRIx64 " %016" PRIx64 " %016" PRIx64
          " %016" PRIx64 "\n",
          n, bits (s->value), bits (s->biased), bits (s->alpha),
          bits (s->beta), bits (s->exp));
}

static void test_smooth (kissat *solver) {
  printf ("== smooth\n");
  const int windows[] = {2, 3, 10, 33, 100000};
  const int rounds[] = {10, 2000, 300, 300, 300};
  generator rng = 7;
  for (int w = 0; w < 5; w++) {
    smooth s;
    kissat_init_smooth (solver, &s, windows[w], "s");
    print_smooth ("init", &s);
    for (int i = 0; i < rounds[w]; i++) {
      double y;
      switch (i % 3) {
      case 0:
        y = kissat_pick_random (&rng, 0, 100);
        break;
      case 1:
        y = kissat_pick_double (&rng) * 1e6;
        break;
      default:
        y = -kissat_pick_double (&rng);
        break;
      }
      kissat_update_smooth (solver, &s, y);
      if (w != 1 || i % 50 == 0 || i > 1800)
        print_smooth ("upd", &s);
    }
    print_smooth ("final", &s);
  }
  averages a;
  memset (&a, 0, sizeof a);
  solver->options.emafast = 33;
  solver->options.emaslow = 100000;
  kissat_init_averages (solver, &a);
  kissat_update_smooth (solver, &a.fast_glue, 3.0);
  solver->options.emafast = 7;
  kissat_init_averages (solver, &a); /* no-op */
  printf ("avg %d %" PRIu64 "\n", (int) a.initialized, a.saved_decisions);
  print_smooth ("fast_glue", &a.fast_glue);
  print_smooth ("slow_glue", &a.slow_glue);
  print_smooth ("level", &a.level);
  print_smooth ("size", &a.size);
  print_smooth ("trail", &a.trail);
  print_smooth ("decision_rate", &a.decision_rate);
}

/*------------------------------------------------------------------------*/

static void print_reluctant (reluctant *r) {
  printf ("rel %d %d %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64
          "\n",
          (int) r->limited, (int) r->trigger, r->period, r->wait, r->u, r->v,
          r->limit);
}

static void test_reluctant (kissat *solver) {
  printf ("== reluctant\n");
  const uint64_t periods[] = {1024, 3, 2, 5, 1};
  const uint64_t limits[] = {1 << 20, 100, 0, 3, 0};
  const unsigned ticks[] = {3000000, 10000, 20000, 1000, 5000};
  for (int c = 0; c < 5; c++) {
    reluctant r;
    memset (&r, 0, sizeof r);
    kissat_enable_reluctant (&r, periods[c], limits[c]);
    print_reluctant (&r);
    for (unsigned t = 1; t <= ticks[c]; t++) {
      kissat_tick_reluctant (&r);
      if (t % 7 == 3)
        continue; /* leave trigger pending sometimes */
      if (kissat_reluctant_triggered (&r)) {
        printf ("trig %u ", t);
        print_reluctant (&r);
      }
    }
    kissat_disable_reluctant (&r);
    kissat_tick_reluctant (&r);
    print_reluctant (&r);
  }
  solver->options.reluctant = 1;
  solver->options.reluctantint = 1 << 10;
  solver->options.reluctantlim = 1 << 20;
  kissat_init_reluctant (solver);
  print_reluctant (&solver->reluctant);
  solver->options.reluctant = 0;
  kissat_init_reluctant (solver);
  print_reluctant (&solver->reluctant);
}

/*------------------------------------------------------------------------*/

static uint64_t heap_hash (heap *h) {
  uint64_t r = MIX_INIT;
  r = mix (r, h->tainted);
  r = mix (r, h->vars);
  r = mix (r, h->size);
  r = mix (r, SIZE_STACK (h->stack));
  for (unsigned i = 0; i < SIZE_STACK (h->stack); i++)
    r = mix (r, PEEK_STACK (h->stack, i));
  for (unsigned i = 0; i < h->vars; i++)
    r = mix (r, h->pos[i]);
  for (unsigned i = 0; i < h->vars; i++)
    r = mix (r, bits (h->score[i]));
  return r;
}

static void heap_dump (heap *h) {
  printf ("stack");
  for (unsigned i = 0; i < SIZE_STACK (h->stack); i++)
    printf (" %u", PEEK_STACK (h->stack, i));
  printf ("\npos");
  for (unsigned i = 0; i < h->vars; i++)
    printf (" %u", h->pos[i]);
  printf ("\nscore");
  for (unsigned i = 0; i < h->vars; i++)
    printf (" %016" PRIx64, bits (h->score[i]));
  printf ("\n");
}

static void test_heap (kissat *solver) {
  printf ("== heap\n");
  heap H;
  memset (&H, 0, sizeof H);
  kissat_resize_heap (solver, &H, 8);
  for (unsigned i = 0; i < 4; i++)
    kissat_push_heap (solver, &H, 2 * i);
  printf ("init %016" PRIx64 "\n", heap_hash (&H));
  for (unsigned op = 0; op < 5000; op++) {
    unsigned o = rnd (100);
    if (o < 3) {
      if (H.size < 512) {
        kissat_resize_heap (solver, &H, 2 * H.size);
        printf ("resize %u\n", H.size);
      } else
        printf ("noresize\n");
    } else if (o < 30) {
      unsigned idx = rnd (H.size);
      if (!kissat_heap_contains (&H, idx)) {
        kissat_push_heap (solver, &H, idx);
        printf ("push %u\n", idx);
      } else
        printf ("nopush %u\n", idx);
    } else if (o < 42) {
      unsigned idx = rnd (H.size);
      if (kissat_heap_contains (&H, idx)) {
        kissat_pop_heap (solver, &H, idx);
        printf ("pop %u\n", idx);
      } else
        printf ("nopop %u\n", idx);
    } else if (o < 55) {
      if (!kissat_empty_heap (&H)) {
        unsigned m = kissat_max_heap (&H);
        unsigned idx = kissat_pop_max_heap (solver, &H);
        printf ("popmax %u %u\n", m, idx);
      } else
        printf ("empty\n");
    } else if (o < 93) {
      unsigned idx = rnd (H.size);
      unsigned kind = rnd (5);
      double s;
      double old = kissat_get_heap_score (&H, idx);
      switch (kind) {
      case 0:
        s = rnd (10);
        break;
      case 1:
        s = kissat_pick_double (&drv);
        break;
      case 2:
        s = old + kissat_pick_double (&drv) * 1e3;
        break;
      case 3:
        s = -kissat_pick_double (&drv);
        break;
      default:
        s = old;
        break;
      }
      kissat_update_heap (solver, &H, idx, s);
      printf ("update %u %u %016" PRIx64 " pos %u\n", idx, kind, bits (s),
              kissat_get_heap_pos (&H, idx));
    } else if (o < 96) {
      double f = (rnd (2) ? 1e-150 : 0.5);
      kissat_rescale_heap (solver, &H, f);
      printf ("rescale %016" PRIx64 "\n", bits (f));
    } else {
      printf ("maxscore %016" PRIx64 "\n",
              bits (kissat_max_score_on_heap (&H)));
    }
    printf ("h %u %016" PRIx64 " %zu\n", op, heap_hash (&H),
            kissat_size_heap (&H));
    if (op % 500 == 499)
      heap_dump (&H);
  }
  heap_dump (&H);
  kissat_release_heap (solver, &H);
  printf ("released %u %u %d\n", H.vars, H.size, (int) H.tainted);

  heap A;
  memset (&A, 0, sizeof A);
  for (unsigned i = 0; i < 200; i++) {
    unsigned idx = rnd (i < 100 ? 50 : 3000);
    kissat_adjust_heap (solver, &A, idx);
    if (i == 60 || i == 150)
      kissat_update_heap (solver, &A, idx, 1.5 + i);
    if (i % 3 == 0 && idx < A.vars && !kissat_heap_contains (&A, idx))
      kissat_push_heap (solver, &A, idx);
    printf ("adjust %u %u %u %u %016" PRIx64 "\n", idx, A.vars, A.size,
            (unsigned) kissat_size_heap (&A), heap_hash (&A));
  }
  printf ("amax %016" PRIx64 "\n", bits (kissat_max_score_on_heap (&A)));
  while (!kissat_empty_heap (&A))
    printf ("apop %u\n", kissat_pop_max_heap (solver, &A));
  kissat_release_heap (solver, &A);
}

/*------------------------------------------------------------------------*/
/* copies of the static helpers of decide.c and backtrack.c */

static unsigned last_enqueued_unassigned_variable (kissat *solver) {
  assert (solver->unassigned);
  const links *const links = solver->links;
  const value *const values = solver->values;
  unsigned res = solver->queue.search.idx;
  if (values[LIT (res)]) {
    do {
      res = links[res].prev;
      assert (!DISCONNECTED (res));
    } while (values[LIT (res)]);
    kissat_update_queue (solver, links, res);
  }
  return res;
}

static inline void add_unassigned_variable_back_to_queue (kissat *solver,
                                                          links *links,
                                                          unsigned lit) {
  const unsigned idx = IDX (lit);
  if (links[idx].stamp > solver->queue.search.stamp)
    kissat_update_queue (solver, links, idx);
}

#define NQ 64

static uint64_t queue_hash (kissat *solver) {
  uint64_t r = MIX_INIT;
  queue *q = &solver->queue;
  r = mix (r, q->first);
  r = mix (r, q->last);
  r = mix (r, q->stamp);
  r = mix (r, q->search.idx);
  r = mix (r, q->search.stamp);
  for (unsigned i = 0; i < NQ; i++) {
    r = mix (r, solver->links[i].prev);
    r = mix (r, solver->links[i].next);
    r = mix (r, solver->links[i].stamp);
  }
  return r;
}

static void queue_dump (kissat *solver) {
  printf ("queue");
  for (unsigned idx = solver->queue.first; !DISCONNECTED (idx);
       idx = solver->links[idx].next)
    printf (" %u:%u", idx, solver->links[idx].stamp);
  printf ("\n");
}

static void test_queue (kissat *solver) {
  printf ("== queue\n");
  solver->vars = NQ;
  solver->unassigned = NQ;
  solver->values = calloc (2 * NQ, 1);
  solver->links = calloc (NQ, sizeof (links));
  memset (&solver->queue, 0, sizeof solver->queue);
  kissat_init_queue (solver);
  solver->queue.stamp = UINT_MAX - 300;
  bool inq[NQ];
  unsigned inqueue = 0;
  for (unsigned i = 0; i < NQ; i++)
    inq[i] = false;
  for (unsigned i = 0; i < NQ; i++) {
    unsigned idx = rnd (NQ);
    while (inq[idx])
      idx = (idx + 1) % NQ;
    kissat_enqueue (solver, idx);
    inq[idx] = true, inqueue++;
  }
  printf ("init %016" PRIx64 "\n", queue_hash (solver));
  queue_dump (solver);
  for (unsigned op = 0; op < 6000; op++) {
    if (op == 3000)
      solver->queue.stamp = UINT_MAX - 5;
    unsigned o = rnd (100);
    unsigned idx = rnd (NQ);
    const unsigned lit = LIT (idx);
    if (o < 25) {
      if (!solver->values[lit]) {
        value v = rnd (2) ? 1 : -1;
        solver->values[lit] = v;
        solver->values[lit + 1] = -v;
        solver->unassigned--;
        printf ("assign %u %d\n", idx, (int) v);
      } else
        printf ("noassign %u\n", idx);
    } else if (o < 45) {
      if (solver->values[lit]) {
        solver->values[lit] = solver->values[lit + 1] = 0;
        solver->unassigned++;
        if (inq[idx])
          add_unassigned_variable_back_to_queue (solver, solver->links, lit);
        printf ("unassign %u\n", idx);
      } else
        printf ("nounassign %u\n", idx);
    } else if (o < 70) {
      if (inq[idx]) {
        kissat_move_to_front (solver, idx);
        printf ("mtf %u\n", idx);
      } else
        printf ("nomtf %u\n", idx);
    } else if (o < 78) {
      if (inq[idx] && inqueue > 8) {
        kissat_dequeue (solver, idx);
        inq[idx] = false, inqueue--;
        printf ("dequeue %u\n", idx);
      } else
        printf ("nodequeue %u\n", idx);
    } else if (o < 86) {
      if (!inq[idx]) {
        kissat_enqueue (solver, idx);
        inq[idx] = true, inqueue++;
        printf ("enqueue %u\n", idx);
      } else
        printf ("noenqueue %u\n", idx);
    } else if (o < 97) {
      bool some = false;
      for (unsigned i = 0; i < NQ; i++)
        if (inq[i] && !solver->values[LIT (i)])
          some = true;
      if (some)
        printf ("decide %u\n", last_enqueued_unassigned_variable (solver));
      else
        printf ("nodecide\n");
    } else {
      kissat_reset_search_of_queue (solver);
      printf ("reset\n");
    }
    printf ("q %u %016" PRIx64 "\n", op, queue_hash (solver));
    if (op % 500 == 499)
      queue_dump (solver);
  }
  queue_dump (solver);
  free (solver->values);
  free (solver->links);
}

int main (void) {
  kissat S;
  memset (&S, 0, sizeof S);
  test_random ();
  test_smooth (&S);
  test_reluctant (&S);
  test_heap (&S);
  test_queue (&S);
  return 0;
}
