/* Minimal stub of Kissat's internal.h for the unit differential test. */
#ifndef _internal_h_INCLUDED
#define _internal_h_INCLUDED
#include <assert.h>
#include <limits.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include "allocate.h"
#include "averages.h"
#include "heap.h"
#include "queue.h"
#include "random.h"
#include "reluctant.h"
#include "smooth.h"
#include "stack.h"
typedef signed char value;
#define LIT(IDX) (assert ((IDX) < (1u << 31)), ((IDX) << 1))
#define IDX(L) ((L) >> 1)
#define VARS (solver->vars)
#define VALUE(L) (solver->values[L])
struct options_stub {
  int emafast, emaslow, reluctant, reluctantint, reluctantlim;
};
#define GET_OPTION(N) (solver->options.N)
typedef struct kissat kissat;
struct kissat {
  unsigned vars;
  unsigned unassigned;
  value *values;
  links *links;
  queue queue;
  reluctant reluctant;
  struct options_stub options;
};
#endif
