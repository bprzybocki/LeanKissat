/* Minimal stub of Kissat's internal.h for the sorting differential test
   (sort.h, rank.h, sort.c). */
#ifndef _internal_h_INCLUDED
#define _internal_h_INCLUDED
#include <assert.h>
#include <limits.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include "allocate.h"
#include "stack.h"
#include "utilities.h"
typedef signed char value;
typedef struct assigned assigned;
struct assigned {
  unsigned level;
};
#define IDX(L) ((L) >> 1)
#define START(...) do { } while (0)
#define STOP(...) do { } while (0)
typedef struct kissat kissat;
struct kissat {
  value *values;
  assigned *assigned;
  sizes sorter;
};
void kissat_sort_literals (kissat *, unsigned size, unsigned *lits);
#endif
