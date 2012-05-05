#include "caml/mlvalues.h"
#include "caml/memory.h"
#include "caml/alloc.h"
#include <stdio.h>

extern value stub1();

value stub2() {
  printf("This is stub2, calling stub1:\n"); fflush(stdout);
  stub1();
  printf("Ok!\n"); fflush(stdout);
  return Val_unit;
}
