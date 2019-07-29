#pragma once

#include <klee/klee.h>


#define symbol_bool(name) (klee_int(name) != 0)

#define symbol_make(ptr, size) klee_make_symbolic(ptr, size, #ptr)
