#ifndef _DYNAMIC_VALUE_H_INCLUDED_
#define _DYNAMIC_VALUE_H_INCLUDED_

#include "stdint.h"
#include "libvig/verified/vigor-time.h"

struct DynamicValue {
  uint64_t bucket_size;
  vigor_time_t bucket_time;
};

#endif //_DYNAMIC_VALUE_H_INCLUDED_
