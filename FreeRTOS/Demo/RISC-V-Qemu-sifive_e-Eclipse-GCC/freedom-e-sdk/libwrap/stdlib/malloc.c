/* See LICENSE for license details. */

/* These functions are intended for embedded RV32 systems and are
   obviously incorrect in general. */

void* __wrap_malloc(unsigned long sz)
{
  extern void* sbrk(long);
  void* res = sbrk(sz);
  if ((long)res == -1)
    return 0;
  return res;
}

void __wrap_free(void* ptr)
{
}
