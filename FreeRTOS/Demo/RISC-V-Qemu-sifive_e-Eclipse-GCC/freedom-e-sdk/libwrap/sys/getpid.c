/* See LICENSE of license details. */
#include "weak_under_alias.h"

int __wrap_getpid(void)
{
  return 1;
}
weak_under_alias(getpid);
