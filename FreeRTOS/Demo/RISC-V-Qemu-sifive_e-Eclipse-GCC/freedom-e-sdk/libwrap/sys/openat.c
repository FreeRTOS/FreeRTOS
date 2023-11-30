/* See LICENSE of license details. */

#include <errno.h>
#include "stub.h"
#include "weak_under_alias.h"

int __wrap_openat(int dirfd, const char* name, int flags, int mode)
{
  return _stub(ENOENT);
}
weak_under_alias(openat);
