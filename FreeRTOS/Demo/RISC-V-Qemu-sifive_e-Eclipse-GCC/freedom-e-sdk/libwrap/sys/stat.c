/* See LICENSE of license details. */

#include <errno.h>
#include <sys/stat.h>
#include "stub.h"
#include "weak_under_alias.h"

int __wrap_stat(const char* file, struct stat* st)
{
  return _stub(EACCES);
}
weak_under_alias(stat);
