/* See LICENSE of license details. */

#include <errno.h>
#include "stub.h"
#include "weak_under_alias.h"

int __wrap_kill(int pid, int sig)
{
  return _stub(EINVAL);
}
weak_under_alias(kill);
