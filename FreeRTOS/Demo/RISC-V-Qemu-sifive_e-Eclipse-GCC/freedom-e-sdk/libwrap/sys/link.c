/* See LICENSE of license details. */

#include <errno.h>
#include "stub.h"
#include "weak_under_alias.h"

int __wrap_link(const char *old_name, const char *new_name)
{
  return _stub(EMLINK);
}
weak_under_alias(link);
