/* See LICENSE of license details. */

#include <errno.h>
#include "stub.h"

int fork(void)
{
  return _stub(EAGAIN);
}
