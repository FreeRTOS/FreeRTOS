/* See LICENSE of license details. */

#include <errno.h>
#include "stub.h"

int wait(int* status)
{
  return _stub(ECHILD);
}
