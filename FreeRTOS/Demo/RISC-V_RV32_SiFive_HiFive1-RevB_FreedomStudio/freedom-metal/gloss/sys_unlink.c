#include <errno.h>

int
_unlink(const char *name)
{
  errno = ENOSYS;
  return -1;
}
