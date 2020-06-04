#include <errno.h>

int
_fork()
{
  errno = ENOSYS;
  return -1;
}
