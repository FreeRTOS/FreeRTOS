#include <errno.h>
#include <sys/timeb.h>

int
_ftime(struct timeb *tp)
{
  errno = ENOSYS;
  return -1;
}
