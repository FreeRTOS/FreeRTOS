#include <errno.h>
struct utimbuf;

int
_utime(const char *path, const struct utimbuf *times)
{
  errno = ENOSYS;
  return -1;
}
