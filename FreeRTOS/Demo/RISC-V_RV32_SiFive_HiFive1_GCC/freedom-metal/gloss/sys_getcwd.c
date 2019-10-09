#include <errno.h>

char *
_getcwd(char *buf, size_t size)
{
  errno = -ENOSYS;
  return NULL;
}
