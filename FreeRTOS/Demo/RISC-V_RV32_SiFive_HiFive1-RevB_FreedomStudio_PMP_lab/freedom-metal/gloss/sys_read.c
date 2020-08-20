#include <sys/types.h>
#include <errno.h>

ssize_t
_read(int file, void *ptr, size_t len)
{
  errno = ENOSYS;
  return -1;
}
