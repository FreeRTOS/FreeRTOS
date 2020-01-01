#include <sys/types.h>
#include <errno.h>

off_t
_lseek(int file, off_t ptr, int dir)
{
  errno = ENOSYS;
  return -1;
}
