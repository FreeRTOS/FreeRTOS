#include <metal/tty.h>
#include <sys/types.h>
#include <errno.h>
#include <unistd.h>

/* Write to a file.  */
ssize_t
_write(int file, const void *ptr, size_t len)
{
  if (file != STDOUT_FILENO) {
    errno = ENOSYS;
    return -1;
  }

  const char *bptr = ptr;
  for (size_t i = 0; i < len; ++i)
    metal_tty_putc(bptr[i]);
  return 0;
}
