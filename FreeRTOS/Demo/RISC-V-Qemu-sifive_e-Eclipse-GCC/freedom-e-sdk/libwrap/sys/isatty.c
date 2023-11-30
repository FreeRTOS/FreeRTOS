/* See LICENSE of license details. */

#include <unistd.h>
#include "weak_under_alias.h"

int __wrap_isatty(int fd)
{
  if (fd == STDOUT_FILENO || fd == STDERR_FILENO)
    return 1;

  return 0;
}
weak_under_alias(isatty);
