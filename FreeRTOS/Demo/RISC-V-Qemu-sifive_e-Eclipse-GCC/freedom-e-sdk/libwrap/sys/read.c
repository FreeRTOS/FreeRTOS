/* See LICENSE of license details. */

#include <stdint.h>
#include <errno.h>
#include <unistd.h>
#include <sys/types.h>

#include "platform.h"
#include "stub.h"
#include "weak_under_alias.h"

ssize_t __wrap_read(int fd, void* ptr, size_t len)
{
  uint8_t * current = (uint8_t *)ptr;
  volatile uint32_t * uart_rx = (uint32_t *)(UART0_CTRL_ADDR + UART_REG_RXFIFO);
  volatile uint8_t * uart_rx_cnt = (uint8_t *)(UART0_CTRL_ADDR + UART_REG_RXCTRL + 2);

  ssize_t result = 0;

  if (isatty(fd)) {
    for (current = (uint8_t *)ptr;
        (current < ((uint8_t *)ptr) + len) && (*uart_rx_cnt > 0);
        current ++) {
      *current = *uart_rx;
      result++;
    }
    return result;
  }

  return _stub(EBADF);
}
weak_under_alias(read);
