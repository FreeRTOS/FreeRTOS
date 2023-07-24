
#ifndef HW_PLATFORM_H
#define HW_PLATFORM_H

#define SYS_CLK_FREQ            50000000UL  // 50MHz

#define DEFAULT_RSTVEC          0x00001000
#define EXT_IO_BASE             0x40000000
#define DRAM_BASE               0x80000000

#define CLINT_BASE              0x02000000
#define CLINT_SIZE              0x000c0000
#define MTIMECMP_BASE_ADDRESS   0x4000UL
#define MTIME_BASE_ADDRESS      0xBFF8UL

/***************************************************************************/
#define FPGA_UART_0_FREQUENCY 50000000
#define FPGA_UART_0_BASE 0x10000000
#define STDIO_BAUD_RATE  UART_115200_BAUD

#endif // HW_PLATFORM_H
