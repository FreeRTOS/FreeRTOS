#ifndef __PLATFORM_CONFIG_H_
#define __PLATFORM_CONFIG_H_

#define STDOUT_IS_PS7_UART
#define UART_DEVICE_ID 0
#ifdef __PPC__
#define CACHEABLE_REGION_MASK 0xff000001
#endif

#endif
