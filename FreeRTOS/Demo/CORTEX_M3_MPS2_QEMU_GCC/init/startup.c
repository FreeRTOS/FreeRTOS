#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

//#include "uart.h"

extern uint32_t _estack, _sidata, _sdata, _edata, _sbss, _ebss;

/*
static void serial_init(void) {
  struct usart_config usart_conf;

  usart_get_config_defaults(&usart_conf);
  usart_conf.mux_setting = USART_RX_3_TX_2_XCK_3;
  usart_conf.pinmux_pad0 = PINMUX_UNUSED;
  usart_conf.pinmux_pad1 = PINMUX_UNUSED;
  usart_conf.pinmux_pad2 = PINMUX_PB22D_SERCOM5_PAD2;
  usart_conf.pinmux_pad3 = PINMUX_PB23D_SERCOM5_PAD3;

  usart_serial_init(&stdio_uart_module, SERCOM5, &usart_conf);
  usart_enable(&stdio_uart_module);
}
*/

void* memset(uint32_t *dst, int num, size_t len)
{
    while ( len > 0 )
    {
        * (dst + (--len)) = num;
    }
    return dst;
}
void memcpy(void *dest, void *src, size_t n)
{
   // Typecast src and dest addresses to (char *)
   char *csrc = (char *)src;
   char *cdest = (char *)dest;

   // Copy contents of src[] to dest[]
   for (int i=0; i<n; i++)
       cdest[i] = csrc[i];
}
__attribute__((naked)) void Reset_Handler(void) {
    // set stack pointer
    __asm volatile ("ldr r0, =_estack");
    __asm volatile ("mov sp, r0");
    // copy .data section from flash to RAM
    for (uint32_t *src = &_sidata, *dest = &_sdata; dest < &_edata;) {
        *dest++ = *src++;
    }
    // zero out .bss section
    for (uint32_t *dest = &_sbss; dest < &_ebss;) {
        *dest++ = 0;
    }
    // jump to board initialisation
    void _start(void);
    _start();
}

void Default_Handler(void) {
    for (;;) {
    }
}
void Default_Handler1(void) {
    for (;;) {
    }
}
void Default_Handler2(void) {
    for (;;) {
    }
}
void Default_Handler3(void) {
    for (;;) {
    }
}
void Default_Handler4(void) {
    for (;;) {
    }
}

void Default_Handler5(void) {
}

void Default_Handler6(void) {
    for (;;) {
    }
}
void Default_Handler7(void) {
    for (;;) {
    }
}
void Default_Handler8(void) {
    for (;;) {
    }
}
extern void vPortSVCHandler( void );
extern void xPortPendSVHandler( void );
extern void xPortSysTickHandler( void );

const uint32_t isr_vector[] __attribute__((section(".isr_vector"))) = {
    (uint32_t)&_estack,
    (uint32_t)&Reset_Handler,
    (uint32_t)&Default_Handler, // NMI_Handler
    (uint32_t)&Default_Handler1, // HardFault_Handler
    (uint32_t)&Default_Handler2, // MemManage_Handler
    (uint32_t)&Default_Handler3, // BusFault_Handler
    (uint32_t)&Default_Handler4, // UsageFault_Handler
    0,
    0,
    0,
    0,
    (uint32_t)&vPortSVCHandler, // SVC_Handler
    (uint32_t)&Default_Handler6, // DebugMon_Handler
    0,
    (uint32_t)&xPortPendSVHandler, // PendSV handler
    (uint32_t)&xPortSysTickHandler, // SysTick_Handler
};
extern int Main();
int main()
{
	Main();
	return 0;
}

void _start2(void) {
    // Enable the UART
    //uart_init();

    //__libc_init_array();
    // Now that we have a basic system up and running we can call main
    extern int Main();
    Main(0, 0);

    // Finished
    exit(0);
}

__attribute__((naked)) void exit(int status) {
    // Force qemu to exit using ARM Semihosting
    __asm volatile (
        "mov r1, r0\n"
        "cmp r1, #0\n"
        "bne .notclean\n"
        "ldr r1, =0x20026\n" // ADP_Stopped_ApplicationExit, a clean exit
        ".notclean:\n"
        "movs r0, #0x18\n" // SYS_EXIT
        "bkpt 0xab\n"
        );
    for (;;) {
    }
}
#ifndef NDEBUG
void __assert_func(const char *file, int line, const char *func, const char *expr) {
    (void)func;
    //printf("Assertion '%s' failed, at file %s:%d\n", expr, file, line);
    exit(1);
}
#endif

// The following are needed for tinytest
int setvbuf(FILE *stream, char *buf, int mode, size_t size) {
    return 0;
}

struct _reent *_impure_ptr;

