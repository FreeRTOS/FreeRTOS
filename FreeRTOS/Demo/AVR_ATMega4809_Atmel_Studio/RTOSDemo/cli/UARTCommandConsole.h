#ifndef UART_COMMAND_CONSOLE_H
#define UART_COMMAND_CONSOLE_H

/*
 * Create the task that implements a command console using the USB virtual com
 * port driver for intput and output.
 */
void vUARTCommandConsoleStart( uint16_t usStackSize, unsigned portBASE_TYPE uxPriority );

#endif /* UART_COMMAND_CONSOLE_H */
