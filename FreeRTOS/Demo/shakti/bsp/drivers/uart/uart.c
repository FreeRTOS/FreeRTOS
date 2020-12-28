/****************************************************************************
 * Project                               : shakti devt board
 * Name of the file                      : uart.c
 * Brief Description of file             : src  file for uart
 * Name of Author                        : Kotteeswaran and Niketan Shahapur
 * Email ID                              : <kottee.1@gmail.com>  <niketanshahpur@gmail.com> 

 Copyright (C) 2019 IIT Madras. All rights reserved.

 This program is free software: you can redistribute it and/or modify
 it under the terms of the GNU General Public License as published by
 the Free Software Foundation, either version 3 of the License, or
 (at your option) any later version.

 This program is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with this program.  If not, see <https://www.gnu.org/licenses/>.
 *****************************************************************************/
/**
  @file uart.c
  @brief Contains the driver routines for UART interface.
  @detail The UART driver .has software functions to configure, transmit 
  and receive over UART interface.
 */

#include "uart.h"
#include "gpio.h"
#include "utils.h"

uart_struct *uart_instance[MAX_UART_COUNT];

#define RTS GPIO4
//#define USE_INTERRUPT 

unsigned char uart0_complete = 0;
unsigned char uart1_complete = 0;
unsigned char uart2_complete = 0;
unsigned int uart0_tx_isr_count = 0;
unsigned int uart0_rcv_isr_count = 0;
unsigned int uart1_tx_isr_count = 0;
unsigned int uart1_rcv_isr_count = 0;
unsigned int uart2_tx_isr_count = 0;
unsigned int uart2_rcv_isr_count = 0;

#ifdef USE_INTERRUPT
unsigned char u0_rcv_char[UARTX_BUFFER_SIZE] = {'\0'};
unsigned char u1_rcv_char[UARTX_BUFFER_SIZE] = {'\0'};
unsigned char u2_rcv_char[UARTX_BUFFER_SIZE] = {'\0'};
#endif

/**
 * @fn void uart_init()
 * @brief Initialise UART Array 
 * @details Initialises given number of UART Arrays which has 
 *          complete set of UART registers.
 */
void uart_init()
{
	for(int i=0; i< MAX_UART_COUNT; i++)
	{
		uart_instance[i] = (uart_struct*) (UART0_START+i*UART_OFFSET);
	}
}

/**
 * @fn int getchar()
 * @brief Function to read a single character from the standard input device.
 * @details This function will be called to write a single character from the stdin.
 * @return integer equivalent of the received character.
 */
#undef getchar
int getchar()
{
	while((uart_instance[0]->status & STS_RX_NOT_EMPTY) == 0); 
	return (uart_instance[0]->rcv_reg);
}

/**
 * @fn int putchar(int ch)
 * @brief Function to write a single character to the standard output device.
 * @details This function will be called to print a single character to the stdout by passing 
 * character as an integer.
 * @param character as int.
 * @return Zero
 */
#undef putchar
int putchar(int ch)
{
	while(uart_instance[0]->status & STS_TX_FULL);

	uart_instance[0]->tx_reg = ch;

	return 0;
}

/**
 * @fn void set_baud_rate(uart_struct * UART, unsigned int baudrate)
 * @brief Function to initialize a specific UART with the baudrate.
 * @details This function will be called to initialize a specific UART by passing baudrate value
 * which in turn used to calculate the baud_count to set the baudrate.
 * @param UART instance
 * @param unsigned int baudrate
 */
void set_baud_rate(uart_struct *instance, unsigned int baudrate)
{
	unsigned int baud_count = 0;
	baud_count = CLOCK_FREQUENCY / (16 * baudrate);
	instance->baud = baud_count;
}

/**
 * @fn void enable_uart_interrupts(uart_struct * instance, unsigned char interrupt) 
 * @brief Function to enable the interrupts of a perticular uart instance.
 * @details This function will be called to enable the interrupts of a specific uart instance by passing
 * the interrupt's values.
 * @param uart instance 
 * @param unsigned char interrupt
 */
void enable_uart_interrupts(uart_struct * instance, unsigned char interrupt)
{
	instance->ien = interrupt; 
}

#ifdef USE_RX_THRESHOLD
/**
 * @fn void set_uart_rx_threshold(uart_struct * instance, unsigned char rxthreshold)
 * @brief Funtion to set the threshold value of the Rx FIFO.
 * @details This function will be called to set the threshold value of the Rx FIFO of a specific uart instance
 * by passing the threshold value.
 * @param uart instance 
 * @param unsigned char rxthreshold
 */
void set_uart_rx_threshold(uart_struct * instance, unsigned char rxthreshold)
{
	instance->rx_threshold = rxthreshold;
}
#endif

/**
 * @fn uint32_t write_uart_character(uart_struct * instance, uint8_t prn_character)
 * @brief Function to write a single character to a specific uart instance. 
 * @details This function will be called to write a character to a specific uart instance by passing the
 * character.
 * @param uart instance
 * @param character.
 */
uint32_t write_uart_character(uart_struct * instance, uint8_t prn_character)
{
	while(instance->status & STS_TX_FULL);

	instance->tx_reg = prn_character;

	return 0;
}

/**
 * @fn uint32_t write_uart_string(uart_struct * instance, uint8_t * ptr_string)
 * @brief Function to write a string to a specific uart instance.
 * @details This function will be called to write a string to a specific uart instance by passing the
 * string.
 * @param uart instance 
 * @param string.
 * @return Zero
 */
uint32_t write_uart_string(uart_struct * instance, uint8_t * ptr_string)
{
	uint32_t i = 0;
	uint8_t temp;

	do
	{
		temp = ptr_string[i++];
		write_uart_character(instance, temp);
	} while(temp != 0);

	return 0;
}

/**
 * @fn uint8_t read_uart_character(instance_TypeDef * instance, char * prn_character)
 * @brief Function to read a character from a specific instance.
 * @details This function will be called to read a character from a specific uart instance by passing the
 * character pointer to store the character.
 * @param uart instance 
 * @param pointer to a character.
 * @return number of characters read
 */
uint8_t read_uart_character(uart_struct * instance, char * prn_character)
{
	uint8_t temp = 0;

	while ((instance->status & STS_RX_NOT_EMPTY) == 0);

	temp = instance->rcv_reg;
	*prn_character = temp;

	return 1;
}

/**
 * @fn uint8_t read_uart_string(uart_struct * instance, char * ptr_string)
 * @brief Function to read a string from a specific uart instance.
 * @details This function will be called to read a string, one character at a time from a 
 * specific uart instance by passing the array in which to store the string by reference using pointers.
 * @param UART instance
 * @param pointer to an array of character.
 * @return length of the received string
 */
uint8_t read_uart_string(uart_struct * instance, char * ptr_string)
{
	uint32_t i = 0;
	uint8_t temp = 0;

	while(1)
	{
		while ((instance->status & STS_RX_NOT_EMPTY) == 0);

		temp = instance->rcv_reg;
		ptr_string[i++] = temp;
		putchar(temp);

		if (temp == 0x0D)
		{
			ptr_string[i++] = 0x0A;
			ptr_string[i++] = 0x00;
			return(i);
		}
	}
}

/**
 * @fn void flush_uart((uart_struct * instance)
 * @brief Function to flush the UART fifo queue.
 * @details This function will be called to flush the previous values stored in the UART fifo queue by
 * passing UART number for different offset addresses.
 * @param UART instance.
 */
void flush_uart(uart_struct * instance)
{
	__attribute__((unused)) char temp;

	while ((instance->status & STS_RX_NOT_EMPTY) != 0)
	{
		temp = instance->rcv_reg ;
	}
}

/*Enable USE_INTERRUPT in command line*/

#ifdef USE_INTERRUPT
/**
 * @fn unsigned char uart0_isr()
 * @brief Function to offer interrupt service routine for uart_instance[0].
 * @details This function will be called to offer interrupt service routine for UART0 to read the
 * array of characters by handling interrupts such as RX_threshold, Rx_full, and RX_not_empty
 * based on the Rx fifo status and handles accordingly.
 * @return Currently not returning any value
 */
unsigned char uart0_isr()
{
	uint32_t read_value = '\0';

	if(uart_instance[0]->status & STS_RX_THRESHOLD)
	{
		while(uart_instance[0]->status & STS_RX_NOT_EMPTY)
		{
			read_value = uart_instance[0]->rcv_reg;
			u0_rcv_char[uart0_rcv_isr_count++] = read_value;
			write_uart_character(uart_instance[0], read_value);
		}
	}
	else if(uart_instance[0]->status & STS_RX_FULL)
	{
		write_word(GPIO_DIRECTION_CNTRL_REG, RTS);
		write_word(GPIO_DATA_REG, read_word(GPIO_DATA_REG) | RTS);

		while(uart_instance[0]->status & STS_RX_NOT_EMPTY)
		{
			read_value = uart_instance[0]->rcv_reg;
			u0_rcv_char[uart0_rcv_isr_count++] = read_value;
			write_uart_character(uart_instance[0], read_value);
		}
		write_word(GPIO_DATA_REG, read_word(GPIO_DATA_REG) & ~(RTS));
	}
	else if(uart_instance[0]->status & STS_RX_NOT_EMPTY)
	{
		read_value = uart_instance[0]->rcv_reg;
		u0_rcv_char[uart0_rcv_isr_count++] = read_value;
		write_uart_character(uart_instance[0], read_value);
	}
	return 0;
}

/**
 * @fn unsigned char uart1_isr()
 * @brief Function to offer interrupt service routine for uart_instance[1].
 * @details This function will be called to offer interrupt service routine for uart_instance[1] to read the
 * array of characters by handling interrupts such as RX_threshold, Rx_full, and RX_not_empty
 * based on the Rx fifo status and handles accordingly.
 * @return Currently not returning any value
 */
unsigned char uart1_isr()
{
	uint32_t read_value = '\0';

	if(uart_instance[1]->status & STS_RX_THRESHOLD)
	{
		while(uart_instance[1]->status & STS_RX_NOT_EMPTY)
		{
			read_value = uart_instance[1]->rcv_reg;
			u1_rcv_char[uart1_rcv_isr_count++] = read_value;
			write_uart_character(uart_instance[1], read_value);
		}
	}
	else if(uart_instance[1]->status & STS_RX_FULL)
	{
		write_word(GPIO_DIRECTION_CNTRL_REG, RTS);
		write_word(GPIO_DATA_REG, read_word(GPIO_DATA_REG) | RTS);

		while(uart_instance[1]->status & STS_RX_NOT_EMPTY)
		{
			read_value = uart_instance[1]->rcv_reg;
			u1_rcv_char[uart1_rcv_isr_count++] = read_value;
			write_uart_character(uart_instance[1], read_value);
		}
		write_word(GPIO_DATA_REG, read_word(GPIO_DATA_REG) & ~(RTS));
	}
	else if(uart_instance[1]->status & STS_RX_NOT_EMPTY)
	{
		read_value = uart_instance[1]->rcv_reg;
		u1_rcv_char[uart1_rcv_isr_count++] = read_value;
		write_uart_character(uart_instance[1], read_value);
	}
	return 0;
}

/**
 * @fn unsigned char uart2_isr()
 * @brief Function to offer interrupt service routine for UART2.
 * @details This function will be called to offer interrupt service routine for UART2 to read the
 * array of characters by handling interrupts such as RX_threshold, Rx_full, and RX_not_empty
 * based on the Rx fifo status and handles accordingly.
 * @return Currently not returning any value
 */
unsigned char uart2_isr()
{
	uint32_t read_value = '\0';

	if(uart_instance[2]->status & STS_RX_THRESHOLD)
	{
		while(uart_instance[2]->status & STS_RX_NOT_EMPTY)
		{
			read_value = uart_instance[2]->rcv_reg;
			u2_rcv_char[uart2_rcv_isr_count++] = read_value;
			write_uart_character(uart_instance[2], read_value);
		}
	}
	else if(uart_instance[2]->status & STS_RX_FULL)
	{
		write_word(GPIO_DIRECTION_CNTRL_REG, RTS);
		write_word(GPIO_DATA_REG, read_word(GPIO_DATA_REG) | RTS);

		while(uart_instance[2]->status & STS_RX_NOT_EMPTY)
		{
			read_value = uart_instance[2]->rcv_reg;
			u2_rcv_char[uart2_rcv_isr_count++] = read_value;
			write_uart_character(uart_instance[2], read_value);
		}
		write_word(GPIO_DATA_REG, read_word(GPIO_DATA_REG) & ~(RTS));
	}
	else if(uart_instance[2]->status & STS_RX_NOT_EMPTY)
	{
		read_value = uart_instance[2]->rcv_reg;
		u2_rcv_char[uart2_rcv_isr_count++] = read_value;
		write_uart_character(uart_instance[2], read_value);
	}
	return 0;
}
#endif
