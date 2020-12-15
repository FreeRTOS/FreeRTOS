/*
 * FreeRTOS V202012.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

/******************************************************************************
 * This project provides two demo applications.  A simple blinky style project,
 * and a more comprehensive test and demo application.  The
 * mainCREATE_SIMPLE_BLINKY_DEMO_ONLY setting (defined in this file) is used to
 * select between the two.  The simply blinky demo is implemented and described
 * in main_blinky.c.  The more comprehensive test and demo application is
 * implemented and described in main_full.c.
 *
 * This file implements the code that is not demo specific, including the
 * hardware setup and standard FreeRTOS hook functions.
 *
 * ENSURE TO READ THE DOCUMENTATION PAGE FOR THIS PORT AND DEMO APPLICATION ON
 * THE http://www.FreeRTOS.org WEB SITE FOR FULL INFORMATION ON USING THIS DEMO
 * APPLICATION, AND ITS ASSOCIATE FreeRTOS ARCHITECTURE PORT!
 *
 */

/* Scheduler include files. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

/* Library includes. */
#include "board.h"
#include "asf.h"

/* Set mainCREATE_SIMPLE_BLINKY_DEMO_ONLY to one to run the simple blinky demo,
or 0 to run the more comprehensive test and demo application. */
#define mainCREATE_SIMPLE_BLINKY_DEMO_ONLY	1

/*-----------------------------------------------------------*/

/*
 * Configure the hardware as necessary to run this demo.
 */
static void prvSetupHardware( void );

/*
 * main_blinky() is used when mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is set to 1.
 * main_full() is used when mainCREATE_SIMPLE_BLINKY_DEMO_ONLY is set to 0.
 */
#if mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 1
	extern void main_blinky( void );
#else
	extern void main_full( void );
#endif /* #if mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 1 */

/* Prototypes for the standard FreeRTOS callback/hook functions implemented
within this file. */
void vApplicationMallocFailedHook( void );
void vApplicationIdleHook( void );
void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName );
void vApplicationTickHook( void );

/*-----------------------------------------------------------*/

int main( void )
{
	/* Configure the hardware ready to run the demo. */
	prvSetupHardware();

	/* The mainCREATE_SIMPLE_BLINKY_DEMO_ONLY setting is described at the top
	of this file. */
	#if( mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 1 )
	{
		main_blinky();
	}
	#else
	{
		main_full();
	}
	#endif

	return 0;
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
	sysclk_init();
	board_init();
}
/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
	/* Called if a call to pvPortMalloc() fails because there is insufficient
	free memory available in the FreeRTOS heap.  pvPortMalloc() is called
	internally by FreeRTOS API functions that create tasks, queues, software
	timers, and semaphores.  The size of the FreeRTOS heap is set by the
	configTOTAL_HEAP_SIZE configuration constant in FreeRTOSConfig.h. */

	/* Force an assert. */
	configASSERT( ( volatile void * ) NULL );
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName )
{
	( void ) pcTaskName;
	( void ) pxTask;

	/* Run time stack overflow checking is performed if
	configCHECK_FOR_STACK_OVERFLOW is defined to 1 or 2.  This hook
	function is called if a stack overflow is detected. */

	/* Force an assert. */
	configASSERT( ( volatile void * ) NULL );
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
volatile size_t xFreeHeapSpace;

	/* This is just a trivial example of an idle hook.  It is called on each
	cycle of the idle task.  It must *NOT* attempt to block.  In this case the
	idle task just queries the amount of FreeRTOS heap that remains.  See the
	memory management section on the http://www.FreeRTOS.org web site for memory
	management options.  If there is a lot of heap memory free then the
	configTOTAL_HEAP_SIZE value in FreeRTOSConfig.h can be reduced to free up
	RAM. */
	xFreeHeapSpace = xPortGetFreeHeapSize();

	/* Remove compiler warning about xFreeHeapSpace being set but never used. */
	( void ) xFreeHeapSpace;
}
/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
	#if( mainCREATE_SIMPLE_BLINKY_DEMO_ONLY == 0 )
	{
	extern void vFullDemoTickHook( void );
	
		/* The full demo includes some tests that execute in an interrupt
		context, and the tick hook is used for this purpose. */
		vFullDemoTickHook();	
	}
	#endif
}
/*-----------------------------------------------------------*/



















#if 0



/**
 * \file
 *
 * \brief Getting Started Application.
 *
 * Copyright (c) 2011-2015 Atmel Corporation. All rights reserved.
 *
 * \asf_license_start
 *
 * \page License
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 *
 * 3. The name of Atmel may not be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * 4. This software may only be redistributed and used in connection with an
 *    Atmel microcontroller product.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * EXPRESSLY AND SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
 * ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *
 * \asf_license_stop
 *
 */

/**
 * \mainpage Getting Started Application
 *
 * \section Purpose
 *
 * The Getting Started example will help new users get familiar with Atmel's
 * SAM family of microcontrollers. This basic application shows the startup
 * sequence of a chip and how to use its core peripherals.
 *
 * \section Requirements
 *
 * This package can be used with SAM evaluation kits.
 *
 * \section Description
 *
 * The demonstration program makes the LED(s) on the board blink at a fixed rate.
 * This rate is generated by using Time tick timer. The blinking can be stopped
 * using the push button.
 *
 * \section Usage
 *
 * -# Build the program and download it inside the evaluation board.
 * -# On the computer, open and configure a terminal application
 *    (e.g. HyperTerminal on Microsoft Windows) with these settings:
 *   - 115200 bauds
 *   - 8 bits of data
 *   - No parity
 *   - 1 stop bit
 *   - No flow control
 * -# Start the application.
 * -# The LED(s) should start blinking on the board. In the terminal window, the
 *    following text should appear (values depend on the board and chip used):
 *    \code
	-- Getting Started Example xxx --
	-- xxxxxx-xx
	-- Compiled: xxx xx xxxx xx:xx:xx --
\endcode
 * -# Pressing and release button 1 should make one LED stop & restart
 *    blinking.
 * -# If the button 2 available, pressing button 2 should make the other LED
 *    stop & restart blinking.
 *
 */
/*
 * Support and FAQ: visit <a href="http://www.atmel.com/design-support/">Atmel Support</a>
 */

#include "FreeRTOS.h"
#include "task.h"

#include "asf.h"
#include "stdio_serial.h"
#include "conf_board.h"
#include "conf_clock.h"

/** IRQ priority for PIO (The lower the value, the greater the priority) */
// [main_def_pio_irq_prior]
#define IRQ_PRIOR_PIO    0
// [main_def_pio_irq_prior]

/** LED0 blink time, LED1 blink half this time, in ms */
#define BLINK_PERIOD     1000

#define STRING_EOL    "\r"
#define STRING_HEADER "-- Getting Started Example --\r\n" \
		"-- "BOARD_NAME" --\r\n" \
		"-- Compiled: "__DATE__" "__TIME__" --"STRING_EOL

/** LED0 blinking control. */
// [main_var_led0_control]
volatile bool g_b_led0_active = true;
// [main_var_led0_control]

#ifdef LED1_GPIO
/** LED1 blinking control. */
// [main_var_led1_control]
volatile bool g_b_led1_active = true;
// [main_var_led1_control]
#endif

/** Global g_ul_ms_ticks in milliseconds since start of application */
// [main_var_ticks]
volatile uint32_t g_ul_ms_ticks = 0;
// [main_var_ticks]

/// @cond 0
/**INDENT-OFF**/
#ifdef __cplusplus
extern "C" {
#endif
/**INDENT-ON**/
/// @endcond


/* Prototypes for the standard FreeRTOS callback/hook functions implemented
within this file. */
void vApplicationMallocFailedHook( void );
void vApplicationIdleHook( void );
void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName );
void vApplicationTickHook( void );


/**
 *  \brief Process Buttons Events
 *
 *  Change active states of LEDs when corresponding button events happened.
 */
static void ProcessButtonEvt(uint8_t uc_button)
{
// [main_button1_evnt_process]
	if (uc_button == 0) {
		g_b_led0_active = !g_b_led0_active;
		if (!g_b_led0_active) {
			ioport_set_pin_level(LED0_GPIO, IOPORT_PIN_LEVEL_HIGH);
		}
	}
// [main_button1_evnt_process]
#ifdef LED1_GPIO 
	else {
// [main_button2_evnt_process]
		g_b_led1_active = !g_b_led1_active;

		/* Enable LED#2 and TC if they were enabled */
		if (g_b_led1_active) {
			ioport_set_pin_level(LED1_GPIO, IOPORT_PIN_LEVEL_LOW);
			tc_start(TC0, 0);
		}
		/* Disable LED#2 and TC if they were disabled */
		else {
			ioport_set_pin_level(LED1_GPIO, IOPORT_PIN_LEVEL_HIGH);
			tc_stop(TC0, 0);
		}
// [main_button2_evnt_process]
	}
#endif
}

/**
 *  \brief Handler for System Tick interrupt.
 *
 *  Process System Tick Event
 *  Increments the g_ul_ms_ticks counter.
 */
// [main_systick_handler]
void _SysTick_Handler(void)
{
	g_ul_ms_ticks++;
}
// [main_systick_handler]

/**
 *  \brief Handler for Button 1 rising edge interrupt.
 *
 *  Handle process led1 status change.
 */
// [main_button1_handler]
static void Button1_Handler(uint32_t id, uint32_t mask)
{
	if (PIN_PUSHBUTTON_1_ID == id && PIN_PUSHBUTTON_1_MASK == mask) {
		ProcessButtonEvt(0);
	}
}
// [main_button1_handler]

#ifndef BOARD_NO_PUSHBUTTON_2
/**
 *  \brief Handler for Button 2 falling edge interrupt.
 *
 *  Handle process led2 status change.
 */
// [main_button2_handler] 
static void Button2_Handler(uint32_t id, uint32_t mask)
{
	if (PIN_PUSHBUTTON_2_ID == id && PIN_PUSHBUTTON_2_MASK == mask) {
		ProcessButtonEvt(1);
	}
}
// [main_button2_handler]
#endif

/**
 *  \brief Configure the Pushbuttons
 *
 *  Configure the PIO as inputs and generate corresponding interrupt when
 *  pressed or released.
 */
static void configure_buttons(void)
{
// [main_button1_configure]
	/* Configure Pushbutton 1 */
	pmc_enable_periph_clk(PIN_PUSHBUTTON_1_ID);
	pio_set_debounce_filter(PIN_PUSHBUTTON_1_PIO, PIN_PUSHBUTTON_1_MASK, 10);
	/* Interrupt on rising edge  */
	pio_handler_set(PIN_PUSHBUTTON_1_PIO, PIN_PUSHBUTTON_1_ID,
			PIN_PUSHBUTTON_1_MASK, PIN_PUSHBUTTON_1_ATTR, Button1_Handler);
	NVIC_EnableIRQ((IRQn_Type) PIN_PUSHBUTTON_1_ID);
	pio_handler_set_priority(PIN_PUSHBUTTON_1_PIO,
			(IRQn_Type) PIN_PUSHBUTTON_1_ID, IRQ_PRIOR_PIO);
	pio_enable_interrupt(PIN_PUSHBUTTON_1_PIO, PIN_PUSHBUTTON_1_MASK);
// [main_button1_configure]
#ifndef BOARD_NO_PUSHBUTTON_2
// [main_button2_configure]
	/* Configure Pushbutton 2 */
	pmc_enable_periph_clk(PIN_PUSHBUTTON_2_ID);
	pio_set_debounce_filter(PIN_PUSHBUTTON_2_PIO, PIN_PUSHBUTTON_2_MASK, 10);
	/* Interrupt on falling edge */
	pio_handler_set(PIN_PUSHBUTTON_2_PIO, PIN_PUSHBUTTON_2_ID,
			PIN_PUSHBUTTON_2_MASK, PIN_PUSHBUTTON_2_ATTR, Button2_Handler);
	NVIC_EnableIRQ((IRQn_Type) PIN_PUSHBUTTON_2_ID);
	pio_handler_set_priority(PIN_PUSHBUTTON_2_PIO,
			(IRQn_Type) PIN_PUSHBUTTON_2_ID, IRQ_PRIOR_PIO);
	pio_enable_interrupt(PIN_PUSHBUTTON_2_PIO, PIN_PUSHBUTTON_2_MASK);
// [main_button2_configure]
#endif
}

/**
 *  Interrupt handler for TC0 interrupt. Toggles the state of LED\#2.
 */
// [main_tc0_handler]
#ifndef BOARD_NO_LED_1
void TC0_Handler(void)
{
	volatile uint32_t ul_dummy;

	/* Clear status bit to acknowledge interrupt */
	ul_dummy = tc_get_status(TC0, 0);

	/* Avoid compiler warning */
	UNUSED(ul_dummy);

#ifdef LED1_GPIO
	/** Toggle LED state. */
	ioport_toggle_pin_level(LED1_GPIO);
#endif

	printf("2 ");
}
// [main_tc0_handler]

/**
 *  Configure Timer Counter 0 to generate an interrupt every 250ms.
 */
// [main_tc_configure]
static void configure_tc(void)
{
	uint32_t ul_div;
	uint32_t ul_tcclks;
	uint32_t ul_sysclk = sysclk_get_cpu_hz();

	/* Configure PMC */
	pmc_enable_periph_clk(ID_TC0);
#if SAMG55
	/* Enable PCK output */
	pmc_disable_pck(PMC_PCK_3);
	pmc_switch_pck_to_sclk(PMC_PCK_3, PMC_PCK_PRES_CLK_1);
	pmc_enable_pck(PMC_PCK_3);
#endif

	/** Configure TC for a 4Hz frequency and trigger on RC compare. */
	tc_find_mck_divisor(4, ul_sysclk, &ul_div, &ul_tcclks, ul_sysclk);
	tc_init(TC0, 0, ul_tcclks | TC_CMR_CPCTRG);
	tc_write_rc(TC0, 0, (ul_sysclk / ul_div) / 4);

	/* Configure and enable interrupt on RC compare */
	NVIC_EnableIRQ((IRQn_Type) ID_TC0);
	tc_enable_interrupt(TC0, 0, TC_IER_CPCS);

#ifdef LED1_GPIO
	/** Start the counter if LED1 is enabled. */
	if (g_b_led1_active) {
		tc_start(TC0, 0);
	}
#else
	tc_start(TC0, 0);
#endif
}
#endif
// [main_tc_configure]

/**
 *  Configure UART console.
 */
// [main_console_configure]
static void configure_console(void)
{
	const usart_serial_options_t uart_serial_options = {
		.baudrate = CONF_UART_BAUDRATE,
#ifdef CONF_UART_CHAR_LENGTH
		.charlength = CONF_UART_CHAR_LENGTH,
#endif
		.paritytype = CONF_UART_PARITY,
#ifdef CONF_UART_STOP_BITS
		.stopbits = CONF_UART_STOP_BITS,
#endif
	};

	/* Configure console UART. */
	sysclk_enable_peripheral_clock(CONSOLE_UART_ID);
	stdio_serial_init(CONF_UART, &uart_serial_options);
}

// [main_console_configure]

/**
 * \brief Wait for the given number of milliseconds (using the g_ul_ms_ticks
 * generated by the SAM's microcontrollers's system tick).
 *
 * \param ul_dly_ticks  Delay to wait for, in milliseconds.
 */
// [main_ms_delay]
static void mdelay(uint32_t ul_dly_ticks)
{
	uint32_t ul_cur_ticks;

	ul_cur_ticks = g_ul_ms_ticks;
	while ((g_ul_ms_ticks - ul_cur_ticks) < ul_dly_ticks);
}
// [main_ms_delay]

/**
 *  \brief getting-started Application entry point.
 *
 *  \return Unused (ANSI-C compatibility).
 */
// [main]
int main(void)
{
//! [main_step_sys_init]
	/* Initialize the SAM system */
	sysclk_init();
	board_init();
//! [main_step_sys_init]

#ifndef BOARD_NO_PUSHBUTTON_2
#if (SAMV71 || SAMV70 || SAMS70 || SAME70)
	if (GPIO_PUSH_BUTTON_2 == PIO_PB12_IDX) {
		matrix_set_system_io(matrix_get_system_io() | CCFG_SYSIO_SYSIO12);
	}
	ioport_set_pin_dir(GPIO_PUSH_BUTTON_2, IOPORT_DIR_INPUT);
	ioport_set_pin_mode(GPIO_PUSH_BUTTON_2, GPIO_PUSH_BUTTON_2_FLAGS);
	ioport_set_pin_sense_mode(GPIO_PUSH_BUTTON_2, GPIO_PUSH_BUTTON_2_SENSE);
#endif
#endif
//! [main_step_console_init]
	/* Initialize the console uart */
	configure_console();
//! [main_step_console_init]

	/* Output example information */
	puts(STRING_HEADER);

	/* Configure systick for 1 ms */
	puts("Configure system tick to get 1ms tick period.\r");
//! [main_step_systick_init]
	if (SysTick_Config(sysclk_get_cpu_hz() / 1000)) {
		puts("-F- Systick configuration error\r");
		while (1);
	}
//! [main_step_systick_init]

#ifndef BOARD_NO_LED_1
	puts("Configure TC.\r");
//! [main_step_tc_init]
	configure_tc();
//! [main_step_tc_init]
#endif

	puts("Configure buttons with debouncing.\r");
//! [main_step_btn_init]
	configure_buttons();
//! [main_step_btn_init]

	printf("Press %s to Start/Stop the %s blinking.\r\n",
			PUSHBUTTON_1_NAME, LED_0_NAME);

#ifndef BOARD_NO_PUSHBUTTON_2
	printf("Press %s to Start/Stop the %s blinking.\r\n",
			PUSHBUTTON_2_NAME, LED_1_NAME);
#endif

//! [main_step_loop]
	while (1) {
		/* Wait for LED to be active */
		while (!g_b_led0_active);

		/* Toggle LED state if active */
		if (g_b_led0_active) {
			ioport_toggle_pin_level(LED0_GPIO);
			printf("1 ");
		}

		/* Wait for 500ms */
		mdelay(500);
	}
//! [main_step_loop]
}
// [main]
/// @cond 0
/**INDENT-OFF**/
#ifdef __cplusplus
}
#endif
/**INDENT-ON**/
/// @endcond

void vApplicationMallocFailedHook( void )
{
	/* Called if a call to pvPortMalloc() fails because there is insufficient
	free memory available in the FreeRTOS heap.  pvPortMalloc() is called
	internally by FreeRTOS API functions that create tasks, queues, software
	timers, and semaphores.  The size of the FreeRTOS heap is set by the
	configTOTAL_HEAP_SIZE configuration constant in FreeRTOSConfig.h. */

	/* Force an assert. */
	configASSERT( ( volatile void * ) NULL );
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName )
{
	( void ) pcTaskName;
	( void ) pxTask;

	/* Run time stack overflow checking is performed if
	configCHECK_FOR_STACK_OVERFLOW is defined to 1 or 2.  This hook
	function is called if a stack overflow is detected. */

	/* Force an assert. */
	configASSERT( ( volatile void * ) NULL );
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
volatile size_t xFreeHeapSpace;

	/* This is just a trivial example of an idle hook.  It is called on each
	cycle of the idle task.  It must *NOT* attempt to block.  In this case the
	idle task just queries the amount of FreeRTOS heap that remains.  See the
	memory management section on the http://www.FreeRTOS.org web site for memory
	management options.  If there is a lot of heap memory free then the
	configTOTAL_HEAP_SIZE value in FreeRTOSConfig.h can be reduced to free up
	RAM. */
	xFreeHeapSpace = xPortGetFreeHeapSize();

	/* Remove compiler warning about xFreeHeapSpace being set but never used. */
	( void ) xFreeHeapSpace;
}
/*-----------------------------------------------------------*/

void vApplicationTickHook( void )
{
}
/*-----------------------------------------------------------*/

#endif
