/*******************************************************************************
 * Copyright 2019-2020 Microchip FPGA Embedded Systems Solution.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software example
 *
 */
/*******************************************************************************
 *
 * Code running on E51
 *
 */

#include <stdio.h>
#include <string.h>
#include "mpfs_hal/mss_hal.h"
#include "inc/common.h"

#ifndef SIFIVE_HIFIVE_UNLEASHED
#include "drivers/mss/mss_mmuart/mss_uart.h"
#else
#include "drivers/FU540_uart/FU540_uart.h"
#endif

#include "FreeRTOS.h"
#include "task.h"

static volatile uint32_t count_sw_ints_h0 = 0U;

/*******************************************************************************
 * Instruction message. This message will be transmitted over the UART to
 * HyperTerminal when the program starts.
 ******************************************************************************/
const uint8_t g_message[] =
        "\r\n\r\n\r\n\
MPFS HAL example version 0.3.1\r\n\
This program is run from E51\r\n\
Type 0  Show this menu\r\n\
Type 1  Raise sw int hart 1\r\n\
Type 2  Raise sw int hart 2\r\n\
Type 3  Raise sw int hart 3\r\n\
Type 4  Raise sw int hart 4\r\n\
Type 5  Print debug messages from hart0\r\n\
";

#ifndef  MPFS_HAL_SHARED_MEM_ENABLED
#endif

/* Main function for the HART0(E51 processor).
 * Application code running on HART0 is placed here.
 */
void e51(void)
{
    int8_t info_string[100];
    uint64_t mcycle_start = 0U;
    uint64_t mcycle_end = 0U;
    uint64_t delta_mcycle = 0U;
    uint64_t hartid = read_csr(mhartid);
    uint8_t rx_buff[1];
    uint8_t rx_size = 0;
    uint8_t debug_hart0 = 0U;

    extern void main_blinky( void );
    main_blinky();
    /* Turn on UART0 clock */
    SYSREG->SUBBLK_CLOCK_CR |= SUBBLK_CLOCK_CR_MMUART0_MASK;
    /* Remove soft reset */
    SYSREG->SOFT_RESET_CR   &= ~SOFT_RESET_CR_MMUART0_MASK;

    HLS_DATA* hls = (HLS_DATA*)(uintptr_t)get_tp_reg();
    /* This mutex is used to serialize accesses to UART0 when all harts want to
     * TX/RX on UART0. This mutex is shared across all harts. */
    HART_SHARED_DATA * hart_share = (HART_SHARED_DATA *)hls->shared_mem;
    /* set point for sharing across harts */
    hart_share->g_mss_uart0_lo = &g_mss_uart0_lo;

    MSS_UART_init( hart_share->g_mss_uart0_lo,
            MSS_UART_115200_BAUD,
            MSS_UART_DATA_8_BITS | MSS_UART_NO_PARITY | MSS_UART_ONE_STOP_BIT);

    sprintf(info_string, "\r\nHart %u, HLS mem address 0x%lx, Shared mem 0x%lx\r\n",\
                                                          hls->my_hart_id, (uint64_t)hls, (uint64_t)hls->shared_mem);
    spinlock(&hart_share->mutex_uart0);
    MSS_UART_polled_tx(hart_share->g_mss_uart0_lo, (const uint8_t*)info_string,(uint32_t)strlen(info_string));
    spinunlock(&hart_share->mutex_uart0);

    MSS_UART_polled_tx_string (&g_mss_uart0_lo, g_message);

    /* Start the other harts with appropriate UART input from user */
    while (1)
    {
      mcycle_start = readmcycle();

      if (1u == debug_hart0)
      {
          debug_hart0 = 0U;
          sprintf(info_string,"Hart %ld, %ld delta_mcycle %ld mtime\r\n",
          hartid, delta_mcycle, readmtime());
          spinlock(&hart_share->mutex_uart0);
          MSS_UART_polled_tx(hart_share->g_mss_uart0_lo, info_string,strlen(info_string));
          spinunlock(&hart_share->mutex_uart0);
      }

      spinlock(&hart_share->mutex_uart0);
      rx_size = MSS_UART_get_rx(hart_share->g_mss_uart0_lo, rx_buff, sizeof(rx_buff));
      spinunlock(&hart_share->mutex_uart0);

        if (rx_size > 0)
        {
            switch(rx_buff[0])
            {
                case '0':
                    spinlock(&hart_share->mutex_uart0);
                    MSS_UART_polled_tx_string (hart_share->g_mss_uart0_lo, g_message );
                    spinunlock(&hart_share->mutex_uart0);
                    break;
                case '1':
                    raise_soft_interrupt(1u);
                    break;
                case '2':
                    raise_soft_interrupt(2u);
                    break;
                case '3':
                    raise_soft_interrupt(3u);
                    break;
                case '4':
                    raise_soft_interrupt(4u);
                    break;
                case '5':
                    debug_hart0 = 1;
                    break;

                default:
                    /* echo input */
                    spinlock(&hart_share->mutex_uart0);
                    MSS_UART_polled_tx_string(hart_share->g_mss_uart0_lo, rx_buff);
                    spinunlock(&hart_share->mutex_uart0);
                    break;
            }
        }

        mcycle_end    = readmcycle();
        delta_mcycle = mcycle_end - mcycle_start;
    }
}

/* HART0 Software interrupt handler */
void Software_h0_IRQHandler(void)
{
    uint64_t hart_id = read_csr(mhartid);
    count_sw_ints_h0++;
}

void vAssertCalled( void )
{
	taskDISABLE_INTERRUPTS();

	for( ;; )
	{
			__asm volatile( "nop" );

	}
}
