/******************************************************************************
*
* Copyright 2013 Altera Corporation. All Rights Reserved.
* 
* Redistribution and use in source and binary forms, with or without
* modification, are permitted provided that the following conditions are met:
* 
* 1. Redistributions of source code must retain the above copyright notice,
* this list of conditions and the following disclaimer.
* 
* 2. Redistributions in binary form must reproduce the above copyright notice,
* this list of conditions and the following disclaimer in the documentation
* and/or other materials provided with the distribution.
* 
* 3. The name of the author may not be used to endorse or promote products
* derived from this software without specific prior written permission.
* 
* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER "AS IS" AND ANY EXPRESS OR
* IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
* MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE, ARE DISCLAIMED. IN NO
* EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
* EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT
* OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
* INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
* CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING
* IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY
* OF SUCH DAMAGE.
* 
******************************************************************************/

#ifndef __ALT_INT_COMMON_H__
#define __ALT_INT_COMMON_H__

#include "hwlib.h"
#include <stdbool.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C"
{
#endif

/*!
 * \addtogroup INT_COMMON Interrupt Controller Common Definitions
 *
 * This module contains the definitions common to the Interrupt Controller
 * Low-Level API and Interrupt Controller Manager Interface.
 *
 * @{
 */

/*!
 * This type definition enumerates all the interrupt identification types.
 */
typedef enum ALT_INT_INTERRUPT_e
{
    ALT_INT_INTERRUPT_SGI0  =  0, /*!< # */
    ALT_INT_INTERRUPT_SGI1  =  1, /*!< # */
    ALT_INT_INTERRUPT_SGI2  =  2, /*!< # */
    ALT_INT_INTERRUPT_SGI3  =  3, /*!< # */
    ALT_INT_INTERRUPT_SGI4  =  4, /*!< # */
    ALT_INT_INTERRUPT_SGI5  =  5, /*!< # */
    ALT_INT_INTERRUPT_SGI6  =  6, /*!< # */
    ALT_INT_INTERRUPT_SGI7  =  7, /*!< # */
    ALT_INT_INTERRUPT_SGI8  =  8, /*!< # */
    ALT_INT_INTERRUPT_SGI9  =  9, /*!< # */
    ALT_INT_INTERRUPT_SGI10 = 10, /*!< # */
    ALT_INT_INTERRUPT_SGI11 = 11, /*!< # */
    ALT_INT_INTERRUPT_SGI12 = 12, /*!< # */
    ALT_INT_INTERRUPT_SGI13 = 13, /*!< # */
    ALT_INT_INTERRUPT_SGI14 = 14, /*!< # */
    ALT_INT_INTERRUPT_SGI15 = 15,
    /*!<
     * Software Generated Interrupts (SGI), 0 - 15.
     *  * All interrupts in this group are software triggered.
     */

    ALT_INT_INTERRUPT_PPI_TIMER_GLOBAL   = 27, /*!< # */
    ALT_INT_INTERRUPT_PPI_TIMER_PRIVATE  = 29, /*!< # */
    ALT_INT_INTERRUPT_PPI_TIMER_WATCHDOG = 30, /*!< # */
    /*!<
     * Private Peripheral Interrupts (PPI) for the Global Timer, per CPU
     * private timer, and watchdog timer.
     *  * All interrupts in this group are edge triggered.
     */

    ALT_INT_INTERRUPT_CPU0_PARITYFAIL         = 32, /*!< # */
    ALT_INT_INTERRUPT_CPU0_PARITYFAIL_BTAC    = 33, /*!< # */
    ALT_INT_INTERRUPT_CPU0_PARITYFAIL_GHB     = 34, /*!< # */
    ALT_INT_INTERRUPT_CPU0_PARITYFAIL_I_TAG   = 35, /*!< # */
    ALT_INT_INTERRUPT_CPU0_PARITYFAIL_I_DATA  = 36, /*!< # */
    ALT_INT_INTERRUPT_CPU0_PARITYFAIL_TLB     = 37, /*!< # */
    ALT_INT_INTERRUPT_CPU0_PARITYFAIL_D_OUTER = 38, /*!< # */
    ALT_INT_INTERRUPT_CPU0_PARITYFAIL_D_TAG   = 39, /*!< # */
    ALT_INT_INTERRUPT_CPU0_PARITYFAIL_D_DATA  = 40, /*!< # */
    ALT_INT_INTERRUPT_CPU0_DEFLAGS0           = 41, /*!< # */
    ALT_INT_INTERRUPT_CPU0_DEFLAGS1           = 42, /*!< # */
    ALT_INT_INTERRUPT_CPU0_DEFLAGS2           = 43, /*!< # */
    ALT_INT_INTERRUPT_CPU0_DEFLAGS3           = 44, /*!< # */
    ALT_INT_INTERRUPT_CPU0_DEFLAGS4           = 45, /*!< # */
    ALT_INT_INTERRUPT_CPU0_DEFLAGS5           = 46, /*!< # */
    ALT_INT_INTERRUPT_CPU0_DEFLAGS6           = 47,
    /*!<
     * Interrupts sourced from CPU0.
     *
     * The ALT_INT_INTERRUPT_CPU0_PARITYFAIL interrupt combines the
     * BTAC, GHB, I_TAG, I_DATA, TLB, D_OUTER, D_TAG, and D_DATA interrupts
     * for CPU0.
     *
     *  * PARITYFAIL interrupts in this group are edge triggered.
     *  * DEFFLAGS interrupts in this group are level triggered.
     */

    ALT_INT_INTERRUPT_CPU1_PARITYFAIL         = 48, /*!< # */
    ALT_INT_INTERRUPT_CPU1_PARITYFAIL_BTAC    = 49, /*!< # */
    ALT_INT_INTERRUPT_CPU1_PARITYFAIL_GHB     = 50, /*!< # */
    ALT_INT_INTERRUPT_CPU1_PARITYFAIL_I_TAG   = 51, /*!< # */
    ALT_INT_INTERRUPT_CPU1_PARITYFAIL_I_DATA  = 52, /*!< # */
    ALT_INT_INTERRUPT_CPU1_PARITYFAIL_TLB     = 53, /*!< # */
    ALT_INT_INTERRUPT_CPU1_PARITYFAIL_D_OUTER = 54, /*!< # */
    ALT_INT_INTERRUPT_CPU1_PARITYFAIL_D_TAG   = 55, /*!< # */
    ALT_INT_INTERRUPT_CPU1_PARITYFAIL_D_DATA  = 56, /*!< # */
    ALT_INT_INTERRUPT_CPU1_DEFLAGS0           = 57, /*!< # */
    ALT_INT_INTERRUPT_CPU1_DEFLAGS1           = 58, /*!< # */
    ALT_INT_INTERRUPT_CPU1_DEFLAGS2           = 59, /*!< # */
    ALT_INT_INTERRUPT_CPU1_DEFLAGS3           = 60, /*!< # */
    ALT_INT_INTERRUPT_CPU1_DEFLAGS4           = 61, /*!< # */
    ALT_INT_INTERRUPT_CPU1_DEFLAGS5           = 62, /*!< # */
    ALT_INT_INTERRUPT_CPU1_DEFLAGS6           = 63,
    /*!<
     * Interrupts sourced from CPU1.
     *
     * The ALT_INT_INTERRUPT_CPU1_PARITYFAIL interrupt combines the
     * BTAC, GHB, I_TAG, I_DATA, TLB, D_OUTER, D_TAG, and D_DATA interrupts
     * for CPU1.
     *
     *  * PARITYFAIL interrupts in this group are edge triggered.
     *  * DEFFLAGS interrupts in this group are level triggered.
     */
    
    ALT_INT_INTERRUPT_SCU_PARITYFAIL0 =  64, /*!< # */
    ALT_INT_INTERRUPT_SCU_PARITYFAIL1 =  65, /*!< # */
    ALT_INT_INTERRUPT_SCU_EV_ABORT    =  66,
    /*!<
     * Interrupts sourced from the Snoop Control Unit (SCU).
     *  * All interrupts in this group are edge triggered.
     */
    
    ALT_INT_INTERRUPT_L2_ECC_BYTE_WR_IRQ     = 67, /*!< # */
    ALT_INT_INTERRUPT_L2_ECC_CORRECTED_IRQ   = 68, /*!< # */
    ALT_INT_INTERRUPT_L2_ECC_UNCORRECTED_IRQ = 69, /*!< # */
    ALT_INT_INTERRUPT_L2_COMBINED_IRQ        = 70,
    /*!<
     * Interrupts sourced from the L2 Cache Controller.
     *
     * The ALT_INT_INTERRUPT_L2_COMBINED_IRQ interrupt combines the cache
     * controller internal DECERRINTR, ECNTRINTR, ERRRDINTR, ERRRTINTR,
     * ERRWDINTR, ERRWTINTR, PARRDINTR, PARRTINTR, and SLVERRINTR interrupts.
     * Consult the L2C documentation for information on these interrupts.
     *
     *  * ECC interrupts in this group are edge triggered.
     *  * Other interrupts in this group are level triggered.
     */

    ALT_INT_INTERRUPT_DDR_ECC_ERROR_IRQ =  71,
    /*!<
     * Interrupts sourced from the SDRAM Controller.
     *  * All interrupts in this group are level triggered.
     */

    ALT_INT_INTERRUPT_F2S_FPGA_IRQ0  =  72, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ1  =  73, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ2  =  74, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ3  =  75, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ4  =  76, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ5  =  77, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ6  =  78, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ7  =  79, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ8  =  80, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ9  =  81, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ10 =  82, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ11 =  83, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ12 =  84, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ13 =  85, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ14 =  86, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ15 =  87, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ16 =  88, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ17 =  89, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ18 =  90, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ19 =  91, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ20 =  92, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ21 =  93, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ22 =  94, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ23 =  95, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ24 =  96, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ25 =  97, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ26 =  98, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ27 =  99, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ28 = 100, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ29 = 101, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ30 = 102, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ31 = 103, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ32 = 104, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ33 = 105, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ34 = 106, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ35 = 107, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ36 = 108, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ37 = 109, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ38 = 110, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ39 = 111, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ40 = 112, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ41 = 113, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ42 = 114, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ43 = 115, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ44 = 116, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ45 = 117, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ46 = 118, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ47 = 119, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ48 = 120, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ49 = 121, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ50 = 122, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ51 = 123, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ52 = 124, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ53 = 125, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ54 = 126, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ55 = 127, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ56 = 128, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ57 = 129, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ58 = 130, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ59 = 131, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ60 = 132, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ61 = 133, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ62 = 134, /*!< # */
    ALT_INT_INTERRUPT_F2S_FPGA_IRQ63 = 135,
    /*!<
     * Interrupt request from the FPGA logic, 0 - 63.
     *  * Trigger type depends on the implementation in the FPGA.
     */

    ALT_INT_INTERRUPT_DMA_IRQ0                = 136, /*!< # */
    ALT_INT_INTERRUPT_DMA_IRQ1                = 137, /*!< # */
    ALT_INT_INTERRUPT_DMA_IRQ2                = 138, /*!< # */
    ALT_INT_INTERRUPT_DMA_IRQ3                = 139, /*!< # */
    ALT_INT_INTERRUPT_DMA_IRQ4                = 140, /*!< # */
    ALT_INT_INTERRUPT_DMA_IRQ5                = 141, /*!< # */
    ALT_INT_INTERRUPT_DMA_IRQ6                = 142, /*!< # */
    ALT_INT_INTERRUPT_DMA_IRQ7                = 143, /*!< # */
    ALT_INT_INTERRUPT_DMA_IRQ_ABORT           = 144, /*!< # */
    ALT_INT_INTERRUPT_DMA_ECC_CORRECTED_IRQ   = 145, /*!< # */
    ALT_INT_INTERRUPT_DMA_ECC_UNCORRECTED_IRQ = 146,
    /*!<
     * Interrupts sourced from the DMA Controller.
     *  * All interrupts in this group are level triggered.
     */

    ALT_INT_INTERRUPT_EMAC0_IRQ                    = 147, /*!< # */
    ALT_INT_INTERRUPT_EMAC0_TX_ECC_CORRECTED_IRQ   = 148, /*!< # */
    ALT_INT_INTERRUPT_EMAC0_TX_ECC_UNCORRECTED_IRQ = 149, /*!< # */
    ALT_INT_INTERRUPT_EMAC0_RX_ECC_CORRECTED_IRQ   = 150, /*!< # */
    ALT_INT_INTERRUPT_EMAC0_RX_ECC_UNCORRECTED_IRQ = 151,
    /*!<
     * Interrupts sourced from the Ethernet MAC 0 (EMAC0).
     *  * All interrupts in this group are level triggered.
     */

    ALT_INT_INTERRUPT_EMAC1_IRQ                    = 152, /*!< # */
    ALT_INT_INTERRUPT_EMAC1_TX_ECC_CORRECTED_IRQ   = 153, /*!< # */
    ALT_INT_INTERRUPT_EMAC1_TX_ECC_UNCORRECTED_IRQ = 154, /*!< # */
    ALT_INT_INTERRUPT_EMAC1_RX_ECC_CORRECTED_IRQ   = 155, /*!< # */
    ALT_INT_INTERRUPT_EMAC1_RX_ECC_UNCORRECTED_IRQ = 156,
    /*!<
     * Interrupts sourced from the Ethernet MAC 1 (EMAC1).
     *  * All interrupts in this group are level triggered.
     */

    ALT_INT_INTERRUPT_USB0_IRQ             = 157, /*!< # */
    ALT_INT_INTERRUPT_USB0_ECC_CORRECTED   = 158, /*!< # */
    ALT_INT_INTERRUPT_USB0_ECC_UNCORRECTED = 159,
    /*!<
     * Interrupts sourced from the USB OTG 0.
     *  * All interrupts in this group are level triggered.
     */

    ALT_INT_INTERRUPT_USB1_IRQ             = 160, /*!< # */
    ALT_INT_INTERRUPT_USB1_ECC_CORRECTED   = 161, /*!< # */
    ALT_INT_INTERRUPT_USB1_ECC_UNCORRECTED = 162,
    /*!<
     * Interrupts sourced from the USB OTG 1.
     *  * All interrupts in this group are level triggered.
     */

    ALT_INT_INTERRUPT_CAN0_STS_IRQ             = 163, /*!< # */
    ALT_INT_INTERRUPT_CAN0_MO_IRQ              = 164, /*!< # */
    ALT_INT_INTERRUPT_CAN0_ECC_CORRECTED_IRQ   = 165, /*!< # */
    ALT_INT_INTERRUPT_CAN0_ECC_UNCORRECTED_IRQ = 166,
    /*!<
     * Interrupts sourced from the CAN Controller 0.
     *  * All interrupts in this group are level triggered.
     */

    ALT_INT_INTERRUPT_CAN1_STS_IRQ             = 167, /*!< # */
    ALT_INT_INTERRUPT_CAN1_MO_IRQ              = 168, /*!< # */
    ALT_INT_INTERRUPT_CAN1_ECC_CORRECTED_IRQ   = 169, /*!< # */
    ALT_INT_INTERRUPT_CAN1_ECC_UNCORRECTED_IRQ = 170,
    /*!<
     * Interrupts sourced from the CAN Controller 1.
     *  * All interrupts in this group are level triggered.
     */

    ALT_INT_INTERRUPT_SDMMC_IRQ                   = 171, /*!< # */
    ALT_INT_INTERRUPT_SDMMC_PORTA_ECC_CORRECTED   = 172, /*!< # */
    ALT_INT_INTERRUPT_SDMMC_PORTA_ECC_UNCORRECTED = 173, /*!< # */
    ALT_INT_INTERRUPT_SDMMC_PORTB_ECC_CORRECTED   = 174, /*!< # */
    ALT_INT_INTERRUPT_SDMMC_PORTB_ECC_UNCORRECTED = 175,
    /*!<
     * Interrupts sourced from the SDMMC Controller.
     *  * All interrupts in this group are level triggered.
     */

    ALT_INT_INTERRUPT_NAND_IRQ                  = 176, /*!< # */
    ALT_INT_INTERRUPT_NANDR_ECC_CORRECTED_IRQ   = 177, /*!< # */
    ALT_INT_INTERRUPT_NANDR_ECC_UNCORRECTED_IRQ = 178, /*!< # */
    ALT_INT_INTERRUPT_NANDW_ECC_CORRECTED_IRQ   = 179, /*!< # */
    ALT_INT_INTERRUPT_NANDW_ECC_UNCORRECTED_IRQ = 180, /*!< # */
    ALT_INT_INTERRUPT_NANDE_ECC_CORRECTED_IRQ   = 181, /*!< # */
    ALT_INT_INTERRUPT_NANDE_ECC_UNCORRECTED_IRQ = 182,
    /*!<
     * Interrupts sourced from the NAND Controller.
     *  * All interrupts in this group are level triggered.
     */

    ALT_INT_INTERRUPT_QSPI_IRQ                 = 183, /*!< # */
    ALT_INT_INTERRUPT_QSPI_ECC_CORRECTED_IRQ   = 184, /*!< # */
    ALT_INT_INTERRUPT_QSPI_ECC_UNCORRECTED_IRQ = 185,
    /*!<
     * Interrupts sourced from the QSPI Controller.
     *  * All interrupts in this group are level triggered.
     */

    ALT_INT_INTERRUPT_SPI0_IRQ = 186, /*!< # */
    ALT_INT_INTERRUPT_SPI1_IRQ = 187, /*!< # */
    ALT_INT_INTERRUPT_SPI2_IRQ = 188, /*!< # */
    ALT_INT_INTERRUPT_SPI3_IRQ = 189,
    /*!<
     * Interrupts sourced from the SPI Controllers 0 - 3.
     * SPI0_IRQ corresponds to SPIM0. SPI1_IRQ corresponds to SPIM1.
     * SPI2_IRQ corresponds to SPIS0. SPI3_IRQ corresponds to SPIS1.
     *  * All interrupts in this group are level triggered.
     */

    ALT_INT_INTERRUPT_I2C0_IRQ = 190, /*!< # */
    ALT_INT_INTERRUPT_I2C1_IRQ = 191, /*!< # */
    ALT_INT_INTERRUPT_I2C2_IRQ = 192, /*!< # */
    ALT_INT_INTERRUPT_I2C3_IRQ = 193,
    /*!<
     * Interrupts sourced from the I2C Controllers 0 - 3.
     *  * All interrupts in this group are level triggered.
     */

    ALT_INT_INTERRUPT_UART0 = 194, /*!< # */
    ALT_INT_INTERRUPT_UART1 = 195,
    /*!<
     * Interrupts sourced from the UARTs 0 - 1.
     *  * All interrupts in this group are level triggered.
     */

    ALT_INT_INTERRUPT_GPIO0 = 196, /*!< # */
    ALT_INT_INTERRUPT_GPIO1 = 197, /*!< # */
    ALT_INT_INTERRUPT_GPIO2 = 198,
    /*!<
     * Interrupts sourced from the GPIO 0 - 2.
     *  * All interrupts in this group are level triggered.
     */
    
    ALT_INT_INTERRUPT_TIMER_L4SP_0_IRQ = 199, /*!< # */
    ALT_INT_INTERRUPT_TIMER_L4SP_1_IRQ = 200, /*!< # */
    ALT_INT_INTERRUPT_TIMER_OSC1_0_IRQ = 201, /*!< # */
    ALT_INT_INTERRUPT_TIMER_OSC1_1_IRQ = 202,
    /*!<
     * Interrupts sourced from the Timer controllers.
     *  * All interrupts in this group are level triggered.
     */

    ALT_INT_INTERRUPT_WDOG0_IRQ = 203, /*!< # */
    ALT_INT_INTERRUPT_WDOG1_IRQ = 204,
    /*!<
     * Interrupts sourced from the Watchdog Timers 0 - 1.
     *  * All interrupts in this group are level triggered.
     */

    ALT_INT_INTERRUPT_CLKMGR_IRQ = 205,
    /*!<
     * Interrupts sourced from the Clock Manager.
     *  * All interrupts in this group are level triggered.
     */

    ALT_INT_INTERRUPT_MPUWAKEUP_IRQ = 206,
    /*!<
     * Interrupts sourced from the Clock Manager MPU Wakeup.
     *  * All interrupts in this group are level triggered.
     */

    ALT_INT_INTERRUPT_FPGA_MAN_IRQ = 207,
    /*!<
     * Interrupts sourced from the FPGA Manager.
     *  * All interrupts in this group are level triggered.
     */

    ALT_INT_INTERRUPT_NCTIIRQ0 = 208, /*!< # */
    ALT_INT_INTERRUPT_NCTIIRQ1 = 209,
    /*!<
     * Interrupts sourced from the CoreSight for CPU0 and CPU1's CTI.
     *  * All interrupts in this group are level triggered.
     */

    ALT_INT_INTERRUPT_RAM_ECC_CORRECTED_IRQ   = 210, /*!< # */
    ALT_INT_INTERRUPT_RAM_ECC_UNCORRECTED_IRQ = 211
    /*!<
     * Interrupts sourced from the On-chip RAM.
     *  * All interrupts in this group are level triggered.
     */

} ALT_INT_INTERRUPT_t;

/*!
 * This is the CPU target type. It is used to specify a set of CPUs on the
 * system. If only bit 0 is set then it specifies a set of CPUs containing
 * only CPU 0. Multiple CPUs can be specified by setting the appropriate bit
 * up to the number of CPUs on the system.
 */
typedef uint32_t alt_int_cpu_target_t;

/*!
 * This type definition enumerates all the interrupt trigger types.
 */
typedef enum ALT_INT_TRIGGER_e
{
    /*!
     * Edge triggered interrupt. This applies to Private Peripheral Interrupts
     * (PPI) and Shared Peripheral Interrupts (SPI) only, with interrupt IDs
     * 16 - 1019.
     */
    ALT_INT_TRIGGER_EDGE,

    /*!
     * Level triggered interrupt. This applies to Private Peripheral
     * Interrupts (PPI) and Shared Peripheral Interrupts (SPI) only, with
     * interrupt IDs 16 - 1019.
     */
    ALT_INT_TRIGGER_LEVEL,

    /*!
     * Software triggered interrupt. This applies to Software Generated
     * Interrupts (SGI) only, with interrupt IDs 0 - 15.
     */
    ALT_INT_TRIGGER_SOFTWARE,

    /*!
     * All triggering types except for those in the Shared Peripheral Interrupts
     * (SPI) F2S FPGA family interrupts can be determined by the system
     * automatically. In all functions which ask for the triggering type, the
     * ALT_INT_TRIGGER_AUTODETECT can be used to select the correct trigger
     * type for all non F2S interrupt types.
     */
    ALT_INT_TRIGGER_AUTODETECT,

    /*!
     * The interrupt triggering information is not applicable. This is possibly
     * due to querying an invalid interrupt identifier.
     */
    ALT_INT_TRIGGER_NA
}
ALT_INT_TRIGGER_t;

/*!
 * This type definition enumerates all the target list filter options. This is
 * used by the trigger Software Generated Interrupt (SGI) feature to issue a
 * SGI to the specified processor(s) in the system. Depending on the target
 * list filter and the target list, interrupts can be routed to any
 * combinations of CPUs.
 */
typedef enum ALT_INT_SGI_TARGET_e
{
    /*!
     * This filter list uses the target list parameter to specify which CPUs
     * to send the interrupt to. If target list is 0, no interrupts are sent.
     */
    ALT_INT_SGI_TARGET_LIST,

    /*!
     * This filter list sends the interrupt all CPUs except the current CPU.
     * The target list parameter is ignored.
     */
    ALT_INT_SGI_TARGET_ALL_EXCL_SENDER,

    /*!
     * This filter list sends the interrupt to the current CPU only. The
     * target list parameter is ignored.
     */
    ALT_INT_SGI_TARGET_SENDER_ONLY
}
ALT_INT_SGI_TARGET_t;

/*!
 * Extracts the CPUID field from the ICCIAR register.
 */
#define ALT_INT_ICCIAR_CPUID_GET(icciar)    ((icciar >> 10) & 0x7)

/*!
 * Extracts the ACKINTID field from the ICCIAR register.
 */
#define ALT_INT_ICCIAR_ACKINTID_GET(icciar) (icciar & 0x3FF)

/*!
 * The callback to use when an interrupt needs to be serviced.
 *
 * \param       icciar          The Interrupt Controller CPU Interrupt
 *                              Acknowledgement Register value (ICCIAR) value
 *                              corresponding to the current interrupt.
 *
 * \param       context         The user provided context.
 */
typedef void (*alt_int_callback_t)(uint32_t icciar, void * context);

/*!
 * @}
 */

#ifdef __cplusplus
}
#endif

#endif /* __ALT_INT_COMMON_H__ */
