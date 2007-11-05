/*
    FreeRTOS MCF5235 port - Copyright (C) 2006 Christian Walter.

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    FreeRTOS is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with FreeRTOS; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

    A special exception to the GPL can be applied should you wish to distribute
    a combined work that includes FreeRTOS, without being obliged to provide
    the source code for any proprietary components.  See the licensing section
    of http://www.FreeRTOS.org for full details of how and when the exception
    can be applied.

    ***************************************************************************
    See http://www.FreeRTOS.org for documentation, latest information, license
    and contact details.  Please ensure to read the configuration and relevant
    port sections of the online documentation.

	Also see http://www.SafeRTOS.com a version that has been certified for use
	in safety critical systems, plus commercial licensing, development and
	support options.
    ***************************************************************************
*/

#include "mcf5xxx.h"
#include "mcf523x.h"

/* Function prototypes */
void            init_main( void );
static void     disable_interrupts( void );
static void     disable_watchdog_timer( void );
static void     disable_cache( void );
static void     init_ipsbar( void );
static void     init_basics( void );
static void     init_clock_config( void );
static void     init_chip_selects( void );
static void     init_bus_config( void );
static void     init_cache( void );
static void     init_eport( void );
static void     init_flexcan( void );
static void     init_power_management( void );
static void     init_dma_timers( void );
static void     init_interrupt_timers( void );
static void     init_watchdog_timers( void );
static void     init_pin_assignments( void );
static void     init_sdram_controller( void );
static void     init_interrupt_controller( void );


/*********************************************************************
* init_main - Main entry point for initialisation code               *
**********************************************************************/
void
init_main( void )
{

    /* Initialise base address of peripherals, VBR, etc */
    init_ipsbar(  );
    init_basics(  );
    init_clock_config(  );

    /* Disable interrupts, watchdog timer, cache */
    disable_interrupts(  );
    disable_watchdog_timer(  );
    disable_cache(  );

    /* Initialise individual modules */
    init_chip_selects(  );
    init_bus_config(  );
    init_cache(  );
    init_eport(  );
    init_flexcan(  );
    init_power_management(  );
    init_dma_timers(  );
    init_interrupt_timers(  );
    init_watchdog_timers(  );
    init_pin_assignments(  );
    init_sdram_controller(  );

    /* Initialise interrupt controller */
    init_interrupt_controller(  );
}

/*********************************************************************
* disable_interrupts - Disable all interrupt sources                 *
**********************************************************************/
static void
disable_interrupts( void )
{
    vuint8         *p;
    int             i;


    /* Set ICR008-ICR063 to 0x0 */
    p = ( vuint8 * ) & MCF_INTC0_ICR8;
    for( i = 8; i <= 63; i++ )
        *p++ = 0x0;

    /* Set ICR108-ICR163 to 0x0 */
    p = ( vuint8 * ) & MCF_INTC1_ICR8;
    for( i = 108; i <= 163; i++ )
        *p++ = 0x0;
}


/*********************************************************************
* disable_watchdog_timer - Disable system watchdog timer             *
**********************************************************************/
static void
disable_watchdog_timer( void )
{

    /* Disable Core Watchdog Timer */
    MCF_SCM_CWCR = 0;
}

/*********************************************************************
* disable_cache - Disable and invalidate cache                       *
**********************************************************************/
static void
disable_cache( void )
{
    asm ( "move.l   #0x01000000, %d0" );
    asm ( "movec    %d0, %CACR" );
}

/*********************************************************************
* init_basics - Configuration Information & VBR                      *
**********************************************************************/
static void
init_basics( void )
{
    int             i;
    extern uint32   __RAMVEC[];
    extern uint32   __ROMVEC[];

    /* Transfer size not driven on SIZ[1:0] pins during external cycles
       Processor Status (PST) and Debug Data (DDATA) functions disabled
       Bus monitor disabled
       Output pads configured for full strength
     */
    MCF_CCM_CCR = ( 0x1 << 15 ) | MCF_CCM_CCR_BME;

    /* Set up RAM vectors */
    for( i = 0; i < 256; i++ )

    {
        __RAMVEC[i] = __ROMVEC[i];
    }
    asm( "move.l   %0,%%d0": :"i"( __RAMVEC ) );
    asm( "movec    %d0,%vbr" );
}


/*********************************************************************
* init_clock_config - Clock Module                                   *
**********************************************************************/
static void
init_clock_config( void )
{
    /* Clock module uses normal PLL mode with 25.0000 MHz external reference (Fref)
       MFD = 0, RFD = 1
       Bus clock frequency = 25.00 MHz
       Processor clock frequency = 2 x bus clock = 50.00 MHz
       Frequency Modulation disabled
       Loss of clock detection disabled
       Reset/Interrupt on loss of lock disabled
     */
    MCF_FMPLL_SYNCR = 0x00100000;       /* Set RFD=RFD+1 to avoid frequency overshoot */
    while( ( MCF_FMPLL_SYNSR & 0x08 ) == 0 )    /* Wait for PLL to lock */
        ;
    MCF_FMPLL_SYNCR = 0x00080000;       /* Set desired RFD */
    while( ( MCF_FMPLL_SYNSR & 0x08 ) == 0 )    /* Wait for PLL to lock */
        ;
}


/*********************************************************************
* init_ipsbar - Internal Peripheral System Base Address (IPSBAR)     *
**********************************************************************/
static void
init_ipsbar( void )
{
    extern int  __SRAM;

    /* Base address of internal peripherals (IPSBAR) = 0x40000000

       Note: Processor powers up with IPS base address = 0x40000000
       Write to IPS base + 0x00000000 to set new value
     */
    *( vuint32 * ) 0x40000000 = ( vuint32 ) __IPSBAR + 1;

    /* Configure RAMBAR in SCM module and allow dual-ported access. */
    MCF_SCM_RAMBAR = ( uint32 ) &__SRAM | MCF_SCM_RAMBAR_BDE;
}

/*********************************************************************
* init_chip_selects - Chip Select Module                             *
**********************************************************************/
static void
init_chip_selects( void )
{
    extern void __FLASH;
    uint32 FLASH_ADDR = (uint32)&__FLASH;

    /* Chip Select 0 - External Flash */
    MCF_CS_CSAR0 = MCF_CS_CSAR_BA( FLASH_ADDR );
    MCF_CS_CSCR0 = ( 0
                     | MCF_CS_CSCR_IWS( 6 )
                     | MCF_CS_CSCR_AA | MCF_CS_CSCR_PS_16 );
    MCF_CS_CSMR0 = MCF_CS_CSMR_BAM_2M | MCF_CS_CSMR_V;

    /* Chip Select 1 disabled (CSMR1[V] = 0) */
    MCF_CS_CSAR1 = 0;
    MCF_CS_CSMR1 = 0;
    MCF_CS_CSCR1 = 0;

    /* Chip Select 2 disabled (CSMR2[V] = 0) */
    MCF_CS_CSAR2 = 0;
    MCF_CS_CSMR2 = 0;
    MCF_CS_CSCR2 = 0;

    /* Chip Select 3 disabled (CSMR3[V] = 0) */
    MCF_CS_CSAR3 = 0;
    MCF_CS_CSMR3 = 0;
    MCF_CS_CSCR3 = 0;

    /* Chip Select 4 disabled (CSMR4[V] = 0) */
    MCF_CS_CSAR4 = 0;
    MCF_CS_CSMR4 = 0;
    MCF_CS_CSCR4 = 0;

    /* Chip Select 5 disabled (CSMR5[V] = 0) */
    MCF_CS_CSAR5 = 0;
    MCF_CS_CSMR5 = 0;
    MCF_CS_CSCR5 = 0;

    /* Chip Select 6 disabled (CSMR6[V] = 0) */
    MCF_CS_CSAR6 = 0;
    MCF_CS_CSMR6 = 0;
    MCF_CS_CSCR6 = 0;

    /* Chip Select 7 disabled (CSMR7[V] = 0) */
    MCF_CS_CSAR7 = 0;
    MCF_CS_CSMR7 = 0;
    MCF_CS_CSCR7 = 0;
}

/*********************************************************************
* init_bus_config - Internal Bus Arbitration                         *
**********************************************************************/
static void
init_bus_config( void )
{

    /* Use round robin arbitration scheme
       Assigned priorities (highest first):
       Ethernet
       DMA Controller
       ColdFire Core
       DMA bandwidth control disabled
       Park on last active bus master
     */
    MCF_SCM_MPARK =
        MCF_SCM_MPARK_M3_PRTY( 0x3 ) | MCF_SCM_MPARK_M2_PRTY( 0x2 ) |
        MCF_SCM_MPARK_M1_PRTY( 0x1 );
}

/*********************************************************************
* init_cache - Instruction/Data Cache                                *
**********************************************************************/
static void
init_cache( void )
{
    /* Configured as split cache: 4 KByte instruction cache and 4 Kbyte data cache
       ACR0: Don't cache accesses to 16 MB memory region at address $20000000
       ACR1: Don't cache accesses to 1 GB memory region at address $40000000
       CACR: Cache accesses to the rest of memory
    */
    asm("move.l   #0x80000000,%d0");
    asm("movec    %d0,%CACR");
    asm("move.l   #0x2000c040,%d0");
    asm("movec    %d0,%ACR0");
    asm("move.l   #0x403fc040,%d0");
    asm("movec    %d0,%ACR1");

    /* Instruction/Data cache disabled. */
    //asm( "move.l   #0x00000000, %d0" );
    //asm( "movec    %d0,%cacr" );
}

/*********************************************************************
* init_eport - Edge Port Module (EPORT)                              *
**********************************************************************/
static void
init_eport( void )
{

    /* Pins 1-7 configured as GPIO inputs */
    MCF_EPORT_EPPAR = 0;
    MCF_EPORT_EPDDR = 0;
    MCF_EPORT_EPIER = 0;
}

/*********************************************************************
* init_flexcan - FlexCAN Module                                      *
**********************************************************************/
static void
init_flexcan( void )
{

    /* FlexCAN controller 0 disabled (CANMCR0[MDIS]=1) */
    MCF_CAN_IMASK0 = 0;
    MCF_CAN_RXGMASK0 = MCF_CAN_RXGMASK_MI( 0x1fffffff );
    MCF_CAN_RX14MASK0 = MCF_CAN_RX14MASK_MI( 0x1fffffff );
    MCF_CAN_RX15MASK0 = MCF_CAN_RX15MASK_MI( 0x1fffffff );
    MCF_CAN_CANCTRL0 = 0;
    MCF_CAN_CANMCR0 =
        MCF_CAN_CANMCR_MDIS | MCF_CAN_CANMCR_FRZ | MCF_CAN_CANMCR_HALT |
        MCF_CAN_CANMCR_SUPV | MCF_CAN_CANMCR_MAXMB( 0xf );

    /* FlexCAN controller 1 disabled (CANMCR1[MDIS]=1) */
    MCF_CAN_IMASK1 = 0;
    MCF_CAN_RXGMASK1 = MCF_CAN_RXGMASK_MI( 0x1fffffff );
    MCF_CAN_RX14MASK1 = MCF_CAN_RX14MASK_MI( 0x1fffffff );
    MCF_CAN_RX15MASK1 = MCF_CAN_RX15MASK_MI( 0x1fffffff );
    MCF_CAN_CANCTRL1 = 0;
    MCF_CAN_CANMCR1 =
        MCF_CAN_CANMCR_MDIS | MCF_CAN_CANMCR_FRZ | MCF_CAN_CANMCR_HALT |
        MCF_CAN_CANMCR_SUPV | MCF_CAN_CANMCR_MAXMB( 0xf );
}

/*********************************************************************
* init_power_management - Power Management                           *
**********************************************************************/
static void
init_power_management( void )
{

    /* On executing STOP instruction, processor enters RUN mode
       Mode is exited when an interrupt of level 1 or higher is received
     */
    MCF_SCM_LPICR = MCF_SCM_LPICR_ENBSTOP;
    MCF_CCM_LPCR = 0;
}

/*********************************************************************
* init_sdram_controller - SDRAM Controller                           *
**********************************************************************/
static void
init_sdram_controller( void )
{
    extern void __SDRAM;
    uint32 SDRAM_ADDR = (uint32)&__SDRAM;
    int             i;


    /*
     * Check to see if the SDRAM has already been initialized
     * by a run control tool
     */
    if( !( MCF_SDRAMC_DACR0 & MCF_SDRAMC_DACR0_RE ) )
    {
        /* Initialize DRAM Control Register: DCR */
        MCF_SDRAMC_DCR = ( MCF_SDRAMC_DCR_RTIM( 1 ) |
                           MCF_SDRAMC_DCR_RC( ( 15 * FSYS_2 ) >> 4 ) );

        /* Initialize DACR0 */
        MCF_SDRAMC_DACR0 = ( MCF_SDRAMC_DACR0_BA( SDRAM_ADDR >> 18UL ) |
                             MCF_SDRAMC_DACR0_CASL( 1 ) |
                             MCF_SDRAMC_DACR0_CBM( 3 ) |
                             MCF_SDRAMC_DACR0_PS( 0 ) );

        /* Initialize DMR0 */
        MCF_SDRAMC_DMR0 = ( MCF_SDRAMC_DMR_BAM_16M | MCF_SDRAMC_DMR0_V );

        /* Set IP (bit 3) in DACR */
        MCF_SDRAMC_DACR0 |= MCF_SDRAMC_DACR0_IP;

        /* Wait 30ns to allow banks to precharge */
        for( i = 0; i < 5; i++ )
        {
            asm volatile    ( " nop" );
        }
        /* Write to this block to initiate precharge */
        *( uint32 * ) ( SDRAM_ADDR ) = 0xA5A59696;

        /* Set RE (bit 15) in DACR */
        MCF_SDRAMC_DACR0 |= MCF_SDRAMC_DACR0_RE;

        /* Wait for at least 8 auto refresh cycles to occur */
        for( i = 0; i < 2000; i++ )
        {
            asm volatile    ( "nop" );
        }
        /* Finish the configuration by issuing the IMRS. */
        MCF_SDRAMC_DACR0 |= MCF_SDRAMC_DACR0_MRS;

        /* Write to the SDRAM Mode Register */
        *( uint32 * ) ( SDRAM_ADDR + 0x400 ) = 0xA5A59696;
    }
}

/*********************************************************************
* init_dma_timers - DMA Timer Modules                                *
**********************************************************************/
static void
init_dma_timers( void )
{

    /* DMA Timer 0 disabled (DTMR0[RST] = 0) */
    MCF_TIMER_DTMR0 = 0;
    MCF_TIMER_DTXMR0 = 0;
    MCF_TIMER_DTRR0 = 0xffffffff;

    /* DMA Timer 1 disabled (DTMR1[RST] = 0) */
    MCF_TIMER_DTMR1 = 0;
    MCF_TIMER_DTXMR1 = 0;
    MCF_TIMER_DTRR1 = 0xffffffff;

    /* DMA Timer 2 disabled (DTMR2[RST] = 0) */
    MCF_TIMER_DTMR2 = 0;
    MCF_TIMER_DTXMR2 = 0;
    MCF_TIMER_DTRR2 = 0xffffffff;

    /* DMA Timer 3 disabled (DTMR3[RST] = 0) */
    MCF_TIMER_DTMR3 = 0;
    MCF_TIMER_DTXMR3 = 0;
    MCF_TIMER_DTRR3 = 0xffffffff;
}

/**********************************************************************
* init_interrupt_timers - Programmable Interrupt Timer (PIT) Modules  *
***********************************************************************/
static void
init_interrupt_timers( void )
{

    /* PIT0 disabled (PCSR0[EN]=0) */
    MCF_PIT_PCSR0 = 0;

    /* PIT1 disabled (PCSR1[EN]=0) */
    MCF_PIT_PCSR1 = 0;

    /* PIT2 disabled (PCSR2[EN]=0) */
    MCF_PIT_PCSR2 = 0;

    /* PIT3 disabled (PCSR3[EN]=0) */
    MCF_PIT_PCSR3 = 0;
}

/*********************************************************************
* init_watchdog_timers - Watchdog Timer Modules                      *
**********************************************************************/
static void
init_watchdog_timers( void )
{

    /* Watchdog Timer disabled (WCR[EN]=0)
       NOTE: WCR and WMR cannot be written again until after the
       processor is reset.
     */
    MCF_WTM_WCR = MCF_WTM_WCR_WAIT | MCF_WTM_WCR_DOZE | MCF_WTM_WCR_HALTED;
    MCF_WTM_WMR = 0xffff;

    /* Core Watchdog Timer disabled (CWCR[CWE]=0) */
    MCF_SCM_CWCR = 0;
}

/*********************************************************************
* init_interrupt_controller - Interrupt Controller                   *
**********************************************************************/
static void
init_interrupt_controller( void )
{

    /* Configured interrupt sources in order of priority...
       Level 7:  External interrupt /IRQ7, (initially masked)
       Level 6:  External interrupt /IRQ6, (initially masked)
       Level 5:  External interrupt /IRQ5, (initially masked)
       Level 4:  External interrupt /IRQ4, (initially masked)
       Level 3:  External interrupt /IRQ3, (initially masked)
       Level 2:  External interrupt /IRQ2, (initially masked)
       Level 1:  External interrupt /IRQ1, (initially masked)
     */
    MCF_INTC0_ICR1 = 0;
    MCF_INTC0_ICR2 = 0;
    MCF_INTC0_ICR3 = 0;
    MCF_INTC0_ICR4 = 0;
    MCF_INTC0_ICR5 = 0;
    MCF_INTC0_ICR6 = 0;
    MCF_INTC0_ICR7 = 0;
    MCF_INTC0_ICR8 = 0;
    MCF_INTC0_ICR9 = 0;
    MCF_INTC0_ICR10 = 0;
    MCF_INTC0_ICR11 = 0;
    MCF_INTC0_ICR12 = 0;
    MCF_INTC0_ICR13 = 0;
    MCF_INTC0_ICR14 = 0;
    MCF_INTC0_ICR15 = 0;
    MCF_INTC0_ICR17 = 0;
    MCF_INTC0_ICR18 = 0;
    MCF_INTC0_ICR19 = 0;
    MCF_INTC0_ICR20 = 0;
    MCF_INTC0_ICR21 = 0;
    MCF_INTC0_ICR22 = 0;
    MCF_INTC0_ICR23 = 0;
    MCF_INTC0_ICR24 = 0;
    MCF_INTC0_ICR25 = 0;
    MCF_INTC0_ICR26 = 0;
    MCF_INTC0_ICR27 = 0;
    MCF_INTC0_ICR28 = 0;
    MCF_INTC0_ICR29 = 0;
    MCF_INTC0_ICR30 = 0;
    MCF_INTC0_ICR31 = 0;
    MCF_INTC0_ICR32 = 0;
    MCF_INTC0_ICR33 = 0;
    MCF_INTC0_ICR34 = 0;
    MCF_INTC0_ICR35 = 0;
    MCF_INTC0_ICR36 = 0;
    MCF_INTC0_ICR37 = 0;
    MCF_INTC0_ICR38 = 0;
    MCF_INTC0_ICR39 = 0;
    MCF_INTC0_ICR40 = 0;
    MCF_INTC0_ICR41 = 0;
    MCF_INTC0_ICR42 = 0;
    MCF_INTC0_ICR43 = 0;
    MCF_INTC0_ICR44 = 0;
    MCF_INTC0_ICR45 = 0;
    MCF_INTC0_ICR46 = 0;
    MCF_INTC0_ICR47 = 0;
    MCF_INTC0_ICR48 = 0;
    MCF_INTC0_ICR49 = 0;
    MCF_INTC0_ICR50 = 0;
    MCF_INTC0_ICR51 = 0;
    MCF_INTC0_ICR52 = 0;
    MCF_INTC0_ICR53 = 0;
    MCF_INTC0_ICR54 = 0;
    MCF_INTC0_ICR55 = 0;
    MCF_INTC0_ICR56 = 0;
    MCF_INTC0_ICR57 = 0;
    MCF_INTC0_ICR58 = 0;
    MCF_INTC0_ICR59 = 0;
    MCF_INTC0_ICR60 = 0;
    MCF_INTC1_ICR8 = 0;
    MCF_INTC1_ICR9 = 0;
    MCF_INTC1_ICR10 = 0;
    MCF_INTC1_ICR11 = 0;
    MCF_INTC1_ICR12 = 0;
    MCF_INTC1_ICR13 = 0;
    MCF_INTC1_ICR14 = 0;
    MCF_INTC1_ICR15 = 0;
    MCF_INTC1_ICR16 = 0;
    MCF_INTC1_ICR17 = 0;
    MCF_INTC1_ICR18 = 0;
    MCF_INTC1_ICR19 = 0;
    MCF_INTC1_ICR20 = 0;
    MCF_INTC1_ICR21 = 0;
    MCF_INTC1_ICR22 = 0;
    MCF_INTC1_ICR23 = 0;
    MCF_INTC1_ICR24 = 0;
    MCF_INTC1_ICR25 = 0;
    MCF_INTC1_ICR27 = 0;
    MCF_INTC1_ICR28 = 0;
    MCF_INTC1_ICR29 = 0;
    MCF_INTC1_ICR30 = 0;
    MCF_INTC1_ICR31 = 0;
    MCF_INTC1_ICR32 = 0;
    MCF_INTC1_ICR33 = 0;
    MCF_INTC1_ICR34 = 0;
    MCF_INTC1_ICR35 = 0;
    MCF_INTC1_ICR36 = 0;
    MCF_INTC1_ICR37 = 0;
    MCF_INTC1_ICR38 = 0;
    MCF_INTC1_ICR39 = 0;
    MCF_INTC1_ICR40 = 0;
    MCF_INTC1_ICR41 = 0;
    MCF_INTC1_ICR42 = 0;
    MCF_INTC1_ICR59 = 0;
    MCF_INTC0_IMRH = 0xffffffff;
    MCF_INTC0_IMRL =
        MCF_INTC0_IMRL_INT_MASK31 | MCF_INTC0_IMRL_INT_MASK30 |
        MCF_INTC0_IMRL_INT_MASK29 | MCF_INTC0_IMRL_INT_MASK28 |
        MCF_INTC0_IMRL_INT_MASK27 | MCF_INTC0_IMRL_INT_MASK26 |
        MCF_INTC0_IMRL_INT_MASK25 | MCF_INTC0_IMRL_INT_MASK24 |
        MCF_INTC0_IMRL_INT_MASK23 | MCF_INTC0_IMRL_INT_MASK22 |
        MCF_INTC0_IMRL_INT_MASK21 | MCF_INTC0_IMRL_INT_MASK20 |
        MCF_INTC0_IMRL_INT_MASK19 | MCF_INTC0_IMRL_INT_MASK18 |
        MCF_INTC0_IMRL_INT_MASK17 | MCF_INTC0_IMRL_INT_MASK16 |
        MCF_INTC0_IMRL_INT_MASK15 | MCF_INTC0_IMRL_INT_MASK14 |
        MCF_INTC0_IMRL_INT_MASK13 | MCF_INTC0_IMRL_INT_MASK12 |
        MCF_INTC0_IMRL_INT_MASK11 | MCF_INTC0_IMRL_INT_MASK10 |
        MCF_INTC0_IMRL_INT_MASK9 | MCF_INTC0_IMRL_INT_MASK8 |
        MCF_INTC0_IMRL_INT_MASK7 | MCF_INTC0_IMRL_INT_MASK6 |
        MCF_INTC0_IMRL_INT_MASK5 | MCF_INTC0_IMRL_INT_MASK4 |
        MCF_INTC0_IMRL_INT_MASK3 | MCF_INTC0_IMRL_INT_MASK2 |
        MCF_INTC0_IMRL_INT_MASK1;
    MCF_INTC1_IMRH = 0xffffffff;
    MCF_INTC1_IMRL =
        MCF_INTC1_IMRL_INT_MASK31 | MCF_INTC1_IMRL_INT_MASK30 |
        MCF_INTC1_IMRL_INT_MASK29 | MCF_INTC1_IMRL_INT_MASK28 |
        MCF_INTC1_IMRL_INT_MASK27 | MCF_INTC1_IMRL_INT_MASK26 |
        MCF_INTC1_IMRL_INT_MASK25 | MCF_INTC1_IMRL_INT_MASK24 |
        MCF_INTC1_IMRL_INT_MASK23 | MCF_INTC1_IMRL_INT_MASK22 |
        MCF_INTC1_IMRL_INT_MASK21 | MCF_INTC1_IMRL_INT_MASK20 |
        MCF_INTC1_IMRL_INT_MASK19 | MCF_INTC1_IMRL_INT_MASK18 |
        MCF_INTC1_IMRL_INT_MASK17 | MCF_INTC1_IMRL_INT_MASK16 |
        MCF_INTC1_IMRL_INT_MASK15 | MCF_INTC1_IMRL_INT_MASK14 |
        MCF_INTC1_IMRL_INT_MASK13 | MCF_INTC1_IMRL_INT_MASK12 |
        MCF_INTC1_IMRL_INT_MASK11 | MCF_INTC1_IMRL_INT_MASK10 |
        MCF_INTC1_IMRL_INT_MASK9 | MCF_INTC1_IMRL_INT_MASK8 |
        MCF_INTC1_IMRL_INT_MASK7 | MCF_INTC1_IMRL_INT_MASK6 |
        MCF_INTC1_IMRL_INT_MASK5 | MCF_INTC1_IMRL_INT_MASK4 |
        MCF_INTC1_IMRL_INT_MASK3 | MCF_INTC1_IMRL_INT_MASK2 |
        MCF_INTC1_IMRL_INT_MASK1;
}

/*********************************************************************
* init_pin_assignments - Pin Assignment and General Purpose I/O      *
**********************************************************************/
static void
init_pin_assignments( void )
{

    /* Pin assignments for port ADDR
       Pins are all GPIO inputs
     */
    MCF_GPIO_PDDR_APDDR = 0;
    MCF_GPIO_PAR_AD = MCF_GPIO_PAR_AD_PAR_ADDR23
        | MCF_GPIO_PAR_AD_PAR_ADDR22
        | MCF_GPIO_PAR_AD_PAR_ADDR21 | MCF_GPIO_PAR_AD_PAR_DATAL;

    /* Pin assignments for ports DATAH and DATAL
       Pins are all GPIO inputs
     */
    MCF_GPIO_PDDR_DATAH = 0;
    MCF_GPIO_PDDR_DATAL = 0;

    /* Pin assignments for port BUSCTL
       Pin /OE        : External bus output enable, /OE
       Pin /TA        : External bus transfer acknowledge, /TA
       Pin /TEA       : External bus transfer error acknowledge, /TEA
       Pin R/W        : External bus read/write indication, R/W
       Pin TSIZ1      : External bus transfer size TSIZ1 or DMA acknowledge /DACK1
       Pin TSIZ0      : External bus transfer size TSIZ0 or DMA acknowledge /DACK0
       Pin /TS        : External bus transfer start, /TS
       Pin /TIP       : External bus transfer in progess, /TIP
     */
    MCF_GPIO_PDDR_BUSCTL = 0;
    MCF_GPIO_PAR_BUSCTL =
        MCF_GPIO_PAR_BUSCTL_PAR_OE | MCF_GPIO_PAR_BUSCTL_PAR_TA |
        MCF_GPIO_PAR_BUSCTL_PAR_TEA( 0x3 ) | MCF_GPIO_PAR_BUSCTL_PAR_RWB |
        MCF_GPIO_PAR_BUSCTL_PAR_TSIZ1 | MCF_GPIO_PAR_BUSCTL_PAR_TSIZ0 |
        MCF_GPIO_PAR_BUSCTL_PAR_TS( 0x3 ) |
        MCF_GPIO_PAR_BUSCTL_PAR_TIP( 0x3 );

    /* Pin assignments for port BS
       Pin /BS3       : External byte strobe /BS3
       Pin /BS2       : External byte strobe /BS2
       Pin /BS1       : External byte strobe /BS1
       Pin /BS0       : External byte strobe /BS0
     */
    MCF_GPIO_PDDR_BS = 0;
    MCF_GPIO_PAR_BS =
        MCF_GPIO_PAR_BS_PAR_BS3 | MCF_GPIO_PAR_BS_PAR_BS2 |
        MCF_GPIO_PAR_BS_PAR_BS1 | MCF_GPIO_PAR_BS_PAR_BS0;

    /* Pin assignments for port CS
       Pin /CS7       : Chip select /CS7
       Pin /CS6       : Chip select /CS6
       Pin /CS5       : Chip select /CS5
       Pin /CS4       : Chip select /CS4
       Pin /CS3       : Chip select /CS3
       Pin /CS2       : Chip select /CS2
       Pin /CS1       : Chip select /CS1
     */
    MCF_GPIO_PDDR_CS = 0;
    MCF_GPIO_PAR_CS =
        MCF_GPIO_PAR_CS_PAR_CS7 | MCF_GPIO_PAR_CS_PAR_CS6 |
        MCF_GPIO_PAR_CS_PAR_CS5 | MCF_GPIO_PAR_CS_PAR_CS4 |
        MCF_GPIO_PAR_CS_PAR_CS3 | MCF_GPIO_PAR_CS_PAR_CS2 |
        MCF_GPIO_PAR_CS_PAR_CS1;

    /* Pin assignments for port SDRAM
       Pin /SD_WE     : SDRAM controller /SD_WE
       Pin /SD_SCAS   : SDRAM controller /SD_SCAS
       Pin /SD_SRAS   : SDRAM controller /SD_SRAS
       Pin /SD_SCKE   : SDRAM controller /SD_SCKE
       Pin /SD_CS1    : SDRAM controller /SD_CS1
       Pin /SD_CS0    : SDRAM controller /SD_CS0
     */
    MCF_GPIO_PDDR_SDRAM = 0;
    MCF_GPIO_PAR_SDRAM =
        MCF_GPIO_PAR_SDRAM_PAR_SDWE | MCF_GPIO_PAR_SDRAM_PAR_SCAS |
        MCF_GPIO_PAR_SDRAM_PAR_SRAS | MCF_GPIO_PAR_SDRAM_PAR_SCKE |
        MCF_GPIO_PAR_SDRAM_PAR_SDCS1 | MCF_GPIO_PAR_SDRAM_PAR_SDCS0;

    /* Pin assignments for port FECI2C
       Pins are all GPIO inputs
     */
    MCF_GPIO_PDDR_FECI2C = 0;
    MCF_GPIO_PAR_FECI2C =
        MCF_GPIO_PAR_FECI2C_PAR_EMDC_FEC | MCF_GPIO_PAR_FECI2C_PAR_EMDIO_FEC;

    /* Pin assignments for port UARTL
       Pins are all GPIO inputs
     */
    MCF_GPIO_PDDR_UARTL = 0;
    MCF_GPIO_PAR_UART = 0;

    /* Pin assignments for port UARTH
       Pin U2TXD      : GPIO input
       Pin U2RXD      : GPIO input
       Pin /IRQ2      : Interrupt request /IRQ2 or GPIO
     */
    MCF_GPIO_PDDR_UARTH = 0;

    /* Pin assignments for port QSPI
       Pins are all GPIO inputs
     */
    MCF_GPIO_PDDR_QSPI = 0;
    MCF_GPIO_PAR_QSPI = 0;

    /* Pin assignments for port TIMER
       Pins are all GPIO inputs
     */
    MCF_GPIO_PDDR_TIMER = 0;
    MCF_GPIO_PAR_TIMER = 0;

    /* Pin assignments for port ETPU
       Pins are all GPIO inputs
     */
    MCF_GPIO_PDDR_ETPU = 0;
    MCF_GPIO_PAR_ETPU = 0;
}
