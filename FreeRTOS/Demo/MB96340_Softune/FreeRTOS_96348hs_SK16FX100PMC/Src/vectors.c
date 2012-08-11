/* THIS SAMPLE CODE IS PROVIDED AS IS AND IS SUBJECT TO ALTERATIONS. FUJITSU */
/* MICROELECTRONICS ACCEPTS NO RESPONSIBILITY OR LIABILITY FOR ANY ERRORS OR */
/* ELIGIBILITY FOR ANY PURPOSES.                                             */
/*                 (C) Fujitsu Microelectronics Europe GmbH                  */

/*---------------------------------------------------------------------------
  VECTORS.C
  - Interrupt level (priority) setting
  - Interrupt vector definition
-----------------------------------------------------------------------------*/
#include "mb96348hs.h"
#include "FreeRTOSConfig.h"

/*---------------------------------------------------------------------------
   InitIrqLevels()
   This function  pre-sets all interrupt control registers. It can be used
   to set all interrupt priorities in static applications. If this file
   contains assignments to dedicated resources, verify  that the
   appropriate controller is used.
   NOTE: value 7 disables the interrupt and value 0 sets highest priority.
-----------------------------------------------------------------------------*/
#define MIN_ICR				12
#define MAX_ICR				96

#define DEFAULT_ILM_MASK	7

void InitIrqLevels( void )
{
volatile int irq;

	for( irq = MIN_ICR; irq <= MAX_ICR; irq++ )
	{
		ICR = ( irq << 8 ) | DEFAULT_ILM_MASK;
	}

	ICR = ( (51 & 0xFF) << 8 ) | configKERNEL_INTERRUPT_PRIORITY;			/* Reload Timer 0 of MB9634x Series */
	ICR = ( (12 & 0xFF) << 8 ) | configKERNEL_INTERRUPT_PRIORITY;			/* Delayed interrupt of 16FX Family */

	ICR = ( 79 << 8 ) | configKERNEL_INTERRUPT_PRIORITY;				/* UART 0 Rx of MB9634x Series */
	ICR = ( 80 << 8 ) | configKERNEL_INTERRUPT_PRIORITY;				/* UART 0 Tx of MB9634x Series */
}

/*---------------------------------------------------------------------------
   Prototypes
   Add your own prototypes here. Each vector definition needs is proto-
   type. Either do it here or include a header file containing them.
-----------------------------------------------------------------------------*/
__interrupt void		DefaultIRQHandler( void );

extern __interrupt void prvRLT0_TICKISR( void );

extern __interrupt void UART0_RxISR( void );
extern __interrupt void UART0_TxISR( void );
extern __interrupt void UART0_TraceRxISR( void );
extern __interrupt void vPortYield( void );
extern __interrupt void vPortYieldDelayed( void );

#if ( INCLUDE_TraceListTasks == 1 )
	extern __interrupt void UART1_RxISR( void );
#endif

/*---------------------------------------------------------------------------
   Vector definiton for MB9634x
   Use following statements to define vectors. All resource related
   vectors are predefined. Remaining software interrupts can be added here
   as well.
   NOTE: If software interrupts 0 to 7 are defined here, this might 
   conflict with the reset vector in the start-up file.
-----------------------------------------------------------------------------*/
#pragma intvect DefaultIRQHandler 11		/* Non-maskable Interrupt       */

#pragma intvect vPortYieldDelayed 12		/* Delayed Interrupt            */

#pragma intvect DefaultIRQHandler 13		/* RC Timer                     */
#pragma intvect DefaultIRQHandler 14		/* Main Clock Timer             */
#pragma intvect DefaultIRQHandler 15		/* Sub Clock Timer              */
#pragma intvect DefaultIRQHandler 16		/* Reserved                     */
#pragma intvect DefaultIRQHandler 17		/* EXT0                         */
#pragma intvect DefaultIRQHandler 18		/* EXT1                         */
#pragma intvect DefaultIRQHandler 19		/* EXT2                         */
#pragma intvect DefaultIRQHandler 20		/* EXT3                         */
#pragma intvect DefaultIRQHandler 21		/* EXT4                         */
#pragma intvect DefaultIRQHandler 22		/* EXT5                         */
#pragma intvect DefaultIRQHandler 23		/* EXT6                         */
#pragma intvect DefaultIRQHandler 24		/* EXT7                         */
#pragma intvect DefaultIRQHandler 25		/* EXT8                         */
#pragma intvect DefaultIRQHandler 26		/* EXT9                         */
#pragma intvect DefaultIRQHandler 27		/* EXT10                        */
#pragma intvect DefaultIRQHandler 28		/* EXT11                        */
#pragma intvect DefaultIRQHandler 29		/* EXT12                        */
#pragma intvect DefaultIRQHandler 30		/* EXT13                        */
#pragma intvect DefaultIRQHandler 31		/* EXT14                        */
#pragma intvect DefaultIRQHandler 32		/* EXT15                        */
#pragma intvect DefaultIRQHandler 33		/* CAN0                         */
#pragma intvect DefaultIRQHandler 34		/* CAN1                         */
#pragma intvect DefaultIRQHandler 35		/* PPG0                         */
#pragma intvect DefaultIRQHandler 36		/* PPG1                         */
#pragma intvect DefaultIRQHandler 37		/* PPG2                         */
#pragma intvect DefaultIRQHandler 38		/* PPG3                         */
#pragma intvect DefaultIRQHandler 39		/* PPG4                         */
#pragma intvect DefaultIRQHandler 40		/* PPG5                         */
#pragma intvect DefaultIRQHandler 41		/* PPG6                         */
#pragma intvect DefaultIRQHandler 42		/* PPG7                         */
#pragma intvect DefaultIRQHandler 43		/* PPG8                         */
#pragma intvect DefaultIRQHandler 44		/* PPG9                         */
#pragma intvect DefaultIRQHandler 45		/* PPG10                        */
#pragma intvect DefaultIRQHandler 46		/* PPG11                        */
#pragma intvect DefaultIRQHandler 47		/* PPG12                        */
#pragma intvect DefaultIRQHandler 48		/* PPG13                        */
#pragma intvect DefaultIRQHandler 49		/* PPG14                        */
#pragma intvect DefaultIRQHandler 50		/* PPG15                        */

#pragma intvect prvRLT0_TICKISR 51			/* RLT0                         */

#pragma intvect DefaultIRQHandler 52		/* RLT1                         */
#pragma intvect DefaultIRQHandler 53		/* RLT2                         */
#pragma intvect DefaultIRQHandler 54		/* RLT3                         */
#pragma intvect DefaultIRQHandler 55		/* PPGRLT - RLT6                */
#pragma intvect DefaultIRQHandler 56		/* ICU0                         */
#pragma intvect DefaultIRQHandler 57		/* ICU1                         */
#pragma intvect DefaultIRQHandler 58		/* ICU2                         */
#pragma intvect DefaultIRQHandler 59		/* ICU3                         */
#pragma intvect DefaultIRQHandler 60		/* ICU4                         */
#pragma intvect DefaultIRQHandler 61		/* ICU5                         */
#pragma intvect DefaultIRQHandler 62		/* ICU6                         */
#pragma intvect DefaultIRQHandler 63		/* ICU7                         */
#pragma intvect DefaultIRQHandler 64		/* OCU0                         */
#pragma intvect DefaultIRQHandler 65		/* OCU1                         */
#pragma intvect DefaultIRQHandler 66		/* OCU2                         */
#pragma intvect DefaultIRQHandler 67		/* OCU3                         */
#pragma intvect DefaultIRQHandler 68		/* OCU4                         */
#pragma intvect DefaultIRQHandler 69		/* OCU5                         */
#pragma intvect DefaultIRQHandler 70		/* OCU6                         */
#pragma intvect DefaultIRQHandler 71		/* OCU7                         */
#pragma intvect DefaultIRQHandler 72		/* FRT0                         */
#pragma intvect DefaultIRQHandler 73		/* FRT1                         */
#pragma intvect DefaultIRQHandler 74		/* I2C0                         */
#pragma intvect DefaultIRQHandler 75		/* I2C1                         */
#pragma intvect DefaultIRQHandler 76		/* ADC                          */
#pragma intvect DefaultIRQHandler 77		/* ALARM0                       */
#pragma intvect DefaultIRQHandler 78		/* ALARM1                       */

#if ( INCLUDE_TraceListTasks == 1 )  
	#pragma intvect UART0_TraceRxISR       79   /* LIN-UART 0 RX                */	
	#pragma intvect DefaultIRQHandler       80   /* LIN-UART 0 TX                */
#else
	#pragma intvect UART0_RxISR 79   /* LIN-UART 0 RX                */
	#pragma intvect UART0_TxISR 80   /* LIN-UART 0 TX                */
#endif

#pragma intvect DefaultIRQHandler 81	/* LIN-UART 1 RX                */
#pragma intvect DefaultIRQHandler 82		/* LIN-UART 1 TX                */
#pragma intvect DefaultIRQHandler 83		/* LIN-UART 2 RX                */
#pragma intvect DefaultIRQHandler 84		/* LIN-UART 2 TX                */
#pragma intvect DefaultIRQHandler 85		/* LIN-UART 3 RX                */
#pragma intvect DefaultIRQHandler 86		/* LIN-UART 3 TX                */
#pragma intvect DefaultIRQHandler 87		/* MAIN FLASH IRQ               */
#pragma intvect DefaultIRQHandler 88		/* SATELLITE FLASH IRQ (not on all devices) */
#pragma intvect DefaultIRQHandler 89		/* LIN-UART 7 RX (not on all devices) */
#pragma intvect DefaultIRQHandler 90		/* LIN-UART 7 TX (not on all devices) */
#pragma intvect DefaultIRQHandler 91		/* LIN-UART 8 RX (not on all devices) */
#pragma intvect DefaultIRQHandler 92		/* LIN-UART 8 TX (not on all devices) */
#pragma intvect DefaultIRQHandler 93		/* LIN-UART 9 RX (not on all devices) */
#pragma intvect DefaultIRQHandler 94		/* LIN-UART 9 TX (not on all devices) */
#pragma intvect DefaultIRQHandler 95		/* RTC (not on all devices)     */
#pragma intvect DefaultIRQHandler 96		/* CAL (not on all devices)     */

#pragma intvect vPortYield 122				/* INT #122       */

/*---------------------------------------------------------------------------
   DefaultIRQHandler()
   This function is a placeholder for all vector definitions. Either use
   your own placeholder or add necessary code here. 
-----------------------------------------------------------------------------*/
__interrupt void DefaultIRQHandler( void )
{
	__DI();				/* disable interrupts */
	while( 1 )
	{
		__wait_nop();	/* halt system */
	}
}
