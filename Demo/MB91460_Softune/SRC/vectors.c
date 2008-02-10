/* THIS SAMPLE CODE IS PROVIDED AS IS AND IS SUBJECT TO ALTERATIONS. FUJITSU */
/* MICROELECTRONICS ACCEPTS NO RESPONSIBILITY OR LIABILITY FOR ANY ERRORS OR */
/* ELIGIBILITY FOR ANY PURPOSES.											 */
/*				 (C) Fujitsu Microelectronics Europe GmbH				  */
/*------------------------------------------------------------------------
  VECTORS.C
  - Interrupt level (priority) setting
  - Interrupt vector definition

  31.04.05  1.00   UMa	Initial Version
  08.11.05  1.01   MSt	SWB Mondeb switch for ICR00 Register added
  27.02.06  1.02   UMa	added comment in DefaultIRQHandler 
  17.03.06  1.03   UMa	comment out ICR01
  28.07.06  1.04   UMa	changed comment
  06.10.06  1.05   UMa	changed DefaultIRQHandler
-------------------------------------------------------------------------*/

#include "mb91467d.h"
#include "watchdog.h"

/*------------------------------------------------------------------------
  InitIrqLevels()

  This function  pre-sets all interrupt control registers. It can be used
  to set all interrupt priorities in static applications. If this file
  contains assignments to dedicated resources, verify  that the
  appropriate controller is used. Not all devices of the MB91460 Series
  offer all recources.

  NOTE: value 31 disables the interrupt and value 16 sets highest priority.
-------------------------------------------------------------------------*/
void InitIrqLevels(void)
{
	/*  ICRxx */ 
	/* Softune Workbench Monitor Debugger is using ext int0 for abort function */
	/*  ICR00 = 31;  *//* External Interrupt 0		 */
					/* External Interrupt 1		*/				 
	ICR01 = 31;		/* External Interrupt 2		*/
					/* External Interrupt 3		*/
	ICR02 = 31;		/* External Interrupt 4		*/
					/* External Interrupt 5		*/
	ICR03 = 31;		/* External Interrupt 6		*/
					/* External Interrupt 7		*/
	ICR04 = 31;		/* External Interrupt 8		*/
					/* External Interrupt 9		*/
	ICR05 = 31;		/* External Interrupt 10	*/
					/* External Interrupt 11	*/
	ICR06 = 31;		/* External Interrupt 12	*/
					/* External Interrupt 13	*/
	ICR07 = 31;		/* External Interrupt 14	*/
					/* External Interrupt 15	*/
	ICR08 = 23;		/* Reload Timer 0			*/
					/* Reload Timer 1			*/
	ICR09 = 31;		/* Reload Timer 2			*/
					/* Reload Timer 3			*/
	ICR10 = 31;		/* Reload Timer 4			*/
					/* Reload Timer 5			*/
	ICR11 = 31;		/* Reload Timer 6			*/
					/* Reload Timer 7			*/
	ICR12 = 31;		/* Free Run Timer 0			*/
					/* Free Run Timer 1			*/
	ICR13 = 31;		/* Free Run Timer 2			*/
					/* Free Run Timer 3			*/
	ICR14 = 31;		/* Free Run Timer 4			*/
					/* Free Run Timer 5			*/
	ICR15 = 31;		/* Free Run Timer 6			*/
					/* Free Run Timer 7			*/
	ICR16 = 31;		/* CAN 0					*/
					/* CAN 1					*/
	ICR17 = 31;		/* CAN 2					*/
					/* CAN 3					*/
	ICR18 = 31;		/* CAN 4					*/
					/* CAN 5					*/
	ICR19 = 31;		/* USART (LIN) 0 RX			*/
					/* USART (LIN) 0 TX			*/
	ICR20 = 31;		/* USART (LIN) 1 RX			*/
					/* USART (LIN) 1 TX			*/
	ICR21 = 21;		/* USART (LIN) 2 RX			*/
					/* USART (LIN) 2 TX			*/
	ICR22 = 31;		/* USART (LIN) 3 RX			*/
					/* USART (LIN) 3 TX			*/
	ICR23 = 23;		/* System Reserved			*/
					/* Delayed Interrupt		*/
	ICR24 = 31;		/* System Reserved			*/
					/* System Reserved			*/
	ICR25 = 31;		/* USART (LIN, FIFO) 4 RX	*/
					/* USART (LIN, FIFO) 4 TX	*/
	ICR26 = 21;		/* USART (LIN, FIFO) 5 RX	*/
					/* USART (LIN, FIFO) 5 TX	*/
	ICR27 = 31;		/* USART (LIN, FIFO) 6 RX	*/
					/* USART (LIN, FIFO) 6 TX	*/
	ICR28 = 31;		/* USART (LIN, FIFO) 7 RX	*/
					/* USART (LIN, FIFO) 7 TX	*/
	ICR29 = 31;		/* I2C 0 / I2C 2			*/
					/* I2C 1 / I2C 3			*/
	ICR30 = 31;		/* USART (LIN, FIFO) 8 RX	*/
					/* USART (LIN, FIFO) 8 TX	*/
	ICR31 = 31;		/* USART (LIN, FIFO) 9 RX	*/
					/* USART (LIN, FIFO) 9 TX	*/
	ICR32 = 31;		/* USART (LIN, FIFO) 10 RX	*/
					/* USART (LIN, FIFO) 10 TX	*/
	ICR33 = 31;		/* USART (LIN, FIFO) 11 RX	*/
					/* USART (LIN, FIFO) 11 TX	*/
	ICR34 = 31;		/* USART (LIN, FIFO) 12 RX	*/
					/* USART (LIN, FIFO) 12 TX	*/
	ICR35 = 31;		/* USART (LIN, FIFO) 13 RX	*/
					/* USART (LIN, FIFO) 13 TX	*/
	ICR36 = 31;		/* USART (LIN, FIFO) 14 RX	*/
					/* USART (LIN, FIFO) 14 TX	*/
	ICR37 = 31;		/* USART (LIN, FIFO) 15 RX	*/
					/* USART (LIN, FIFO) 15 TX	*/
	ICR38 = 31;		/* Input Capture 0			*/
					/* Input Capture 1			*/
	ICR39 = 31;		/* Input Capture 2			*/
					/* Input Capture 3			*/
	ICR40 = 31;		/* Input Capture 4			*/
					/* Input Capture 5			*/
	ICR41 = 31;		/* Input Capture 6			*/
					/* Input Capture 7			*/
	ICR42 = 31;		/* Output Compare 0			*/
					/* Output Compare 1			*/
	ICR43 = 31;		/* Output Compare 2			*/
					/* Output Compare 3			*/
	ICR44 = 31;		/* Output Compare 4			*/
					/* Output Compare 5			*/
	ICR45 = 31;		/* Output Compare 6			*/
					/* Output Compare 7			*/
	ICR46 = 31;		/* Sound Generator			*/
					/* Phase Frequ. Modulator	*/
	ICR47 = 31;		/* System Reserved			*/
					/* System Reserved			*/
	ICR48 = 31;		/* Prog. Pulse Gen. 0		*/
					/* Prog. Pulse Gen. 1		*/
	ICR49 = 31;		/* Prog. Pulse Gen. 2		*/
					/* Prog. Pulse Gen. 3		*/
	ICR50 = 31;		/* Prog. Pulse Gen. 4		*/
					/* Prog. Pulse Gen. 5		*/
	ICR51 = 31;		/* Prog. Pulse Gen. 6		*/
					/* Prog. Pulse Gen. 7		*/
	ICR52 = 31;		/* Prog. Pulse Gen. 8		*/
					/* Prog. Pulse Gen. 9		*/
	ICR53 = 31;		/* Prog. Pulse Gen. 10		*/
					/* Prog. Pulse Gen. 11		*/
	ICR54 = 31;		/* Prog. Pulse Gen. 12		*/
					/* Prog. Pulse Gen. 13		*/
	ICR55 = 31;		/* Prog. Pulse Gen. 14		*/
					/* Prog. Pulse Gen. 15		*/
	ICR56 = 31;		/* Up/Down Counter 0		*/
					/* Up/Down Counter 1		*/
	ICR57 = 31;		/* Up/Down Counter 2		*/
					/* Up/Down Counter 3		*/
	ICR58 = 31;		/* Real Time Clock			*/
					/* Calibration Unit			*/
	ICR59 = 31;		/* A/D Converter 0			*/
					/* -						*/
	ICR60 = 31;		/* Alarm Comperator 0		*/
					/* Alarm Comperator 1		*/
	ICR61 = 31;		/* Low Volage Detector		*/
					/* SMC Zero Point 0-5		*/
	ICR62 = 31;		/* Timebase Overflow		*/
					/* PLL Clock Gear			*/
	ICR63 = 31;		/* DMA Controller			*/
					/* Main/Sub OSC stability wait  */
}


/*------------------------------------------------------------------------
  Prototypes
  
  Add your own prototypes here. Each vector definition needs is proto-
  type. Either do it here or include a header file containing them.
-------------------------------------------------------------------------*/
__interrupt void DefaultIRQHandler (void);
extern __interrupt void ReloadTimer0_IRQHandler ( void );
extern __interrupt void vPortYield ( void );
extern __interrupt void vPortYieldDelayed (void);

extern __interrupt void UART2_RxISR(void);
extern __interrupt void UART2_TxISR(void);
extern __interrupt void UART5_RxISR(void);

/*------------------------------------------------------------------------
   Vector definiton

   Use following statements to define vectors. All resource related
   vectors are predefined. Remaining software interrupts can be added here
   as well.
------------------------------------------------------------------------*/
#pragma intvect 0xBFF8			0	 /* (fixed) reset vector		*/
#pragma intvect 0x06000000		1	 /* (fixed) Mode Byte			*/

#pragma intvect DefaultIRQHandler 15	/* Non Maskable Interrupt	*/
#pragma intvect DefaultIRQHandler 16	/* External Interrupt 0		*/
#pragma intvect DefaultIRQHandler 17	/* External Interrupt 1		*/

#pragma intvect DefaultIRQHandler 18	/* External Interrupt 2		*/

#pragma intvect DefaultIRQHandler 19	/* External Interrupt 3		*/
#pragma intvect DefaultIRQHandler 20	/* External Interrupt 4		*/
#pragma intvect DefaultIRQHandler 21	/* External Interrupt 5		*/
#pragma intvect DefaultIRQHandler 22	/* External Interrupt 6		*/
#pragma intvect DefaultIRQHandler 23	/* External Interrupt 7		*/
#pragma intvect DefaultIRQHandler 24	/* External Interrupt 8		*/
#pragma intvect DefaultIRQHandler 25	/* External Interrupt 9		*/
#pragma intvect DefaultIRQHandler 26	/* External Interrupt 10	*/
#pragma intvect DefaultIRQHandler 27	/* External Interrupt 11	*/
#pragma intvect DefaultIRQHandler 28	/* External Interrupt 12	*/
#pragma intvect DefaultIRQHandler 29	/* External Interrupt 13	*/
#pragma intvect DefaultIRQHandler 30	/* External Interrupt 14	*/
#pragma intvect DefaultIRQHandler 31	/* External Interrupt 15	*/

#pragma intvect ReloadTimer0_IRQHandler 32	/* Reload Timer 0		*/

#pragma intvect DefaultIRQHandler 33	/* Reload Timer 1			*/
#pragma intvect DefaultIRQHandler 34	/* Reload Timer 2			*/
#pragma intvect DefaultIRQHandler 35	/* Reload Timer 3			*/
#pragma intvect DefaultIRQHandler 36	/* Reload Timer 4			*/
#pragma intvect DefaultIRQHandler 37	/* Reload Timer 5			*/
#pragma intvect DefaultIRQHandler 38	/* Reload Timer 6			*/
#pragma intvect DefaultIRQHandler 39	/* Reload Timer 7			*/
#pragma intvect DefaultIRQHandler 40	/* Free Run Timer 0			*/
#pragma intvect DefaultIRQHandler 41	/* Free Run Timer 1			*/
#pragma intvect DefaultIRQHandler 42	/* Free Run Timer 2			*/
#pragma intvect DefaultIRQHandler 43	/* Free Run Timer 3			*/
#pragma intvect DefaultIRQHandler 44	/* Free Run Timer 4			*/
#pragma intvect DefaultIRQHandler 45	/* Free Run Timer 5			*/
#pragma intvect DefaultIRQHandler 46	/* Free Run Timer 6			*/
#pragma intvect DefaultIRQHandler 47	/* Free Run Timer 7			*/
#pragma intvect DefaultIRQHandler 48	/* CAN 0					*/
#pragma intvect DefaultIRQHandler 49	/* CAN 1					*/
#pragma intvect DefaultIRQHandler 50	/* CAN 2					*/
#pragma intvect DefaultIRQHandler 51	/* CAN 3					*/
#pragma intvect DefaultIRQHandler 52	/* CAN 4					*/
#pragma intvect DefaultIRQHandler 53	/* CAN 5					*/
#pragma intvect DefaultIRQHandler 54	/* USART (LIN) 0 RX			*/
#pragma intvect DefaultIRQHandler 55	/* USART (LIN) 0 TX			*/
#pragma intvect DefaultIRQHandler 56	/* USART (LIN) 1 RX			*/
#pragma intvect DefaultIRQHandler 57	/* USART (LIN) 1 TX			*/

#pragma intvect UART2_RxISR  	  58	/* USART (LIN) 2 RX			*/
#pragma intvect UART2_TxISR  	  59	/* USART (LIN) 2 TX			*/

#pragma intvect DefaultIRQHandler 60	/* USART (LIN) 3 RX			*/
#pragma intvect DefaultIRQHandler 61	/* USART (LIN) 3 TX			*/
#pragma intvect DefaultIRQHandler 62	/* System Reserved			*/

#pragma intvect vPortYieldDelayed 63	/* Delayed Interrupt		*/

#pragma intvect vPortYield		64		/* INT 64					*/

#pragma intvect DefaultIRQHandler 65	/* System Reserved			*/
#pragma intvect DefaultIRQHandler 66	/* USART (LIN, FIFO) 4 RX	*/
#pragma intvect DefaultIRQHandler 67	/* USART (LIN, FIFO) 4 TX	*/

#pragma intvect UART5_RxISR	   68		/* USART (LIN, FIFO) 5 RX	*/

#pragma intvect DefaultIRQHandler 69	/* USART (LIN, FIFO) 5 TX	*/
#pragma intvect DefaultIRQHandler 70	/* USART (LIN, FIFO) 6 RX	*/
#pragma intvect DefaultIRQHandler 71	/* USART (LIN, FIFO) 6 TX	*/
#pragma intvect DefaultIRQHandler 72	/* USART (LIN, FIFO) 7 RX	*/
#pragma intvect DefaultIRQHandler 73	/* USART (LIN, FIFO) 7 TX	*/
#pragma intvect DefaultIRQHandler 74	/* I2C 0 / I2C 2			*/
#pragma intvect DefaultIRQHandler 75	/* I2C 1 / I2C 3			*/
#pragma intvect DefaultIRQHandler 76	/* USART (LIN, FIFO) 8 RX	*/
#pragma intvect DefaultIRQHandler 77	/* USART (LIN, FIFO) 8 TX	*/
#pragma intvect DefaultIRQHandler 78	/* USART (LIN, FIFO) 9 RX	*/
#pragma intvect DefaultIRQHandler 79	/* USART (LIN, FIFO) 9 TX	*/
#pragma intvect DefaultIRQHandler 80	/* USART (LIN, FIFO) 10 RX	*/
#pragma intvect DefaultIRQHandler 81	/* USART (LIN, FIFO) 10 TX	*/
#pragma intvect DefaultIRQHandler 82	/* USART (LIN, FIFO) 11 RX	*/
#pragma intvect DefaultIRQHandler 83	/* USART (LIN, FIFO) 11 TX	*/
#pragma intvect DefaultIRQHandler 84	/* USART (LIN, FIFO) 12 RX	*/
#pragma intvect DefaultIRQHandler 85	/* USART (LIN, FIFO) 12 TX	*/
#pragma intvect DefaultIRQHandler 86	/* USART (LIN, FIFO) 13 RX	*/
#pragma intvect DefaultIRQHandler 87	/* USART (LIN, FIFO) 13 TX	*/
#pragma intvect DefaultIRQHandler 88	/* USART (LIN, FIFO) 14 RX	*/
#pragma intvect DefaultIRQHandler 89	/* USART (LIN, FIFO) 14 TX	*/
#pragma intvect DefaultIRQHandler 90	/* USART (LIN, FIFO) 15 RX	*/
#pragma intvect DefaultIRQHandler 91	/* USART (LIN, FIFO) 15 TX	*/
#pragma intvect DefaultIRQHandler 92	/* Input Capture 0			*/
#pragma intvect DefaultIRQHandler 93	/* Input Capture 1			*/
#pragma intvect DefaultIRQHandler 94	/* Input Capture 2			*/
#pragma intvect DefaultIRQHandler 95	/* Input Capture 3			*/
#pragma intvect DefaultIRQHandler 96	/* Input Capture 4			*/
#pragma intvect DefaultIRQHandler 97	/* Input Capture 5			*/
#pragma intvect DefaultIRQHandler 98	/* Input Capture 6			*/
#pragma intvect DefaultIRQHandler 99	/* Input Capture 7			*/
#pragma intvect DefaultIRQHandler 100   /* Output Compare 0			*/
#pragma intvect DefaultIRQHandler 101   /* Output Compare 1			*/
#pragma intvect DefaultIRQHandler 102   /* Output Compare 2			*/
#pragma intvect DefaultIRQHandler 103   /* Output Compare 3			*/
#pragma intvect DefaultIRQHandler 104   /* Output Compare 4			*/
#pragma intvect DefaultIRQHandler 105   /* Output Compare 5			*/
#pragma intvect DefaultIRQHandler 106   /* Output Compare 6			*/
#pragma intvect DefaultIRQHandler 107   /* Output Compare 7			*/
#pragma intvect DefaultIRQHandler 108   /* Sound Generator			*/
#pragma intvect DefaultIRQHandler 109   /* Phase Frequ. Modulator	*/
#pragma intvect DefaultIRQHandler 110   /* System Reserved			*/
#pragma intvect DefaultIRQHandler 111   /* System Reserved			*/
#pragma intvect DefaultIRQHandler 112   /* Prog. Pulse Gen. 0		*/
#pragma intvect DefaultIRQHandler 113   /* Prog. Pulse Gen. 1		*/
#pragma intvect DefaultIRQHandler 114   /* Prog. Pulse Gen. 2		*/
#pragma intvect DefaultIRQHandler 115   /* Prog. Pulse Gen. 3		*/
#pragma intvect DefaultIRQHandler 116   /* Prog. Pulse Gen. 4		*/
#pragma intvect DefaultIRQHandler 117   /* Prog. Pulse Gen. 5		*/
#pragma intvect DefaultIRQHandler 118   /* Prog. Pulse Gen. 6		*/
#pragma intvect DefaultIRQHandler 119   /* Prog. Pulse Gen. 7		*/
#pragma intvect DefaultIRQHandler 120   /* Prog. Pulse Gen. 8		*/
#pragma intvect DefaultIRQHandler 121   /* Prog. Pulse Gen. 9		*/
#pragma intvect DefaultIRQHandler 122   /* Prog. Pulse Gen. 10		*/
#pragma intvect DefaultIRQHandler 123   /* Prog. Pulse Gen. 11		*/
#pragma intvect DefaultIRQHandler 124   /* Prog. Pulse Gen. 12		*/
#pragma intvect DefaultIRQHandler 125   /* Prog. Pulse Gen. 13		*/
#pragma intvect DefaultIRQHandler 126   /* Prog. Pulse Gen. 14		*/
#pragma intvect DefaultIRQHandler 127   /* Prog. Pulse Gen. 15		*/
#pragma intvect DefaultIRQHandler 128   /* Up/Down Counter 0		*/
#pragma intvect DefaultIRQHandler 129   /* Up/Down Counter 1		*/
#pragma intvect DefaultIRQHandler 130   /* Up/Down Counter 2		*/
#pragma intvect DefaultIRQHandler 131   /* Up/Down Counter 3		*/
#pragma intvect DefaultIRQHandler 132   /* Real Time Clock			*/
#pragma intvect DefaultIRQHandler 133   /* Calibration Unit			*/
#pragma intvect DefaultIRQHandler 134   /* A/D Converter 0			*/
#pragma intvect DefaultIRQHandler 135   /* -						*/
#pragma intvect DefaultIRQHandler 136   /* Alarm Comperator 0		*/
#pragma intvect DefaultIRQHandler 137   /* Alarm Comperator 1		*/
#pragma intvect DefaultIRQHandler 138   /* Low Volage Detector		*/
#pragma intvect DefaultIRQHandler 139   /* SMC Zero Point 0-5		*/
#pragma intvect DefaultIRQHandler 140   /* Timebase Overflow		*/
#pragma intvect DefaultIRQHandler 141   /* PLL Clock Gear			*/
#pragma intvect DefaultIRQHandler 142   /* DMA Controller			*/
#pragma intvect DefaultIRQHandler 143   /* Main/Sub OSC stability wait  */
#pragma intvect 0xFFFFFFFF		144   /* Boot Sec. Vector (MB91V460A) */

/*------------------------------------------------------------------------
  DefaultIRQHandler()

  This function is a placeholder for all vector definitions. Either use
  your own placeholder or add necessary code here. 
-------------------------------------------------------------------------*/
__interrupt 
void DefaultIRQHandler (void)
{
	/* RB_SYNC; */						/* Synchronisation with R-Bus   */
										/* May be required, if there is */
										/* no R-Bus access after the	*/
										/* reset of the interrupt flag  */

	__DI();								/* disable interrupts		   */
	while(1)
	{
		Kick_Watchdog();				/* feed hardware watchdog	   */
	}
										/* halt system */
}
