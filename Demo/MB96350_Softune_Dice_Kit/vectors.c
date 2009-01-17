/* THIS SAMPLE CODE IS PROVIDED AS IS AND IS SUBJECT TO ALTERATIONS. FUJITSU */
/* MICROELECTRONICS ACCEPTS NO RESPONSIBILITY OR LIABILITY FOR ANY ERRORS OR */
/* ELIGIBILITY FOR ANY PURPOSES.                                             */
/*                 (C) Fujitsu Microelectronics Europe GmbH                  */
/*---------------------------------------------------------------------------
  VECTORS.C
  - Interrupt level (priority) setting
  - Interrupt vector definition
-----------------------------------------------------------------------------*/

#include "mb96356rs.h"

/*---------------------------------------------------------------------------
   InitIrqLevels()
   This function  pre-sets all interrupt control registers. It can be used
   to set all interrupt priorities in static applications. If this file
   contains assignments to dedicated resources, verify  that the
   appropriate controller is used.
   NOTE: value 7 disables the interrupt and value 0 sets highest priority.
-----------------------------------------------------------------------------*/

#define MIN_ICR  11
#define MAX_ICR  93

#define DEFAULT_ILM_MASK 7

void InitIrqLevels(void)
{
  volatile int irq;
  
  for (irq = MIN_ICR; irq <= MAX_ICR; irq++) 
  {
    ICR = (irq << 8) | DEFAULT_ILM_MASK;
  }
  
}

/*---------------------------------------------------------------------------
   Prototypes
   Add your own prototypes here. Each vector definition needs is proto-
   type. Either do it here or include a header file containing them.
-----------------------------------------------------------------------------*/

__interrupt void DefaultIRQHandler (void);

/*---------------------------------------------------------------------------
   Vector definiton for MB9635x
   Use following statements to define vectors. All resource related
   vectors are predefined. Remaining software interrupts can be added here
   as well.
   NOTE: If software interrupts 0 to 7 are defined here, this might 
   conflict with the reset vector in the start-up file.
-----------------------------------------------------------------------------*/

#pragma intvect DefaultIRQHandler 11   /* Non-maskable Interrupt       */
#pragma intvect DefaultIRQHandler 12   /* Delayed Interrupt            */
#pragma intvect DefaultIRQHandler 13   /* RC Timer                     */
#pragma intvect DefaultIRQHandler 14   /* Main Clock Timer             */
#pragma intvect DefaultIRQHandler 15   /* Sub Clock Timer              */
#pragma intvect DefaultIRQHandler 16   /* Reserved                     */
#pragma intvect DefaultIRQHandler 17   /* EXT0                         */
#pragma intvect DefaultIRQHandler 18   /* EXT1                         */
#pragma intvect DefaultIRQHandler 19   /* EXT2                         */
#pragma intvect DefaultIRQHandler 20   /* EXT3                         */
#pragma intvect DefaultIRQHandler 21   /* EXT4                         */
#pragma intvect DefaultIRQHandler 22   /* EXT5                         */
#pragma intvect DefaultIRQHandler 23   /* EXT7                         */
#pragma intvect DefaultIRQHandler 24   /* EXT8                         */
#pragma intvect DefaultIRQHandler 25   /* EXT9                         */
#pragma intvect DefaultIRQHandler 26   /* EXT10                        */
#pragma intvect DefaultIRQHandler 27   /* EXT11                        */
#pragma intvect DefaultIRQHandler 28   /* EXT12                        */
#pragma intvect DefaultIRQHandler 29   /* EXT13                        */
#pragma intvect DefaultIRQHandler 30   /* EXT14                        */
#pragma intvect DefaultIRQHandler 31   /* EXT15                        */
#pragma intvect DefaultIRQHandler 32   /* CAN1                         */
#pragma intvect DefaultIRQHandler 33   /* CAN2                         */
#pragma intvect DefaultIRQHandler 34   /* PPG0                         */
#pragma intvect DefaultIRQHandler 35   /* PPG1                         */
#pragma intvect DefaultIRQHandler 36   /* PPG2                         */
#pragma intvect DefaultIRQHandler 37   /* PPG3                         */
#pragma intvect DefaultIRQHandler 38   /* PPG4                         */
#pragma intvect DefaultIRQHandler 39   /* PPG5                         */
#pragma intvect DefaultIRQHandler 40   /* PPG6                         */
#pragma intvect DefaultIRQHandler 41   /* PPG7                         */
#pragma intvect DefaultIRQHandler 42   /* PPG8                         */
#pragma intvect DefaultIRQHandler 43   /* PPG9                         */
#pragma intvect DefaultIRQHandler 44   /* PPG10                        */
#pragma intvect DefaultIRQHandler 45   /* PPG11                        */
#pragma intvect DefaultIRQHandler 46   /* PPG12                        */
#pragma intvect DefaultIRQHandler 47   /* PPG13                        */
#pragma intvect DefaultIRQHandler 48   /* PPG14                        */
#pragma intvect DefaultIRQHandler 49   /* PPG15                        */
#pragma intvect DefaultIRQHandler 50   /* PPG16                        */
#pragma intvect DefaultIRQHandler 51   /* PPG17                        */
#pragma intvect DefaultIRQHandler 52   /* PPG18                        */
#pragma intvect DefaultIRQHandler 53   /* PPG19                        */
#pragma intvect DefaultIRQHandler 54   /* RLT0                         */
#pragma intvect DefaultIRQHandler 55   /* RLT1                         */
#pragma intvect DefaultIRQHandler 56   /* RLT2                         */
#pragma intvect DefaultIRQHandler 57   /* RLT3                         */
#pragma intvect DefaultIRQHandler 58   /* PPGRLT - RLT6                */
#pragma intvect DefaultIRQHandler 59   /* ICU0                         */
#pragma intvect DefaultIRQHandler 60   /* ICU1                         */
#pragma intvect DefaultIRQHandler 63   /* ICU4                         */
#pragma intvect DefaultIRQHandler 64   /* ICU5                         */
#pragma intvect DefaultIRQHandler 65   /* ICU6                         */
#pragma intvect DefaultIRQHandler 66   /* ICU7                         */
#pragma intvect DefaultIRQHandler 71   /* OCU4                         */
#pragma intvect DefaultIRQHandler 72   /* OCU5                         */
#pragma intvect DefaultIRQHandler 73   /* OCU6                         */
#pragma intvect DefaultIRQHandler 74   /* OCU7                         */
#pragma intvect DefaultIRQHandler 77   /* FRT0                         */
#pragma intvect DefaultIRQHandler 78   /* FRT1                         */
#pragma intvect DefaultIRQHandler 81   /* RTC0                         */
#pragma intvect DefaultIRQHandler 82   /* CAL0                         */
#pragma intvect DefaultIRQHandler 83   /* I2C0                         */
#pragma intvect DefaultIRQHandler 84   /* ADC                          */
#pragma intvect DefaultIRQHandler 85   /* LIN-UART 2 RX                */
#pragma intvect DefaultIRQHandler 86   /* LIN-UART 2 TX                */
#pragma intvect DefaultIRQHandler 87   /* LIN-UART 3 RX                */
#pragma intvect DefaultIRQHandler 88   /* LIN-UART 3 TX                */
#pragma intvect DefaultIRQHandler 89   /* LIN-UART 7 RX                */
#pragma intvect DefaultIRQHandler 90   /* LIN-UART 7 TX                */
#pragma intvect DefaultIRQHandler 91   /* LIN-UART 8 RX                */
#pragma intvect DefaultIRQHandler 92   /* LIN-UART 8 TX                */
#pragma intvect DefaultIRQHandler 93   /* MAIN FLASH IRQ               */

/*---------------------------------------------------------------------------
   DefaultIRQHandler()
   This function is a placeholder for all vector definitions. Either use
   your own placeholder or add necessary code here. 
-----------------------------------------------------------------------------*/

__interrupt 
void DefaultIRQHandler (void)
{
    __DI();                              /* disable interrupts */
    while(1)
    {
        __wait_nop();                    /* halt system */
    }
}
