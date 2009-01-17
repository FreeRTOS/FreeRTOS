/* THIS SAMPLE CODE IS PROVIDED AS IS AND IS SUBJECT TO ALTERATIONS. FUJITSU */
/* MICROELECTRONICS ACCEPTS NO RESPONSIBILITY OR LIABILITY FOR ANY ERRORS OR */
/* ELIGIBILITY FOR ANY PURPOSES.                                             */
/*                 (C) Fujitsu Microelectronics Europe GmbH                  */
/*---------------------------------------------------------------------------
  MAIN.C
  - description
  - See README.TXT for project description and disclaimer.

/*---------------------------------------------------------------------------*/


#include "mb96356rs.h"

#define DICE_MIN    1
#define DICE_MAX    6
#define DICERUN_MIN  600000L
#define DICERUN_MAX 1200000L

const char DICE7SEG1[11]={0x48, 0xeb, 0x8c, 0x89, 0x2b, 0x19, 0x18, 0xcb, 0x08, 0x09, 0xf7};
const char DICE7SEG2[11]={0xa0, 0xf3, 0xc4, 0xc1, 0x93, 0x89, 0x88, 0xe3, 0x80, 0x81, 0x7f};

unsigned char temp;
unsigned char dice1, dice2;
unsigned long dice1run, dice2run;
unsigned long dice1state, dice2state;
unsigned long dice1delay, dice2delay;
unsigned long dice1delayrld, dice2delayrld;
  
/*===========================================================================*/
/*====== MAIN ===============================================================*/
/*===========================================================================*/

void main(void)
{
  InitIrqLevels();
  __set_il(7);     // allow all levels     
  __EI();          // globally enable interrupts
  
  // initialize I/O-ports
  
  PIER00 = 0x03;   // Enable P00_0/INT8 and P00_1/INT9 as input
  PDR00  = 0x00;
  DDR00  = 0xfc;   // P00_0: SW2(INT8)   P00_1: SW3(INT9)

/* Do not use when Background Debugging is enabled
  PIER01 = 0x04;   // enable P01_2/SIN3 as input
  PDR01  = 0x08;   // SOT3 = 1
  DDR01  = 0xfb;   // SIN3 = input
*/
  
  PIER02 = 0x00;   // All inputs are disabled on this port 
  PDR02  = 0x00;
  DDR02  = 0xff;
    
  PIER03 = 0x00;   // All inputs are disabled on this port 
  PDR03  = 0xff; 
  DDR03  = 0xff;   // Set Port3 as output (7Segment Display)
  
  PIER04 = 0x04;   // Enable P04_2/RX as input
  PDR04  = 0x08;   // CAN TX = 1
  DDR04  = 0xfb;   // CAN RX = input
  
  PIER05 = 0x00;   // All inputs are disabled on this port 
  ADER1  = 0;      // Use Port 5 as I/O-Port
  PDR05  = 0x7f;
  DDR05  = 0xff;   // Set Port5 as output (7Segment Display)
  
  PIER06 = 0x00;   // All inputs are disabled on this port 
  PDR06  = 0x00;
  DDR06  = 0xff;
  
  while (1)
  {
    // DICE 1
      
    switch (dice1state)
    {
      case 0x00: // dice1 stopped
                 if (PDR00_P0 == 1)              // Key SW2:INT8 pressed
                 {
                   dice1run = DICERUN_MIN;
                   srand((unsigned char)dice1run);
                   dice1state = 0x01;
                 }

                 break;
                
      case 0x01: // dice1 startup
                 if (dice1run < DICERUN_MAX)     // variable running time
                   dice1run++;
                 else
                   dice1run = DICERUN_MIN;
            
                 if (PDR00_P0 == 0)              // Key SW2:INT8 released
                 {
                   dice1delay    = 1;
                   dice1delayrld = 1;
                   dice1state = 0x02;
                 }
                                  
                 break;

      case 0x02: // dice1 running
                 dice1run--;
                 dice1delay--;

                 if (!dice1delay)
                 {
                   do                       // get new random number
                   {
                    temp = rand() % 6 + 1;
                   }
                   while (temp == dice1);
                   dice1 = temp;
                   
                   PDR03 = (PDR03 | 0xf7) & DICE7SEG1[dice1];
                   dice1delayrld = dice1delayrld + 100;
                   dice1delay = dice1delayrld;
                 }

                 if (dice1run == 0)         // dice stopped
                 {
                   PDR03 = (PDR03 | 0xf7) & DICE7SEG1[rand() % 6 + 1];
                   dice1state = 0x00;
                 }

                 break;

    }//switch (dice1state)
      
      
    // DICE 2
      
    switch (dice2state)
    {
      case 0x00: // dice2 stopped
                 if (PDR00_P1 == 1)              // Key SW3:INT9 pressed
                 {
                   dice2run = DICERUN_MIN;
                   srand((unsigned char)dice1run);
                   dice2state = 0x01;
                 }

                 break;
                
      case 0x01: // dice2 startup
                 if (dice2run < DICERUN_MAX)     // variable running time
                   dice2run++;
                 else
                   dice2run = DICERUN_MIN;
            
                 if (dice2 == DICE_MAX)          // simple 'random' number
                   dice2 = DICE_MIN;
                 else dice2++;

                 if (PDR00_P1 == 0)              // Key SW3:INT9 released
                 {
                   dice2delay    = 1;
                   dice2delayrld = 1;
                   dice2state = 0x02;
                 }
                                  
                 break;

      case 0x02: // dice2 running
                 dice2run--;
                 dice2delay--;

                 if (!dice2delay)
                 {
                   do                       // get new random number
                   {
                    temp = rand() % 6 + 1;
                   }
                   while (temp == dice2);
                   dice2 = temp;
                   
                   PDR05 = DICE7SEG2[dice2];
                   dice2delayrld = dice2delayrld + 100;
                   dice2delay = dice2delayrld;
                 }

                 if (dice2run == 0)         // dice stopped
                 {
                   PDR05 = DICE7SEG2[rand() % 6 + 1];
                   dice2state = 0x00;
                 }

                 break;

    }//switch (dice2state)
    
  } // while(1)

}

void vApplicationIdleHook( void )
{
}

