/** 
 * sci.c controls SCI for GCC/HCS12 version of FreeRTOS Demo
 * Parts taken from the CodeWarrior Demo in order to work similar.
 *
 * Author Jefferson L Smith, Robotronics Inc.
 */

#include "sci.h"
#include <sys/ports.h>

//static word SerFlag;                   /* Flags for serial communication */
                                       /* Bits: 0 - OverRun error */
                                       /*       1 - Framing error */
                                       /*       2 - Parity error */
                                       /*       3 - Char in RX buffer */
                                       /*       4 - Full TX buffer */
                                       /*       5 - Running int from TX */
                                       /*       6 - Full RX buffer */
                                       /*       7 - Noise error */
                                       /*       8 - Idle character  */
                                       /*       9 - Break detected  */
                                       /*      10 - Unused */
static word PrescaleValue;
//static byte NumMode;                   /* Number of selected baud mode */


/**
 * SCI_SetBaudRateMode
 *
 * Changes the speed (baud rate).
 */
byte SCI_SetBaudRateMode(byte Mod)
{
  // wired for 24 MHz bus --jeffs
  static const word SCI_Presc[4] = {39,78,156,313};

  if(Mod >= 4)                         /* Is mode in baud mode list */
    return ERR_VALUE;                  /* If no then error */
  //NumMode = Mod;                       /* New baud mode */
  PrescaleValue = SCI_Presc[Mod];     /* Prescaler in high speed mode */

  /* SCI0CR1: LOOPS=0,SCISWAI=0,RSRC=0,M=0,WAKE=0,ILT=0,PE=0,PT=0 */
  SCICR1 = 0x00;                       /* Set the SCI configuration */
  /* SCI0SR2: ??=0,??=0,??=0,??=0,??=0,BRK13=0,TXDIR=0,RAF=0 */
  SCISR2 = 0x00;                       /* Set the Break Character Length and Transmitter pin data direction in Single-wire mode */
  SCISR1;                             /* Reset interrupt request flags */
  SCIBD = PrescaleValue;                  /* Set prescaler bits */
  /* SCI0CR2: SCTIE=0,TCIE=0,RIE=1,ILIE=0,TE=1,RE=1,RWU=0,SBK=0 */
  SCICR2 = 0x2c;                         /* Disable error interrupts */

  return ERR_OK;                       /* OK */
}

#if 0  //(not used)

/**
 * SCI_Init (bean AsynchroSerial)
 *
 * This enables SCI.
 */
void SCI_Init(void)
{
  PrescaleValue = 39;                      /* Precaler in high speed mode */

  /* SCI0CR1: LOOPS=0,SCISWAI=0,RSRC=0,M=0,WAKE=0,ILT=0,PE=0,PT=0 */
  SCICR1 = 0x00;                       /* Set the SCI configuration */
  /* SCI0SR2: ??=0,??=0,??=0,??=0,??=0,BRK13=0,TXDIR=0,RAF=0 */
  SCISR2 = 0x00;                       /* Set the Break Character Length and Transmitter pin data direction in Single-wire mode */
  SCISR1;                             /* Reset interrupt request flags */
  SCIBD = PrescaleValue;                  /* Set prescaler bits */
  /* SCI0CR2: SCTIE=0,TCIE=0,RIE=1,ILIE=0,TE=1,RE=1,RWU=0,SBK=0 */
  SCICR2 = 0x2c;                         /* Disable error interrupts */
}
#endif

