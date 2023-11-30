/** 
 * sci.h controls SCI for GCC/HCS12 version of FreeRTOS Demo
 * Parts taken from the CodeWarrior Demo in order to work similar.
 *
 * Author Jefferson L Smith, Robotronics Inc.
 */

#ifndef __SCI
#define __SCI

#include "cpu.h"

#define COM0_Bm_38400baud         0    /* Constant for switch to mode 0 */
#define COM0_Bm_19200baud         1    /* Constant for switch to mode 1 */
#define COM0_Bm_9600baud          2    /* Constant for switch to mode 2 */
#define COM0_Bm_4800baud          3    /* Constant for switch to mode 3 */


/**
 * SCI_SetBaudRateMode
 *
 * Changes the speed (baud rate).
 */
byte SCI_SetBaudRateMode(byte Mod);


/**
 * SCI_Init (bean AsynchroSerial)
 *
 * This enables SCI.
 */
void SCI_Init(void);

#endif /* ifndef __SCI */
