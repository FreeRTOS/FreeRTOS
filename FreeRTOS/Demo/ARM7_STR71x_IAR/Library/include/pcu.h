/******************** (C) COPYRIGHT 2003 STMicroelectronics ********************
* File Name          : pcu.h
* Author             : MCD Application Team
* Date First Issued  : 30/05/2003
* Description        : This file contains all the functions prototypes for the
*                      PCU software library.
********************************************************************************
* History:
*  30/11/2004 : V2.0
*  14/07/2004 : V1.3
*  01/01/2004 : V1.2
*******************************************************************************
 THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS WITH
 CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
 AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT, INDIRECT
 OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE CONTENT
 OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING INFORMATION
 CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/
#ifndef __PCU_H
#define __PCU_H

#include "71x_map.h"

typedef enum
{
  PCU_WREN = 0x8000,
  PCU_VROK = 0x1000
} PCU_Flags;

typedef enum
{
  PCU_STABLE,
  PCU_UNSTABLE
} PCU_VR_Status;

typedef enum
{
  PCU_MVR = 0x0008,
  PCU_LPR = 0x0020
} PCU_VR;

typedef enum
{
  WFI_CLOCK2_16,
  WFI_EXTERNAL
} WFI_CLOCKS;

typedef enum
{
  PCU_SLOW,
  PCU_STOP,
  PCU_STANDBY
} LPM_MODES;


// VR_OK  : Voltage Regulator OK
#define PCU_VROK_Mask       0x1000

// Main Voltage Regulator
#define PCU_MVR_Mask        0x0008

// Low Power Voltage Regulator
#define PCU_LPR_Mask        0x0020

// PCU register Write Enable Bit
#define PCU_WREN_Mask       0x8000

// Low Voltage Detector
#define PCU_LVD_Mask        0x0100

// Power Down Flag
#define PCU_PWRDWN_Mask     0x0040

// WFI Mode Clock Selection Bit
#define PCU_WFI_CKSEL_Mask  0x00000002

// Halt Mode Enable Bit
#define PCU_EN_HALT_Mask    0x00000800

// Halt Mode Flag
#define PCU_HALT_Mask       0x0002

// Stop Mode Enable Bit
#define PCU_STOP_EN_Mask    0x00000400

// Low Power Regulator in Wait For interrupt Mode
#define PCU_LPRWFI_Mask     0x0020

// Low Power Mode in Wait For interrupt Mode
#define PCU_LPOWFI_Mask     0x00000001

// Software Reset Enable
#define PCU_SRESEN_Mask     0x00000001


/*******************************************************************************
* Function Name  : PCU_MVRStatus
* Description    : This routine is used to check the Main Voltage Regulator
*                : NewState.
* Input          : None
* Return         : STABLE, UNSTABLE
*******************************************************************************/
inline PCU_VR_Status PCU_MVRStatus ( void )
{
	return (PCU->PWRCR & PCU_VROK_Mask) == 0x00 ? PCU_UNSTABLE : PCU_STABLE;
}

/*******************************************************************************
* Function Name  : PCU_FlagStatus
* Description    : This routine is used to return the PCU register flag
* Input 1        : The flag to get
* Return         : RESET, SET
*******************************************************************************/
inline FlagStatus PCU_FlagStatus ( PCU_Flags Xflag )
{
	return ( PCU->PWRCR & Xflag ) == 0x00 ? RESET : SET;
}

/*******************************************************************************
* Function Name  : PCU_VRConfig
* Description    : This routine is used to configure PCU voltage regultors
* Input 1        : MVR : Main voltage Regulator
                   LPR : Low Power Regulator
* Input 2        : ENABLE : Enable the Voltage Regulator
                   DISABLE: Disable ( ByPass ) the VR
* Return         : None
*******************************************************************************/
void PCU_VRConfig ( PCU_VR xVR, FunctionalState NewState );

/*******************************************************************************
* Function Name  : PCU_VRStatus
* Description    : This routine is used to get the PCU voltage regultors status
* Input          : MVR : Main voltage Regulator
                   LPR : Low Power Regulator
* Return         : ENABLE : Enable the Voltage Regulator
                   DISABLE: Disable ( ByPass ) the VR
*******************************************************************************/
inline FunctionalState PCU_VRStatus ( PCU_VR xVR )
{
	return ( PCU->PWRCR & xVR ) == 0  ? ENABLE : DISABLE;
}

/*******************************************************************************
* Function Name  : PCU_LVDDisable
* Description    : This routine is used to disable the Low Voltage Detector.
* Input          : None
* Return         : None
*******************************************************************************/
inline void PCU_LVDDisable ( void )
{
	PCU->PWRCR |= PCU_WREN_Mask;	// Unlock Power Control Register
	PCU->PWRCR |= PCU_LVD_Mask;	// Set the LVD DIS Flag
}

/*******************************************************************************
* Function Name  : PCU_LVDStatus
* Description    : This routine is used to get the LVD NewState.
* Input          : None
* Return         : ENABLE, DISABLE
*******************************************************************************/
inline FunctionalState PCU_LVDStatus ( void )
{
	return ( PCU->PWRCR & PCU_LVD_Mask ) == 0 ? ENABLE : DISABLE;
}

/*******************************************************************************
* Function Name  : PCU_WFIEnter
* Description    : This routine is used to force the Device to enter in WFI mode
* Input 1        : CLOCK2_16 : Clock2_16 as system clock for WFI mode
*                  EXTERNAL  : external clock as system clock for WFI mode
* Input 2        : ENABLE : Enable Low Power Regulator during Wait For Interrupt Mode
*                  DISABLE: Disable Low Power Regulator during Wait For Interrupt Mode
* Input 3        : ENABLE : Enable Low Power Mode during Wait For Interrupt Mode
*                  DISABLE: Disable Low Power Mode during Wait For Interrupt Mode
* Return         : None
*******************************************************************************/
void PCU_WFIEnter ( WFI_CLOCKS Xclock, FunctionalState Xlpr, FunctionalState Xlpm );

/*******************************************************************************
* Function Name  : PCU_LPMEnter
* Description    : This routine is used to force the Device to enter low
*                  power mode
* Input          : SLOW : Slow Mode
                   STOP : Stop Mode
                   HALT : Halt Mode
* Return         : None
*******************************************************************************/
void PCU_LPMEnter ( LPM_MODES Xmode);

#endif	// __PCU_H

/******************* (C) COPYRIGHT 2003 STMicroelectronics *****END OF FILE****/
