/******************** (C) COPYRIGHT 2006 STMicroelectronics ********************
* File Name          : 91x_fmi.h
* Author             : MCD Application Team
* Date First Issued  : 05/18/2006 : Version 1.0
* Description        : This file contains all the functions prototypes for the
*                      FMI software library.
********************************************************************************
* History:
* 05/24/2006 : Version 1.1
* 05/18/2006 : Version 1.0
********************************************************************************
* THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS WITH
* CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME. AS
* A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT, INDIRECT
* OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE CONTENT
* OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING INFORMATION
* CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
*******************************************************************************/


/* Define to prevent recursive inclusion ------------------------------------ */

#ifndef __91x_FMI_H
#define __91x_FMI_H

/* ========================================================================== */
/*    When bank 1 is remapped at address 0x0, decomment the following line    */
/* ========================================================================== */

//#define Remap_Bank_1


/* Includes ------------------------------------------------------------------*/

#include "91x_map.h"

/* Exported types ------------------------------------------------------------*/
/* Exported constants --------------------------------------------------------*/

/* FMI banks */

#ifdef Remap_Bank_1

#define    FMI_BANK_0     ((*(vu32*)0x54000010) << 2)   /* FMI Bank 0 */
#define    FMI_BANK_1     ((*(vu32*)0x5400000C) << 2)   /* FMI Bank 1 */

#else /* Remap Bank 0 */

#define    FMI_BANK_0     ((*(vu32*)0x5400000C) << 2)   /* FMI Bank 0 */
#define    FMI_BANK_1     ((*(vu32*)0x54000010) << 2)   /* FMI Bank 1 */

#endif

/* FMI sectors */

#define    FMI_B0S0     0x00000000 + FMI_BANK_0     /* Bank 0 sector 0 */
#define    FMI_B0S1     0x00010000 + FMI_BANK_0     /* Bank 0 sector 1 */
#define    FMI_B0S2     0x00020000 + FMI_BANK_0     /* Bank 0 sector 2 */
#define    FMI_B0S3	0x00030000 + FMI_BANK_0     /* Bank 0 sector 3 */
#define    FMI_B0S4     0x00040000 + FMI_BANK_0     /* Bank 0 sector 4 */
#define    FMI_B0S5     0x00050000 + FMI_BANK_0     /* Bank 0 sector 5 */
#define    FMI_B0S6     0x00060000 + FMI_BANK_0     /* Bank 0 sector 6 */
#define    FMI_B0S7     0x00070000 + FMI_BANK_0     /* Bank 0 sector 7 */

#define    FMI_B1S0     0x00000000 + FMI_BANK_1     /* Bank 1 sector 0 */
#define    FMI_B1S1     0x00002000 + FMI_BANK_1     /* Bank 1 sector 1 */
#define    FMI_B1S2     0x00004000 + FMI_BANK_1     /* Bank 1 sector 2 */
#define    FMI_B1S3     0x00006000 + FMI_BANK_1     /* Bank 1 sector 3 */

/* FMI Flags */

#define    FMI_FLAG_SPS        0x02       /* Sector Protection Status Flag */
#define    FMI_FLAG_PSS        0x04       /* Program Suspend Status Flag   */
#define    FMI_FLAG_PS         0x10       /* Program Status Flag           */
#define    FMI_FLAG_ES         0x20       /* Erase Status Flag             */
#define    FMI_FLAG_ESS        0x40       /* Erase Suspend Status Flag     */
#define    FMI_FLAG_PECS       0x80       /* FPEC Status Flag              */

/* FMI read wait states */

#define    FMI_READ_WAIT_STATE_1     0x0000    /* One read wait state    */
#define    FMI_READ_WAIT_STATE_2     0x2000    /* Two read wait states   */
#define    FMI_READ_WAIT_STATE_3     0x4000    /* Three read wait states */

/* FMI write wait states */

#define    FMI_WRITE_WAIT_STATE_0     0xFFFFFEFF    /* Zero wait state */
#define    FMI_WRITE_WAIT_STATE_1     0x00000100    /* One wait state  */

/* FMI power down configuration */

#define    FMI_PWD_ENABLE       0x1000    /* FMI Power Down Enable  */
#define    FMI_PWD_DISABLE      0x0000    /* FMI Power Down Disable */

/* FMI low voltage detector */

#define    FMI_LVD_ENABLE       0x0000    /* FMI Low Voltage Detector Enable  */
#define    FMI_LVD_DISABLE      0x0800    /* FMI Low Voltage Detector Disable */

/* FMI frequency range */

#define    FMI_FREQ_LOW         0x0000    /* FMI Low bus working frequency   */
#define    FMI_FREQ_HIGH        0x0040    /* FMI High bus working gfrequency */
                                          /* Above 66 MHz*/
/* FMI OTP word addresses */      

#define    FMI_OTP_WORD_0       0x00   /* OTP word 0 */
#define    FMI_OTP_WORD_1       0x04   /* OTP word 1 */
#define    FMI_OTP_WORD_2       0x08   /* OTP word 2 */
#define    FMI_OTP_WORD_3       0x0C   /* OTP word 3 */
#define    FMI_OTP_WORD_4       0x10   /* OTP word 4 */
#define    FMI_OTP_WORD_5       0x14   /* OTP word 5 */
#define    FMI_OTP_WORD_6       0x18   /* OTP word 6 */
#define    FMI_OTP_WORD_7       0x1C   /* OTP word 7 */
                                    
/* FMI OTP halfword addresses */

#define    FMI_OTP_LOW_HALFWORD_0       0x00   /* OTP Low halfword 0  */
#define    FMI_OTP_HIGH_HALFWORD_0      0x02   /* OTP High halfword 0 */
#define    FMI_OTP_LOW_HALFWORD_1       0x04   /* OTP Low halfword 1  */
#define    FMI_OTP_HIGH_HALFWORD_1      0x06   /* OTP High halfword 1 */
#define    FMI_OTP_LOW_HALFWORD_2       0x08   /* OTP Low halfword 2  */
#define    FMI_OTP_HIGH_HALFWORD_2      0x0A   /* OTP High halfword 2 */
#define    FMI_OTP_LOW_HALFWORD_3       0x0C   /* OTP Low halfword 3  */
#define    FMI_OTP_HIGH_HALFWORD_3      0x0E   /* OTP High halfword 3 */
#define    FMI_OTP_LOW_HALFWORD_4       0x10   /* OTP Low halfword 4  */
#define    FMI_OTP_HIGH_HALFWORD_4      0x12   /* OTP High halfword 4 */
#define    FMI_OTP_LOW_HALFWORD_5       0x14   /* OTP Low halfword 5  */
#define    FMI_OTP_HIGH_HALFWORD_5      0x16   /* OTP High halfword 5 */
#define    FMI_OTP_LOW_HALFWORD_6       0x18   /* OTP Low halfword 6  */
#define    FMI_OTP_HIGH_HALFWORD_6      0x1A   /* OTP High halfword 6 */
#define    FMI_OTP_LOW_HALFWORD_7       0x1C   /* OTP Low halfword 7  */
#define    FMI_OTP_HIGH_HALFWORD_7      0x1E   /* OTP High halfword 7 */

/* FMI sectors Masks */

#define FMI_B0S0_MASK   0x0001       /* FMI B0S0 mask */
#define FMI_B0S1_MASK   0x0002       /* FMI B0S1 mask */
#define FMI_B0S2_MASK   0x0004       /* FMI B0S2 mask */
#define FMI_B0S3_MASK   0x0008       /* FMI B0S3 mask */
#define FMI_B0S4_MASK   0x0010       /* FMI B0S4 mask */
#define FMI_B0S5_MASK   0x0020       /* FMI B0S5 mask */
#define FMI_B0S6_MASK   0x0040       /* FMI B0S6 mask */
#define FMI_B0S7_MASK   0x0080       /* FMI B0S7 mask */

#define FMI_B1S0_MASK   0x0100       /* FMI B1S0 mask */
#define FMI_B1S1_MASK   0x0200       /* FMI B1S1 mask */
#define FMI_B1S2_MASK   0x0400       /* FMI B1S2 mask */
#define FMI_B1S3_MASK   0x0800       /* FMI B1S3 mask */

/* Timeout error */

#define FMI_TIME_OUT_ERROR      0x00       /* Timeout error    */     
#define FMI_NO_TIME_OUT_ERROR   0x01       /* No Timeout error */

/* Module private variables --------------------------------------------------*/
/* Exported macro ------------------------------------------------------------*/
/* Private functions ---------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */

void FMI_BankRemapConfig(u8 FMI_BootBankSize, u8 FMI_NonBootBankSize, \
                         u32 FMI_BootBankAddress, u32 FMI_NonBootBankAddress);
void FMI_Config(u16 FMI_ReadWaitState, u32 FMI_WriteWaitState, u16 FMI_PWD,\
                u16 FMI_LVDEN, u16 FMI_FreqRange);
void FMI_EraseSector(vu32 FMI_Sector);
void FMI_EraseBank(vu32 FMI_Bank);
void FMI_WriteHalfWord(u32 FMI_Address, u16 FMI_Data);
void FMI_WriteOTPHalfWord(u8 FMI_OTPHWAddress, u16 FMI_OTPData);
u32 FMI_ReadWord(u32 FMI_Address);
u32 FMI_ReadOTPData(u8 FMI_OTPAddress);
FlagStatus FMI_GetFlagStatus(u8 FMI_Flag, vu32 FMI_Bank);
u16 FMI_GetReadWaitStateValue(void);
u16 FMI_GetWriteWaitStateValue(void);
void FMI_SuspendEnable(vu32 FMI_Bank);
void FMI_ResumeEnable(vu32 FMI_Bank);
void FMI_ClearFlag(vu32 FMI_Bank);
void FMI_WriteProtectionCmd(vu32 FMI_Sector, FunctionalState FMI_NewState);
FlagStatus FMI_GetWriteProtectionStatus(u32 FMI_Sector_Protection);
u8 FMI_WaitForLastOperation(vu32 FMI_Bank);

#endif /* __91x_FMI_H */

/******************* (C) COPYRIGHT 2006 STMicroelectronics *****END OF FILE****/

