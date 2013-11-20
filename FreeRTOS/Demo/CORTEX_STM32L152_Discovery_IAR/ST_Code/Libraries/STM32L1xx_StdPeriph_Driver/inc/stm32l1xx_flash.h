/**
  ******************************************************************************
  * @file    stm32l1xx_flash.h
  * @author  MCD Application Team
  * @version V1.1.1
  * @date    05-March-2012
  * @brief   This file contains all the functions prototypes for the FLASH 
  *          firmware library.
  ******************************************************************************
  * @attention
  *
  * <h2><center>&copy; COPYRIGHT 2012 STMicroelectronics</center></h2>
  *
  * Licensed under MCD-ST Liberty SW License Agreement V2, (the "License");
  * You may not use this file except in compliance with the License.
  * You may obtain a copy of the License at:
  *
  *        http://www.st.com/software_license_agreement_liberty_v2
  *
  * Unless required by applicable law or agreed to in writing, software 
  * distributed under the License is distributed on an "AS IS" BASIS, 
  * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  * See the License for the specific language governing permissions and
  * limitations under the License.
  *
  ******************************************************************************
  */

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __STM32L1xx_FLASH_H
#define __STM32L1xx_FLASH_H

#ifdef __cplusplus
 extern "C" {
#endif

/* Includes ------------------------------------------------------------------*/
#include "stm32l1xx.h"

/** @addtogroup STM32L1xx_StdPeriph_Driver
  * @{
  */

/** @addtogroup FLASH
  * @{
  */

/* Exported types ------------------------------------------------------------*/

/** 
  * @brief  FLASH Status  
  */ 
typedef enum
{ 
  FLASH_BUSY = 1,
  FLASH_ERROR_WRP,
  FLASH_ERROR_PROGRAM,
  FLASH_COMPLETE,
  FLASH_TIMEOUT
}FLASH_Status;

/* Exported constants --------------------------------------------------------*/
  
/** @defgroup FLASH_Exported_Constants
  * @{
  */ 
  
/** @defgroup FLASH_Latency 
  * @{
  */ 
#define FLASH_Latency_0                ((uint8_t)0x00)  /*!< FLASH Zero Latency cycle */
#define FLASH_Latency_1                ((uint8_t)0x01)  /*!< FLASH One Latency cycle */

#define IS_FLASH_LATENCY(LATENCY) (((LATENCY) == FLASH_Latency_0) || \
                                   ((LATENCY) == FLASH_Latency_1))
/**
  * @}
  */ 

/** @defgroup FLASH_Interrupts 
  * @{
  */
   
#define FLASH_IT_EOP               FLASH_PECR_EOPIE  /*!< End of programming interrupt source */
#define FLASH_IT_ERR               FLASH_PECR_ERRIE  /*!< Error interrupt source */
#define IS_FLASH_IT(IT) ((((IT) & (uint32_t)0xFFFCFFFF) == 0x00000000) && (((IT) != 0x00000000)))
/**
  * @}
  */ 

/** @defgroup FLASH_Address 
  * @{
  */
  
#define IS_FLASH_DATA_ADDRESS(ADDRESS) (((ADDRESS) >= 0x08080000) && ((ADDRESS) <= 0x08082FFF))
#define IS_FLASH_PROGRAM_ADDRESS(ADDRESS) (((ADDRESS) >= 0x08000000) && ((ADDRESS) <= 0x0805FFFF))  

/**
  * @}
  */ 

/** @defgroup Option_Bytes_Write_Protection 
  * @{
  */
  
#define OB_WRP_Pages0to15              ((uint32_t)0x00000001) /* Write protection of Sector0 */
#define OB_WRP_Pages16to31             ((uint32_t)0x00000002) /* Write protection of Sector1 */
#define OB_WRP_Pages32to47             ((uint32_t)0x00000004) /* Write protection of Sector2 */
#define OB_WRP_Pages48to63             ((uint32_t)0x00000008) /* Write protection of Sector3 */
#define OB_WRP_Pages64to79             ((uint32_t)0x00000010) /* Write protection of Sector4 */
#define OB_WRP_Pages80to95             ((uint32_t)0x00000020) /* Write protection of Sector5 */
#define OB_WRP_Pages96to111            ((uint32_t)0x00000040) /* Write protection of Sector6 */
#define OB_WRP_Pages112to127           ((uint32_t)0x00000080) /* Write protection of Sector7 */
#define OB_WRP_Pages128to143           ((uint32_t)0x00000100) /* Write protection of Sector8 */
#define OB_WRP_Pages144to159           ((uint32_t)0x00000200) /* Write protection of Sector9 */
#define OB_WRP_Pages160to175           ((uint32_t)0x00000400) /* Write protection of Sector10 */
#define OB_WRP_Pages176to191           ((uint32_t)0x00000800) /* Write protection of Sector11 */
#define OB_WRP_Pages192to207           ((uint32_t)0x00001000) /* Write protection of Sector12 */
#define OB_WRP_Pages208to223           ((uint32_t)0x00002000) /* Write protection of Sector13 */
#define OB_WRP_Pages224to239           ((uint32_t)0x00004000) /* Write protection of Sector14 */
#define OB_WRP_Pages240to255           ((uint32_t)0x00008000) /* Write protection of Sector15 */
#define OB_WRP_Pages256to271           ((uint32_t)0x00010000) /* Write protection of Sector16 */
#define OB_WRP_Pages272to287           ((uint32_t)0x00020000) /* Write protection of Sector17 */
#define OB_WRP_Pages288to303           ((uint32_t)0x00040000) /* Write protection of Sector18 */
#define OB_WRP_Pages304to319           ((uint32_t)0x00080000) /* Write protection of Sector19 */
#define OB_WRP_Pages320to335           ((uint32_t)0x00100000) /* Write protection of Sector20 */
#define OB_WRP_Pages336to351           ((uint32_t)0x00200000) /* Write protection of Sector21 */
#define OB_WRP_Pages352to367           ((uint32_t)0x00400000) /* Write protection of Sector22 */
#define OB_WRP_Pages368to383           ((uint32_t)0x00800000) /* Write protection of Sector23 */
#define OB_WRP_Pages384to399           ((uint32_t)0x01000000) /* Write protection of Sector24 */
#define OB_WRP_Pages400to415           ((uint32_t)0x02000000) /* Write protection of Sector25 */
#define OB_WRP_Pages416to431           ((uint32_t)0x04000000) /* Write protection of Sector26 */
#define OB_WRP_Pages432to447           ((uint32_t)0x08000000) /* Write protection of Sector27 */
#define OB_WRP_Pages448to463           ((uint32_t)0x10000000) /* Write protection of Sector28 */
#define OB_WRP_Pages464to479           ((uint32_t)0x20000000) /* Write protection of Sector29 */
#define OB_WRP_Pages480to495           ((uint32_t)0x40000000) /* Write protection of Sector30 */
#define OB_WRP_Pages496to511           ((uint32_t)0x80000000) /* Write protection of Sector31 */

#define OB_WRP_AllPages                ((uint32_t)0xFFFFFFFF) /*!< Write protection of all Sectors */

#define OB_WRP1_Pages512to527          ((uint32_t)0x00000001) /* Write protection of Sector32 */
#define OB_WRP1_Pages528to543          ((uint32_t)0x00000002) /* Write protection of Sector33 */
#define OB_WRP1_Pages544to559          ((uint32_t)0x00000004) /* Write protection of Sector34 */
#define OB_WRP1_Pages560to575          ((uint32_t)0x00000008) /* Write protection of Sector35 */
#define OB_WRP1_Pages576to591          ((uint32_t)0x00000010) /* Write protection of Sector36 */
#define OB_WRP1_Pages592to607          ((uint32_t)0x00000020) /* Write protection of Sector37 */
#define OB_WRP1_Pages608to623          ((uint32_t)0x00000040) /* Write protection of Sector38 */
#define OB_WRP1_Pages624to639          ((uint32_t)0x00000080) /* Write protection of Sector39 */
#define OB_WRP1_Pages640to655          ((uint32_t)0x00000100) /* Write protection of Sector40 */
#define OB_WRP1_Pages656to671          ((uint32_t)0x00000200) /* Write protection of Sector41 */
#define OB_WRP1_Pages672to687          ((uint32_t)0x00000400) /* Write protection of Sector42 */
#define OB_WRP1_Pages688to703          ((uint32_t)0x00000800) /* Write protection of Sector43 */
#define OB_WRP1_Pages704to719          ((uint32_t)0x00001000) /* Write protection of Sector44 */
#define OB_WRP1_Pages720to735          ((uint32_t)0x00002000) /* Write protection of Sector45 */
#define OB_WRP1_Pages736to751          ((uint32_t)0x00004000) /* Write protection of Sector46 */
#define OB_WRP1_Pages752to767          ((uint32_t)0x00008000) /* Write protection of Sector47 */
#define OB_WRP1_Pages768to783          ((uint32_t)0x00010000) /* Write protection of Sector48 */
#define OB_WRP1_Pages784to799          ((uint32_t)0x00020000) /* Write protection of Sector49 */
#define OB_WRP1_Pages800to815          ((uint32_t)0x00040000) /* Write protection of Sector50 */
#define OB_WRP1_Pages816to831          ((uint32_t)0x00080000) /* Write protection of Sector51 */
#define OB_WRP1_Pages832to847          ((uint32_t)0x00100000) /* Write protection of Sector52 */
#define OB_WRP1_Pages848to863          ((uint32_t)0x00200000) /* Write protection of Sector53 */
#define OB_WRP1_Pages864to879          ((uint32_t)0x00400000) /* Write protection of Sector54 */
#define OB_WRP1_Pages880to895          ((uint32_t)0x00800000) /* Write protection of Sector55 */
#define OB_WRP1_Pages896to911          ((uint32_t)0x01000000) /* Write protection of Sector56 */
#define OB_WRP1_Pages912to927          ((uint32_t)0x02000000) /* Write protection of Sector57 */
#define OB_WRP1_Pages928to943          ((uint32_t)0x04000000) /* Write protection of Sector58 */
#define OB_WRP1_Pages944to959          ((uint32_t)0x08000000) /* Write protection of Sector59 */
#define OB_WRP1_Pages960to975          ((uint32_t)0x10000000) /* Write protection of Sector60 */
#define OB_WRP1_Pages976to991          ((uint32_t)0x20000000) /* Write protection of Sector61 */
#define OB_WRP1_Pages992to1007         ((uint32_t)0x40000000) /* Write protection of Sector62 */
#define OB_WRP1_Pages1008to1023        ((uint32_t)0x80000000) /* Write protection of Sector63 */

#define OB_WRP1_AllPages               ((uint32_t)0xFFFFFFFF) /*!< Write protection of all Sectors */

#define OB_WRP2_Pages1024to1039        ((uint32_t)0x00000001) /* Write protection of Sector64 */
#define OB_WRP2_Pages1040to1055        ((uint32_t)0x00000002) /* Write protection of Sector65 */
#define OB_WRP2_Pages1056to1071        ((uint32_t)0x00000004) /* Write protection of Sector66 */
#define OB_WRP2_Pages1072to1087        ((uint32_t)0x00000008) /* Write protection of Sector67 */
#define OB_WRP2_Pages1088to1103        ((uint32_t)0x00000010) /* Write protection of Sector68 */
#define OB_WRP2_Pages1104to1119        ((uint32_t)0x00000020) /* Write protection of Sector69 */
#define OB_WRP2_Pages1120to1135        ((uint32_t)0x00000040) /* Write protection of Sector70 */
#define OB_WRP2_Pages1136to1151        ((uint32_t)0x00000080) /* Write protection of Sector71 */
#define OB_WRP2_Pages1152to1167        ((uint32_t)0x00000100) /* Write protection of Sector72 */
#define OB_WRP2_Pages1168to1183        ((uint32_t)0x00000200) /* Write protection of Sector73 */
#define OB_WRP2_Pages1184to1199        ((uint32_t)0x00000400) /* Write protection of Sector74 */
#define OB_WRP2_Pages1200to1215        ((uint32_t)0x00000800) /* Write protection of Sector75 */
#define OB_WRP2_Pages1216to1231        ((uint32_t)0x00001000) /* Write protection of Sector76 */
#define OB_WRP2_Pages1232to1247        ((uint32_t)0x00002000) /* Write protection of Sector77 */
#define OB_WRP2_Pages1248to1263        ((uint32_t)0x00004000) /* Write protection of Sector78 */
#define OB_WRP2_Pages1264to1279        ((uint32_t)0x00008000) /* Write protection of Sector79 */
#define OB_WRP2_Pages1280to1295        ((uint32_t)0x00010000) /* Write protection of Sector80 */
#define OB_WRP2_Pages1296to1311        ((uint32_t)0x00020000) /* Write protection of Sector81 */
#define OB_WRP2_Pages1312to1327        ((uint32_t)0x00040000) /* Write protection of Sector82 */
#define OB_WRP2_Pages1328to1343        ((uint32_t)0x00080000) /* Write protection of Sector83 */
#define OB_WRP2_Pages1344to1359        ((uint32_t)0x00100000) /* Write protection of Sector84 */
#define OB_WRP2_Pages1360to1375        ((uint32_t)0x00200000) /* Write protection of Sector85 */
#define OB_WRP2_Pages1376to1391        ((uint32_t)0x00400000) /* Write protection of Sector86 */
#define OB_WRP2_Pages1392to1407        ((uint32_t)0x00800000) /* Write protection of Sector87 */
#define OB_WRP2_Pages1408to1423        ((uint32_t)0x01000000) /* Write protection of Sector88 */
#define OB_WRP2_Pages1424to1439        ((uint32_t)0x02000000) /* Write protection of Sector89 */
#define OB_WRP2_Pages1440to1455        ((uint32_t)0x04000000) /* Write protection of Sector90 */
#define OB_WRP2_Pages1456to1471        ((uint32_t)0x08000000) /* Write protection of Sector91 */
#define OB_WRP2_Pages1472to1487        ((uint32_t)0x10000000) /* Write protection of Sector92 */
#define OB_WRP2_Pages1488to1503        ((uint32_t)0x20000000) /* Write protection of Sector93 */
#define OB_WRP2_Pages1504to1519        ((uint32_t)0x40000000) /* Write protection of Sector94 */
#define OB_WRP2_Pages1520to1535        ((uint32_t)0x80000000) /* Write protection of Sector95 */

#define OB_WRP2_AllPages               ((uint32_t)0xFFFFFFFF) /*!< Write protection of all Sectors */

#define IS_OB_WRP(PAGE) (((PAGE) != 0x0000000))

/**
  * @}
  */

/** @defgroup Option_Bytes_Read_Protection 
  * @{
  */ 

/** 
  * @brief  Read Protection Level  
  */ 
#define OB_RDP_Level_0   ((uint8_t)0xAA)
#define OB_RDP_Level_1   ((uint8_t)0xBB)
/*#define OB_RDP_Level_2   ((uint8_t)0xCC)*/ /* Warning: When enabling read protection level 2 
                                                it's no more possible to go back to level 1 or 0 */

#define IS_OB_RDP(LEVEL) (((LEVEL) == OB_RDP_Level_0)||\
                          ((LEVEL) == OB_RDP_Level_1))/*||\
                          ((LEVEL) == OB_RDP_Level_2))*/
/**
  * @}
  */ 

/** @defgroup Option_Bytes_IWatchdog 
  * @{
  */

#define OB_IWDG_SW                     ((uint8_t)0x10)  /*!< Software WDG selected */
#define OB_IWDG_HW                     ((uint8_t)0x00)  /*!< Hardware WDG selected */
#define IS_OB_IWDG_SOURCE(SOURCE) (((SOURCE) == OB_IWDG_SW) || ((SOURCE) == OB_IWDG_HW))

/**
  * @}
  */

/** @defgroup Option_Bytes_nRST_STOP 
  * @{
  */

#define OB_STOP_NoRST                  ((uint8_t)0x20) /*!< No reset generated when entering in STOP */
#define OB_STOP_RST                    ((uint8_t)0x00) /*!< Reset generated when entering in STOP */
#define IS_OB_STOP_SOURCE(SOURCE) (((SOURCE) == OB_STOP_NoRST) || ((SOURCE) == OB_STOP_RST))

/**
  * @}
  */

/** @defgroup Option_Bytes_nRST_STDBY 
  * @{
  */

#define OB_STDBY_NoRST                 ((uint8_t)0x40) /*!< No reset generated when entering in STANDBY */
#define OB_STDBY_RST                   ((uint8_t)0x00) /*!< Reset generated when entering in STANDBY */
#define IS_OB_STDBY_SOURCE(SOURCE) (((SOURCE) == OB_STDBY_NoRST) || ((SOURCE) == OB_STDBY_RST))

/**
  * @}
  */

/** @defgroup Option_Bytes_BOOT
  * @{
  */

#define OB_BOOT_BANK2                  ((uint8_t)0x00) /*!< At startup, if boot pins are set in boot from user Flash position
                                                            and this parameter is selected the device will boot from Bank 2 
                                                            or Bank 1, depending on the activation of the bank */
#define OB_BOOT_BANK1                  ((uint8_t)0x80) /*!< At startup, if boot pins are set in boot from user Flash position
                                                            and this parameter is selected the device will boot from Bank1(Default) */
#define IS_OB_BOOT_BANK(BANK) (((BANK) == OB_BOOT_BANK2) || ((BANK) == OB_BOOT_BANK1))

/**
  * @}
  */

/** @defgroup Option_Bytes_BOR_Level 
  * @{
  */

#define OB_BOR_OFF       ((uint8_t)0x00) /*!< BOR is disabled at power down, the reset is asserted when the VDD 
                                              power supply reaches the PDR(Power Down Reset) threshold (1.5V) */
#define OB_BOR_LEVEL1    ((uint8_t)0x08) /*!< BOR Reset threshold levels for 1.7V - 1.8V VDD power supply    */
#define OB_BOR_LEVEL2    ((uint8_t)0x09) /*!< BOR Reset threshold levels for 1.9V - 2.0V VDD power supply    */
#define OB_BOR_LEVEL3    ((uint8_t)0x0A) /*!< BOR Reset threshold levels for 2.3V - 2.4V VDD power supply    */
#define OB_BOR_LEVEL4    ((uint8_t)0x0B) /*!< BOR Reset threshold levels for 2.55V - 2.65V VDD power supply  */
#define OB_BOR_LEVEL5    ((uint8_t)0x0C) /*!< BOR Reset threshold levels for 2.8V - 2.9V VDD power supply    */

#define IS_OB_BOR_LEVEL(LEVEL)  (((LEVEL) == OB_BOR_OFF) || \
                                 ((LEVEL) == OB_BOR_LEVEL1) || \
                                 ((LEVEL) == OB_BOR_LEVEL2) || \
                                 ((LEVEL) == OB_BOR_LEVEL3) || \
                                 ((LEVEL) == OB_BOR_LEVEL4) || \
                                 ((LEVEL) == OB_BOR_LEVEL5))

/**
  * @}
  */
  
/** @defgroup FLASH_Flags 
  * @{
  */ 

#define FLASH_FLAG_BSY                 FLASH_SR_BSY  /*!< FLASH Busy flag */
#define FLASH_FLAG_EOP                 FLASH_SR_EOP  /*!< FLASH End of Programming flag */
#define FLASH_FLAG_ENDHV               FLASH_SR_ENHV  /*!< FLASH End of High Voltage flag */
#define FLASH_FLAG_READY               FLASH_SR_READY  /*!< FLASH Ready flag after low power mode */
#define FLASH_FLAG_WRPERR              FLASH_SR_WRPERR  /*!< FLASH Write protected error flag */
#define FLASH_FLAG_PGAERR              FLASH_SR_PGAERR  /*!< FLASH Programming Alignment error flag */
#define FLASH_FLAG_SIZERR              FLASH_SR_SIZERR  /*!< FLASH Size error flag  */
#define FLASH_FLAG_OPTVERR             FLASH_SR_OPTVERR  /*!< FLASH Option Validity error flag  */
#define FLASH_FLAG_OPTVERRUSR          FLASH_SR_OPTVERRUSR  /*!< FLASH Option User Validity error flag  */
 
#define IS_FLASH_CLEAR_FLAG(FLAG) ((((FLAG) & (uint32_t)0xFFFFE0FD) == 0x00000000) && ((FLAG) != 0x00000000))

#define IS_FLASH_GET_FLAG(FLAG)  (((FLAG) == FLASH_FLAG_BSY) || ((FLAG) == FLASH_FLAG_EOP) || \
                                  ((FLAG) == FLASH_FLAG_ENDHV) || ((FLAG) == FLASH_FLAG_READY ) || \
                                  ((FLAG) ==  FLASH_FLAG_WRPERR) || ((FLAG) == FLASH_FLAG_PGAERR ) || \
                                  ((FLAG) ==  FLASH_FLAG_SIZERR) || ((FLAG) == FLASH_FLAG_OPTVERR) || \
                                  ((FLAG) ==  FLASH_FLAG_OPTVERRUSR))
/**
  * @}
  */ 

/** @defgroup FLASH_Keys 
  * @{
  */ 

#define FLASH_PDKEY1               ((uint32_t)0x04152637) /*!< Flash power down key1 */
#define FLASH_PDKEY2               ((uint32_t)0xFAFBFCFD) /*!< Flash power down key2: used with FLASH_PDKEY1 
                                                              to unlock the RUN_PD bit in FLASH_ACR */

#define FLASH_PEKEY1               ((uint32_t)0x89ABCDEF) /*!< Flash program erase key1 */
#define FLASH_PEKEY2               ((uint32_t)0x02030405) /*!< Flash program erase key: used with FLASH_PEKEY2
                                                               to unlock the write access to the FLASH_PECR register and
                                                               data EEPROM */

#define FLASH_PRGKEY1              ((uint32_t)0x8C9DAEBF) /*!< Flash program memory key1 */
#define FLASH_PRGKEY2              ((uint32_t)0x13141516) /*!< Flash program memory key2: used with FLASH_PRGKEY2
                                                               to unlock the program memory */

#define FLASH_OPTKEY1              ((uint32_t)0xFBEAD9C8) /*!< Flash option key1 */
#define FLASH_OPTKEY2              ((uint32_t)0x24252627) /*!< Flash option key2: used with FLASH_OPTKEY1 to
                                                              unlock the write access to the option byte block */
/**
  * @}
  */
  
/** @defgroup Timeout_definition 
  * @{
  */ 
#define FLASH_ER_PRG_TIMEOUT         ((uint32_t)0x8000)

/**
  * @}
  */ 

/** @defgroup CMSIS_Legacy 
  * @{
  */
#if defined ( __ICCARM__ )   
#define InterruptType_ACTLR_DISMCYCINT_Msk         IntType_ACTLR_DISMCYCINT_Msk
#endif
/**
  * @}
  */ 
/**
  * @}
  */ 

/* Exported macro ------------------------------------------------------------*/
/* Exported functions ------------------------------------------------------- */
  
/** 
  * @brief  FLASH memory functions that can be executed from FLASH.  
  */  
/* FLASH Interface configuration functions ************************************/  
void FLASH_SetLatency(uint32_t FLASH_Latency);
void FLASH_PrefetchBufferCmd(FunctionalState NewState);
void FLASH_ReadAccess64Cmd(FunctionalState NewState);
void FLASH_SLEEPPowerDownCmd(FunctionalState NewState);

/* FLASH Memory Programming functions *****************************************/   
void FLASH_Unlock(void);
void FLASH_Lock(void);
FLASH_Status FLASH_ErasePage(uint32_t Page_Address);
FLASH_Status FLASH_FastProgramWord(uint32_t Address, uint32_t Data);

/* DATA EEPROM Programming functions ******************************************/  
void DATA_EEPROM_Unlock(void);
void DATA_EEPROM_Lock(void);
void DATA_EEPROM_FixedTimeProgramCmd(FunctionalState NewState);
FLASH_Status DATA_EEPROM_EraseByte(uint32_t Address);
FLASH_Status DATA_EEPROM_EraseHalfWord(uint32_t Address);
FLASH_Status DATA_EEPROM_EraseWord(uint32_t Address);
FLASH_Status DATA_EEPROM_FastProgramByte(uint32_t Address, uint8_t Data);
FLASH_Status DATA_EEPROM_FastProgramHalfWord(uint32_t Address, uint16_t Data);
FLASH_Status DATA_EEPROM_FastProgramWord(uint32_t Address, uint32_t Data);
FLASH_Status DATA_EEPROM_ProgramByte(uint32_t Address, uint8_t Data);
FLASH_Status DATA_EEPROM_ProgramHalfWord(uint32_t Address, uint16_t Data);
FLASH_Status DATA_EEPROM_ProgramWord(uint32_t Address, uint32_t Data);

/* Option Bytes Programming functions *****************************************/
void FLASH_OB_Unlock(void);
void FLASH_OB_Lock(void);
void FLASH_OB_Launch(void);
FLASH_Status FLASH_OB_WRPConfig(uint32_t OB_WRP, FunctionalState NewState);
FLASH_Status FLASH_OB_WRP1Config(uint32_t OB_WRP1, FunctionalState NewState);
FLASH_Status FLASH_OB_WRP2Config(uint32_t OB_WRP2, FunctionalState NewState);
FLASH_Status FLASH_OB_RDPConfig(uint8_t OB_RDP);
FLASH_Status FLASH_OB_UserConfig(uint8_t OB_IWDG, uint8_t OB_STOP, uint8_t OB_STDBY);
FLASH_Status FLASH_OB_BORConfig(uint8_t OB_BOR);
FLASH_Status FLASH_OB_BootConfig(uint8_t OB_BOOT);
uint8_t FLASH_OB_GetUser(void);
uint32_t FLASH_OB_GetWRP(void);
uint32_t FLASH_OB_GetWRP1(void);
uint32_t FLASH_OB_GetWRP2(void);
FlagStatus FLASH_OB_GetRDP(void);
uint8_t FLASH_OB_GetBOR(void);

/* Interrupts and flags management functions **********************************/  
void FLASH_ITConfig(uint32_t FLASH_IT, FunctionalState NewState);
FlagStatus FLASH_GetFlagStatus(uint32_t FLASH_FLAG);
void FLASH_ClearFlag(uint32_t FLASH_FLAG);
FLASH_Status FLASH_GetStatus(void);
FLASH_Status FLASH_WaitForLastOperation(uint32_t Timeout);

/** 
  * @brief  FLASH memory functions that should be executed from internal SRAM.
  *         These functions are defined inside the "stm32l1xx_flash_ramfunc.c"
  *         file.
  */ 
__RAM_FUNC FLASH_RUNPowerDownCmd(FunctionalState NewState);
__RAM_FUNC FLASH_EraseParallelPage(uint32_t Page_Address1, uint32_t Page_Address2);
__RAM_FUNC FLASH_ProgramHalfPage(uint32_t Address, uint32_t* pBuffer);
__RAM_FUNC FLASH_ProgramParallelHalfPage(uint32_t Address1, uint32_t* pBuffer1, uint32_t Address2, uint32_t* pBuffer2);
__RAM_FUNC DATA_EEPROM_EraseDoubleWord(uint32_t Address);
__RAM_FUNC DATA_EEPROM_ProgramDoubleWord(uint32_t Address, uint64_t Data);
  
#ifdef __cplusplus
}
#endif

#endif /* __STM32L1xx_FLASH_H */

/**
  * @}
  */

/**
  * @}
  */ 

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
