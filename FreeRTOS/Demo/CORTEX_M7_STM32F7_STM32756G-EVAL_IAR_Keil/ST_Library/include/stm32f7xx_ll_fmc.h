/**
  ******************************************************************************
  * @file    stm32f7xx_ll_fmc.h
  * @author  MCD Application Team
  * @version V1.0.0
  * @date    12-May-2015
  * @brief   Header file of FMC HAL module.
  ******************************************************************************
  * @attention
  *
  * <h2><center>&copy; COPYRIGHT(c) 2015 STMicroelectronics</center></h2>
  *
  * Redistribution and use in source and binary forms, with or without modification,
  * are permitted provided that the following conditions are met:
  *   1. Redistributions of source code must retain the above copyright notice,
  *      this list of conditions and the following disclaimer.
  *   2. Redistributions in binary form must reproduce the above copyright notice,
  *      this list of conditions and the following disclaimer in the documentation
  *      and/or other materials provided with the distribution.
  *   3. Neither the name of STMicroelectronics nor the names of its contributors
  *      may be used to endorse or promote products derived from this software
  *      without specific prior written permission.
  *
  * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
  * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
  * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
  * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
  * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
  * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
  * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
  * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
  * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
  * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
  *
  ******************************************************************************
  */ 

/* Define to prevent recursive inclusion -------------------------------------*/
#ifndef __STM32F7xx_LL_FMC_H
#define __STM32F7xx_LL_FMC_H

#ifdef __cplusplus
 extern "C" {
#endif

/* Includes ------------------------------------------------------------------*/
#include "stm32f7xx_hal_def.h"

/** @addtogroup STM32F7xx_HAL_Driver
  * @{
  */

/** @addtogroup FMC_LL
  * @{
  */

/** @addtogroup FMC_LL_Private_Macros
  * @{
  */
#define IS_FMC_NORSRAM_BANK(BANK) (((BANK) == FMC_NORSRAM_BANK1) || \
                                   ((BANK) == FMC_NORSRAM_BANK2) || \
                                   ((BANK) == FMC_NORSRAM_BANK3) || \
                                   ((BANK) == FMC_NORSRAM_BANK4))

#define IS_FMC_MUX(__MUX__) (((__MUX__) == FMC_DATA_ADDRESS_MUX_DISABLE) || \
                              ((__MUX__) == FMC_DATA_ADDRESS_MUX_ENABLE))

#define IS_FMC_MEMORY(__MEMORY__) (((__MEMORY__) == FMC_MEMORY_TYPE_SRAM) || \
                                    ((__MEMORY__) == FMC_MEMORY_TYPE_PSRAM)|| \
                                    ((__MEMORY__) == FMC_MEMORY_TYPE_NOR))

#define IS_FMC_NORSRAM_MEMORY_WIDTH(__WIDTH__) (((__WIDTH__) == FMC_NORSRAM_MEM_BUS_WIDTH_8)  || \
                                                 ((__WIDTH__) == FMC_NORSRAM_MEM_BUS_WIDTH_16) || \
                                                 ((__WIDTH__) == FMC_NORSRAM_MEM_BUS_WIDTH_32))

#define IS_FMC_ACCESS_MODE(__MODE__) (((__MODE__) == FMC_ACCESS_MODE_A) || \
                                       ((__MODE__) == FMC_ACCESS_MODE_B) || \
                                       ((__MODE__) == FMC_ACCESS_MODE_C) || \
                                       ((__MODE__) == FMC_ACCESS_MODE_D))

#define IS_FMC_NAND_BANK(BANK) ((BANK) == FMC_NAND_BANK3)

#define IS_FMC_WAIT_FEATURE(FEATURE) (((FEATURE) == FMC_NAND_WAIT_FEATURE_DISABLE) || \
                                      ((FEATURE) == FMC_NAND_WAIT_FEATURE_ENABLE))

#define IS_FMC_NAND_MEMORY_WIDTH(WIDTH) (((WIDTH) == FMC_NAND_MEM_BUS_WIDTH_8) || \
                                         ((WIDTH) == FMC_NAND_MEM_BUS_WIDTH_16))

#define IS_FMC_ECC_STATE(STATE) (((STATE) == FMC_NAND_ECC_DISABLE) || \
                                 ((STATE) == FMC_NAND_ECC_ENABLE))

#define IS_FMC_ECCPAGE_SIZE(SIZE) (((SIZE) == FMC_NAND_ECC_PAGE_SIZE_256BYTE)  || \
                                   ((SIZE) == FMC_NAND_ECC_PAGE_SIZE_512BYTE)  || \
                                   ((SIZE) == FMC_NAND_ECC_PAGE_SIZE_1024BYTE) || \
                                   ((SIZE) == FMC_NAND_ECC_PAGE_SIZE_2048BYTE) || \
                                   ((SIZE) == FMC_NAND_ECC_PAGE_SIZE_4096BYTE) || \
                                   ((SIZE) == FMC_NAND_ECC_PAGE_SIZE_8192BYTE))
								   
#define IS_FMC_SDMEMORY_WIDTH(WIDTH) (((WIDTH) == FMC_SDRAM_MEM_BUS_WIDTH_8)  || \
                                      ((WIDTH) == FMC_SDRAM_MEM_BUS_WIDTH_16) || \
                                      ((WIDTH) == FMC_SDRAM_MEM_BUS_WIDTH_32))

#define IS_FMC_WRITE_PROTECTION(__WRITE__) (((__WRITE__) == FMC_SDRAM_WRITE_PROTECTION_DISABLE) || \
                                            ((__WRITE__) == FMC_SDRAM_WRITE_PROTECTION_ENABLE))									  

#define IS_FMC_SDCLOCK_PERIOD(__PERIOD__) (((__PERIOD__) == FMC_SDRAM_CLOCK_DISABLE)  || \
                                           ((__PERIOD__) == FMC_SDRAM_CLOCK_PERIOD_2) || \
                                           ((__PERIOD__) == FMC_SDRAM_CLOCK_PERIOD_3))
										   
#define IS_FMC_READ_BURST(__RBURST__) (((__RBURST__) == FMC_SDRAM_RBURST_DISABLE) || \
                                       ((__RBURST__) == FMC_SDRAM_RBURST_ENABLE))
									   
#define IS_FMC_READPIPE_DELAY(__DELAY__) (((__DELAY__) == FMC_SDRAM_RPIPE_DELAY_0) || \
                                          ((__DELAY__) == FMC_SDRAM_RPIPE_DELAY_1) || \
                                          ((__DELAY__) == FMC_SDRAM_RPIPE_DELAY_2))

#define IS_FMC_COMMAND_MODE(__COMMAND__) (((__COMMAND__) == FMC_SDRAM_CMD_NORMAL_MODE)      || \
                                          ((__COMMAND__) == FMC_SDRAM_CMD_CLK_ENABLE)       || \
                                          ((__COMMAND__) == FMC_SDRAM_CMD_PALL)             || \
                                          ((__COMMAND__) == FMC_SDRAM_CMD_AUTOREFRESH_MODE) || \
                                          ((__COMMAND__) == FMC_SDRAM_CMD_LOAD_MODE)        || \
                                          ((__COMMAND__) == FMC_SDRAM_CMD_SELFREFRESH_MODE) || \
                                          ((__COMMAND__) == FMC_SDRAM_CMD_POWERDOWN_MODE))

#define IS_FMC_COMMAND_TARGET(__TARGET__) (((__TARGET__) == FMC_SDRAM_CMD_TARGET_BANK1) || \
                                           ((__TARGET__) == FMC_SDRAM_CMD_TARGET_BANK2) || \
                                           ((__TARGET__) == FMC_SDRAM_CMD_TARGET_BANK1_2)) 										  
						   
/** @defgroup FMC_TCLR_Setup_Time FMC TCLR Setup Time
  * @{
  */
#define IS_FMC_TCLR_TIME(__TIME__) ((__TIME__) <= 255)
/**
  * @}
  */

/** @defgroup FMC_TAR_Setup_Time FMC TAR Setup Time 
  * @{
  */
#define IS_FMC_TAR_TIME(TIME) ((TIME) <= 255)
/**
  * @}
  */

/** @defgroup FMC_Setup_Time FMC Setup Time 
  * @{
  */
#define IS_FMC_SETUP_TIME(TIME) ((TIME) <= 255)
/**
  * @}
  */

/** @defgroup FMC_Wait_Setup_Time FMC Wait Setup Time 
  * @{
  */
#define IS_FMC_WAIT_TIME(TIME) ((TIME) <= 255)
/**
  * @}
  */

/** @defgroup FMC_Hold_Setup_Time FMC Hold Setup Time 
  * @{
  */
#define IS_FMC_HOLD_TIME(TIME) ((TIME) <= 255)
/**
  * @}
  */

/** @defgroup FMC_HiZ_Setup_Time FMC HiZ Setup Time 
  * @{
  */
#define IS_FMC_HIZ_TIME(TIME) ((TIME) <= 255)
/**
  * @}
  */

#define IS_FMC_BURSTMODE(__STATE__) (((__STATE__) == FMC_BURST_ACCESS_MODE_DISABLE) || \
                                      ((__STATE__) == FMC_BURST_ACCESS_MODE_ENABLE))

#define IS_FMC_WAIT_POLARITY(__POLARITY__) (((__POLARITY__) == FMC_WAIT_SIGNAL_POLARITY_LOW) || \
                                             ((__POLARITY__) == FMC_WAIT_SIGNAL_POLARITY_HIGH))

#define IS_FMC_WAIT_SIGNAL_ACTIVE(__ACTIVE__) (((__ACTIVE__) == FMC_WAIT_TIMING_BEFORE_WS) || \
                                                ((__ACTIVE__) == FMC_WAIT_TIMING_DURING_WS)) 

#define IS_FMC_WRITE_OPERATION(__OPERATION__) (((__OPERATION__) == FMC_WRITE_OPERATION_DISABLE) || \
                                                ((__OPERATION__) == FMC_WRITE_OPERATION_ENABLE))

#define IS_FMC_WAITE_SIGNAL(__SIGNAL__) (((__SIGNAL__) == FMC_WAIT_SIGNAL_DISABLE) || \
                                          ((__SIGNAL__) == FMC_WAIT_SIGNAL_ENABLE))

#define IS_FMC_EXTENDED_MODE(__MODE__) (((__MODE__) == FMC_EXTENDED_MODE_DISABLE) || \
                                         ((__MODE__) == FMC_EXTENDED_MODE_ENABLE))

#define IS_FMC_ASYNWAIT(__STATE__) (((__STATE__) == FMC_ASYNCHRONOUS_WAIT_DISABLE) || \
                                     ((__STATE__) == FMC_ASYNCHRONOUS_WAIT_ENABLE))

/** @defgroup FMC_Data_Latency FMC Data Latency 
  * @{
  */
#define IS_FMC_DATA_LATENCY(__LATENCY__) (((__LATENCY__) > 1) && ((__LATENCY__) <= 17))
/**
  * @}
  */

#define IS_FMC_WRITE_BURST(__BURST__) (((__BURST__) == FMC_WRITE_BURST_DISABLE) || \
                                        ((__BURST__) == FMC_WRITE_BURST_ENABLE))

#define IS_FMC_CONTINOUS_CLOCK(CCLOCK) (((CCLOCK) == FMC_CONTINUOUS_CLOCK_SYNC_ONLY) || \
                                        ((CCLOCK) == FMC_CONTINUOUS_CLOCK_SYNC_ASYNC))


/** @defgroup FMC_Address_Setup_Time FMC Address Setup Time
  * @{
  */
#define IS_FMC_ADDRESS_SETUP_TIME(__TIME__) ((__TIME__) <= 15)
/**
  * @}
  */

/** @defgroup FMC_Address_Hold_Time FMC Address Hold Time
  * @{
  */
#define IS_FMC_ADDRESS_HOLD_TIME(__TIME__) (((__TIME__) > 0) && ((__TIME__) <= 15))
/**
  * @}
  */

/** @defgroup FMC_Data_Setup_Time FMC Data Setup Time
  * @{
  */
#define IS_FMC_DATASETUP_TIME(__TIME__) (((__TIME__) > 0) && ((__TIME__) <= 255))
/**
  * @}
  */

/** @defgroup FMC_Bus_Turn_around_Duration FMC Bus Turn around Duration
  * @{
  */
#define IS_FMC_TURNAROUND_TIME(__TIME__) ((__TIME__) <= 15)
/**
  * @}
  */

/** @defgroup FMC_CLK_Division FMC CLK Division 
  * @{
  */
#define IS_FMC_CLK_DIV(DIV) (((DIV) > 1) && ((DIV) <= 16))
/**
  * @}
  */

/** @defgroup FMC_SDRAM_LoadToActive_Delay FMC SDRAM LoadToActive Delay
  * @{
  */
#define IS_FMC_LOADTOACTIVE_DELAY(__DELAY__) (((__DELAY__) > 0) && ((__DELAY__) <= 16))
/**
  * @}
  */
  
/** @defgroup FMC_SDRAM_ExitSelfRefresh_Delay FMC SDRAM ExitSelfRefresh Delay
  * @{
  */
#define IS_FMC_EXITSELFREFRESH_DELAY(__DELAY__) (((__DELAY__) > 0) && ((__DELAY__) <= 16))
/**
  * @}
  */ 
     
/** @defgroup FMC_SDRAM_SelfRefresh_Time FMC SDRAM SelfRefresh Time
  * @{
  */  
#define IS_FMC_SELFREFRESH_TIME(__TIME__) (((__TIME__) > 0) && ((__TIME__) <= 16))
/**
  * @}
  */
  
/** @defgroup FMC_SDRAM_RowCycle_Delay FMC SDRAM RowCycle Delay
  * @{
  */  
#define IS_FMC_ROWCYCLE_DELAY(__DELAY__) (((__DELAY__) > 0) && ((__DELAY__) <= 16))
/**
  * @}
  */  
  
/** @defgroup FMC_SDRAM_Write_Recovery_Time FMC SDRAM Write Recovery Time
  * @{
  */  
#define IS_FMC_WRITE_RECOVERY_TIME(__TIME__) (((__TIME__) > 0) && ((__TIME__) <= 16))
/**
  * @}
  */         
  
/** @defgroup FMC_SDRAM_RP_Delay FMC SDRAM RP Delay
  * @{
  */  
#define IS_FMC_RP_DELAY(__DELAY__) (((__DELAY__) > 0) && ((__DELAY__) <= 16))
/**
  * @}
  */ 
  
/** @defgroup FMC_SDRAM_RCD_Delay FMC SDRAM RCD Delay
  * @{
  */  
#define IS_FMC_RCD_DELAY(__DELAY__) (((__DELAY__) > 0) && ((__DELAY__) <= 16))
/**
  * @}
  */
  
/** @defgroup FMC_SDRAM_AutoRefresh_Number FMC SDRAM AutoRefresh Number
  * @{
  */  
#define IS_FMC_AUTOREFRESH_NUMBER(__NUMBER__) (((__NUMBER__) > 0) && ((__NUMBER__) <= 16))
/**
  * @}
  */

/** @defgroup FMC_SDRAM_ModeRegister_Definition FMC SDRAM ModeRegister Definition
  * @{
  */
#define IS_FMC_MODE_REGISTER(__CONTENT__) ((__CONTENT__) <= 8191)
/**
  * @}
  */

/** @defgroup FMC_SDRAM_Refresh_rate FMC SDRAM Refresh rate
  * @{
  */
#define IS_FMC_REFRESH_RATE(__RATE__) ((__RATE__) <= 8191)
/**
  * @}
  */
  
/** @defgroup FMC_NORSRAM_Device_Instance FMC NORSRAM Device Instance
  * @{
  */
#define IS_FMC_NORSRAM_DEVICE(__INSTANCE__) ((__INSTANCE__) == FMC_NORSRAM_DEVICE)
/**
  * @}
  */

/** @defgroup FMC_NORSRAM_EXTENDED_Device_Instance FMC NORSRAM EXTENDED Device Instance
  * @{
  */
#define IS_FMC_NORSRAM_EXTENDED_DEVICE(__INSTANCE__) ((__INSTANCE__) == FMC_NORSRAM_EXTENDED_DEVICE)
/**
  * @}
  */
  
/** @defgroup FMC_NAND_Device_Instance FMC NAND Device Instance
  * @{
  */
#define IS_FMC_NAND_DEVICE(__INSTANCE__) ((__INSTANCE__) == FMC_NAND_DEVICE)
/**
  * @}
  */

/** @defgroup FMC_SDRAM_Device_Instance FMC SDRAM Device Instance
  * @{
  */
#define IS_FMC_SDRAM_DEVICE(__INSTANCE__) ((__INSTANCE__) == FMC_SDRAM_DEVICE)
/**
  * @}
  */

#define IS_FMC_SDRAM_BANK(BANK) (((BANK) == FMC_SDRAM_BANK1) || \
                                 ((BANK) == FMC_SDRAM_BANK2))

#define IS_FMC_COLUMNBITS_NUMBER(COLUMN) (((COLUMN) == FMC_SDRAM_COLUMN_BITS_NUM_8)  || \
                                          ((COLUMN) == FMC_SDRAM_COLUMN_BITS_NUM_9)  || \
                                          ((COLUMN) == FMC_SDRAM_COLUMN_BITS_NUM_10) || \
                                          ((COLUMN) == FMC_SDRAM_COLUMN_BITS_NUM_11))

#define IS_FMC_ROWBITS_NUMBER(ROW) (((ROW) == FMC_SDRAM_ROW_BITS_NUM_11) || \
                                    ((ROW) == FMC_SDRAM_ROW_BITS_NUM_12) || \
                                    ((ROW) == FMC_SDRAM_ROW_BITS_NUM_13))

#define IS_FMC_INTERNALBANK_NUMBER(NUMBER) (((NUMBER) == FMC_SDRAM_INTERN_BANKS_NUM_2) || \
                                            ((NUMBER) == FMC_SDRAM_INTERN_BANKS_NUM_4))


#define IS_FMC_CAS_LATENCY(LATENCY) (((LATENCY) == FMC_SDRAM_CAS_LATENCY_1) || \
                                     ((LATENCY) == FMC_SDRAM_CAS_LATENCY_2) || \
                                     ((LATENCY) == FMC_SDRAM_CAS_LATENCY_3))

#define IS_FMC_PAGESIZE(__SIZE__) (((__SIZE__) == FMC_PAGE_SIZE_NONE) || \
                                   ((__SIZE__) == FMC_PAGE_SIZE_128) || \
                                   ((__SIZE__) == FMC_PAGE_SIZE_256) || \
                                   ((__SIZE__) == FMC_PAGE_SIZE_1024))

#define IS_FMC_WRITE_FIFO(__FIFO__) (((__FIFO__) == FMC_WRITE_FIFO_DISABLE) || \
                                     ((__FIFO__) == FMC_WRITE_FIFO_ENABLE))
/**
  * @}
  */

/* Exported typedef ----------------------------------------------------------*/
/** @defgroup FMC_Exported_typedef FMC Low Layer Exported Types
  * @{
  */
#define FMC_NORSRAM_TypeDef            FMC_Bank1_TypeDef
#define FMC_NORSRAM_EXTENDED_TypeDef   FMC_Bank1E_TypeDef
#define FMC_NAND_TypeDef               FMC_Bank3_TypeDef
#define FMC_SDRAM_TypeDef              FMC_Bank5_6_TypeDef

#define FMC_NORSRAM_DEVICE             FMC_Bank1
#define FMC_NORSRAM_EXTENDED_DEVICE    FMC_Bank1E
#define FMC_NAND_DEVICE                FMC_Bank3
#define FMC_SDRAM_DEVICE               FMC_Bank5_6

/** 
  * @brief  FMC NORSRAM Configuration Structure definition
  */ 
typedef struct
{
  uint32_t NSBank;                       /*!< Specifies the NORSRAM memory device that will be used.
                                              This parameter can be a value of @ref FMC_NORSRAM_Bank                     */

  uint32_t DataAddressMux;               /*!< Specifies whether the address and data values are
                                              multiplexed on the data bus or not. 
                                              This parameter can be a value of @ref FMC_Data_Address_Bus_Multiplexing    */

  uint32_t MemoryType;                   /*!< Specifies the type of external memory attached to
                                              the corresponding memory device.
                                              This parameter can be a value of @ref FMC_Memory_Type                      */

  uint32_t MemoryDataWidth;              /*!< Specifies the external memory device width.
                                              This parameter can be a value of @ref FMC_NORSRAM_Data_Width               */

  uint32_t BurstAccessMode;              /*!< Enables or disables the burst access mode for Flash memory,
                                              valid only with synchronous burst Flash memories.
                                              This parameter can be a value of @ref FMC_Burst_Access_Mode                */

  uint32_t WaitSignalPolarity;           /*!< Specifies the wait signal polarity, valid only when accessing
                                              the Flash memory in burst mode.
                                              This parameter can be a value of @ref FMC_Wait_Signal_Polarity             */

  uint32_t WaitSignalActive;             /*!< Specifies if the wait signal is asserted by the memory one
                                              clock cycle before the wait state or during the wait state,
                                              valid only when accessing memories in burst mode. 
                                              This parameter can be a value of @ref FMC_Wait_Timing                      */

  uint32_t WriteOperation;               /*!< Enables or disables the write operation in the selected device by the FMC. 
                                              This parameter can be a value of @ref FMC_Write_Operation                  */

  uint32_t WaitSignal;                   /*!< Enables or disables the wait state insertion via wait
                                              signal, valid for Flash memory access in burst mode. 
                                              This parameter can be a value of @ref FMC_Wait_Signal                      */

  uint32_t ExtendedMode;                 /*!< Enables or disables the extended mode.
                                              This parameter can be a value of @ref FMC_Extended_Mode                    */

  uint32_t AsynchronousWait;             /*!< Enables or disables wait signal during asynchronous transfers,
                                              valid only with asynchronous Flash memories.
                                              This parameter can be a value of @ref FMC_AsynchronousWait                 */

  uint32_t WriteBurst;                   /*!< Enables or disables the write burst operation.
                                              This parameter can be a value of @ref FMC_Write_Burst                      */

  uint32_t ContinuousClock;              /*!< Enables or disables the FMC clock output to external memory devices.
                                              This parameter is only enabled through the FMC_BCR1 register, and don't care 
                                              through FMC_BCR2..4 registers.
                                              This parameter can be a value of @ref FMC_Continous_Clock                  */

  uint32_t WriteFifo;                    /*!< Enables or disables the write FIFO used by the FMC controller.
                                              This parameter is only enabled through the FMC_BCR1 register, and don't care 
                                              through FMC_BCR2..4 registers.
                                              This parameter can be a value of @ref FMC_Write_FIFO                      */

  uint32_t PageSize;                     /*!< Specifies the memory page size.
                                              This parameter can be a value of @ref FMC_Page_Size                        */

}FMC_NORSRAM_InitTypeDef;

/** 
  * @brief  FMC NORSRAM Timing parameters structure definition  
  */
typedef struct
{
  uint32_t AddressSetupTime;             /*!< Defines the number of HCLK cycles to configure
                                              the duration of the address setup time. 
                                              This parameter can be a value between Min_Data = 0 and Max_Data = 15.
                                              @note This parameter is not used with synchronous NOR Flash memories.      */

  uint32_t AddressHoldTime;              /*!< Defines the number of HCLK cycles to configure
                                              the duration of the address hold time.
                                              This parameter can be a value between Min_Data = 1 and Max_Data = 15. 
                                              @note This parameter is not used with synchronous NOR Flash memories.      */

  uint32_t DataSetupTime;                /*!< Defines the number of HCLK cycles to configure
                                              the duration of the data setup time.
                                              This parameter can be a value between Min_Data = 1 and Max_Data = 255.
                                              @note This parameter is used for SRAMs, ROMs and asynchronous multiplexed 
                                              NOR Flash memories.                                                        */

  uint32_t BusTurnAroundDuration;        /*!< Defines the number of HCLK cycles to configure
                                              the duration of the bus turnaround.
                                              This parameter can be a value between Min_Data = 0 and Max_Data = 15.
                                              @note This parameter is only used for multiplexed NOR Flash memories.      */

  uint32_t CLKDivision;                  /*!< Defines the period of CLK clock output signal, expressed in number of 
                                              HCLK cycles. This parameter can be a value between Min_Data = 2 and Max_Data = 16.
                                              @note This parameter is not used for asynchronous NOR Flash, SRAM or ROM 
                                              accesses.                                                                  */

  uint32_t DataLatency;                  /*!< Defines the number of memory clock cycles to issue
                                              to the memory before getting the first data.
                                              The parameter value depends on the memory type as shown below:
                                              - It must be set to 0 in case of a CRAM
                                              - It is don't care in asynchronous NOR, SRAM or ROM accesses
                                              - It may assume a value between Min_Data = 2 and Max_Data = 17 in NOR Flash memories
                                                with synchronous burst mode enable                                       */

  uint32_t AccessMode;                   /*!< Specifies the asynchronous access mode. 
                                              This parameter can be a value of @ref FMC_Access_Mode                      */
}FMC_NORSRAM_TimingTypeDef;

/** 
  * @brief  FMC NAND Configuration Structure definition  
  */ 
typedef struct
{
  uint32_t NandBank;               /*!< Specifies the NAND memory device that will be used.
                                        This parameter can be a value of @ref FMC_NAND_Bank                    */

  uint32_t Waitfeature;            /*!< Enables or disables the Wait feature for the NAND Memory device.
                                        This parameter can be any value of @ref FMC_Wait_feature               */

  uint32_t MemoryDataWidth;        /*!< Specifies the external memory device width.
                                        This parameter can be any value of @ref FMC_NAND_Data_Width            */

  uint32_t EccComputation;         /*!< Enables or disables the ECC computation.
                                        This parameter can be any value of @ref FMC_ECC                        */

  uint32_t ECCPageSize;            /*!< Defines the page size for the extended ECC.
                                        This parameter can be any value of @ref FMC_ECC_Page_Size              */

  uint32_t TCLRSetupTime;          /*!< Defines the number of HCLK cycles to configure the
                                        delay between CLE low and RE low.
                                        This parameter can be a value between Min_Data = 0 and Max_Data = 255  */

  uint32_t TARSetupTime;           /*!< Defines the number of HCLK cycles to configure the
                                        delay between ALE low and RE low.
                                        This parameter can be a number between Min_Data = 0 and Max_Data = 255 */
}FMC_NAND_InitTypeDef;

/** 
  * @brief  FMC NAND Timing parameters structure definition
  */
typedef struct
{
  uint32_t SetupTime;            /*!< Defines the number of HCLK cycles to setup address before
                                      the command assertion for NAND-Flash read or write access
                                      to common/Attribute or I/O memory space (depending on
                                      the memory space timing to be configured).
                                      This parameter can be a value between Min_Data = 0 and Max_Data = 255    */

  uint32_t WaitSetupTime;        /*!< Defines the minimum number of HCLK cycles to assert the
                                      command for NAND-Flash read or write access to
                                      common/Attribute or I/O memory space (depending on the
                                      memory space timing to be configured). 
                                      This parameter can be a number between Min_Data = 0 and Max_Data = 255   */

  uint32_t HoldSetupTime;        /*!< Defines the number of HCLK clock cycles to hold address
                                      (and data for write access) after the command de-assertion
                                      for NAND-Flash read or write access to common/Attribute
                                      or I/O memory space (depending on the memory space timing
                                      to be configured).
                                      This parameter can be a number between Min_Data = 0 and Max_Data = 255   */

  uint32_t HiZSetupTime;         /*!< Defines the number of HCLK clock cycles during which the
                                      data bus is kept in HiZ after the start of a NAND-Flash
                                      write access to common/Attribute or I/O memory space (depending
                                      on the memory space timing to be configured).
                                      This parameter can be a number between Min_Data = 0 and Max_Data = 255   */
}FMC_NAND_PCC_TimingTypeDef;

/** 
  * @brief  FMC SDRAM Configuration Structure definition  
  */  
typedef struct
{
  uint32_t SDBank;                      /*!< Specifies the SDRAM memory device that will be used.
                                             This parameter can be a value of @ref FMC_SDRAM_Bank                */

  uint32_t ColumnBitsNumber;            /*!< Defines the number of bits of column address.
                                             This parameter can be a value of @ref FMC_SDRAM_Column_Bits_number. */

  uint32_t RowBitsNumber;               /*!< Defines the number of bits of column address.
                                             This parameter can be a value of @ref FMC_SDRAM_Row_Bits_number.    */

  uint32_t MemoryDataWidth;             /*!< Defines the memory device width.
                                             This parameter can be a value of @ref FMC_SDRAM_Memory_Bus_Width.   */

  uint32_t InternalBankNumber;          /*!< Defines the number of the device's internal banks.
                                             This parameter can be of @ref FMC_SDRAM_Internal_Banks_Number.      */

  uint32_t CASLatency;                  /*!< Defines the SDRAM CAS latency in number of memory clock cycles.
                                             This parameter can be a value of @ref FMC_SDRAM_CAS_Latency.        */

  uint32_t WriteProtection;             /*!< Enables the SDRAM device to be accessed in write mode.
                                             This parameter can be a value of @ref FMC_SDRAM_Write_Protection.   */

  uint32_t SDClockPeriod;               /*!< Define the SDRAM Clock Period for both SDRAM devices and they allow 
                                             to disable the clock before changing frequency.
                                             This parameter can be a value of @ref FMC_SDRAM_Clock_Period.       */

  uint32_t ReadBurst;                   /*!< This bit enable the SDRAM controller to anticipate the next read 
                                             commands during the CAS latency and stores data in the Read FIFO.
                                             This parameter can be a value of @ref FMC_SDRAM_Read_Burst.         */

  uint32_t ReadPipeDelay;               /*!< Define the delay in system clock cycles on read data path.
                                             This parameter can be a value of @ref FMC_SDRAM_Read_Pipe_Delay.    */
}FMC_SDRAM_InitTypeDef;

/** 
  * @brief FMC SDRAM Timing parameters structure definition
  */
typedef struct
{
  uint32_t LoadToActiveDelay;            /*!< Defines the delay between a Load Mode Register command and 
                                              an active or Refresh command in number of memory clock cycles.
                                              This parameter can be a value between Min_Data = 1 and Max_Data = 16  */

  uint32_t ExitSelfRefreshDelay;         /*!< Defines the delay from releasing the self refresh command to 
                                              issuing the Activate command in number of memory clock cycles.
                                              This parameter can be a value between Min_Data = 1 and Max_Data = 16  */

  uint32_t SelfRefreshTime;              /*!< Defines the minimum Self Refresh period in number of memory clock 
                                              cycles.
                                              This parameter can be a value between Min_Data = 1 and Max_Data = 16  */

  uint32_t RowCycleDelay;                /*!< Defines the delay between the Refresh command and the Activate command
                                              and the delay between two consecutive Refresh commands in number of 
                                              memory clock cycles.
                                              This parameter can be a value between Min_Data = 1 and Max_Data = 16  */

  uint32_t WriteRecoveryTime;            /*!< Defines the Write recovery Time in number of memory clock cycles.
                                              This parameter can be a value between Min_Data = 1 and Max_Data = 16  */

  uint32_t RPDelay;                      /*!< Defines the delay between a Precharge Command and an other command 
                                              in number of memory clock cycles.
                                              This parameter can be a value between Min_Data = 1 and Max_Data = 16  */

  uint32_t RCDDelay;                     /*!< Defines the delay between the Activate Command and a Read/Write 
                                              command in number of memory clock cycles.
                                              This parameter can be a value between Min_Data = 1 and Max_Data = 16  */ 
}FMC_SDRAM_TimingTypeDef;

/** 
  * @brief SDRAM command parameters structure definition
  */
typedef struct
{
  uint32_t CommandMode;                  /*!< Defines the command issued to the SDRAM device.
                                              This parameter can be a value of @ref FMC_SDRAM_Command_Mode.          */

  uint32_t CommandTarget;                /*!< Defines which device (1 or 2) the command will be issued to.
                                              This parameter can be a value of @ref FMC_SDRAM_Command_Target.        */

  uint32_t AutoRefreshNumber;            /*!< Defines the number of consecutive auto refresh command issued
                                              in auto refresh mode.
                                              This parameter can be a value between Min_Data = 1 and Max_Data = 16   */
  uint32_t ModeRegisterDefinition;       /*!< Defines the SDRAM Mode register content                                */
}FMC_SDRAM_CommandTypeDef;
/**
  * @}
  */

/* Exported constants --------------------------------------------------------*/
/** @addtogroup FMC_LL_Exported_Constants FMC Low Layer Exported Constants
  * @{
  */

/** @defgroup FMC_LL_NOR_SRAM_Controller FMC NOR/SRAM Controller 
  * @{
  */

/** @defgroup FMC_NORSRAM_Bank FMC NOR/SRAM Bank
  * @{
  */
#define FMC_NORSRAM_BANK1                       ((uint32_t)0x00000000)
#define FMC_NORSRAM_BANK2                       ((uint32_t)0x00000002)
#define FMC_NORSRAM_BANK3                       ((uint32_t)0x00000004)
#define FMC_NORSRAM_BANK4                       ((uint32_t)0x00000006)
/**
  * @}
  */

/** @defgroup FMC_Data_Address_Bus_Multiplexing FMC Data Address Bus Multiplexing
  * @{
  */
#define FMC_DATA_ADDRESS_MUX_DISABLE            ((uint32_t)0x00000000)
#define FMC_DATA_ADDRESS_MUX_ENABLE             ((uint32_t)0x00000002)
/**
  * @}
  */

/** @defgroup FMC_Memory_Type FMC Memory Type
  * @{
  */
#define FMC_MEMORY_TYPE_SRAM                    ((uint32_t)0x00000000)
#define FMC_MEMORY_TYPE_PSRAM                   ((uint32_t)0x00000004)
#define FMC_MEMORY_TYPE_NOR                     ((uint32_t)0x00000008)
/**
  * @}
  */

/** @defgroup FMC_NORSRAM_Data_Width FMC NORSRAM Data Width
  * @{
  */
#define FMC_NORSRAM_MEM_BUS_WIDTH_8             ((uint32_t)0x00000000)
#define FMC_NORSRAM_MEM_BUS_WIDTH_16            ((uint32_t)0x00000010)
#define FMC_NORSRAM_MEM_BUS_WIDTH_32            ((uint32_t)0x00000020)
/**
  * @}
  */

/** @defgroup FMC_NORSRAM_Flash_Access FMC NOR/SRAM Flash Access
  * @{
  */
#define FMC_NORSRAM_FLASH_ACCESS_ENABLE         ((uint32_t)0x00000040)
#define FMC_NORSRAM_FLASH_ACCESS_DISABLE        ((uint32_t)0x00000000)
/**
  * @}
  */

/** @defgroup FMC_Burst_Access_Mode FMC Burst Access Mode
  * @{
  */
#define FMC_BURST_ACCESS_MODE_DISABLE           ((uint32_t)0x00000000) 
#define FMC_BURST_ACCESS_MODE_ENABLE            ((uint32_t)0x00000100)
/**
  * @}
  */

/** @defgroup FMC_Wait_Signal_Polarity FMC Wait Signal Polarity
  * @{
  */
#define FMC_WAIT_SIGNAL_POLARITY_LOW            ((uint32_t)0x00000000)
#define FMC_WAIT_SIGNAL_POLARITY_HIGH           ((uint32_t)0x00000200)
/**
  * @}
  */

/** @defgroup FMC_Wait_Timing FMC Wait Timing
  * @{
  */
#define FMC_WAIT_TIMING_BEFORE_WS               ((uint32_t)0x00000000)
#define FMC_WAIT_TIMING_DURING_WS               ((uint32_t)0x00000800) 
/**
  * @}
  */

/** @defgroup FMC_Write_Operation FMC Write Operation
  * @{
  */
#define FMC_WRITE_OPERATION_DISABLE             ((uint32_t)0x00000000)
#define FMC_WRITE_OPERATION_ENABLE              ((uint32_t)0x00001000)
/**
  * @}
  */

/** @defgroup FMC_Wait_Signal FMC Wait Signal
  * @{
  */
#define FMC_WAIT_SIGNAL_DISABLE                 ((uint32_t)0x00000000)
#define FMC_WAIT_SIGNAL_ENABLE                  ((uint32_t)0x00002000)
/**
  * @}
  */

/** @defgroup FMC_Extended_Mode FMC Extended Mode
  * @{
  */
#define FMC_EXTENDED_MODE_DISABLE               ((uint32_t)0x00000000)
#define FMC_EXTENDED_MODE_ENABLE                ((uint32_t)0x00004000)
/**
  * @}
  */

/** @defgroup FMC_AsynchronousWait FMC Asynchronous Wait
  * @{
  */
#define FMC_ASYNCHRONOUS_WAIT_DISABLE           ((uint32_t)0x00000000)
#define FMC_ASYNCHRONOUS_WAIT_ENABLE            ((uint32_t)0x00008000)
/**
  * @}
  */  

/** @defgroup FMC_Page_Size FMC Page Size
  * @{
  */
#define FMC_PAGE_SIZE_NONE           ((uint32_t)0x00000000)
#define FMC_PAGE_SIZE_128            ((uint32_t)FMC_BCR1_CPSIZE_0)
#define FMC_PAGE_SIZE_256            ((uint32_t)FMC_BCR1_CPSIZE_1)
#define FMC_PAGE_SIZE_1024           ((uint32_t)FMC_BCR1_CPSIZE_2)
/**
  * @}
  */  

/** @defgroup FMC_Write_Burst FMC Write Burst
  * @{
  */
#define FMC_WRITE_BURST_DISABLE                 ((uint32_t)0x00000000)
#define FMC_WRITE_BURST_ENABLE                  ((uint32_t)0x00080000) 
/**
  * @}
  */
  
/** @defgroup FMC_Continous_Clock FMC Continuous Clock
  * @{
  */
#define FMC_CONTINUOUS_CLOCK_SYNC_ONLY          ((uint32_t)0x00000000)
#define FMC_CONTINUOUS_CLOCK_SYNC_ASYNC         ((uint32_t)0x00100000)
/**
  * @}
  */ 

/** @defgroup FMC_Write_FIFO FMC Write FIFO 
  * @{
  */
#define FMC_WRITE_FIFO_DISABLE           ((uint32_t)0x00000000)
#define FMC_WRITE_FIFO_ENABLE            ((uint32_t)FMC_BCR1_WFDIS)
/**
  * @}
  */
	
/** @defgroup FMC_Access_Mode FMC Access Mode 
  * @{
  */
#define FMC_ACCESS_MODE_A                        ((uint32_t)0x00000000)
#define FMC_ACCESS_MODE_B                        ((uint32_t)0x10000000) 
#define FMC_ACCESS_MODE_C                        ((uint32_t)0x20000000)
#define FMC_ACCESS_MODE_D                        ((uint32_t)0x30000000)
/**
  * @}
  */
    
/**
  * @}
  */ 

/** @defgroup FMC_LL_NAND_Controller FMC NAND Controller 
  * @{
  */
/** @defgroup FMC_NAND_Bank FMC NAND Bank 
  * @{
  */
#define FMC_NAND_BANK3                          ((uint32_t)0x00000100) 
/**
  * @}
  */

/** @defgroup FMC_Wait_feature FMC Wait feature
  * @{
  */
#define FMC_NAND_WAIT_FEATURE_DISABLE           ((uint32_t)0x00000000)
#define FMC_NAND_WAIT_FEATURE_ENABLE            ((uint32_t)0x00000002)
/**
  * @}
  */

/** @defgroup FMC_PCR_Memory_Type FMC PCR Memory Type 
  * @{
  */
#define FMC_PCR_MEMORY_TYPE_NAND          ((uint32_t)0x00000008)
/**
  * @}
  */

/** @defgroup FMC_NAND_Data_Width FMC NAND Data Width 
  * @{
  */
#define FMC_NAND_MEM_BUS_WIDTH_8                ((uint32_t)0x00000000)
#define FMC_NAND_MEM_BUS_WIDTH_16               ((uint32_t)0x00000010)
/**
  * @}
  */

/** @defgroup FMC_ECC FMC ECC 
  * @{
  */
#define FMC_NAND_ECC_DISABLE                    ((uint32_t)0x00000000)
#define FMC_NAND_ECC_ENABLE                     ((uint32_t)0x00000040)
/**
  * @}
  */

/** @defgroup FMC_ECC_Page_Size FMC ECC Page Size 
  * @{
  */
#define FMC_NAND_ECC_PAGE_SIZE_256BYTE          ((uint32_t)0x00000000)
#define FMC_NAND_ECC_PAGE_SIZE_512BYTE          ((uint32_t)0x00020000)
#define FMC_NAND_ECC_PAGE_SIZE_1024BYTE         ((uint32_t)0x00040000)
#define FMC_NAND_ECC_PAGE_SIZE_2048BYTE         ((uint32_t)0x00060000)
#define FMC_NAND_ECC_PAGE_SIZE_4096BYTE         ((uint32_t)0x00080000)
#define FMC_NAND_ECC_PAGE_SIZE_8192BYTE         ((uint32_t)0x000A0000)
/**
  * @}
  */
  
/**
  * @}
  */ 

/** @defgroup FMC_LL_SDRAM_Controller FMC SDRAM Controller 
  * @{
  */
/** @defgroup FMC_SDRAM_Bank FMC SDRAM Bank
  * @{
  */
#define FMC_SDRAM_BANK1                       ((uint32_t)0x00000000)
#define FMC_SDRAM_BANK2                       ((uint32_t)0x00000001)
/**
  * @}
  */

/** @defgroup FMC_SDRAM_Column_Bits_number FMC SDRAM Column Bits number 
  * @{
  */
#define FMC_SDRAM_COLUMN_BITS_NUM_8           ((uint32_t)0x00000000)
#define FMC_SDRAM_COLUMN_BITS_NUM_9           ((uint32_t)0x00000001)
#define FMC_SDRAM_COLUMN_BITS_NUM_10          ((uint32_t)0x00000002)
#define FMC_SDRAM_COLUMN_BITS_NUM_11          ((uint32_t)0x00000003)
/**
  * @}
  */

/** @defgroup FMC_SDRAM_Row_Bits_number FMC SDRAM Row Bits number
  * @{
  */
#define FMC_SDRAM_ROW_BITS_NUM_11             ((uint32_t)0x00000000)
#define FMC_SDRAM_ROW_BITS_NUM_12             ((uint32_t)0x00000004)
#define FMC_SDRAM_ROW_BITS_NUM_13             ((uint32_t)0x00000008)
/**
  * @}
  */

/** @defgroup FMC_SDRAM_Memory_Bus_Width FMC SDRAM Memory Bus Width
  * @{
  */
#define FMC_SDRAM_MEM_BUS_WIDTH_8             ((uint32_t)0x00000000)
#define FMC_SDRAM_MEM_BUS_WIDTH_16            ((uint32_t)0x00000010)
#define FMC_SDRAM_MEM_BUS_WIDTH_32            ((uint32_t)0x00000020)
/**
  * @}
  */

/** @defgroup FMC_SDRAM_Internal_Banks_Number FMC SDRAM Internal Banks Number
  * @{
  */
#define FMC_SDRAM_INTERN_BANKS_NUM_2          ((uint32_t)0x00000000)
#define FMC_SDRAM_INTERN_BANKS_NUM_4          ((uint32_t)0x00000040)
/**
  * @}
  */

/** @defgroup FMC_SDRAM_CAS_Latency FMC SDRAM CAS Latency
  * @{
  */
#define FMC_SDRAM_CAS_LATENCY_1               ((uint32_t)0x00000080)
#define FMC_SDRAM_CAS_LATENCY_2               ((uint32_t)0x00000100)
#define FMC_SDRAM_CAS_LATENCY_3               ((uint32_t)0x00000180)
/**
  * @}
  */

/** @defgroup FMC_SDRAM_Write_Protection FMC SDRAM Write Protection
  * @{
  */
#define FMC_SDRAM_WRITE_PROTECTION_DISABLE    ((uint32_t)0x00000000)
#define FMC_SDRAM_WRITE_PROTECTION_ENABLE     ((uint32_t)0x00000200)
/**
  * @}
  */

/** @defgroup FMC_SDRAM_Clock_Period FMC SDRAM Clock Period
  * @{
  */
#define FMC_SDRAM_CLOCK_DISABLE               ((uint32_t)0x00000000)
#define FMC_SDRAM_CLOCK_PERIOD_2              ((uint32_t)0x00000800)
#define FMC_SDRAM_CLOCK_PERIOD_3              ((uint32_t)0x00000C00)
/**
  * @}
  */

/** @defgroup FMC_SDRAM_Read_Burst FMC SDRAM Read Burst
  * @{
  */
#define FMC_SDRAM_RBURST_DISABLE              ((uint32_t)0x00000000)
#define FMC_SDRAM_RBURST_ENABLE               ((uint32_t)0x00001000)
/**
  * @}
  */
  
/** @defgroup FMC_SDRAM_Read_Pipe_Delay FMC SDRAM Read Pipe Delay
  * @{
  */
#define FMC_SDRAM_RPIPE_DELAY_0               ((uint32_t)0x00000000)
#define FMC_SDRAM_RPIPE_DELAY_1               ((uint32_t)0x00002000)
#define FMC_SDRAM_RPIPE_DELAY_2               ((uint32_t)0x00004000)
/**
  * @}
  */

/** @defgroup FMC_SDRAM_Command_Mode FMC SDRAM Command Mode
  * @{
  */
#define FMC_SDRAM_CMD_NORMAL_MODE             ((uint32_t)0x00000000)
#define FMC_SDRAM_CMD_CLK_ENABLE              ((uint32_t)0x00000001)
#define FMC_SDRAM_CMD_PALL                    ((uint32_t)0x00000002)
#define FMC_SDRAM_CMD_AUTOREFRESH_MODE        ((uint32_t)0x00000003)
#define FMC_SDRAM_CMD_LOAD_MODE               ((uint32_t)0x00000004)
#define FMC_SDRAM_CMD_SELFREFRESH_MODE        ((uint32_t)0x00000005)
#define FMC_SDRAM_CMD_POWERDOWN_MODE          ((uint32_t)0x00000006)
/**
  * @}
  */

/** @defgroup FMC_SDRAM_Command_Target FMC SDRAM Command Target
  * @{
  */
#define FMC_SDRAM_CMD_TARGET_BANK2            FMC_SDCMR_CTB2
#define FMC_SDRAM_CMD_TARGET_BANK1            FMC_SDCMR_CTB1
#define FMC_SDRAM_CMD_TARGET_BANK1_2          ((uint32_t)0x00000018)
/**
  * @}
  */

/** @defgroup FMC_SDRAM_Mode_Status FMC SDRAM Mode Status 
  * @{
  */
#define FMC_SDRAM_NORMAL_MODE                     ((uint32_t)0x00000000)
#define FMC_SDRAM_SELF_REFRESH_MODE               FMC_SDSR_MODES1_0
#define FMC_SDRAM_POWER_DOWN_MODE                 FMC_SDSR_MODES1_1
/**
  * @}
  */

/**
  * @}
  */ 

/** @defgroup FMC_LL_Interrupt_definition FMC Low Layer Interrupt definition  
  * @{
  */  
#define FMC_IT_RISING_EDGE                ((uint32_t)0x00000008)
#define FMC_IT_LEVEL                      ((uint32_t)0x00000010)
#define FMC_IT_FALLING_EDGE               ((uint32_t)0x00000020)
#define FMC_IT_REFRESH_ERROR              ((uint32_t)0x00004000)
/**
  * @}
  */
    
/** @defgroup FMC_LL_Flag_definition FMC Low Layer Flag definition 
  * @{
  */ 
#define FMC_FLAG_RISING_EDGE                    ((uint32_t)0x00000001)
#define FMC_FLAG_LEVEL                          ((uint32_t)0x00000002)
#define FMC_FLAG_FALLING_EDGE                   ((uint32_t)0x00000004)
#define FMC_FLAG_FEMPT                          ((uint32_t)0x00000040)
#define FMC_SDRAM_FLAG_REFRESH_IT               FMC_SDSR_RE
#define FMC_SDRAM_FLAG_BUSY                     FMC_SDSR_BUSY
#define FMC_SDRAM_FLAG_REFRESH_ERROR            FMC_SDRTR_CRE
/**
  * @}
  */
/**
  * @}
  */

/**
  * @}
  */

/* Private macro -------------------------------------------------------------*/
/** @defgroup FMC_LL_Private_Macros FMC_LL  Private Macros
  * @{
  */

/** @defgroup FMC_LL_NOR_Macros FMC NOR/SRAM Macros
 *  @brief macros to handle NOR device enable/disable and read/write operations
 *  @{
 */
 
/**
  * @brief  Enable the NORSRAM device access.
  * @param  __INSTANCE__: FMC_NORSRAM Instance
  * @param  __BANK__: FMC_NORSRAM Bank     
  * @retval None
  */ 
#define __FMC_NORSRAM_ENABLE(__INSTANCE__, __BANK__)  ((__INSTANCE__)->BTCR[(__BANK__)] |= FMC_BCR1_MBKEN)

/**
  * @brief  Disable the NORSRAM device access.
  * @param  __INSTANCE__: FMC_NORSRAM Instance
  * @param  __BANK__: FMC_NORSRAM Bank   
  * @retval None
  */ 
#define __FMC_NORSRAM_DISABLE(__INSTANCE__, __BANK__) ((__INSTANCE__)->BTCR[(__BANK__)] &= ~FMC_BCR1_MBKEN)  

/**
  * @}
  */ 

/** @defgroup FMC_LL_NAND_Macros FMC NAND Macros
 *  @brief macros to handle NAND device enable/disable
 *  @{
 */
 
/**
  * @brief  Enable the NAND device access.
  * @param  __INSTANCE__: FMC_NAND Instance    
  * @retval None
  */  
#define __FMC_NAND_ENABLE(__INSTANCE__)  ((__INSTANCE__)->PCR |= FMC_PCR_PBKEN)

/**
  * @brief  Disable the NAND device access.
  * @param  __INSTANCE__: FMC_NAND Instance  
  * @retval None
  */
#define __FMC_NAND_DISABLE(__INSTANCE__) ((__INSTANCE__)->PCR &= ~FMC_PCR_PBKEN)

/**
  * @}
  */ 
    
/** @defgroup FMC_Interrupt FMC Interrupt
 *  @brief macros to handle FMC interrupts
 * @{
 */ 

/**
  * @brief  Enable the NAND device interrupt.
  * @param  __INSTANCE__:  FMC_NAND instance     
  * @param  __INTERRUPT__: FMC_NAND interrupt 
  *         This parameter can be any combination of the following values:
  *            @arg FMC_IT_RISING_EDGE: Interrupt rising edge.
  *            @arg FMC_IT_LEVEL: Interrupt level.
  *            @arg FMC_IT_FALLING_EDGE: Interrupt falling edge.       
  * @retval None
  */  
#define __FMC_NAND_ENABLE_IT(__INSTANCE__, __INTERRUPT__)  ((__INSTANCE__)->SR |= (__INTERRUPT__))

/**
  * @brief  Disable the NAND device interrupt.
  * @param  __INSTANCE__:  FMC_NAND Instance
  * @param  __INTERRUPT__: FMC_NAND interrupt
  *         This parameter can be any combination of the following values:
  *            @arg FMC_IT_RISING_EDGE: Interrupt rising edge.
  *            @arg FMC_IT_LEVEL: Interrupt level.
  *            @arg FMC_IT_FALLING_EDGE: Interrupt falling edge.   
  * @retval None
  */
#define __FMC_NAND_DISABLE_IT(__INSTANCE__, __INTERRUPT__)  ((__INSTANCE__)->SR &= ~(__INTERRUPT__))
                                                                                                                           
/**
  * @brief  Get flag status of the NAND device.
  * @param  __INSTANCE__: FMC_NAND Instance
  * @param  __BANK__:     FMC_NAND Bank     
  * @param  __FLAG__: FMC_NAND flag
  *         This parameter can be any combination of the following values:
  *            @arg FMC_FLAG_RISING_EDGE: Interrupt rising edge flag.
  *            @arg FMC_FLAG_LEVEL: Interrupt level edge flag.
  *            @arg FMC_FLAG_FALLING_EDGE: Interrupt falling edge flag.
  *            @arg FMC_FLAG_FEMPT: FIFO empty flag.   
  * @retval The state of FLAG (SET or RESET).
  */
#define __FMC_NAND_GET_FLAG(__INSTANCE__, __BANK__, __FLAG__)  (((__INSTANCE__)->SR &(__FLAG__)) == (__FLAG__))

/**
  * @brief  Clear flag status of the NAND device.
  * @param  __INSTANCE__: FMC_NAND Instance   
  * @param  __FLAG__: FMC_NAND flag
  *         This parameter can be any combination of the following values:
  *            @arg FMC_FLAG_RISING_EDGE: Interrupt rising edge flag.
  *            @arg FMC_FLAG_LEVEL: Interrupt level edge flag.
  *            @arg FMC_FLAG_FALLING_EDGE: Interrupt falling edge flag.
  *            @arg FMC_FLAG_FEMPT: FIFO empty flag.   
  * @retval None
  */
#define __FMC_NAND_CLEAR_FLAG(__INSTANCE__, __FLAG__)  ((__INSTANCE__)->SR &= ~(__FLAG__))  

/**
  * @brief  Enable the SDRAM device interrupt.
  * @param  __INSTANCE__: FMC_SDRAM instance  
  * @param  __INTERRUPT__: FMC_SDRAM interrupt 
  *         This parameter can be any combination of the following values:
  *            @arg FMC_IT_REFRESH_ERROR: Interrupt refresh error      
  * @retval None
  */
#define __FMC_SDRAM_ENABLE_IT(__INSTANCE__, __INTERRUPT__)  ((__INSTANCE__)->SDRTR |= (__INTERRUPT__))

/**
  * @brief  Disable the SDRAM device interrupt.
  * @param  __INSTANCE__: FMC_SDRAM instance  
  * @param  __INTERRUPT__: FMC_SDRAM interrupt 
  *         This parameter can be any combination of the following values:
  *            @arg FMC_IT_REFRESH_ERROR: Interrupt refresh error      
  * @retval None
  */
#define __FMC_SDRAM_DISABLE_IT(__INSTANCE__, __INTERRUPT__)  ((__INSTANCE__)->SDRTR &= ~(__INTERRUPT__))

/**
  * @brief  Get flag status of the SDRAM device.
  * @param  __INSTANCE__: FMC_SDRAM instance  
  * @param  __FLAG__: FMC_SDRAM flag
  *         This parameter can be any combination of the following values:
  *            @arg FMC_SDRAM_FLAG_REFRESH_IT: Interrupt refresh error.
  *            @arg FMC_SDRAM_FLAG_BUSY: SDRAM busy flag.
  *            @arg FMC_SDRAM_FLAG_REFRESH_ERROR: Refresh error flag.
  * @retval The state of FLAG (SET or RESET).
  */
#define __FMC_SDRAM_GET_FLAG(__INSTANCE__, __FLAG__)  (((__INSTANCE__)->SDSR &(__FLAG__)) == (__FLAG__))

/**
  * @brief  Clear flag status of the SDRAM device.
  * @param  __INSTANCE__: FMC_SDRAM instance  
  * @param  __FLAG__: FMC_SDRAM flag
  *         This parameter can be any combination of the following values:
  *           @arg FMC_SDRAM_FLAG_REFRESH_ERROR
  * @retval None
  */
#define __FMC_SDRAM_CLEAR_FLAG(__INSTANCE__, __FLAG__)  ((__INSTANCE__)->SDRTR |= (__FLAG__))
/**
  * @}
  */

/**
  * @}
  */ 

/* Private functions ---------------------------------------------------------*/
/** @defgroup FMC_LL_Private_Functions FMC LL Private Functions
  *  @{
  */

/** @defgroup FMC_LL_NORSRAM  NOR SRAM
  *  @{
  */
/** @defgroup FMC_LL_NORSRAM_Private_Functions_Group1 NOR SRAM Initialization/de-initialization functions 
  *  @{
  */
HAL_StatusTypeDef  FMC_NORSRAM_Init(FMC_NORSRAM_TypeDef *Device, FMC_NORSRAM_InitTypeDef *Init);
HAL_StatusTypeDef  FMC_NORSRAM_Timing_Init(FMC_NORSRAM_TypeDef *Device, FMC_NORSRAM_TimingTypeDef *Timing, uint32_t Bank);
HAL_StatusTypeDef  FMC_NORSRAM_Extended_Timing_Init(FMC_NORSRAM_EXTENDED_TypeDef *Device, FMC_NORSRAM_TimingTypeDef *Timing, uint32_t Bank, uint32_t ExtendedMode);
HAL_StatusTypeDef  FMC_NORSRAM_DeInit(FMC_NORSRAM_TypeDef *Device, FMC_NORSRAM_EXTENDED_TypeDef *ExDevice, uint32_t Bank);
/**
  * @}
  */ 

/** @defgroup FMC_LL_NORSRAM_Private_Functions_Group2 NOR SRAM Control functions 
  *  @{
  */
HAL_StatusTypeDef  FMC_NORSRAM_WriteOperation_Enable(FMC_NORSRAM_TypeDef *Device, uint32_t Bank);
HAL_StatusTypeDef  FMC_NORSRAM_WriteOperation_Disable(FMC_NORSRAM_TypeDef *Device, uint32_t Bank);
/**
  * @}
  */
/**
  * @}
  */

/** @defgroup FMC_LL_NAND NAND
  *  @{
  */
/** @defgroup FMC_LL_NAND_Private_Functions_Group1 NAND Initialization/de-initialization functions 
  *  @{
  */
HAL_StatusTypeDef  FMC_NAND_Init(FMC_NAND_TypeDef *Device, FMC_NAND_InitTypeDef *Init);
HAL_StatusTypeDef  FMC_NAND_CommonSpace_Timing_Init(FMC_NAND_TypeDef *Device, FMC_NAND_PCC_TimingTypeDef *Timing, uint32_t Bank);
HAL_StatusTypeDef  FMC_NAND_AttributeSpace_Timing_Init(FMC_NAND_TypeDef *Device, FMC_NAND_PCC_TimingTypeDef *Timing, uint32_t Bank);
HAL_StatusTypeDef  FMC_NAND_DeInit(FMC_NAND_TypeDef *Device, uint32_t Bank);
/**
  * @}
  */

/** @defgroup FMC_LL_NAND_Private_Functions_Group2 NAND Control functions 
  *  @{
  */
HAL_StatusTypeDef  FMC_NAND_ECC_Enable(FMC_NAND_TypeDef *Device, uint32_t Bank);
HAL_StatusTypeDef  FMC_NAND_ECC_Disable(FMC_NAND_TypeDef *Device, uint32_t Bank);
HAL_StatusTypeDef  FMC_NAND_GetECC(FMC_NAND_TypeDef *Device, uint32_t *ECCval, uint32_t Bank, uint32_t Timeout);
/**
  * @}
  */

/** @defgroup FMC_LL_SDRAM SDRAM
  *  @{
  */
/** @defgroup FMC_LL_SDRAM_Private_Functions_Group1 SDRAM Initialization/de-initialization functions 
  *  @{
  */
HAL_StatusTypeDef  FMC_SDRAM_Init(FMC_SDRAM_TypeDef *Device, FMC_SDRAM_InitTypeDef *Init);
HAL_StatusTypeDef  FMC_SDRAM_Timing_Init(FMC_SDRAM_TypeDef *Device, FMC_SDRAM_TimingTypeDef *Timing, uint32_t Bank);
HAL_StatusTypeDef  FMC_SDRAM_DeInit(FMC_SDRAM_TypeDef *Device, uint32_t Bank);

/**
  * @}
  */

/** @defgroup FMC_LL_SDRAM_Private_Functions_Group2 SDRAM Control functions 
  *  @{
  */
HAL_StatusTypeDef  FMC_SDRAM_WriteProtection_Enable(FMC_SDRAM_TypeDef *Device, uint32_t Bank);
HAL_StatusTypeDef  FMC_SDRAM_WriteProtection_Disable(FMC_SDRAM_TypeDef *Device, uint32_t Bank);
HAL_StatusTypeDef  FMC_SDRAM_SendCommand(FMC_SDRAM_TypeDef *Device, FMC_SDRAM_CommandTypeDef *Command, uint32_t Timeout);
HAL_StatusTypeDef  FMC_SDRAM_ProgramRefreshRate(FMC_SDRAM_TypeDef *Device, uint32_t RefreshRate);
HAL_StatusTypeDef  FMC_SDRAM_SetAutoRefreshNumber(FMC_SDRAM_TypeDef *Device, uint32_t AutoRefreshNumber);
uint32_t           FMC_SDRAM_GetModeStatus(FMC_SDRAM_TypeDef *Device, uint32_t Bank);
/**
  * @}
  */

/**
  * @}
  */

/**
  * @}
  */

/**
  * @}
  */

/**
  * @}
  */
#ifdef __cplusplus
}
#endif

#endif /* __STM32F7xx_LL_FMC_H */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
