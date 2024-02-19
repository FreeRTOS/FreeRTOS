/** @file sys_selftest.h
 *   @brief System Memory Header File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - Efuse Self Test Functions
 *   .
 *   which are relevant for the System driver.
 */

/*
 * Copyright (C) 2009-2018 Texas Instruments Incorporated - www.ti.com
 *
 *
 *  Redistribution and use in source and binary forms, with or without
 *  modification, are permitted provided that the following conditions
 *  are met:
 *
 *    Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 *    Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the
 *    distribution.
 *
 *    Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 *  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 *  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 *  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 *  A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 *  OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 *  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 *  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 *  DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 *  THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 *  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 *  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 */

#ifndef __sys_selftest_H__
#define __sys_selftest_H__

#include "reg_pbist.h"
#include "reg_stc.h"
#include "reg_efc.h"
#include "sys_core.h"
#include "system.h"
#include "sys_vim.h"
#include "adc.h"
#include "can.h"
#include "mibspi.h"
#include "het.h"
#include "htu.h"
#include "esm.h"

/* USER CODE BEGIN (0) */
/* USER CODE END */

#define flash1bitError  ( *( volatile uint32 * ) ( 0xF00803F0U ) )
#define flash2bitError  ( *( volatile uint32 * ) ( 0xF00803F8U ) )

#define tcramA1bitError ( *( volatile uint32 * ) ( 0x08400000U ) )
#define tcramA2bitError ( *( volatile uint32 * ) ( 0x08400010U ) )

#define tcramB1bitError ( *( volatile uint32 * ) ( 0x08400008U ) )
#define tcramB2bitError ( *( volatile uint32 * ) ( 0x08400018U ) )

#define tcramA1bit      ( *( volatile uint64 * ) ( 0x08000000U ) )
#define tcramA2bit      ( *( volatile uint64 * ) ( 0x08000010U ) )

#define tcramB1bit      ( *( volatile uint64 * ) ( 0x08000008U ) )
#define tcramB2bit      ( *( volatile uint64 * ) ( 0x08000018U ) )

#define flashBadECC1    ( *( volatile uint32 * ) ( 0x20000000U ) )
#define flashBadECC2    ( *( volatile uint32 * ) ( 0x20000010U ) )

#define CCMSR           ( *( volatile uint32 * ) ( 0xFFFFF600U ) )
#define CCMKEYR         ( *( volatile uint32 * ) ( 0xFFFFF604U ) )

#define DMA_PARCR       ( *( volatile uint32 * ) ( 0xFFFFF1A8U ) )
#define DMA_PARADDR     ( *( volatile uint32 * ) ( 0xFFFFF1ACU ) )
#define DMARAMLOC       ( *( volatile uint32 * ) ( 0xFFF80000U ) )
#define DMARAMPARLOC    ( *( volatile uint32 * ) ( 0xFFF80A00U ) )

#define MIBSPI1RAMLOC   ( *( volatile uint32 * ) ( 0xFF0E0000U ) )
#define MIBSPI3RAMLOC   ( *( volatile uint32 * ) ( 0xFF0C0000U ) )
#define MIBSPI5RAMLOC   ( *( volatile uint32 * ) ( 0xFF0A0000U ) )

#ifndef __PBIST_H__
    #define __PBIST_H__

/** @enum pbistPort
 *   @brief Alias names for pbist Port number
 *
 *   This enumeration is used to provide alias names for the pbist Port number
 *     - PBIST_PORT0
 *     - PBIST_PORT1
 *
 *   @note Check the datasheet for the port avaiability
 */
enum pbistPort
{
    PBIST_PORT0 = 0U, /**< Alias for PBIST Port 0 */
    PBIST_PORT1 = 1U /**< Alias for PBIST Port 1 < Check datasheet for Port 1 availability
                        > */
};

/** @enum pbistAlgo
 *   @brief Alias names for pbist Algorithm
 *
 *   This enumeration is used to provide alias names for the pbist Algorithm
 */
enum pbistAlgo
{
    PBIST_TripleReadSlow = 0x00000001U, /**<TRIPLE_READ_SLOW_READ  for PBIST and STC ROM*/
    PBIST_TripleReadFast = 0x00000002U, /**<TRIPLE_READ_SLOW_READ  for PBIST and STC ROM*/
    PBIST_March13N_DP = 0x00000004U,    /**< March13 N Algo for 2 Port mem */
    PBIST_March13N_SP = 0x00000008U,    /**< March13 N Algo for 1 Port mem */
    PBIST_DOWN1a_DP = 0x00000010U, /**< Down1a Algor forces the switching fo all data bits
                                      & most addr bits on consecutive read cycles */
    PBIST_DOWN1a_SP = 0x00000020U, /**< Down1a Algor forces the switching fo all data bits
                                      & most addr bits on consecutive read cycles */
    PBIST_MapColumn_DP = 0x00000040U, /**< Map Column algo (to identify bit line
                                         senstivities) for 2 Port memory */
    PBIST_MapColumn_SP = 0x00000080U, /**< Map Column algo (to identify bit line
                                         senstivities) for 1 Port memory */
    PBIST_Precharge_DP = 0x00000100U, /**< Pre-Charge algo to exercise pre-charge
                                         capability for 2 port memory */
    PBIST_Precharge_SP = 0x00000200U, /**< Pre-Charge algo to exercise pre-charge
                                         capability for 1 port memory */
    PBIST_DTXN2a_DP = 0x00000400U,    /**< Global column decode logic algo for 2 Port
                                         memories*/
    PBIST_DTXN2a_SP = 0x00000800U,    /**< Global column decode logic algo for 1 Port
                                         memories*/
    PBIST_PMOSOpen_DP = 0x00001000U,  /**<pmos oper algo for 2 port memories*/
    PBIST_PMOSOpen_SP = 0x00002000U,  /**<pmos oper algo for 1 port memories*/
    PBIST_PPMOSOpenSlice1_DP = 0x00004000U, /**<pmos open slice1 for 2port memories*/
    PBIST_PPMOSOpenSlice2_DP = 0x00008000U, /**<pmos open slice2 for 2port memories*/
    PBIST_Flip10_DP = 0x00010000U,          /**<flip10 algo for 2 port memories*/
    PBIST_Flip10_SP = 0x00020000U,          /**<flip10  algo for 1 port memories*/
    PBIST_IDDQ_DP = 0x00040000U,            /**<iddq  algo for 2 port memories*/
    PBIST_IDDQ_SP = 0x00080000U,            /**<iddq  algo for 1 port memories*/
    PBIST_Retention_DP = 0x00100000U,       /**<retention  algo for 2 port memories*/
    PBIST_Retention_SP = 0x00200000U,       /**<retention  algo for 1 port memories*/
    PBIST_IDDQ2_DP = 0x00400000U,           /**<iddq2  algo for 2 port memories*/
    PBIST_IDDQ2_SP = 0x00800000U,           /**<iddq2  algo for 1 port memories*/
    PBIST_Retention2_DP = 0x01000000U,      /**<retention2  algo for 2 port memories*/
    PBIST_Retention2_SP = 0x02000000U,      /**<retention2  algo for 1 port memories*/
    PBIST_IDDQRowStripe_DP = 0x04000000U,   /**<iddqwstripe  algo for 2 port memories*/
    PBIST_IDDQRowStripe_SP = 0x08000000U,   /**<iddqwstripe  algo for 1 port memories*/
    PBIST_IDDQRowStripe2_DP = 0x10000000U,  /**<iddqwstripe2  algo for 2 port memories*/
    PBIST_IDDQRowStripe2_SP = 0x20000000U   /**<iddqwstripe2  algo for 1 port memories*/
};
/* PBIST configuration registers */
typedef struct pbist_config_reg
{
    uint32 CONFIG_RAMT;
    uint32 CONFIG_DLR;
    uint32 CONFIG_PACT;
    uint32 CONFIG_PBISTID;
    uint32 CONFIG_OVER;
    uint32 CONFIG_FSRDL1;
    uint32 CONFIG_ROM;
    uint32 CONFIG_ALGO;
    uint32 CONFIG_RINFOL;
    uint32 CONFIG_RINFOU;
} pbist_config_reg_t;

    /* PBIST and STC ROM - PBIST RAM GROUPING */
    #define PBIST_ROM_PBIST_RAM_GROUP 1U
    #define STC_ROM_PBIST_RAM_GROUP   2U

    /* PBIST congiruration registers initial value */
    #define PBIST_RAMT_CONFIGVALUE    0U
    #define PBIST_DLR_CONFIGVALUE     0U
    #define PBIST_PACT_CONFIGVALUE    0U
    #define PBIST_PBISTID_CONFIGVALUE 0U
    #define PBIST_OVER_CONFIGVALUE    0U
    #define PBIST_FSRDL1_CONFIGVALUE  0U
    #define PBIST_ROM_CONFIGVALUE     0U
    #define PBIST_ALGO_CONFIGVALUE    0U
    #define PBIST_RINFOL_CONFIGVALUE  0U
    #define PBIST_RINFOU_CONFIGVALUE  0U

/* USER CODE BEGIN (1) */
/* USER CODE END */

/** @fn void memoryPort0TestFailNotification(uint32 groupSelect, uint32 dataSelect, uint32
 * address, uint32 data)
 *   @brief Memory Port 0 test fail notification
 *   @param[in] groupSelect Failing Ram group select:
 *   @param[in] dataSelect Failing Ram data select:
 *   @param[in] address Failing Ram offset:
 *   @param[in] data Failing data at address:
 *
 *   @note This function has to be provide by the user.
 */
void memoryPort0TestFailNotification( uint32 groupSelect,
                                      uint32 dataSelect,
                                      uint32 address,
                                      uint32 data );

/** @fn void memoryPort1TestFailNotification(uint32 groupSelect, uint32 dataSelect, uint32
 * address, uint32 data)
 *   @brief Memory Port 1 test fail notification
 *   @param[in] groupSelect Failing Ram group select:
 *   @param[in] dataSelect Failing Ram data select:
 *   @param[in] address Failing Ram offset:
 *   @param[in] data Failing data at address:
 *
 *   @note This function has to be provide by the user.
 */
void memoryPort1TestFailNotification( uint32 groupSelect,
                                      uint32 dataSelect,
                                      uint32 address,
                                      uint32 data );

void pbistGetConfigValue( pbist_config_reg_t * config_reg, config_value_type_t type );
#endif /* ifndef __PBIST_H__ */

#ifndef __STC_H__
    #define __STC_H__

    /* STC General Definitions */

    /* STC Test Intervals supported in the Device */
    #define STC_INTERVAL    24U
    #define STC_MAX_TIMEOUT 0xFFFFFFFFU

/* Configuration registers */
typedef struct stc_config_reg
{
    uint32 CONFIG_STCGCR0;
    uint32 CONFIG_STCGCR1;
    uint32 CONFIG_STCTPR;
    uint32 CONFIG_STCSCSCR;
} stc_config_reg_t;

    /* Configuration registers initial value */
    #define STC_STCGCR0_CONFIGVALUE  0xFFFF0000U
    #define STC_STCGCR1_CONFIGVALUE  0x5U
    #define STC_STCTPR_CONFIGVALUE   0xFFFFFFFFU
    #define STC_STCSCSCR_CONFIGVALUE 0x5U

void stcGetConfigValue( stc_config_reg_t * config_reg, config_value_type_t type );

#endif /* ifndef __STC_H__ */

#ifndef __EFC_H__
    #define __EFC_H__

    #define INPUT_ENABLE              0x0000000FU
    #define INPUT_DISABLE             0x00000000U

    #define SYS_WS_READ_STATES        0x00000000U

    #define SYS_REPAIR_EN_0           0x00000000U
    #define SYS_REPAIR_EN_3           0x00000100U
    #define SYS_REPAIR_EN_5           0x00000200U

    #define SYS_DEID_AUTOLOAD_EN      0x00000400U

    #define EFC_FDI_EN                0x00000800U
    #define EFC_FDI_DIS               0x00000000U

    #define SYS_ECC_OVERRIDE_EN       0x00001000U
    #define SYS_ECC_OVERRIDE_DIS      0x00000000U

    #define SYS_ECC_SELF_TEST_EN      0x00002000U
    #define SYS_ECC_SELF_TEST_DIS     0x00000000U

    #define OUTPUT_ENABLE             0x0003C000U
    #define OUTPUT_DISABLE            0x00000000U

    /*********** OUTPUT **************/

    #define EFC_AUTOLOAD_ERROR_EN     0x00040000U
    #define EFC_INSTRUCTION_ERROR_EN  0x00080000U
    #define EFC_INSTRUCTION_INFO_EN   0x00100000U
    #define EFC_SELF_TEST_ERROR_EN    0x00200000U

    #define EFC_AUTOLOAD_ERROR_DIS    0x00000000U
    #define EFC_INSTRUCTION_ERROR_DIS 0x00000000U
    #define EFC_INSTRUCTION_INFO_DIS  0x00000000U
    #define EFC_SELF_TEST_ERROR_DIS   0x00000000U

    #define DISABLE_READ_ROW0         0x00800000U

    /********************************************************************/

    #define SYS_REPAIR_0              0x00000010U
    #define SYS_REPAIR_3              0x00000010U
    #define SYS_REPAIR_5              0x00000020U

    #define SYS_DEID_AUTOLOAD         0x00000040U
    #define SYS_FCLRZ                 0x00000080U
    #define EFC_READY                 0x00000100U
    #define SYS_ECC_OVERRIDE          0x00000200U
    #define EFC_AUTOLOAD_ERROR        0x00000400U
    #define EFC_INSTRUCTION_ERROR     0x00000800U
    #define EFC_INSTRUCTION_INFO      0x00001000U
    #define SYS_ECC_SELF_TEST         0x00002000U
    #define EFC_SELF_TEST_ERROR       0x00004000U
    #define EFC_SELF_TEST_DONE        0x00008000U

    /**************   0x3C error status register
     * ******************************************************/

    #define TIME_OUT                  0x01
    #define AUTOLOAD_NO_FUSEROM_DATA  0x02U
    #define AUTOLOAD_SIGN_FAIL        0x03U
    #define AUTOLOAD_PROG_INTERRUPT   0x04U
    #define AUTOLOAD_TWO_BIT_ERR      0x05U
    #define PROGRAME_WR_P_SET         0x06U
    #define PROGRAME_MNY_DATA_ITERTN  0x07U
    #define PROGRAME_MNY_CNTR_ITERTN  0x08U
    #define UN_PROGRAME_BIT_SET       0x09U
    #define REDUNDANT_REPAIR_ROW      0x0AU
    #define PROGRAME_MNY_CRA_ITERTN   0x0BU
    #define PROGRAME_SAME_DATA        0x0CU
    #define PROGRAME_CMP_SKIP         0x0DU
    #define PROGRAME_ABORT            0x0EU
    #define PROGRAME_INCORRECT_KEY    0x0FU
    #define FUSEROM_LASTROW_STUCK     0x10U
    #define AUTOLOAD_SINGLE_BIT_ERR   0x15U
    #define DUMPWORD_TWO_BIT_ERR      0x16U
    #define DUMPWORD_ONE_BIT_ERR      0x17U
    #define SELF_TEST_ERROR           0x18U

    #define INSTRUCTION_DONE          0x20U

    /**************   Efuse Instruction set
     * ******************************************************/

    #define TEST_UNPROGRAME_ROM       0x01000000U
    #define PROGRAME_CRA              0x02000000U
    #define DUMP_WORD                 0x04000000U
    #define LOAD_FUSE_SCAN_CHAIN      0x05000000U
    #define PROGRAME_DATA             0x07000000U
    #define RUN_AUTOLOAD_8            0x08000000U
    #define RUN_AUTOLOAD_A            0x0A000000U

/* Configuration registers */
typedef struct efc_config_reg
{
    uint32 CONFIG_BOUNDARY;
    uint32 CONFIG_PINS;
    uint32 CONFIG_SELFTESTCYCLES;
    uint32 CONFIG_SELFTESTSIGN;
} efc_config_reg_t;

    /* Configuration registers initial value */
    #define EFC_BOUNDARY_CONFIGVALUE       0x0000200FU
    #define EFC_PINS_CONFIGVALUE           0x000082E0U
    #define EFC_SELFTESTCYCLES_CONFIGVALUE 0x00000258U
    #define EFC_SELFTESTSIGN_CONFIGVALUE   0x5362F97FU

void efcGetConfigValue( efc_config_reg_t * config_reg, config_value_type_t type );
#endif /* ifndef __EFC_H__ */

#define CCMSELFCHECK_FAIL1        1U
#define CCMSELFCHECK_FAIL2        2U
#define CCMSELFCHECK_FAIL3        3U
#define CCMSELFCHECK_FAIL4        4U
#define PBISTSELFCHECK_FAIL1      5U
#define EFCCHECK_FAIL1            6U
#define EFCCHECK_FAIL2            7U
#define FMCECCCHECK_FAIL1         8U
#define CHECKB0RAMECC_FAIL1       9U
#define CHECKB1RAMECC_FAIL1       10U
#define CHECKFLASHECC_FAIL1       11U
#define VIMPARITYCHECK_FAIL1      12U
#define DMAPARITYCHECK_FAIL1      13U
#define HET1PARITYCHECK_FAIL1     14U
#define HTU1PARITYCHECK_FAIL1     15U
#define HET2PARITYCHECK_FAIL1     16U
#define HTU2PARITYCHECK_FAIL1     17U
#define ADC1PARITYCHECK_FAIL1     18U
#define ADC2PARITYCHECK_FAIL1     19U
#define CAN1PARITYCHECK_FAIL1     20U
#define CAN2PARITYCHECK_FAIL1     21U
#define CAN3PARITYCHECK_FAIL1     22U
#define MIBSPI1PARITYCHECK_FAIL1  23U
#define MIBSPI3PARITYCHECK_FAIL1  24U
#define MIBSPI5PARITYCHECK_FAIL1  25U
#define CHECKRAMECC_FAIL1         26U
#define CHECKRAMECC_FAIL2         27U
#define CHECKCLOCKMONITOR_FAIL1   28U
#define CHECKFLASHEEPROMECC_FAIL1 29U
#define CHECKFLASHEEPROMECC_FAIL2 31U
#define CHECKFLASHEEPROMECC_FAIL3 32U
#define CHECKFLASHEEPROMECC_FAIL4 33U
#define CHECKPLL1SLIP_FAIL1       34U
#define CHECKRAMADDRPARITY_FAIL1  35U
#define CHECKRAMADDRPARITY_FAIL2  36U
#define CHECKRAMUERRTEST_FAIL1    37U
#define CHECKRAMUERRTEST_FAIL2    38U
#define FMCBUS1PARITYCHECK_FAIL1  39U
#define FMCBUS1PARITYCHECK_FAIL2  40U
#define PBISTSELFCHECK_FAIL2      41U
#define PBISTSELFCHECK_FAIL3      42U

/* safety Init Interface Functions */
void ccmSelfCheck( void );

void stcSelfCheck( void );
void stcSelfCheckFail( void );
void cpuSelfTest( uint32 no_of_intervals, uint32 max_timeout, boolean restart_test );
void cpuSelfTestFail( void );

void memoryInit( uint32 ram );

void pbistSelfCheck( void );
void pbistRun( uint32 raminfoL, uint32 algomask );
void pbistStop( void );
boolean pbistIsTestCompleted( void );
boolean pbistIsTestPassed( void );
boolean pbistPortTestStatus( uint32 port );
void pbistFail( void );

uint32 efcCheck( void );
void efcSelfTest( void );
boolean efcStuckZeroTest( void );
boolean checkefcSelfTest( void );

void fmcBus2Check( void );
void fmcECCcheck( void );
void fmcBus1ParityCheck( void );

void checkB0RAMECC( void );
void checkB1RAMECC( void );

void checkFlashECC( void );

void vimParityCheck( void );
void dmaParityCheck( void );
void adc1ParityCheck( void );
void adc2ParityCheck( void );
void het1ParityCheck( void );
void htu1ParityCheck( void );
void het2ParityCheck( void );
void htu2ParityCheck( void );
void can1ParityCheck( void );
void can2ParityCheck( void );
void can3ParityCheck( void );
void mibspi1ParityCheck( void );
void mibspi3ParityCheck( void );
void mibspi5ParityCheck( void );

void checkRAMECC( void );
void checkClockMonitor( void );
void checkFlashEEPROMECC( void );
void checkPLL1Slip( void );
void checkPLL2Slip( void );
void checkRAMAddrParity( void );
void checkRAMUERRTest( void );

void enableParity( void );
void disableParity( void );

void custom_dabort( void );
void selftestFailNotification( uint32 flag );
void errata_PBIST_4( void );

/* USER CODE BEGIN (2) */
/* USER CODE END */

/* Configuration registers */
typedef struct ccmr4_config_reg
{
    uint32 CONFIG_CCMKEYR;
} ccmr4_config_reg_t;

/* Configuration registers initial value */
#define CCMR4_CCMKEYR_CONFIGVALUE 0U

void ccmr4GetConfigValue( ccmr4_config_reg_t * config_reg, config_value_type_t type );
#endif /* ifndef __sys_selftest_H__ */
