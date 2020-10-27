/*******************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only
* intended for use with Renesas products. No other uses are authorized. This
* software is owned by Renesas Electronics Corporation and is protected under
* all applicable laws, including copyright laws.
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES REGARDING
* THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY, INCLUDING BUT NOT
* LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE
* AND NON-INFRINGEMENT. ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED.
* TO THE MAXIMUM EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS
* ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES SHALL BE LIABLE
* FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR
* ANY REASON RELATED TO THIS SOFTWARE, EVEN IF RENESAS OR ITS AFFILIATES HAVE
* BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software
* and to discontinue the availability of this software. By using this software,
* you agree to the additional terms and conditions found by accessing the
* following link:
* http://www.renesas.com/disclaimer
*
* Copyright (C) 2014 Renesas Electronics Corporation. All rights reserved.
*******************************************************************************/
/*******************************************************************************
* File Name    : r_dtc_rx_private.h
* Description  : Functions for using DTC on RX devices.
*******************************************************************************/
/*******************************************************************************
* History : DD.MM.YYYY Version Description
*         : 17.03.2014 1.00    Initial revision
*         : 17.07.2014 2.00    Second  revision
*         : 12.11.2014 2.01    Added RX113.
*         : 30.01.2015 2.02    Added RX71M.
*         : 13.04.2015 2.03    Added RX231 and RX230.
*         : 24.12.2015 2.04    Modified #define name from "DTC_CFG_SHORT_ADDRRESS_MODE"
*         :                    to "DTC_CFG_SHORT_ADDRESS_MODE".
*         :                    Added RX130, RX23T and RX24T.
*         : 30.09.2016 2.05    Added RX65N.
*         :                    Supported to the register added in DTCb.
*         :                    Supported sequence transfer.
*         :                    Added DTC IP version definitions.
*         : 13.03.2017 2.07    Added RX24U and RX24T-512KB.
*         : 31.07.2017 2.08    Supported RX65N-2MB and RX130-512KB.
*         :                    Fixed to correspond to Renesas coding rule.
*         : 28.09.2018 2.10    Supported RX66T.
*         : 01.02.2019 2.20    Supported RX72T, RX65N-64pin
*         : 20.05.2019 3.00    Added support for GNUC and ICCRX.
*         : 18.06.2019 3.01    Removed "defined(__BIG_ENDIAN__)" from DTC_BIG_ENDIAN macro definition.
*         : 28.06.2019 3.10    Added support for RX23W.
*         : 15.08.2019 3.20    Added support for RX72M.
*         : 25.11.2019 3.30    Added support for RX13T.
*         : 30.12.2019 3.40    Added support for RX66N, RX72N.
*         : 31.03.2020 3.50    Added support for RX23E-A.
*******************************************************************************/
#ifndef DTC_RX_PRIVATE_H
#define DTC_RX_PRIVATE_H

/*******************************************************************************
Includes   <System Includes> , "Project Includes"
*******************************************************************************/
/* Fixed width integer support. */
#include <stdint.h>
/* Bool support */
#include <stdbool.h>

#if   defined(BSP_MCU_RX23T)
    #include ".\src\targets\rx23t\r_dtc_rx_target.h"
    #if (DTC_CFG_USE_DMAC_FIT_MODULE == DTC_ENABLE)
        #error "This MCU does not have DMAC module."
        #error "Change to DTC_CFG_USE_DMAC_FIT_MODULE (DTC_DISABLE) in r_dtc_rx_config.h."
    #endif
    #if (DTC_CFG_USE_SEQUENCE_TRANSFER == DTC_ENABLE)
        #error "Change to DTC_CFG_USE_SEQUENCE_TRANSFER (DTC_DISABLE) in r_dtc_rx_config.h."
    #endif
#elif defined(BSP_MCU_RX24T)
    #include ".\src\targets\rx24t\r_dtc_rx_target.h"
    #if (DTC_CFG_USE_DMAC_FIT_MODULE == DTC_ENABLE)
        #error "This MCU does not have DMAC module."
        #error "Change to DTC_CFG_USE_DMAC_FIT_MODULE (DTC_DISABLE) in r_dtc_rx_config.h."
    #endif
    #if (DTC_CFG_USE_SEQUENCE_TRANSFER == DTC_ENABLE)
        #error "Change to DTC_CFG_USE_SEQUENCE_TRANSFER (DTC_DISABLE) in r_dtc_rx_config.h."
    #endif
#elif defined(BSP_MCU_RX24U)
    #include ".\src\targets\rx24u\r_dtc_rx_target.h"
    #if (DTC_CFG_USE_DMAC_FIT_MODULE == DTC_ENABLE)
        #error "This MCU does not have DMAC module."
        #error "Change to DTC_CFG_USE_DMAC_FIT_MODULE (DTC_DISABLE) in r_dtc_rx_config.h."
    #endif
    #if (DTC_CFG_USE_SEQUENCE_TRANSFER == DTC_ENABLE)
        #error "Change to DTC_CFG_USE_SEQUENCE_TRANSFER (DTC_DISABLE) in r_dtc_rx_config.h."
    #endif
#elif defined(BSP_MCU_RX130)
    #include ".\src\targets\rx130\r_dtc_rx_target.h"
    #if (DTC_CFG_USE_DMAC_FIT_MODULE == DTC_ENABLE)
        #error "This MCU does not have DMAC module."
        #error "Change to DTC_CFG_USE_DMAC_FIT_MODULE (DTC_DISABLE) in r_dtc_rx_config.h."
    #endif
    #if (DTC_CFG_USE_SEQUENCE_TRANSFER == DTC_ENABLE)
        #error "Change to DTC_CFG_USE_SEQUENCE_TRANSFER (DTC_DISABLE) in r_dtc_rx_config.h."
    #endif
#elif defined(BSP_MCU_RX13T)
    #include ".\src\targets\rx13t\r_dtc_rx_target.h"
    #if (DTC_CFG_USE_DMAC_FIT_MODULE == DTC_ENABLE)
        #error "This MCU does not have DMAC module."
        #error "Change to DTC_CFG_USE_DMAC_FIT_MODULE (DTC_DISABLE) in r_dtc_rx_config.h."
    #endif
    #if (DTC_CFG_USE_SEQUENCE_TRANSFER == DTC_ENABLE) && (DTC_ENABLE == DTC_CFG_SHORT_ADDRESS_MODE)
        #error "Change to DTC_CFG_USE_SEQUENCE_TRANSFER (DTC_DISABLE) in r_dtc_rx_config.h."
    #endif
#elif defined(BSP_MCU_RX113)
    #include ".\src\targets\rx113\r_dtc_rx_target.h"
    #if (DTC_CFG_USE_DMAC_FIT_MODULE == DTC_ENABLE)
        #error "This MCU does not have DMAC module."
        #error "Change to DTC_CFG_USE_DMAC_FIT_MODULE (DTC_DISABLE) in r_dtc_rx_config.h."
    #endif
    #if (DTC_CFG_USE_SEQUENCE_TRANSFER == DTC_ENABLE)
        #error "Change to DTC_CFG_USE_SEQUENCE_TRANSFER (DTC_DISABLE) in r_dtc_rx_config.h."
    #endif
#elif defined(BSP_MCU_RX111)
    #include ".\src\targets\rx111\r_dtc_rx_target.h"
    #if (DTC_CFG_USE_DMAC_FIT_MODULE == DTC_ENABLE)
        #error "This MCU does not have DMAC module."
        #error "Change to DTC_CFG_USE_DMAC_FIT_MODULE (DTC_DISABLE) in r_dtc_rx_config.h."
    #endif
    #if (DTC_CFG_USE_SEQUENCE_TRANSFER == DTC_ENABLE)
        #error "Change to DTC_CFG_USE_SEQUENCE_TRANSFER (DTC_DISABLE) in r_dtc_rx_config.h."
    #endif
#elif defined(BSP_MCU_RX110)
    #include ".\src\targets\rx110\r_dtc_rx_target.h"
    #if (DTC_CFG_USE_DMAC_FIT_MODULE == DTC_ENABLE)
        #error "This MCU does not have DMAC module."
        #error "Change to DTC_CFG_USE_DMAC_FIT_MODULE (DTC_DISABLE) in r_dtc_rx_config.h."
    #endif
    #if (DTC_CFG_USE_SEQUENCE_TRANSFER == DTC_ENABLE)
        #error "Change to DTC_CFG_USE_SEQUENCE_TRANSFER (DTC_DISABLE) in r_dtc_rx_config.h."
    #endif
#elif defined(BSP_MCU_RX64M)
    #include ".\src\targets\rx64m\r_dtc_rx_target.h"
    #if (DTC_CFG_USE_SEQUENCE_TRANSFER == DTC_ENABLE)
        #error "Change to DTC_CFG_USE_SEQUENCE_TRANSFER (DTC_DISABLE) in r_dtc_rx_config.h."
    #endif
#elif defined(BSP_MCU_RX71M)
    #include ".\src\targets\rx71m\r_dtc_rx_target.h"
    #if (DTC_CFG_USE_SEQUENCE_TRANSFER == DTC_ENABLE)
        #error "Change to DTC_CFG_USE_SEQUENCE_TRANSFER (DTC_DISABLE) in r_dtc_rx_config.h."
    #endif
#elif defined(BSP_MCU_RX231)
    #include ".\src\targets\rx231\r_dtc_rx_target.h"
    #if (DTC_CFG_USE_SEQUENCE_TRANSFER == DTC_ENABLE)
        #error "Change to DTC_CFG_USE_SEQUENCE_TRANSFER (DTC_DISABLE) in r_dtc_rx_config.h."
    #endif
#elif defined(BSP_MCU_RX23E_A)
    #include ".\src\targets\rx23e-a\r_dtc_rx_target.h"
    #if (DTC_CFG_USE_SEQUENCE_TRANSFER == DTC_ENABLE)
        #error "Change to DTC_CFG_USE_SEQUENCE_TRANSFER (DTC_DISABLE) in r_dtc_rx_config.h."
    #endif
#elif defined(BSP_MCU_RX23W)
    #include ".\src\targets\rx23w\r_dtc_rx_target.h"
    #if (DTC_CFG_USE_SEQUENCE_TRANSFER == DTC_ENABLE)
        #error "Change to DTC_CFG_USE_SEQUENCE_TRANSFER (DTC_DISABLE) in r_dtc_rx_config.h."
    #endif
#elif defined(BSP_MCU_RX230)
    #include ".\src\targets\rx230\r_dtc_rx_target.h"
    #if (DTC_CFG_USE_SEQUENCE_TRANSFER == DTC_ENABLE)
        #error "Change to DTC_CFG_USE_SEQUENCE_TRANSFER (DTC_DISABLE) in r_dtc_rx_config.h."
    #endif
#elif defined(BSP_MCU_RX65N)
    #if (DTC_CFG_USE_SEQUENCE_TRANSFER == DTC_ENABLE) && (DTC_ENABLE == DTC_CFG_SHORT_ADDRESS_MODE)
        #error "Change to DTC_CFG_USE_SEQUENCE_TRANSFER (DTC_DISABLE) in r_dtc_rx_config.h."
    #endif
    #include ".\src\targets\rx65n\r_dtc_rx_target.h"
#elif defined(BSP_MCU_RX66T)
    #include ".\src\targets\rx66t\r_dtc_rx_target.h"
    #if (DTC_CFG_USE_SEQUENCE_TRANSFER == DTC_ENABLE)
        #error "Change to DTC_CFG_USE_SEQUENCE_TRANSFER (DTC_DISABLE) in r_dtc_rx_config.h."
    #endif
#elif defined(BSP_MCU_RX66N)
    #if (DTC_CFG_USE_SEQUENCE_TRANSFER == DTC_ENABLE) && (DTC_ENABLE == DTC_CFG_SHORT_ADDRESS_MODE)
        #error "Change to DTC_CFG_USE_SEQUENCE_TRANSFER (DTC_DISABLE) in r_dtc_rx_config.h."
    #endif
    #include ".\src\targets\rx66n\r_dtc_rx_target.h"
#elif defined(BSP_MCU_RX72T)
    #include ".\src\targets\rx72t\r_dtc_rx_target.h"
    #if (DTC_CFG_USE_SEQUENCE_TRANSFER == DTC_ENABLE)
        #error "Change to DTC_CFG_USE_SEQUENCE_TRANSFER (DTC_DISABLE) in r_dtc_rx_config.h."
    #endif
#elif defined(BSP_MCU_RX72M)
    #if (DTC_CFG_USE_SEQUENCE_TRANSFER == DTC_ENABLE) && (DTC_ENABLE == DTC_CFG_SHORT_ADDRESS_MODE)
        #error "Change to DTC_CFG_USE_SEQUENCE_TRANSFER (DTC_DISABLE) in r_dtc_rx_config.h."
    #endif
    #include ".\src\targets\rx72m\r_dtc_rx_target.h"
#elif defined(BSP_MCU_RX72N)
    #if (DTC_CFG_USE_SEQUENCE_TRANSFER == DTC_ENABLE) && (DTC_ENABLE == DTC_CFG_SHORT_ADDRESS_MODE)
        #error "Change to DTC_CFG_USE_SEQUENCE_TRANSFER (DTC_DISABLE) in r_dtc_rx_config.h."
    #endif
    #include ".\src\targets\rx72n\r_dtc_rx_target.h"
#else
    #error "This MCU is not supported by the current r_dtc_rx module."
#endif

/*****************************************************************************
Macro definitions
******************************************************************************/
#define DTC_BIG_ENDIAN        (defined(__BIG) || defined(__RX_BIG_ENDIAN__))
#define DTC_INVALID_CMND      ((uint32_t)0x00000001)
/* DTC IP version */
#define DTC_IP_VER_DTC      (0)
#define DTC_IP_VER_DTCa     (1)
#define DTC_IP_VER_DTCb     (2)

/*****************************************************************************
Typedef definitions
******************************************************************************/
/* The DTC Mode Register A (MRA) structure */

R_BSP_PRAGMA_UNPACK;

#if (DTC_IP_VER_DTCa == DTC_IP)
typedef union dtc_mra {
    uint8_t BYTE;
    R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT_4 (
        uint8_t MD:2, /* b7,b6: DTC Transfer Mode Select */
        uint8_t SZ:2, /* DTC Data Transfer Size */
        uint8_t SM:2, /* Transfer Source Address Addressing Mode */
        uint8_t rs:2 /* reserved */
    ) BIT;

} dtc_mra_t;

/* The DTC Mode Register B (MRB) structure */
typedef union dtc_mrb {
    uint8_t BYTE;
    R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT_6 (
        uint8_t CHNE :1,  /* b7: DTC Chain Transfer Enable */
        uint8_t CHNS :1,  /* DTC Chain Transfer Select */
        uint8_t DISEL:1,  /* DTC Interrupt Select */
        uint8_t DTS  :1,  /* DTC Transfer Mode Select */
        uint8_t DM   :2,  /* Transfer Destination Address Addressing Mode */
        uint8_t rs   :2  /* reserved */
    ) BIT;

} dtc_mrb_t;
#else
typedef union dtc_mra {
    uint8_t BYTE;
    R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT_5 (
        uint8_t MD:2, /* b7,b6: DTC Transfer Mode Select */
        uint8_t SZ:2, /* DTC Data Transfer Size */
        uint8_t SM:2, /* Transfer Source Address Addressing Mode */
        uint8_t rs:1, /* reserved */
        uint8_t WBDIS:1 /* Write-back Disable */
    ) BIT;

} dtc_mra_t;

/* The DTC Mode Register B (MRB) structure */
typedef union dtc_mrb {
    uint8_t BYTE;
    R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT_7 (
        uint8_t CHNE :1,  /* b7: DTC Chain Transfer Enable */
        uint8_t CHNS :1,  /* DTC Chain Transfer Select */
        uint8_t DISEL:1,  /* DTC Interrupt Select */
        uint8_t DTS  :1,  /* DTC Transfer Mode Select */
        uint8_t DM   :2,  /* Transfer Destination Address Addressing Mode */
        uint8_t INDX:1,   /* Index Table Reference */
        uint8_t SQEND:1  /* Sequence Transfer End */
    ) BIT;

} dtc_mrb_t;

/* The DTC Mode Register C (MRC) structure */
typedef union dtc_mrc {
    uint8_t BYTE;
    R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT_2 (
        uint8_t rs :7,    /* reserved */
        uint8_t DISPE :1
    ) BIT;

} dtc_mrc_t;
#endif /* (DTC_IP_VER_DTCa == DTC_IP) */

/* The DTC Transfer Count Register A (CRA) structure */
typedef union dtc_cra {
    uint16_t WORD;
    struct {
#if (DTC_BIG_ENDIAN)
        uint8_t CRA_H;
        uint8_t CRA_L;
#else /* little endian */
        uint8_t CRA_L;
        uint8_t CRA_H;
#endif /* (DTC_BIG_ENDIAN) */
    } BYTE;
} dtc_cra_t;

/* The DTC Transfer Count Register B (CRB) structure */
typedef union dtc_crb {
    uint16_t WORD;
} dtc_crb_t;

#if (DTC_ENABLE == DTC_CFG_SHORT_ADDRESS_MODE) /* Transfer data in short-address mode */
typedef struct st_dtc_short_transfer_data {
    union {
        uint32_t LWORD;
        struct {
#if (DTC_BIG_ENDIAN) /* Big-Endian */
            dtc_mra_t     MRA;
            uint8_t SAR[3];
#else /* Little-Endian */
            uint8_t SAR[3];
            dtc_mra_t     MRA;
#endif /* (DTC_BIG_ENDIAN) */

        } REG;

    } FIRST_LWORD;
    union {
        uint32_t LWORD;
        struct {
#if (DTC_BIG_ENDIAN) /* Big-Endian */
            dtc_mrb_t       MRB;
            uint8_t   DAR[3];
#else /* Little-Endian */
            uint8_t SAR[3];
            dtc_mrb_t     MRB;
#endif /* (DTC_BIG_ENDIAN) */

        } REG;
    } SECOND_LWORD;
    union {
        uint32_t LWORD;
        struct {
#if (DTC_BIG_ENDIAN) /* Big-Endian */
            dtc_cra_t CRA;
            dtc_crb_t CRB;
#else /* Little-Endian */
            dtc_crb_t CRB;
            dtc_cra_t CRA;
#endif /* (DTC_BIG_ENDIAN) */
        } REG;
    } THIRD_LWORD;
} dtc_internal_registers_t;

#else /* Transfer data in full-address mode */
typedef struct st_dtc_full_transfer_data {
    union {
        uint32_t LWORD;
        struct {
#if (DTC_BIG_ENDIAN) /* Big-Endian */
            dtc_mra_t MRA;
            dtc_mrb_t MRB;
#if (DTC_IP_VER_DTCa == DTC_IP)
            uint16_t  reserver; /* reserve area */
#else
            dtc_mrc_t MRC;
            uint8_t   reserver; /* reserve area */
#endif /* (DTC_IP_VER_DTCa == DTC_IP) */

#else /* Little-Endian */
#if (DTC_IP_VER_DTCa == DTC_IP)
            uint16_t  reserver; /* reserve area */
#else
            uint8_t   reserver; /* reserve area */
            dtc_mrc_t MRC;
#endif /* (DTC_IP_VER_DTCa == DTC_IP) */
            dtc_mrb_t MRB;
            dtc_mra_t MRA;
#endif /* (DTC_BIG_ENDIAN) */
        } REG;
    } FIRST_LWORD;
    union {
        uint32_t SAR;
    } SECOND_LWORD;
    union {
        uint32_t DAR;
    } THIRD_LWORD;
    union {
        uint32_t LWORD;
        struct {
#if (DTC_BIG_ENDIAN) /* Big-Endian */
            dtc_cra_t CRA;
            dtc_crb_t CRB;
#else /* Little-Endian */
            dtc_crb_t CRB;
            dtc_cra_t CRA;
#endif /* (DTC_BIG_ENDIAN) */
        } REG;
    } FOURTH_LWORD;
} dtc_internal_registers_t;

#endif /* DTC_CFG_SHORT_ADDRESS_MODE */

R_BSP_PRAGMA_PACKOPTION;

/*******************************************************************************
Exported global variables and functions (to be accessed by other files)
*******************************************************************************/
void r_dtc_module_enable(void);
void r_dtc_module_disable(void);
#if ((0 != BSP_CFG_USER_LOCKING_ENABLED) || (bsp_lock_t != BSP_CFG_USER_LOCKING_TYPE) \
      || (DTC_ENABLE != DTC_CFG_USE_DMAC_FIT_MODULE))
bool r_dtc_check_DMAC_locking_byUSER(void);
#endif


#endif /* DTC_RX_PRIVATE_H */

/* End of File */
