/** @file reg_etpwm.h
 *   @brief ETPWM Register Layer Header File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file contains:
 *   - Definitions
 *   - Types
 *   - Interface Prototypes
 *   .
 *   which are relevant for the ETPWM driver.
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

#ifndef __REG_ETPWM_H__
#define __REG_ETPWM_H__

#include "sys_common.h"

/* USER CODE BEGIN (0) */
/* USER CODE END */

/* ETPWM Register Frame Definition */

/** @struct etpwmBASE
 *   @brief ETPWM Register Frame Definition
 *
 *   This type is used to access the ETPWM Registers.
 */

/** @typedef etpwmBASE_t
 *   @brief ETPWM Register Frame Type Definition
 *
 *   This type is used to access the ETPWM Registers.
 */
#if( ( __little_endian__ == 1 ) || ( __LITTLE_ENDIAN__ == 1 ) )

typedef volatile struct etpwmBASE
{
    uint16 TBCTL;  /**<  0x0000 Time-Base Control Register*/
    uint16 TBSTS;  /**<  0x0002 Time-Base Status Register*/
    uint16 rsvd1;  /**<  0x0004 Reserved*/
    uint16 TBPHS;  /**<  0x0006 Time-Base Phase Register*/
    uint16 TBCTR;  /**<  0x0008 Time-Base Counter Register*/
    uint16 TBPRD;  /**<  0x000A Time-Base Period Register*/
    uint16 rsvd2;  /**<  0x000C Reserved*/
    uint16 CMPCTL; /**<  0x000E Counter-Compare Control Register*/
    uint16 rsvd3;  /**<  0x0010 Reserved*/
    uint16 CMPA;   /**<  0x0012 Counter-Compare A Register*/
    uint16 CMPB;   /**<  0x0014 Counter-Compare B Register*/
    uint16 AQCTLA; /**<  0x0016 Action-Qualifier Control Register for Output A (ETPWMxA)*/
    uint16 AQCTLB; /**<  0x0018 Action-Qualifier Control Register for Output B (ETPWMxB)*/
    uint16 AQSFRC; /**<  0x001A Action-Qualifier Software Force Register*/
    uint16 AQCSFRC; /**<  0x001C Action-Qualifier Continuous S/W Force Register Set*/
    uint16 DBCTL;   /**<  0x001E Dead-Band Generator Control Register*/
    uint16 DBRED;   /**<  0x0020 Dead-Band Generator Rising Edge Delay Count Register*/
    uint16 DBFED;   /**<  0x0022 Dead-Band Generator Falling Edge Delay Count Register*/
    uint16 TZSEL;   /**<  0x0024 Trip-Zone Select Register*/
    uint16 TZDCSEL; /**<  0x0026 Trip Zone Digital Compare Select Register*/
    uint16 TZCTL;   /**<  0x0028 Trip-Zone Control Register*/
    uint16 TZEINT;  /**<  0x002A Trip-Zone Enable Interrupt Register*/
    uint16 TZFLG;   /**<  0x002C Trip-Zone Flag Register*/
    uint16 TZCLR;   /**<  0x002E Trip-Zone Clear Register*/
    uint16 TZFRC;   /**<  0x0030 Trip-Zone Force Register*/
    uint16 ETSEL;   /**<  0x0032 Event-Trigger Selection Register*/
    uint16 ETPS;    /**<  0x0034 Event-Trigger Pre-Scale Register*/
    uint16 ETFLG;   /**<  0x0036 Event-Trigger Flag Register*/
    uint16 ETCLR;   /**<  0x0038 Event-Trigger Clear Register*/
    uint16 ETFRC;   /**<  0x003A Event-Trigger Force Register*/
    uint16 PCCTL;   /**<  0x003C PWM-Chopper Control Register*/
    uint16 rsvd4;   /**<  0x003E Reserved*/
    uint16 rsvd5[ 16U ]; /**<  0x0040 Reserved*/
    uint16 DCTRIPSEL;    /**<  0x0060 Digital Compare Trip Select Register*/
    uint16 DCACTL;       /**<  0x0062 Digital Compare A Control Register*/
    uint16 DCBCTL;       /**<  0x0064 Digital Compare B Control Register*/
    uint16 DCFCTL;       /**<  0x0066 Digital Compare Filter Control Register*/
    uint16 DCCAPCTL;     /**<  0x0068 Digital Compare Capture Control Register*/
    uint16 DCFOFFSET;    /**<  0x006A Digital Compare Filter Offset Register*/
    uint16 DCFOFFSETCNT; /**<  0x006C Digital Compare Filter Offset Counter Register*/
    uint16 DCFWINDOW;    /**<  0x006E Digital Compare Filter Window Register*/
    uint16 DCFWINDOWCNT; /**<  0x0070 Digital Compare Filter Window Counter Register*/
    uint16 DCCAP;        /**<  0x0072 Digital Compare Counter Capture Register*/
} etpwmBASE_t;

#else /* if ( ( __little_endian__ == 1 ) || ( __LITTLE_ENDIAN__ == 1 ) ) */

typedef volatile struct etpwmBASE
{
    uint16 TBSTS;  /**<  0x0000 Time-Base Status Register*/
    uint16 TBCTL;  /**<  0x0002 Time-Base Control Register*/
    uint16 TBPHS;  /**<  0x0004 Time-Base Phase Register*/
    uint16 rsvd1;  /**<  0x0006 Reserved*/
    uint16 TBPRD;  /**<  0x0008 Time-Base Period Register*/
    uint16 TBCTR;  /**<  0x000A Time-Base Counter Register*/
    uint16 CMPCTL; /**<  0x000C Counter-Compare Control Register*/
    uint16 rsvd2;  /**<  0x000E Reserved*/
    uint16 CMPA;   /**<  0x0010 Counter-Compare A Register*/
    uint16 rsvd3;  /**<  0x0012 Reserved*/
    uint16 AQCTLA; /**<  0x0014 Action-Qualifier Control Register for Output A (ETPWMxA)*/
    uint16 CMPB;   /**<  0x0016 Counter-Compare B Register*/
    uint16 AQSFRC; /**<  0x0018 Action-Qualifier Software Force Register*/
    uint16 AQCTLB; /**<  0x001A Action-Qualifier Control Register for Output B (ETPWMxB)*/
    uint16 DBCTL;  /**<  0x001C Dead-Band Generator Control Register*/
    uint16 AQCSFRC; /**<  0x001E Action-Qualifier Continuous S/W Force Register Set*/
    uint16 DBFED;   /**<  0x0020 Dead-Band Generator Falling Edge Delay Count Register*/
    uint16 DBRED;   /**<  0x0022 Dead-Band Generator Rising Edge Delay Count Register*/
    uint16 TZDCSEL; /**<  0x0024 Trip Zone Digital Compare Select Register*/
    uint16 TZSEL;   /**<  0x0026 Trip-Zone Select Register*/
    uint16 TZEINT;  /**<  0x0028 Trip-Zone Enable Interrupt Register*/
    uint16 TZCTL;   /**<  0x002A Trip-Zone Control Register*/
    uint16 TZCLR;   /**<  0x002C Trip-Zone Clear Register*/
    uint16 TZFLG;   /**<  0x002E Trip-Zone Flag Register*/
    uint16 ETSEL;   /**<  0x0030 Event-Trigger Selection Register*/
    uint16 TZFRC;   /**<  0x0032 Trip-Zone Force Register*/
    uint16 ETFLG;   /**<  0x0034 Event-Trigger Flag Register*/
    uint16 ETPS;    /**<  0x0036 Event-Trigger Pre-Scale Register*/
    uint16 ETFRC;   /**<  0x0038 Event-Trigger Force Register*/
    uint16 ETCLR;   /**<  0x003A Event-Trigger Clear Register*/
    uint16 rsvd4;   /**<  0x003C Reserved*/
    uint16 PCCTL;   /**<  0x003E PWM-Chopper Control Register*/
    uint16 rsvd5[ 16U ]; /**<  0x0040 Reserved*/
    uint16 DCACTL;       /**<  0x0060 Digital Compare A Control Register*/
    uint16 DCTRIPSEL;    /**<  0x0062 Digital Compare Trip Select Register*/
    uint16 DCFCTL;       /**<  0x0064 Digital Compare Filter Control Register*/
    uint16 DCBCTL;       /**<  0x0066 Digital Compare B Control Register*/
    uint16 DCFOFFSET;    /**<  0x0068 Digital Compare Filter Offset Register*/
    uint16 DCCAPCTL;     /**<  0x006A Digital Compare Capture Control Register*/
    uint16 DCFWINDOW;    /**<  0x006C Digital Compare Filter Window Register*/
    uint16 DCFOFFSETCNT; /**<  0x006E Digital Compare Filter Offset Counter Register*/
    uint16 DCCAP;        /**<  0x0070 Digital Compare Counter Capture Register*/
    uint16 DCFWINDOWCNT; /**<  0x0072 Digital Compare Filter Window Counter Register*/
} etpwmBASE_t;

#endif /* if ( ( __little_endian__ == 1 ) || ( __LITTLE_ENDIAN__ == 1 ) ) */

/** @def etpwmREG1
 *   @brief ETPWM1 Register Frame Pointer
 *
 *   This pointer is used by the ETPWM driver to access the ETPWM1 registers.
 */
#define etpwmREG1 ( ( etpwmBASE_t * ) 0xFCF78C00U )

/** @def etpwmREG2
 *   @brief ETPWM2 Register Frame Pointer
 *
 *   This pointer is used by the ETPWM driver to access the ETPWM2 registers.
 */
#define etpwmREG2 ( ( etpwmBASE_t * ) 0xFCF78D00U )

/** @def etpwmREG3
 *   @brief ETPWM3 Register Frame Pointer
 *
 *   This pointer is used by the ETPWM driver to access the ETPWM3 registers.
 */
#define etpwmREG3 ( ( etpwmBASE_t * ) 0xFCF78E00U )

/** @def etpwmREG4
 *   @brief ETPWM4 Register Frame Pointer
 *
 *   This pointer is used by the ETPWM driver to access the ETPWM4 registers.
 */
#define etpwmREG4 ( ( etpwmBASE_t * ) 0xFCF78F00U )

/** @def etpwmREG5
 *   @brief ETPWM5 Register Frame Pointer
 *
 *   This pointer is used by the ETPWM driver to access the ETPWM5 registers.
 */
#define etpwmREG5 ( ( etpwmBASE_t * ) 0xFCF79000U )

/** @def etpwmREG6
 *   @brief ETPWM6 Register Frame Pointer
 *
 *   This pointer is used by the ETPWM driver to access the ETPWM6 registers.
 */
#define etpwmREG6 ( ( etpwmBASE_t * ) 0xFCF79100U )

/** @def etpwmREG7
 *   @brief ETPWM7 Register Frame Pointer
 *
 *   This pointer is used by the ETPWM driver to access the ETPWM7 registers.
 */
#define etpwmREG7 ( ( etpwmBASE_t * ) 0xFCF79200U )

/* USER CODE BEGIN (1) */
/* USER CODE END */

#endif /* ifndef __REG_ETPWM_H__ */
