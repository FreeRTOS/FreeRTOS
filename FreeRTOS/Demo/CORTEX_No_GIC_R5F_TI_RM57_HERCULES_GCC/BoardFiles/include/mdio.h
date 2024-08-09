/**
 *  \file   mdio.h
 *
 *  \brief  MDIO APIs and macros.
 *
 *   This file contains the driver API prototypes and macro definitions.
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

#ifndef __MDIO_H__
#define __MDIO_H__

/* USER CODE BEGIN (0) */
/* USER CODE END */

#include "sys_common.h"
#include "system.h"
#include "hw_mdio.h"

#ifdef __cplusplus
extern "C" {
#endif

/* USER CODE BEGIN (1) */
/* USER CODE END */

/* MDIO input and output frequencies in Hz */
#define MDIO_FREQ_INPUT  ( ( uint32 ) ( VCLK3_FREQ * 1000000.00F ) )
#define MDIO_FREQ_OUTPUT 1000000U
/*****************************************************************************/

/**
 *  @addtogroup EMACMDIO
 *  @{
 */
/*
** Prototypes for the APIs
*/
extern uint32 MDIOPhyAliveStatusGet( uint32 baseAddr );
extern uint32 MDIOPhyLinkStatusGet( uint32 baseAddr );
extern void MDIOInit( uint32 baseAddr, uint32 mdioInputFreq, uint32 mdioOutputFreq );
extern boolean MDIOPhyRegRead( uint32 baseAddr,
                               uint32 phyAddr,
                               uint32 regNum,
                               volatile uint16 * dataPtr );
extern void MDIOPhyRegWrite( uint32 baseAddr,
                             uint32 phyAddr,
                             uint32 regNum,
                             uint16 RegVal );
extern void MDIOEnable( uint32 baseAddr );
extern void MDIODisable( uint32 baseAddr );

/* USER CODE BEGIN (2) */
/* USER CODE END */

#ifdef __cplusplus
}
#endif

/**@}*/
#endif /* __MDIO_H__ */
