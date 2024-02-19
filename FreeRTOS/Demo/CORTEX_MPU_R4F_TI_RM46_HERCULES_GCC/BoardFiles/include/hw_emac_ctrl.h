/*
 * hw_emac1.h
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

#ifndef _HW_EMAC_CTRL_H_
#define _HW_EMAC_CTRL_H_

/* USER CODE BEGIN (0) */
/* USER CODE END */

#ifdef __cplusplus
extern "C" {
#endif

/* USER CODE BEGIN (1) */
/* USER CODE END */

#define EMAC_CTRL_REVID        ( 0x0U )
#define EMAC_CTRL_SOFTRESET    ( 0x4U )
#define EMAC_CTRL_INTCONTROL   ( 0xCU )
#define EMAC_CTRL_C0RXTHRESHEN ( 0x10U )
#define EMAC_CTRL_CnRXEN( n )  ( ( uint32 ) 0x14u + ( uint32 ) ( ( uint32 ) ( n ) << 4 ) )
#define EMAC_CTRL_CnTXEN( n )  ( ( uint32 ) 0x18u + ( uint32 ) ( ( uint32 ) ( n ) << 4 ) )
#define EMAC_CTRL_CnMISCEN( n ) \
    ( ( uint32 ) 0x1Cu + ( uint32 ) ( ( uint32 ) ( n ) << 4 ) )
#define EMAC_CTRL_CnRXTHRESHEN( n ) \
    ( ( uint32 ) 0x20u + ( uint32 ) ( ( uint32 ) ( n ) << 4 ) )
#define EMAC_CTRL_C0RXTHRESHSTAT ( 0x40U )
#define EMAC_CTRL_C0RXSTAT       ( 0x44U )
#define EMAC_CTRL_C0TXSTAT       ( 0x48U )
#define EMAC_CTRL_C0MISCSTAT     ( 0x4CU )
#define EMAC_CTRL_C1RXTHRESHSTAT ( 0x50U )
#define EMAC_CTRL_C1RXSTAT       ( 0x54U )
#define EMAC_CTRL_C1TXSTAT       ( 0x58U )
#define EMAC_CTRL_C1MISCSTAT     ( 0x5CU )
#define EMAC_CTRL_C2RXTHRESHSTAT ( 0x60U )
#define EMAC_CTRL_C2RXSTAT       ( 0x64U )
#define EMAC_CTRL_C2TXSTAT       ( 0x68U )
#define EMAC_CTRL_C2MISCSTAT     ( 0x6CU )
#define EMAC_CTRL_C0RXIMAX       ( 0x70U )
#define EMAC_CTRL_C0TXIMAX       ( 0x74U )
#define EMAC_CTRL_C1RXIMAX       ( 0x78U )
#define EMAC_CTRL_C1TXIMAX       ( 0x7CU )
#define EMAC_CTRL_C2RXIMAX       ( 0x80U )
#define EMAC_CTRL_C2TXIMAX       ( 0x84U )

/**************************************************************************\
* Field Definition Macros
\**************************************************************************/

#ifdef __cplusplus
}
#endif

/* USER CODE BEGIN (2) */
/* USER CODE END */

#endif /* ifndef _HW_EMAC_CTRL_H_ */
