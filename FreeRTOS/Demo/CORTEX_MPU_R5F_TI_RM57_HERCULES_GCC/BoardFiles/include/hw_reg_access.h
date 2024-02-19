/*
 * hw_reg_access.h
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

#ifndef _HW_REG_ACCESS_H_
#define _HW_REG_ACCESS_H_

/* USER CODE BEGIN (0) */
/* USER CODE END */

#ifdef __cplusplus
extern "C" {
#endif

/* USER CODE BEGIN (1) */
/* USER CODE END */

/*******************************************************************************
 *
 * Macros for hardware access, both direct and via the bit-band region.
 *
 *****************************************************************************/
#define HWREG( x )  ( *( ( volatile uint32 * ) ( x ) ) )
#define HWREGH( x ) ( *( ( volatile uint16 * ) ( x ) ) )
#define HWREGB( x ) ( *( ( volatile uint8 * ) ( x ) ) )
#define HWREGBITW( x, b )                                                \
    ( HWREG( ( ( uint32 ) ( x ) & 0xF0000000U ) | ( uint32 ) 0x02000000U \
             | ( ( ( uint32 ) ( x ) & 0x000FFFFFU ) << 5U )              \
             | ( uint32 ) ( ( uint32 ) ( b ) << 2U ) ) )
#define HWREGBITH( x, b )                                                 \
    ( HWREGH( ( ( uint32 ) ( x ) & 0xF0000000U ) | ( uint32 ) 0x02000000U \
              | ( ( ( uint32 ) ( x ) & 0x000FFFFFU ) << 5U )              \
              | ( uint32 ) ( ( uint32 ) ( b ) << 2U ) ) )
#define HWREGBITB( x, b )                                                 \
    ( HWREGB( ( ( uint32 ) ( x ) & 0xF0000000U ) | ( uint32 ) 0x02000000U \
              | ( ( ( uint32 ) ( x ) & 0x000FFFFFU ) << 5U )              \
              | ( uint32 ) ( ( uint32 ) ( b ) << 2U ) ) )

/* USER CODE BEGIN (2) */
/* USER CODE END */

#ifdef __cplusplus
}
#endif

#endif /* __HW_TYPES_H__ */
