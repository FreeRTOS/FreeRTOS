/*

Copyright (c) 2010 - 2021, Nordic Semiconductor ASA All rights reserved.

SPDX-License-Identifier: BSD-3-Clause

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this
   list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright
   notice, this list of conditions and the following disclaimer in the
   documentation and/or other materials provided with the distribution.

3. Neither the name of Nordic Semiconductor ASA nor the names of its
   contributors may be used to endorse or promote products derived from this
   software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
IMPLIED WARRANTIES OF MERCHANTABILITY, AND FITNESS FOR A PARTICULAR PURPOSE
ARE DISCLAIMED. IN NO EVENT SHALL NORDIC SEMICONDUCTOR ASA OR CONTRIBUTORS BE
LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
POSSIBILITY OF SUCH DAMAGE.

*/

#ifndef NRF52_TO_NRF52810_H
#define NRF52_TO_NRF52810_H

/*lint ++flb "Enter library region */

/* This file is given to prevent your SW from not compiling with the name changes between nRF51 or nRF52832 and nRF52810 devices.
 * It redefines the old nRF51 or nRF52832 names into the new ones as long as the functionality is still supported. If the
 * functionality is gone, there old names are not defined, so compilation will fail. Note that also includes macros
 * from the nrf52_namechange.h file. */
 
/* Differences between latest nRF52 headers and nRF52810 headers. */

/* Interrupt service routines handlers. Note that handlers SPIM0_SPIS0_TWIM0_TWIS0_SPI0_TWI0_IRQHandler and 
   SPIM1_SPIS1_TWIM1_TWIS1_SPI1_TWI1_IRQHandler are not redefined since functionality is not equivalent. */
#ifndef COMP_LPCOMP_IRQHandler
    #define COMP_LPCOMP_IRQHandler      COMP_IRQHandler
#endif
#ifndef SWI2_EGU2_IRQHandler
    #define SWI2_EGU2_IRQHandler        SWI2_IRQHandler
#endif
#ifndef SWI3_EGU3_IRQHandler
    #define SWI3_EGU3_IRQHandler        SWI3_IRQHandler
#endif
#ifndef SWI4_EGU4_IRQHandler
    #define SWI4_EGU4_IRQHandler        SWI4_IRQHandler
#endif
#ifndef SWI5_EGU5_IRQHandler
    #define SWI5_EGU5_IRQHandler        SWI5_IRQHandler
#endif

/* Interrupt service routines index. Note that indexes SPIM0_SPIS0_TWIM0_TWIS0_SPI0_TWI0_IRQn and 
   SPIM1_SPIS1_TWIM1_TWIS1_SPI1_TWI1_IRQn are not redefined since functionality is not equivalent. */
#ifndef COMP_LPCOMP_IRQn
    #define COMP_LPCOMP_IRQn            COMP_IRQn
#endif
#ifndef SWI2_EGU2_IRQn
    #define SWI2_EGU2_IRQn              SWI2_IRQn
#endif
#ifndef SWI3_EGU3_IRQn
    #define SWI3_EGU3_IRQn              SWI3_IRQn
#endif
#ifndef SWI4_EGU4_IRQn
    #define SWI4_EGU4_IRQn              SWI4_IRQn
#endif
#ifndef SWI5_EGU5_IRQn
    #define SWI5_EGU5_IRQn              SWI5_IRQn
#endif

/* From nrf52_name_change.h. Several macros changed in different versions of nRF52 headers. By defining the following, any code written for any version of nRF52 headers will still compile. */

/* I2S */
/* Several enumerations changed case. Adding old macros to keep compilation compatibility. */
#ifndef I2S_ENABLE_ENABLE_DISABLE
    #define I2S_ENABLE_ENABLE_DISABLE           I2S_ENABLE_ENABLE_Disabled
#endif
#ifndef I2S_ENABLE_ENABLE_ENABLE
    #define I2S_ENABLE_ENABLE_ENABLE            I2S_ENABLE_ENABLE_Enabled
#endif
#ifndef I2S_CONFIG_MODE_MODE_MASTER
    #define I2S_CONFIG_MODE_MODE_MASTER         I2S_CONFIG_MODE_MODE_Master
#endif
#ifndef I2S_CONFIG_MODE_MODE_SLAVE
    #define I2S_CONFIG_MODE_MODE_SLAVE          I2S_CONFIG_MODE_MODE_Slave
#endif
#ifndef I2S_CONFIG_RXEN_RXEN_DISABLE
    #define I2S_CONFIG_RXEN_RXEN_DISABLE        I2S_CONFIG_RXEN_RXEN_Disabled
#endif
#ifndef I2S_CONFIG_RXEN_RXEN_ENABLE
    #define I2S_CONFIG_RXEN_RXEN_ENABLE         I2S_CONFIG_RXEN_RXEN_Enabled
#endif
#ifndef I2S_CONFIG_TXEN_TXEN_DISABLE
    #define I2S_CONFIG_TXEN_TXEN_DISABLE        I2S_CONFIG_TXEN_TXEN_Disabled
#endif
#ifndef I2S_CONFIG_TXEN_TXEN_ENABLE
    #define I2S_CONFIG_TXEN_TXEN_ENABLE         I2S_CONFIG_TXEN_TXEN_Enabled
#endif
#ifndef I2S_CONFIG_MCKEN_MCKEN_DISABLE
    #define I2S_CONFIG_MCKEN_MCKEN_DISABLE      I2S_CONFIG_MCKEN_MCKEN_Disabled
#endif
#ifndef I2S_CONFIG_MCKEN_MCKEN_ENABLE
    #define I2S_CONFIG_MCKEN_MCKEN_ENABLE       I2S_CONFIG_MCKEN_MCKEN_Enabled
#endif
#ifndef I2S_CONFIG_SWIDTH_SWIDTH_8BIT
    #define I2S_CONFIG_SWIDTH_SWIDTH_8BIT       I2S_CONFIG_SWIDTH_SWIDTH_8Bit
#endif
#ifndef I2S_CONFIG_SWIDTH_SWIDTH_16BIT
    #define I2S_CONFIG_SWIDTH_SWIDTH_16BIT      I2S_CONFIG_SWIDTH_SWIDTH_16Bit
#endif
#ifndef I2S_CONFIG_SWIDTH_SWIDTH_24BIT
    #define I2S_CONFIG_SWIDTH_SWIDTH_24BIT      I2S_CONFIG_SWIDTH_SWIDTH_24Bit
#endif
#ifndef I2S_CONFIG_ALIGN_ALIGN_LEFT
    #define I2S_CONFIG_ALIGN_ALIGN_LEFT         I2S_CONFIG_ALIGN_ALIGN_Left
#endif
#ifndef I2S_CONFIG_ALIGN_ALIGN_RIGHT
    #define I2S_CONFIG_ALIGN_ALIGN_RIGHT        I2S_CONFIG_ALIGN_ALIGN_Right
#endif
#ifndef I2S_CONFIG_FORMAT_FORMAT_ALIGNED
    #define I2S_CONFIG_FORMAT_FORMAT_ALIGNED    I2S_CONFIG_FORMAT_FORMAT_Aligned
#endif
#ifndef I2S_CONFIG_CHANNELS_CHANNELS_STEREO
    #define I2S_CONFIG_CHANNELS_CHANNELS_STEREO I2S_CONFIG_CHANNELS_CHANNELS_Stereo
#endif
#ifndef I2S_CONFIG_CHANNELS_CHANNELS_LEFT
    #define I2S_CONFIG_CHANNELS_CHANNELS_LEFT   I2S_CONFIG_CHANNELS_CHANNELS_Left
#endif 
#ifndef I2S_CONFIG_CHANNELS_CHANNELS_RIGHT
    #define I2S_CONFIG_CHANNELS_CHANNELS_RIGHT  I2S_CONFIG_CHANNELS_CHANNELS_Right
#endif

/* LPCOMP */
/* Corrected typo in RESULT register. */
#ifndef LPCOMP_RESULT_RESULT_Bellow
    #define LPCOMP_RESULT_RESULT_Bellow         LPCOMP_RESULT_RESULT_Below
#endif


/*lint --flb "Leave library region" */

#endif /* NRF52_TO_NRF52810_H */

