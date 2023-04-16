/*
 * FreeRTOS V202212.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

/* Standard includes. */
#include <stdio.h>
#include <stdlib.h>

/* FreeRTOS includes. */
#include "secure_port_macros.h"

/* Device includes. */
#include "nrf.h"
#include "arm_cmse.h"


#if ( __ARM_FEATURE_CMSE & 1 ) == 0
    #error "Need ARMv8-M security extensions"
#elif ( __ARM_FEATURE_CMSE & 2 ) == 0
    #error "Compile with --cmse"
#endif

/* Start address of non-secure application. */
#define mainNONSECURE_APP_START_ADDRESS     ( 0x00080000UL )

/* typedef for non-secure Reset Handler. */
typedef void ( *NonSecureResetHandler_t ) ( void ) __attribute__( ( cmse_nonsecure_call ) );
/*-----------------------------------------------------------*/

/**
 * @brief Boots into the non-secure code.
 *
 * @param[in] ulNonSecureStartAddress Start address of the non-secure application.
 */
static void prvBootNonSecure( uint32_t ulNonSecureStartAddress );

/**
 * @brief Sets up System Protection Unit (SPU) for non-secure and NSC sections.
 */
static void prvSetupSPU( void );
/*-----------------------------------------------------------*/

/* For instructions on how to build and run this demo, visit the following link:
 * https://www.freertos.org/RTOS-Cortex-M33-LPC55S69-MCUXpresso-GCC.html
 */

/* Secure main(). */
int main(void)
{
    printf( "Booting Secure World.\r\n" );

    /* Set CP10 and CP11 full access from Non-Secure code. */
    SCB_NS->CPACR |= ( ( 3UL << 10 * 2 ) | ( 3UL << 11 * 2 ) );

    prvSetupSPU();

    /* Boot the non-secure code. */
    prvBootNonSecure( mainNONSECURE_APP_START_ADDRESS );

    /* Non-secure software does not return, this code is not executed. */
    for( ; ; )
    {
        /* Should not reach here. */
    }
}
/*-----------------------------------------------------------*/

static void prvBootNonSecure( uint32_t ulNonSecureStartAddress )
{
    NonSecureResetHandler_t pxNonSecureResetHandler;

    /* Setup the non-secure vector table. */
    SCB_NS->VTOR = ulNonSecureStartAddress;

    /* Main Stack Pointer value for the non-secure side is the first entry in
     * the non-secure vector table. Read the first entry and assign the same to
     * the non-secure main stack pointer(MSP_NS). */
    secureportSET_MSP_NS( *( ( uint32_t * )( ulNonSecureStartAddress ) ) );

    /* Reset Handler for the non-secure side is the second entry in the
     * non-secure vector table. Read the second entry to get the non-secure
     * Reset Handler. */
    pxNonSecureResetHandler = ( NonSecureResetHandler_t )( * ( ( uint32_t * ) ( ( ulNonSecureStartAddress ) + 4U ) ) );

    /* Start non-secure state software application by jumping to the non-secure
     * Reset Handler. */
    pxNonSecureResetHandler();
}
/*-----------------------------------------------------------*/

static void prvSetupSPU( void )
{
    int i;

    /* The flash memory space is divided into 32 regions of 32 KiB. We configure
     * the flash as follows:
     *
     * Region 0-15  - Secure. Last 4KiB of region 15 is Non-Secure Callable.
     * Region 16-31 - Non-Secure.
     */
    for( i = 0; i < 16; i ++ )
    {
        NRF_SPU_S->FLASHREGION[ i ].PERM = ( SPU_FLASHREGION_PERM_SECATTR_Msk |
                                             SPU_FLASHREGION_PERM_READ_Msk |
                                             SPU_FLASHREGION_PERM_EXECUTE_Msk |
                                             SPU_FLASHREGION_PERM_LOCK_Msk );
    }

    NRF_SPU_S->FLASHNSC[ 0 ].REGION = 15;
    NRF_SPU_S->FLASHNSC[ 0 ].SIZE   = SPU_FLASHNSC_SIZE_SIZE_4096;

    for( i = 16; i < 32; i ++ )
    {
        NRF_SPU_S->FLASHREGION[ i ].PERM = ( SPU_FLASHREGION_PERM_EXECUTE_Msk |
                                             SPU_FLASHREGION_PERM_READ_Msk |
                                             SPU_FLASHREGION_PERM_LOCK_Msk );
    }

    /* The RAM memory space is divided into 32 regions of 8 KiB. We configure
     * the RAM as follows:
     *
     * Region 0-15  - Secure.
     * Region 16-30 - Non-Secure.
     * Region 31 is configured in the startup sequence in the function
     * SystemStoreFICRNS, so we do not touch that.
     */
    for( i = 0; i < 16; i ++ )
    {
        NRF_SPU_S->RAMREGION[ i ].PERM = ( SPU_RAMREGION_PERM_SECATTR_Msk |
                                           SPU_RAMREGION_PERM_READ_Msk |
                                           SPU_RAMREGION_PERM_WRITE_Msk |
                                           SPU_RAMREGION_PERM_LOCK_Msk );
    }

    for( i = 16; i < 31; i ++ )
    {
        NRF_SPU_S->RAMREGION[ i ].PERM = ( SPU_RAMREGION_PERM_READ_Msk |
                                           SPU_RAMREGION_PERM_WRITE_Msk |
                                           SPU_RAMREGION_PERM_LOCK_Msk );
    }
}
/*-----------------------------------------------------------*/
