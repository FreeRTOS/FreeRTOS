/*             ----> DO NOT REMOVE THE FOLLOWING NOTICE <----
 *
 *                 Copyright (c) 2014-2015 Datalight, Inc.
 *                     All Rights Reserved Worldwide.
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; use version 2 of the License.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but "AS-IS," WITHOUT ANY WARRANTY; without even the implied warranty
 *  of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License along
 *  with this program; if not, write to the Free Software Foundation, Inc.,
 *  51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 */

/*  Businesses and individuals that for commercial or other reasons cannot
 *  comply with the terms of the GPLv2 license may obtain a commercial license
 *  before incorporating Reliance Edge into proprietary software for
 *  distribution in any form.  Visit http://www.datalight.com/reliance-edge for
 *  more information.
 */

/** @file
 *  @brief Implements a synchronization object to provide mutual exclusion.
 */
#include <FreeRTOS.h>
#include <semphr.h>

#include <redfs.h>
#include <redosdeviations.h>

#if REDCONF_TASK_COUNT > 1U


    static SemaphoreHandle_t xMutex;
    #if defined( configSUPPORT_STATIC_ALLOCATION ) && ( configSUPPORT_STATIC_ALLOCATION == 1 )
        static StaticSemaphore_t xMutexBuffer;
    #endif


/** @brief Initialize the mutex.
 *
 *  After initialization, the mutex is in the released state.
 *
 *  The behavior of calling this function when the mutex is still initialized
 *  is undefined.
 *
 *  @return A negated ::REDSTATUS code indicating the operation result.
 *
 *  @retval 0   Operation was successful.
 */
    REDSTATUS RedOsMutexInit( void )
    {
        REDSTATUS ret = 0;

        #if defined( configSUPPORT_STATIC_ALLOCATION ) && ( configSUPPORT_STATIC_ALLOCATION == 1 )
            xMutex = xSemaphoreCreateMutexStatic( &xMutexBuffer );

            if( xMutex == NULL )
            {
                /*  The only error case for xSemaphoreCreateMutexStatic is that the mutex
                 *  buffer parameter is NULL, which is not the case.
                 */
                REDERROR();
                ret = -RED_EINVAL;
            }
        #else
            xMutex = xSemaphoreCreateMutex();

            if( xMutex == NULL )
            {
                ret = -RED_ENOMEM;
            }
        #endif /* if defined( configSUPPORT_STATIC_ALLOCATION ) && ( configSUPPORT_STATIC_ALLOCATION == 1 ) */

        return ret;
    }


/** @brief Uninitialize the mutex.
 *
 *  The behavior of calling this function when the mutex is not initialized is
 *  undefined; likewise, the behavior of uninitializing the mutex when it is
 *  in the acquired state is undefined.
 *
 *  @return A negated ::REDSTATUS code indicating the operation result.
 *
 *  @retval 0   Operation was successful.
 */
    REDSTATUS RedOsMutexUninit( void )
    {
        vSemaphoreDelete( xMutex );
        xMutex = NULL;

        return 0;
    }


/** @brief Acquire the mutex.
 *
 *  The behavior of calling this function when the mutex is not initialized is
 *  undefined; likewise, the behavior of recursively acquiring the mutex is
 *  undefined.
 */
    void RedOsMutexAcquire( void )
    {
        while( xSemaphoreTake( xMutex, portMAX_DELAY ) != pdTRUE )
        {
        }
    }


/** @brief Release the mutex.
 *
 *  The behavior is undefined in the following cases:
 *
 *  - Releasing the mutex when the mutex is not initialized.
 *  - Releasing the mutex when it is not in the acquired state.
 *  - Releasing the mutex from a task or thread other than the one which
 *    acquired the mutex.
 */
    void RedOsMutexRelease( void )
    {
        BaseType_t xSuccess;

        xSuccess = xSemaphoreGive( xMutex );
        REDASSERT( xSuccess == pdTRUE );
        IGNORE_ERRORS( xSuccess );
    }

#endif /* if REDCONF_TASK_COUNT > 1U */
