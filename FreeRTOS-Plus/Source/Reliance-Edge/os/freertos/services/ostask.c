/*             ----> DO NOT REMOVE THE FOLLOWING NOTICE <----

                   Copyright (c) 2014-2015 Datalight, Inc.
                       All Rights Reserved Worldwide.

    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; use version 2 of the License.

    This program is distributed in the hope that it will be useful,
    but "AS-IS," WITHOUT ANY WARRANTY; without even the implied warranty
    of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License along
    with this program; if not, write to the Free Software Foundation, Inc.,
    51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
*/
/*  Businesses and individuals that for commercial or other reasons cannot
    comply with the terms of the GPLv2 license may obtain a commercial license
    before incorporating Reliance Edge into proprietary software for
    distribution in any form.  Visit http://www.datalight.com/reliance-edge for
    more information.
*/
/** @file
    @brief Implements task functions.
*/
#include <FreeRTOS.h>
#include <task.h>

#include <redfs.h>

#if (REDCONF_TASK_COUNT > 1U) && (REDCONF_API_POSIX == 1)

#include <redosdeviations.h>

#if INCLUDE_xTaskGetCurrentTaskHandle != 1
  #error "INCLUDE_xTaskGetCurrentTaskHandle must be 1 when REDCONF_TASK_COUNT > 1 and REDCONF_API_POSIX == 1"
#endif


/** @brief Get the current task ID.

    This task ID must be unique for all tasks using the file system.

    @return The task ID.  Must not be 0.
*/
uint32_t RedOsTaskId(void)
{
    /*  Simply casting the xTaskGetCurrentTaskHandle() return value results in
        warnings from some compilers, so use variables.
    */
    TaskHandle_t    xTask = xTaskGetCurrentTaskHandle();
    uintptr_t       taskptr = CAST_TASK_PTR_TO_UINTPTR(xTask);
    uint32_t        ulTaskPtr = (uint32_t)taskptr;

    /*  Assert no information was lost casting from uintptr_t to uint32_t.
    */
    REDASSERT(ulTaskPtr == taskptr);

    /*  NULL is a valid task handle in FreeRTOS, so add one to all task IDs.
    */
    REDASSERT((ulTaskPtr + 1U) != 0U);
    return ulTaskPtr + 1U;
}

#endif

