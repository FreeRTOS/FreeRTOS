/*
 * FreeRTOS V202212.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
/*! @file granular_lock_utest_common.h */

#ifndef GRANULAR_LOCK_UTEST_COMMON_H
#define GRANULAR_LOCK_UTEST_COMMON_H

/* C runtime includes. */
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>

/* Test includes. */
#include "unity.h"
#include "unity_memory.h"

/* FreeRTOS includes */
#include "FreeRTOS.h"
#include "task.h"
#include "global_vars.h"

/* ============================  Unity Fixtures  ============================ */

void granularLocksSetUp( void );
void granularLocksTearDown( void );

/* ==========================  Helper functions =========================== */

/**
 * The purpose of this test is to verify that data group critical sections are independent of each other.
 * When one core enters timer data group critical section, the other core can enter any other data group
 * (user data group in this case) critical section.
 */
void granular_locks_critical_section_independence( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                   portSPINLOCK_TYPE * pxDataGroupISRSpinlock );
void granular_locks_lock_independence( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock );

/**
 * The purpose of this test case is to verify that data group critical sections are mutually exclusive.
 * When one core enters timer data group critical section, the other cannot enter the same data group
 * critical section.
 */
void granular_locks_critical_section_mutual_exclusion( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                       portSPINLOCK_TYPE * pxDataGroupISRSpinlock );
void granular_locks_lock_mutual_exclusion( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock );

/**
 * The purpose of this test case is to verify that critical section nesting count is maintained
 * correctly for nested critical sections within timer operations.
 */
void granular_locks_critical_section_nesting( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                              portSPINLOCK_TYPE * pxDataGroupISRSpinlock );
void granular_locks_lock_nesting( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock );

/**
 * The purpose of this test case is to verify that the task's run state is protected when
 * it holds a timer data group lock. Operations like deletion/suspend are deferred till the
 * lock is held
 */
void granular_locks_critical_section_state_protection_deletion( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                                portSPINLOCK_TYPE * pxDataGroupISRSpinlock );
void granular_locks_critical_section_state_protection_suspension( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                                  portSPINLOCK_TYPE * pxDataGroupISRSpinlock );
void granular_locks_critical_section_state_protection_deletion_suspension( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                                           portSPINLOCK_TYPE * pxDataGroupISRSpinlock );
void granular_locks_critical_section_state_protection_suspension_deletion( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                                           portSPINLOCK_TYPE * pxDataGroupISRSpinlock );
void granular_locks_critical_section_state_protection_suspension_resumption_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                                                  portSPINLOCK_TYPE * pxDataGroupISRSpinlock );
void granular_locks_lock_state_protection_deletion( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock );
void granular_locks_lock_state_protection_suspension( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock );
void granular_locks_lock_state_protection_deletion_suspension( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock );
void granular_locks_lock_state_protection_suspension_deletion( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock );
void granular_locks_lock_state_protection_suspension_resumption_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock );

/**
 * The purpose of this test case is to verify that the task's run state is protected when
 * it holds a timer data group lock. Place the task on an event list won't nullify the
 * task state change after leaving the critical section.
 */
void granular_locks_critical_section_state_protection_vTaskPlaceOnEventList_blocked_deletion_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                                                                   portSPINLOCK_TYPE * pxDataGroupISRSpinlock );
void granular_locks_critical_section_state_protection_vTaskPlaceOnEventList_blocked_suspension_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                                                                     portSPINLOCK_TYPE * pxDataGroupISRSpinlock );
void granular_locks_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_blocked_deletion_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                                                                            portSPINLOCK_TYPE * pxDataGroupISRSpinlock );
void granular_locks_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_blocked_suspension_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                                                                              portSPINLOCK_TYPE * pxDataGroupISRSpinlock );
void granular_locks_critical_section_state_protection_vTaskPlaceOnEventListRestricted_blocked_deletion_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                                                                             portSPINLOCK_TYPE * pxDataGroupISRSpinlock );
void granular_locks_critical_section_state_protection_vTaskPlaceOnEventListRestricted_blocked_suspension_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                                                                               portSPINLOCK_TYPE * pxDataGroupISRSpinlock );
void granular_locks_critical_section_state_protection_vTaskPlaceOnEventList_deletion_blocked_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                                                                   portSPINLOCK_TYPE * pxDataGroupISRSpinlock );
void granular_locks_critical_section_state_protection_vTaskPlaceOnEventList_deletion_blocked_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                                                                   portSPINLOCK_TYPE * pxDataGroupISRSpinlock );
void granular_locks_critical_section_state_protection_vTaskPlaceOnEventList_suspension_blocked_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                                                                     portSPINLOCK_TYPE * pxDataGroupISRSpinlock );
void granular_locks_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_deletion_blocked_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                                                                            portSPINLOCK_TYPE * pxDataGroupISRSpinlock );
void granular_locks_critical_section_state_protection_vTaskPlaceOnUnorderedEventList_suspension_blocked_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                                                                              portSPINLOCK_TYPE * pxDataGroupISRSpinlock );
void granular_locks_critical_section_state_protection_vTaskPlaceOnEventListRestricted_deletion_blocked_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                                                                             portSPINLOCK_TYPE * pxDataGroupISRSpinlock );
void granular_locks_critical_section_state_protection_vTaskPlaceOnEventListRestricted_suspension_blocked_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock,
                                                                                                               portSPINLOCK_TYPE * pxDataGroupISRSpinlock );
void granular_locks_lock_state_protection_vTaskPlaceOnEventList_blocked_deletion_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock );
void granular_locks_lock_state_protection_vTaskPlaceOnEventList_blocked_suspension_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock );
void granular_locks_lock_state_protection_vTaskPlaceOnUnorderedEventList_blocked_deletion_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock );
void granular_locks_lock_state_protection_vTaskPlaceOnUnorderedEventList_blocked_suspension_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock );
void granular_locks_lock_state_protection_vTaskPlaceOnEventListRestricted_blocked_deletion_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock );
void granular_locks_lock_state_protection_vTaskPlaceOnEventListRestricted_blocked_suspension_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock );
void granular_locks_lock_state_protection_vTaskPlaceOnEventList_deletion_blocked_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock );
void granular_locks_lock_state_protection_vTaskPlaceOnEventList_suspension_blocked_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock );
void granular_locks_lock_state_protection_vTaskPlaceOnUnorderedEventList_deletion_blocked_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock );
void granular_locks_lock_state_protection_vTaskPlaceOnUnorderedEventList_suspension_blocked_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock );
void granular_locks_lock_state_protection_vTaskPlaceOnEventListRestricted_deletion_blocked_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock );
void granular_locks_lock_state_protection_vTaskPlaceOnEventListRestricted_suspension_blocked_test( portSPINLOCK_TYPE * pxDataGroupTaskSpinlock );

#endif /* GRANULAR_LOCK_UTEST_COMMON_H */
