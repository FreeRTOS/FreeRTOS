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

#ifndef FAKE_PORT_H
#define FAKE_PORT_H

void vFakePortYield( void );
void vFakePortYieldFromISR( void );
void vFakePortYieldWithinAPI( void );

void vFakePortRestoreInterrupts( UBaseType_t );
uint32_t vFakePortDisableInterrupts( void );
void vFakePortEnableInterrupts( void );
void vFakePortClearInterruptMaskFromISR( UBaseType_t uxNewMaskValue );
void vFakePortClearInterruptMask( UBaseType_t uxNewMaskValue );
UBaseType_t ulFakePortSetInterruptMaskFromISR( void );
UBaseType_t ulFakePortSetInterruptMask( void );

void vFakePortAssertIfInterruptPriorityInvalid( void );

void vFakePortEnterCriticalSection( void );
void vFakePortExitCriticalSection( void );
void vPortCurrentTaskDying( void * pxTaskToDelete,
                            volatile BaseType_t * pxPendYield );

void vPortSuppressTicksAndSleep( TickType_t xExpectedIdleTime );

void portSetupTCB_CB( void * tcb );

void vFakePortGetISRLock( void );
void vFakePortReleaseISRLock( void );
void vFakePortGetTaskLock( void );
void vFakePortReleaseTaskLock( void );

void vFakePortAssertIfISR();
BaseType_t vFakePortCheckIfInISR( void );

unsigned int vFakePortGetCoreID( void );
void vFakePortYieldCore( int );

portBASE_TYPE vFakePortEnterCriticalFromISR( void );
void vFakePortExitCriticalFromISR( portBASE_TYPE uxSavedInterruptState );

void vFakePortAllocateSecureContext( BaseType_t stackSize );

#endif /* FAKE_PORT_H */
