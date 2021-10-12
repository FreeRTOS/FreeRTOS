/*
 * Copyright 2019-2020 NXP
 * All rights reserved.
 *
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

#ifndef __SERIAL_PORT_INTERNAL_H__
#define __SERIAL_PORT_INTERNAL_H__

/*******************************************************************************
 * Definitions
 ******************************************************************************/

/*******************************************************************************
 * API
 ******************************************************************************/

#if defined(__cplusplus)
extern "C" {
#endif /* _cplusplus */

#if (defined(SERIAL_PORT_TYPE_UART) && (SERIAL_PORT_TYPE_UART > 0U))
serial_manager_status_t Serial_UartInit(serial_handle_t serialHandle, void *serialConfig);
serial_manager_status_t Serial_UartDeinit(serial_handle_t serialHandle);
serial_manager_status_t Serial_UartWrite(serial_handle_t serialHandle, uint8_t *buffer, uint32_t length);

#if (defined(SERIAL_MANAGER_NON_BLOCKING_MODE) && (SERIAL_MANAGER_NON_BLOCKING_MODE > 0U))
serial_manager_status_t Serial_UartWriteBlocking(serial_handle_t serialHandle, uint8_t *buffer, uint32_t length);
#endif /* SERIAL_MANAGER_NON_BLOCKING_MODE */

#if (defined(SERIAL_MANAGER_NON_BLOCKING_MODE) && (SERIAL_MANAGER_NON_BLOCKING_MODE > 0U))
#if (defined(SERIAL_MANAGER_NON_BLOCKING_DUAL_MODE) && (SERIAL_MANAGER_NON_BLOCKING_DUAL_MODE > 0U))
serial_manager_status_t Serial_UartRead(serial_handle_t serialHandle, uint8_t *buffer, uint32_t length);
#endif
#else
serial_manager_status_t Serial_UartRead(serial_handle_t serialHandle, uint8_t *buffer, uint32_t length);
#endif

#if (defined(SERIAL_MANAGER_NON_BLOCKING_MODE) && (SERIAL_MANAGER_NON_BLOCKING_MODE > 0U))
serial_manager_status_t Serial_UartCancelWrite(serial_handle_t serialHandle);
serial_manager_status_t Serial_UartInstallTxCallback(serial_handle_t serialHandle,
                                                     serial_manager_callback_t callback,
                                                     void *callbackParam);
serial_manager_status_t Serial_UartInstallRxCallback(serial_handle_t serialHandle,
                                                     serial_manager_callback_t callback,
                                                     void *callbackParam);
void Serial_UartIsrFunction(serial_handle_t serialHandle);
#endif
serial_manager_status_t Serial_UartEnterLowpower(serial_handle_t serialHandle);
serial_manager_status_t Serial_UartExitLowpower(serial_handle_t serialHandle);
#endif

#if (defined(SERIAL_PORT_TYPE_RPMSG) && (SERIAL_PORT_TYPE_RPMSG > 0U))
serial_manager_status_t Serial_RpmsgInit(serial_handle_t serialHandle, void *serialConfig);
serial_manager_status_t Serial_RpmsgDeinit(serial_handle_t serialHandle);
serial_manager_status_t Serial_RpmsgWrite(serial_handle_t serialHandle, uint8_t *buffer, uint32_t length);
serial_manager_status_t Serial_RpmsgWriteBlocking(serial_handle_t serialHandle, uint8_t *buffer, uint32_t length);
#if !(defined(SERIAL_MANAGER_NON_BLOCKING_MODE) && (SERIAL_MANAGER_NON_BLOCKING_MODE > 0U))
serial_manager_status_t Serial_RpmsgRead(serial_handle_t serialHandle, uint8_t *buffer, uint32_t length);
#endif

#if (defined(SERIAL_MANAGER_NON_BLOCKING_MODE) && (SERIAL_MANAGER_NON_BLOCKING_MODE > 0U))
serial_manager_status_t Serial_RpmsgCancelWrite(serial_handle_t serialHandle);
serial_manager_status_t Serial_RpmsgInstallTxCallback(serial_handle_t serialHandle,
                                                      serial_manager_callback_t callback,
                                                      void *callbackParam);
serial_manager_status_t Serial_RpmsgInstallRxCallback(serial_handle_t serialHandle,
                                                      serial_manager_callback_t callback,
                                                      void *callbackParam);
#endif
serial_manager_status_t Serial_RpmsgEnterLowpower(serial_handle_t serialHandle);
serial_manager_status_t Serial_RpmsgExitLowpower(serial_handle_t serialHandle);
#endif

#if (defined(SERIAL_PORT_TYPE_USBCDC) && (SERIAL_PORT_TYPE_USBCDC > 0U))
serial_manager_status_t Serial_UsbCdcInit(serial_handle_t serialHandle, void *config);
serial_manager_status_t Serial_UsbCdcDeinit(serial_handle_t serialHandle);
serial_manager_status_t Serial_UsbCdcWrite(serial_handle_t serialHandle, uint8_t *buffer, uint32_t length);
serial_manager_status_t Serial_UsbCdcRead(serial_handle_t serialHandle, uint8_t *buffer, uint32_t length);
serial_manager_status_t Serial_UsbCdcCancelWrite(serial_handle_t serialHandle);
serial_manager_status_t Serial_UsbCdcInstallTxCallback(serial_handle_t serialHandle,
                                                       serial_manager_callback_t callback,
                                                       void *callbackParam);
serial_manager_status_t Serial_UsbCdcInstallRxCallback(serial_handle_t serialHandle,
                                                       serial_manager_callback_t callback,
                                                       void *callbackParam);
void Serial_UsbCdcIsrFunction(serial_handle_t serialHandle);
#endif

#if (defined(SERIAL_PORT_TYPE_SWO) && (SERIAL_PORT_TYPE_SWO > 0U))
serial_manager_status_t Serial_SwoInit(serial_handle_t serialHandle, void *config);
serial_manager_status_t Serial_SwoDeinit(serial_handle_t serialHandle);
serial_manager_status_t Serial_SwoWrite(serial_handle_t serialHandle, uint8_t *buffer, uint32_t length);
#if !(defined(SERIAL_MANAGER_NON_BLOCKING_MODE) && (SERIAL_MANAGER_NON_BLOCKING_MODE > 0U))
serial_manager_status_t Serial_SwoRead(serial_handle_t serialHandle, uint8_t *buffer, uint32_t length);
#endif
#if (defined(SERIAL_MANAGER_NON_BLOCKING_MODE) && (SERIAL_MANAGER_NON_BLOCKING_MODE > 0U))
serial_manager_status_t Serial_SwoCancelWrite(serial_handle_t serialHandle);
serial_manager_status_t Serial_SwoInstallTxCallback(serial_handle_t serialHandle,
                                                    serial_manager_callback_t callback,
                                                    void *callbackParam);
serial_manager_status_t Serial_SwoInstallRxCallback(serial_handle_t serialHandle,
                                                    serial_manager_callback_t callback,
                                                    void *callbackParam);
void Serial_SwoIsrFunction(serial_handle_t serialHandle);
#endif
#endif

#if (defined(SERIAL_PORT_TYPE_VIRTUAL) && (SERIAL_PORT_TYPE_VIRTUAL > 0U))
serial_manager_status_t Serial_PortVirtualInit(serial_handle_t serialHandle, void *config);
serial_manager_status_t Serial_PortVirtualDeinit(serial_handle_t serialHandle);
serial_manager_status_t Serial_PortVirtualWrite(serial_handle_t serialHandle, uint8_t *buffer, uint32_t length);
serial_manager_status_t Serial_PortVirtualRead(serial_handle_t serialHandle, uint8_t *buffer, uint32_t length);
serial_manager_status_t Serial_PortVirtualCancelWrite(serial_handle_t serialHandle);
serial_manager_status_t Serial_PortVirtualInstallTxCallback(serial_handle_t serialHandle,
                                                            serial_manager_callback_t callback,
                                                            void *callbackParam);
serial_manager_status_t Serial_PortVirtualInstallRxCallback(serial_handle_t serialHandle,
                                                            serial_manager_callback_t callback,
                                                            void *callbackParam);
void Serial_PortVirtualIsrFunction(serial_handle_t serialHandle);
#endif

#if defined(__cplusplus)
}
#endif

#endif /* __SERIAL_PORT_INTERNAL_H__ */
