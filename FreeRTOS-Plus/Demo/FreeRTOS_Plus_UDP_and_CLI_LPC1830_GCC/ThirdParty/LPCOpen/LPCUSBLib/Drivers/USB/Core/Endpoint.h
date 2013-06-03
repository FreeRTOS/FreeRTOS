/*
 * @brief USB Endpoint definitions for all architectures
 *
 * @note
 * Copyright(C) NXP Semiconductors, 2012
 * Copyright(C) Dean Camera, 2011, 2012
 * All rights reserved.
 *
 * @par
 * Software that is described herein is for illustrative purposes only
 * which provides customers with programming information regarding the
 * LPC products.  This software is supplied "AS IS" without any warranties of
 * any kind, and NXP Semiconductors and its licensor disclaim any and
 * all warranties, express or implied, including all implied warranties of
 * merchantability, fitness for a particular purpose and non-infringement of
 * intellectual property rights.  NXP Semiconductors assumes no responsibility
 * or liability for the use of the software, conveys no license or rights under any
 * patent, copyright, mask work right, or any other intellectual property rights in
 * or to any products. NXP Semiconductors reserves the right to make changes
 * in the software without notification. NXP Semiconductors also makes no
 * representation or warranty that such application will be suitable for the
 * specified use without further testing or modification.
 *
 * @par
 * Permission to use, copy, modify, and distribute this software and its
 * documentation is hereby granted, under NXP Semiconductors' and its
 * licensor's relevant copyrights in the software, without fee, provided that it
 * is used in conjunction with NXP Semiconductors microcontrollers.  This
 * copyright, permission, and disclaimer notice must appear in all copies of
 * this code.
 */

/** @ingroup Group_EndpointManagement
 *  @defgroup Group_EndpointRW Endpoint Data Reading and Writing
 *  @brief Endpoint data read/write definitions.
 *
 *  Functions, macros, variables, enums and types related to data reading and writing from and to endpoints.
 */

/** @ingroup Group_EndpointRW
 *  @defgroup Group_EndpointPrimitiveRW Read/Write of Primitive Data Types
 *  @brief Endpoint data primitive read/write definitions.
 *
 *  Functions, macros, variables, enums and types related to data reading and writing of primitive data types
 *  from and to endpoints.
 */

/** @ingroup Group_EndpointManagement
 *  @defgroup Group_EndpointPacketManagement Endpoint Packet Management
 *  @brief USB Endpoint package management definitions.
 *
 *  Functions, macros, variables, enums and types related to packet management of endpoints.
 */

/** @ingroup Group_USB
 *  @defgroup Group_EndpointManagement Endpoint Management
 *  @brief Endpoint management definitions.
 *
 *  Functions, macros and enums related to endpoint management when in USB Device mode. This
 *  module contains the endpoint management macros, as well as endpoint interrupt and data
 *  send/receive functions for various data types.
 *
 *  @{
 */

#ifndef __ENDPOINT_H__
#define __ENDPOINT_H__

	/* Includes: */
		#include "../../../Common/Common.h"
		#include "USBMode.h"
		#include "USBTask.h"
		#include "USBInterrupt.h"
		
	/* Enable C linkage for C++ Compilers: */
		#if defined(__cplusplus)
			extern "C" {
		#endif

	/* Preprocessor Checks: */
		#if !defined(__INCLUDE_FROM_USB_DRIVER)
			#error Do not include this file directly. Include lpcroot/libraries/LPCUSBlib/Drivers/USB/USB.h instead.
		#endif

	/* Public Interface - May be used in end-application: */
		/* Macros: */
			/** Endpoint number mask, for masking against endpoint addresses to retrieve the endpoint's
			 *  numerical address in the device.
			 */
			#define ENDPOINT_EPNUM_MASK                     0x0F

			/** Endpoint address for the default control endpoint, which always resides in address 0. This is
			 *  defined for convenience to give more readable code when used with the endpoint macros.
			 */
			#define ENDPOINT_CONTROLEP                      0
				
			#if defined(__LPC18XX__) || defined(__LPC43XX__)
				#include "DCD/LPC18XX/Endpoint_LPC18xx.h"
			#elif defined(__LPC175X_6X__) || defined(__LPC177X_8X__) || defined(__LPC407X_8X__)
				#include "DCD/LPC17XX/Endpoint_LPC17xx.h"
			#elif defined(__LPC11U1X__) || defined(__LPC11U2X_3X__) || defined(__LPC1347__)
				#include "DCD/LPC11UXX/Endpoint_LPC11Uxx.h"
			#endif
			

			
			/** Mask for the bank mode selection for the @ref Endpoint_ConfigureEndpoint() macro. This indicates
			 *  that the endpoint should have one single bank, which requires less USB FIFO memory but results
			 *  in slower transfers as only one USB device (the LPC or the host) can access the endpoint's
			 *  bank at the one time.
			 */
			#define ENDPOINT_BANK_SINGLE                    (0 << 1)
			
			/** Mask for the bank mode selection for the @ref Endpoint_ConfigureEndpoint() macro. This indicates
			 *  that the endpoint should have two banks, which requires more USB FIFO memory but results
			 *  in faster transfers as one USB device (the LPC or the host) can access one bank while the other
			 *  accesses the second bank.
			 */
			#define ENDPOINT_BANK_DOUBLE                    (1 << 1)
			
			#if (!defined(FIXED_CONTROL_ENDPOINT_SIZE) || defined(__DOXYGEN__))
			/** Default size of the default control endpoint's bank, until altered by the control endpoint bank size
			 *  value in the device descriptor. Not available if the \c FIXED_CONTROL_ENDPOINT_SIZE token is defined.
			 */
			#define ENDPOINT_CONTROLEP_DEFAULT_SIZE     64
			#endif
			
			/** Retrieves the maximum bank size in bytes of a given endpoint.
			 *
			 *  @note This macro will only work correctly on endpoint indexes that are compile-time constants
			 *        defined by the preprocessor.
			 *
			 *  @param EPIndex  Endpoint number, a value between 0 and (\ref ENDPOINT_TOTAL_ENDPOINTS - 1)
			 */
			#define ENDPOINT_MAX_SIZE(EPIndex)              512
			
			#if !defined(CONTROL_ONLY_DEVICE) || defined(__DOXYGEN__)
			/** Total number of endpoints (including the default control endpoint at address 0) which may
			 *  be used in the device. Different USB LPC models support different amounts of endpoints,
			 *  this value reflects the maximum number of endpoints for the currently selected LPC model.
			 */
			#define ENDPOINT_TOTAL_ENDPOINTS0            ENDPOINT_DETAILS_MAXEP0
			#define ENDPOINT_TOTAL_ENDPOINTS1            ENDPOINT_DETAILS_MAXEP1
			#define ENDPOINT_TOTAL_ENDPOINTS(corenum)		 ((corenum) ? ENDPOINT_DETAILS_MAXEP1 : ENDPOINT_DETAILS_MAXEP0)
			#else
			#define ENDPOINT_TOTAL_ENDPOINTS            1
			#endif
			
			/* Enums: */
			/** Enum for the possible error return codes of the @ref Endpoint_WaitUntilReady() function.
			 *
			 *  @ingroup Group_EndpointRW
			 */
			enum Endpoint_WaitUntilReady_ErrorCodes_t {
				ENDPOINT_READYWAIT_NoError                 = 0,	/**< Endpoint is ready for next packet, no error. */
				ENDPOINT_READYWAIT_EndpointStalled         = 1,	/**< The endpoint was stalled during the stream
																 *   transfer by the host or device.
																 */
				ENDPOINT_READYWAIT_DeviceDisconnected      = 2,	/**< Device was disconnected from the host while
																 *   waiting for the endpoint to become ready.
																 */
				ENDPOINT_READYWAIT_BusSuspended            = 3,	/**< The USB bus has been suspended by the host and
																 *   no USB endpoint traffic can occur until the bus
																 *   has resumed.
																 */
				ENDPOINT_READYWAIT_Timeout                 = 4,	/**< The host failed to accept or send the next packet
																 *   within the software timeout period set by the
																 *   @ref USB_STREAM_TIMEOUT_MS macro.
																 */
			};
			
			/**
			 * @brief  Get the endpoint address of the currently selected endpoint. This is typically used to save
			 *  the currently selected endpoint number so that it can be restored after another endpoint has
			 *  been manipulated.
			 * @param  corenum :        ID Number of USB Core to be processed.
			 * @return Index of the currently selected endpoint
			 */
			PRAGMA_ALWAYS_INLINE
			static inline uint8_t Endpoint_GetCurrentEndpoint(uint8_t corenum) ATTR_WARN_UNUSED_RESULT ATTR_ALWAYS_INLINE;

			static inline uint8_t Endpoint_GetCurrentEndpoint(uint8_t corenum)
			{
				return endpointselected[corenum];
			}
			
			/**
			 * @brief  Selects the given endpoint number. If the address from the device descriptors is used, the
			 *  value should be masked with the @ref ENDPOINT_EPNUM_MASK constant to extract only the endpoint
			 *  number (and discarding the endpoint direction bit).
			 *
			 *  Any endpoint operations which do not require the endpoint number to be indicated will operate on
			 *  the currently selected endpoint.
			 *
			 * @param  corenum :        ID Number of USB Core to be processed.
			 * @param  EndpointNumber : Endpoint number to select
			 * @return Nothing
			 */
			PRAGMA_ALWAYS_INLINE
			static inline void Endpoint_SelectEndpoint(uint8_t corenum, const uint8_t EndpointNumber) ATTR_ALWAYS_INLINE;

			static inline void Endpoint_SelectEndpoint(uint8_t corenum, const uint8_t EndpointNumber)
			{
				endpointselected[corenum] = EndpointNumber;
				// usb_data_buffer_index = 0;
			}
			
			/**
			 * @brief  Reads one byte from the currently selected endpoint's bank, for OUT direction endpoints.
			 *
			 *  @ingroup Group_EndpointPrimitiveRW
			 *
			 * @param  corenum :        ID Number of USB Core to be processed.
			 * @return Next byte in the currently selected endpoint's FIFO buffer
			 */
			PRAGMA_ALWAYS_INLINE
			static inline uint8_t Endpoint_Read_8(uint8_t corenum) ATTR_WARN_UNUSED_RESULT ATTR_ALWAYS_INLINE;

			static inline uint8_t Endpoint_Read_8(uint8_t corenum)
			{
				uint8_t tem;
				if (endpointselected[corenum] == ENDPOINT_CONTROLEP) {
					tem = usb_data_buffer[corenum][usb_data_buffer_index[corenum]];
					usb_data_buffer_index[corenum]++;
					usb_data_buffer_size[corenum]--;
				}
				else {
					tem = usb_data_buffer_OUT[corenum][usb_data_buffer_OUT_index[corenum]];
					usb_data_buffer_OUT_index[corenum]++;
					usb_data_buffer_OUT_size[corenum]--;
				}
				return tem;
			}
			
			/**
			 * @brief  Determines the currently selected endpoint's direction
			 * @param  corenum :        ID Number of USB Core to be processed.
			 * @return The currently selected endpoint's direction, as a \c ENDPOINT_DIR_* mask.
			 */
			PRAGMA_ALWAYS_INLINE
			static inline uint8_t Endpoint_GetEndpointDirection(uint8_t corenum) ATTR_WARN_UNUSED_RESULT ATTR_ALWAYS_INLINE;

			static inline uint8_t Endpoint_GetEndpointDirection(uint8_t corenum)
			{
				return (endpointhandle(corenum)[endpointselected[corenum]] % 2) ? ENDPOINT_DIR_IN : ENDPOINT_DIR_OUT;
			}
			
			/**
			 * @brief  Determines if the currently selected endpoint may be read from (if data is waiting in the endpoint
			 *  bank and the endpoint is an OUT direction, or if the bank is not yet full if the endpoint is an IN
			 *  direction). This function will return false if an error has occurred in the endpoint, if the endpoint
			 *  is an OUT direction and no packet (or an empty packet) has been received, or if the endpoint is an IN
			 *  direction and the endpoint bank is full.
			 *
			 *  @ingroup Group_EndpointPacketManagement
			 *
			 * @param  corenum :        ID Number of USB Core to be processed.
			 *  @return Boolean \c true if the currently selected endpoint may be read from or written to, depending
			 *          on its direction.
			 */
			PRAGMA_ALWAYS_INLINE
			static inline bool Endpoint_IsReadWriteAllowed(uint8_t corenum) ATTR_WARN_UNUSED_RESULT ATTR_ALWAYS_INLINE;

			static inline bool Endpoint_IsReadWriteAllowed(uint8_t corenum)
			{
				return (Endpoint_GetEndpointDirection(corenum) == ENDPOINT_DIR_OUT) ? Endpoint_IsOUTReceived(corenum) : Endpoint_IsINReady(corenum);
			}
			
			/**
			 * @brief  Writes one byte to the currently selected endpoint's bank, for IN direction endpoints.
			 *
			 *  @ingroup Group_EndpointPrimitiveRW
			 *
			 * @param  corenum :        ID Number of USB Core to be processed.
			 * @param  Data : Data to write into the the currently selected endpoint's FIFO buffer
			 * @return Nothing
			 */
			PRAGMA_ALWAYS_INLINE
			static inline void Endpoint_Write_8(uint8_t corenum, const uint8_t Data) ATTR_ALWAYS_INLINE;

			static inline void Endpoint_Write_8(uint8_t corenum, const uint8_t Data)
			{
				if (endpointselected[corenum] == ENDPOINT_CONTROLEP) {
					usb_data_buffer[corenum][usb_data_buffer_index[corenum]] = Data;
					usb_data_buffer_index[corenum]++;
				}
				else {
					usb_data_buffer_IN[corenum][usb_data_buffer_IN_index[corenum]] = Data;
					usb_data_buffer_IN_index[corenum]++;
				}
			}
			
			/**
			 * @brief  Discards one byte from the currently selected endpoint's bank, for OUT direction endpoints.
			 * @param  corenum :        ID Number of USB Core to be processed.
			 * @return Nothing
			 *
			 *  @ingroup Group_EndpointPrimitiveRW
			 */
			PRAGMA_ALWAYS_INLINE
			static inline void Endpoint_Discard_8(uint8_t corenum) ATTR_ALWAYS_INLINE;

			static inline void Endpoint_Discard_8(uint8_t corenum)
			{
				volatile uint8_t dummy;
				dummy = Endpoint_Read_8(corenum);
				dummy = dummy;
			}
			
			/**
			 * @brief  Reads two bytes from the currently selected endpoint's bank in little endian format, for OUT
			 *  direction endpoints.
			 *
			 *  @ingroup Group_EndpointPrimitiveRW
			 *  @param  corenum :        ID Number of USB Core to be processed.
			 *  @return Next two bytes in the currently selected endpoint's FIFO buffer.
			 */
			PRAGMA_ALWAYS_INLINE
			static inline uint16_t Endpoint_Read_16_LE(uint8_t corenum) ATTR_WARN_UNUSED_RESULT ATTR_ALWAYS_INLINE;

			static inline uint16_t Endpoint_Read_16_LE(uint8_t corenum)
			{
				uint16_t tem = 0;
				uint8_t tem1, tem2;

				tem1 = Endpoint_Read_8(corenum);
				tem2 = Endpoint_Read_8(corenum);
				tem = (tem2 << 8) | tem1;
				return tem;
			}
			
			/**
			 * @brief  Reads two bytes from the currently selected endpoint's bank in big endian format, for OUT
			 *  direction endpoints.
			 *
			 *  @ingroup Group_EndpointPrimitiveRW
			 *
			 * @param  corenum :        ID Number of USB Core to be processed.
			 *  @return Next two bytes in the currently selected endpoint's FIFO buffer.
			 */
			PRAGMA_ALWAYS_INLINE
			static inline uint16_t Endpoint_Read_16_BE(uint8_t corenum) ATTR_WARN_UNUSED_RESULT ATTR_ALWAYS_INLINE;

			static inline uint16_t Endpoint_Read_16_BE(uint8_t corenum)
			{
				uint16_t tem = 0;
				uint8_t tem1, tem2;

				tem1 = Endpoint_Read_8(corenum);
				tem2 = Endpoint_Read_8(corenum);
				tem = (tem1 << 8) | tem2;
				return tem;
			}
			
			/**
			 * @brief  Writes two bytes to the currently selected endpoint's bank in little endian format, for IN
			 *  direction endpoints.
			 *
			 *  @ingroup Group_EndpointPrimitiveRW
			 *
			 * @param  corenum :        ID Number of USB Core to be processed.
			 * @param  Data : Data to write to the currently selected endpoint's FIFO buffer
			 * @return Nothing
			 */
			PRAGMA_ALWAYS_INLINE
			static inline void Endpoint_Write_16_LE(uint8_t corenum, const uint16_t Data) ATTR_ALWAYS_INLINE;

			static inline void Endpoint_Write_16_LE(uint8_t corenum, const uint16_t Data)
			{
				Endpoint_Write_8(corenum, Data & 0xFF);
				Endpoint_Write_8(corenum, (Data >> 8) & 0xFF);
			}
			
			/**
			 * @brief  Writes two bytes to the currently selected endpoint's bank in big endian format, for IN
			 *  direction endpoints.
			 *
			 *  @ingroup Group_EndpointPrimitiveRW
			 *
			 * @param  corenum :        ID Number of USB Core to be processed.
			 * @param  Data : Data to write to the currently selected endpoint's FIFO buffer
			 * @return Nothing
			 */
			PRAGMA_ALWAYS_INLINE
			static inline void Endpoint_Write_16_BE(uint8_t corenum, const uint16_t Data) ATTR_ALWAYS_INLINE;

			static inline void Endpoint_Write_16_BE(uint8_t corenum, const uint16_t Data)
			{
				Endpoint_Write_8(corenum, (Data >> 8) & 0xFF);
				Endpoint_Write_8(corenum, Data & 0xFF);
			}
			
			/**
			 * @brief  Discards two bytes from the currently selected endpoint's bank, for OUT direction endpoints.
			 * @return Nothing
			 *
			 *  @ingroup Group_EndpointPrimitiveRW
			 * @param  corenum :        ID Number of USB Core to be processed.
			 */
			PRAGMA_ALWAYS_INLINE
			static inline void Endpoint_Discard_16(uint8_t corenum) ATTR_ALWAYS_INLINE;

			static inline void Endpoint_Discard_16(uint8_t corenum)
			{
				uint8_t tem;
				tem = Endpoint_Read_8(corenum);
				tem = Endpoint_Read_8(corenum);
				tem  = tem;
			}
			
			/**
			 * @brief  Reads four bytes from the currently selected endpoint's bank in little endian format, for OUT
			 *  direction endpoints.
			 *
			 *  @ingroup Group_EndpointPrimitiveRW
			 *
			 * @param  corenum :        ID Number of USB Core to be processed.
			 *  @return Next four bytes in the currently selected endpoint's FIFO buffer.
			 */
			PRAGMA_ALWAYS_INLINE
			static inline uint32_t Endpoint_Read_32_LE(uint8_t corenum) ATTR_WARN_UNUSED_RESULT ATTR_ALWAYS_INLINE;

			static inline uint32_t Endpoint_Read_32_LE(uint8_t corenum)
			{
				uint32_t tem = 0;
				uint8_t tem1, tem2, tem3, tem4;

				tem1 = Endpoint_Read_8(corenum);
				tem2 = Endpoint_Read_8(corenum);
				tem3 = Endpoint_Read_8(corenum);
				tem4 = Endpoint_Read_8(corenum);
				tem = (tem4 << 24) | (tem3 << 16) | (tem2 << 8) | tem1;
				return tem;
			}
			
			/**
			 * @brief  Reads four bytes from the currently selected endpoint's bank in big endian format, for OUT
			 *  direction endpoints.
			 *
			 *  @ingroup Group_EndpointPrimitiveRW
			 *
			 *  @param  corenum :        ID Number of USB Core to be processed.
			 *  @return Next four bytes in the currently selected endpoint's FIFO buffer.
			 */
			PRAGMA_ALWAYS_INLINE
			static inline uint32_t Endpoint_Read_32_BE(uint8_t corenum) ATTR_WARN_UNUSED_RESULT ATTR_ALWAYS_INLINE;

			static inline uint32_t Endpoint_Read_32_BE(uint8_t corenum)
			{
				uint32_t tem = 0;
				uint8_t tem1, tem2, tem3, tem4;

				tem1 = Endpoint_Read_8(corenum);
				tem2 = Endpoint_Read_8(corenum);
				tem3 = Endpoint_Read_8(corenum);
				tem4 = Endpoint_Read_8(corenum);
				tem = (tem1 << 24) | (tem2 << 16) | (tem3 << 8) | tem4;
				return tem;
			}
			
			/**
			 * @brief  Writes four bytes to the currently selected endpoint's bank in little endian format, for IN
			 *  direction endpoints.
			 *
			 *  @ingroup Group_EndpointPrimitiveRW
			 *
			 * @param  corenum :        ID Number of USB Core to be processed.
			 * @param  Data : Data to write to the currently selected endpoint's FIFO buffer
			 * @return Nothing
			 */
			PRAGMA_ALWAYS_INLINE
			static inline void Endpoint_Write_32_LE(uint8_t corenum, const uint32_t Data) ATTR_ALWAYS_INLINE;

			static inline void Endpoint_Write_32_LE(uint8_t corenum, const uint32_t Data)
			{
				Endpoint_Write_8(corenum, Data & 0xFF);
				Endpoint_Write_8(corenum, (Data >> 8) & 0xFF);
				Endpoint_Write_8(corenum, (Data >> 16) & 0xFF);
				Endpoint_Write_8(corenum, (Data >> 24) & 0xFF);
			}
			
			/**
			 * @brief  Writes four bytes to the currently selected endpoint's bank in big endian format, for IN
			 *  direction endpoints.
			 *
			 *  @ingroup Group_EndpointPrimitiveRW
			 *
			 * @param  corenum :        ID Number of USB Core to be processed.
			 * @param  Data : Data to write to the currently selected endpoint's FIFO buffer
			 * @return Nothing
			 */
			PRAGMA_ALWAYS_INLINE
			static inline void Endpoint_Write_32_BE(uint8_t corenum, const uint32_t Data) ATTR_ALWAYS_INLINE;

			static inline void Endpoint_Write_32_BE(uint8_t corenum, const uint32_t Data)
			{
				Endpoint_Write_8(corenum, (Data >> 24) & 0xFF);
				Endpoint_Write_8(corenum, (Data >> 16) & 0xFF);
				Endpoint_Write_8(corenum, (Data >> 8) & 0xFF);
				Endpoint_Write_8(corenum, Data & 0xFF);
			}
			
			/**
			 * @brief  Discards four bytes from the currently selected endpoint's bank, for OUT direction endpoints.
			 * @return Nothing
			 *
			 *  @ingroup Group_EndpointPrimitiveRW
			 * @param  corenum :        ID Number of USB Core to be processed.
			 */
			PRAGMA_ALWAYS_INLINE
			static inline void Endpoint_Discard_32(uint8_t corenum) ATTR_ALWAYS_INLINE;

			static inline void Endpoint_Discard_32(uint8_t corenum)
			{
				uint8_t tem;
				tem = Endpoint_Read_8(corenum);
				tem = Endpoint_Read_8(corenum);
				tem = Endpoint_Read_8(corenum);
				tem = Endpoint_Read_8(corenum);
				tem = tem;
			}
			
			void Endpoint_GetSetupPackage(uint8_t corenum, uint8_t *pData);


	/* Disable C linkage for C++ Compilers: */
		#if defined(__cplusplus)
			}
		#endif

#endif

/** @} */

