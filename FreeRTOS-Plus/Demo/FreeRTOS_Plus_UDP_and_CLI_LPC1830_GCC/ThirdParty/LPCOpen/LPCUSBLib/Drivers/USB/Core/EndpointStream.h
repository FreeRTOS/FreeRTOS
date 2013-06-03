/*
 * @brief Endpoint data stream transmission and reception management
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

/** @ingroup Group_EndpointRW  
 *  @defgroup Group_EndpointStreamRW Read/Write of Multi-Byte Streams
 *  @brief Endpoint data stream transmission and reception management.
 *
 *  Functions, macros, variables, enums and types related to data reading and writing of data streams from
 *  and to endpoints.
 *
 *  @{
 */ 

#ifndef __ENDPOINT_STREAM_H__
#define __ENDPOINT_STREAM_H__

	/* Includes: */
		#include "../../../Common/Common.h"
		#include "USBMode.h"

	/* Enable C linkage for C++ Compilers: */
		#if defined(__cplusplus)
			extern "C" {
		#endif

	/* Preprocessor Checks: */
		#if !defined(__INCLUDE_FROM_USB_DRIVER)
			#error Do not include this file directly. Include lpcroot/libraries/LPCUSBlib/Drivers/USB/USB.h instead.
		#endif

	/* Public Interface - May be used in end-application: */
		/* Enums: */
			/** Enum for the possible error return codes of the \c Endpoint_*_Stream_* functions. */
			enum Endpoint_Stream_RW_ErrorCodes_t
			{
				ENDPOINT_RWSTREAM_NoError            = 0, /**< Command completed successfully, no error. */
				ENDPOINT_RWSTREAM_EndpointStalled    = 1, /**< The endpoint was stalled during the stream
				                                           *   transfer by the host or device.
				                                           */
				ENDPOINT_RWSTREAM_DeviceDisconnected = 2, /**< Device was disconnected from the host during
				                                           *   the transfer.
				                                           */
				ENDPOINT_RWSTREAM_BusSuspended       = 3, /**< The USB bus has been suspended by the host and
				                                           *   no USB endpoint traffic can occur until the bus
				                                           *   has resumed.
				                                           */
				ENDPOINT_RWSTREAM_Timeout            = 4, /**< The host failed to accept or send the next packet
				                                           *   within the software timeout period set by the
				                                           *   @ref USB_STREAM_TIMEOUT_MS macro.
				                                           */
				ENDPOINT_RWSTREAM_IncompleteTransfer = 5, /**< Indicates that the endpoint bank became full or empty before
				                                           *   the complete contents of the current stream could be
				                                           *   transferred. The endpoint stream function should be called
				                                           *   again to process the next chunk of data in the transfer.
				                                           */
			};
			
			/** Enum for the possible error return codes of the \c Endpoint_*_Control_Stream_* functions. */
			enum Endpoint_ControlStream_RW_ErrorCodes_t
			{
				ENDPOINT_RWCSTREAM_NoError            = 0, /**< Command completed successfully, no error. */
				ENDPOINT_RWCSTREAM_HostAborted        = 1, /**< The aborted the transfer prematurely. */
				ENDPOINT_RWCSTREAM_DeviceDisconnected = 2, /**< Device was disconnected from the host during
				                                            *   the transfer.
				                                            */
				ENDPOINT_RWCSTREAM_BusSuspended       = 3, /**< The USB bus has been suspended by the host and
				                                            *   no USB endpoint traffic can occur until the bus
				                                            *   has resumed.
				                                            */
			};

		#include "../../../Common/Common.h"
		#include "USBTask.h"
		
		/* Function Prototypes: */
			/** \name Stream functions for null data */
			//@{
		/**
		 * @brief  Reads and discards the given number of bytes from the currently selected endpoint's bank,
		 *  discarding fully read packets from the host as needed. The last packet is not automatically
		 *  discarded once the remaining bytes has been read; the user is responsible for manually
		 *  discarding the last packet from the host via the @ref Endpoint_ClearOUT() macro.
		 *
		 *  If the BytesProcessed parameter is \c NULL, the entire stream transfer is attempted at once,
		 *  failing or succeeding as a single unit. If the BytesProcessed parameter points to a valid
		 *  storage location, the transfer will instead be performed as a series of chunks. Each time
		 *  the endpoint bank becomes empty while there is still data to process (and after the current
		 *  packet has been acknowledged) the BytesProcessed location will be updated with the total number
		 *  of bytes processed in the stream, and the function will exit with an error code of
		 *  @ref ENDPOINT_RWSTREAM_IncompleteTransfer. This allows for any abort checking to be performed
		 *  in the user code - to continue the transfer, call the function again with identical parameters
		 *  and it will resume until the BytesProcessed value reaches the total transfer length.
		 *
		 *  <b>Single Stream Transfer Example:</b>
		 *  \code
		 *  uint8_t ErrorCode;
		 *
		 *  if ((ErrorCode = Endpoint_Discard_Stream(512, NULL)) != ENDPOINT_RWSTREAM_NoError)
		 *  {
		 *       // Stream failed to complete - check ErrorCode here
		 *  }
		 *  \endcode
		 *
		 *  <b>Partial Stream Transfers Example:</b>
		 *  \code
		 *  uint8_t  ErrorCode;
		 *  uint16_t BytesProcessed;
		 *
		 *  BytesProcessed = 0;
		 *  while ((ErrorCode = Endpoint_Discard_Stream(512, &BytesProcessed)) == ENDPOINT_RWSTREAM_IncompleteTransfer)
		 *  {
		 *      // Stream not yet complete - do other actions here, abort if required
		 *  }
		 *
		 *  if (ErrorCode != ENDPOINT_RWSTREAM_NoError)
		 *  {
		 *      // Stream failed to complete - check ErrorCode here
		 *  }
		 *  \endcode
		 *
		 *  @note This routine should not be used on CONTROL type endpoints.
		 *
		 *  @param     corenum         ID Number of USB Core to be processed.
		 *  @param     Length          Number of bytes to discard via the currently selected endpoint.
		 *  @param     BytesProcessed  Pointer to a location where the total number of bytes processed in the current
		 *                             transaction should be updated, \c NULL if the entire stream should be read at once.
		 *
		 * @param  Length :         Number of bytes to discard via the currently selected endpoint
		 * @param  BytesProcessed : Pointer to a location where the total number of bytes processed in the current
		 *                          transaction should be updated, NULL if the entire stream should be read at once.
		 * @return A value from the @ref Endpoint_Stream_RW_ErrorCodes_t enum
		 */
		uint8_t Endpoint_Discard_Stream(uint8_t corenum,
										uint16_t Length,
										uint16_t *const BytesProcessed);

		/**
		 * @brief  Writes a given number of zeroed bytes to the currently selected endpoint's bank, sending
		 *  full packets to the host as needed. The last packet is not automatically sent once the 
		 *  remaining bytes have been written; the user is responsible for manually sending the last
		 *  packet to the host via the @ref Endpoint_ClearIN() macro.
		 *
		 *  If the BytesProcessed parameter is \c NULL, the entire stream transfer is attempted at once,
		 *  failing or succeeding as a single unit. If the BytesProcessed parameter points to a valid
		 *  storage location, the transfer will instead be performed as a series of chunks. Each time
		 *  the endpoint bank becomes full while there is still data to process (and after the current
		 *  packet transmission has been initiated) the BytesProcessed location will be updated with the
		 *  total number of bytes processed in the stream, and the function will exit with an error code of
		 *  @ref ENDPOINT_RWSTREAM_IncompleteTransfer. This allows for any abort checking to be performed
		 *  in the user code - to continue the transfer, call the function again with identical parameters
		 *  and it will resume until the BytesProcessed value reaches the total transfer length.
		 *
		 *  <b>Single Stream Transfer Example:</b>
		 *  \code
		 *  uint8_t ErrorCode;
		 *
		 *  if ((ErrorCode = Endpoint_Null_Stream(512, NULL)) != ENDPOINT_RWSTREAM_NoError)
		 *  {
		 *       // Stream failed to complete - check ErrorCode here
		 *  }
		 *  \endcode
		 *
		 *  <b>Partial Stream Transfers Example:</b>
		 *  \code
		 *  uint8_t  ErrorCode;
		 *  uint16_t BytesProcessed;
		 *
		 *  BytesProcessed = 0;
		 *  while ((ErrorCode = Endpoint_Null_Stream(512, &BytesProcessed)) == ENDPOINT_RWSTREAM_IncompleteTransfer)
		 *  {
		 *      // Stream not yet complete - do other actions here, abort if required
		 *  }
		 *
		 *  if (ErrorCode != ENDPOINT_RWSTREAM_NoError)
		 *  {
		 *      // Stream failed to complete - check ErrorCode here
		 *  }
		 *  \endcode
		 *
		 *  @note This routine should not be used on CONTROL type endpoints.
		 *
		 *  @param     corenum         ID Number of USB Core to be processed.
		 *  @param     Length          Number of zero bytes to send via the currently selected endpoint.
		 *  @param     BytesProcessed  Pointer to a location where the total number of bytes processed in the current
		 *                             transaction should be updated, \c NULL if the entire stream should be read at once.
		 *
		 * @param  Length :         Number of zero bytes to send via the currently selected endpoint
		 * @param  BytesProcessed : Pointer to a location where the total number of bytes processed in the current
		 *                          transaction should be updated, NULL if the entire stream should be read at once
		 * @return A value from the @ref Endpoint_Stream_RW_ErrorCodes_t enum
		 */
		uint8_t Endpoint_Null_Stream(uint8_t corenum,
									 uint16_t Length,
									 uint16_t *const BytesProcessed);

		//@}

		/** \name Stream functions for RAM source/destination data */
		//@{
				
		/** @brief Writes the given number of bytes to the endpoint from the given buffer in little endian,
		 *  sending full packets to the host as needed. The last packet filled is not automatically sent;
		 *  the user is responsible for manually sending the last written packet to the host via the
		 *  @ref Endpoint_ClearIN() macro.
		 *
		 *  If the BytesProcessed parameter is \c NULL, the entire stream transfer is attempted at once,
		 *  failing or succeeding as a single unit. If the BytesProcessed parameter points to a valid
		 *  storage location, the transfer will instead be performed as a series of chunks. Each time
		 *  the endpoint bank becomes full while there is still data to process (and after the current
		 *  packet transmission has been initiated) the BytesProcessed location will be updated with the
		 *  total number of bytes processed in the stream, and the function will exit with an error code of
		 *  @ref ENDPOINT_RWSTREAM_IncompleteTransfer. This allows for any abort checking to be performed
		 *  in the user code - to continue the transfer, call the function again with identical parameters
		 *  and it will resume until the BytesProcessed value reaches the total transfer length.
		 *
		 *  <b>Single Stream Transfer Example:</b>
		 *  \code
		 *  uint8_t DataStream[512];
		 *  uint8_t ErrorCode;
		 *
		 *  if ((ErrorCode = Endpoint_Write_Stream_LE(DataStream, sizeof(DataStream),
		 *                                            NULL)) != ENDPOINT_RWSTREAM_NoError)
		 *  {
		 *       // Stream failed to complete - check ErrorCode here
		 *  }
		 *  \endcode
		 *
		 *  <b>Partial Stream Transfers Example:</b>
		 *  \code
		 *  uint8_t  DataStream[512];
		 *  uint8_t  ErrorCode;
		 *  uint16_t BytesProcessed;
		 *
		 *  BytesProcessed = 0;
		 *  while ((ErrorCode = Endpoint_Write_Stream_LE(DataStream, sizeof(DataStream),
		 *                                               &BytesProcessed)) == ENDPOINT_RWSTREAM_IncompleteTransfer)
		 *  {
		 *      // Stream not yet complete - do other actions here, abort if required
		 *  }
		 *
		 *  if (ErrorCode != ENDPOINT_RWSTREAM_NoError)
		 *  {
		 *      // Stream failed to complete - check ErrorCode here
		 *  }
		 *  \endcode
		 *
		 *  @note This routine should not be used on CONTROL type endpoints.
		 *
		 *  @param     corenum         ID Number of USB Core to be processed.
		 *  @param     Buffer          Pointer to the source data buffer to read from.
		 *  @param     Length          Number of bytes to read for the currently selected endpoint into the buffer.
		 *  @param     BytesProcessed  Pointer to a location where the total number of bytes processed in the current
		 *                             transaction should be updated, \c NULL if the entire stream should be written at once.
		 *
		 * @param  Buffer :         Pointer to the source data buffer to read from
		 * @param  Length :         Number of bytes to read for the currently selected endpoint into the buffer
		 * @param  BytesProcessed : Pointer to a location where the total number of bytes processed in the current
		 *                          transaction should be updated, NULL if the entire stream should be written at once
		 * @return A value from the @ref Endpoint_Stream_RW_ErrorCodes_t enum
		 */
		uint8_t Endpoint_Write_Stream_LE(uint8_t corenum,
										 const void *const Buffer,
										 uint16_t Length,
										 uint16_t *const BytesProcessed) ATTR_NON_NULL_PTR_ARG(2);

		/**
		 * @brief  Writes the given number of bytes to the endpoint from the given buffer in big endian,
		 *  sending full packets to the host as needed. The last packet filled is not automatically sent;
		 *  the user is responsible for manually sending the last written packet to the host via the
		 *  @ref Endpoint_ClearIN() macro.
		 *
		 *  @note This routine should not be used on CONTROL type endpoints.
		 *
		 * @param     corenum       ID Number of USB Core to be processed.
		 * @param  Buffer :         Pointer to the source data buffer to read from
		 * @param  Length :         Number of bytes to read for the currently selected endpoint into the buffer
		 * @param  BytesProcessed : Pointer to a location where the total number of bytes processed in the current
		 *                          transaction should be updated, \c NULL if the entire stream should be written at once
		 * @return A value from the @ref Endpoint_Stream_RW_ErrorCodes_t enum
		 */
		uint8_t Endpoint_Write_Stream_BE(uint8_t corenum,
										 const void *const Buffer,
										 uint16_t Length,
										 uint16_t *const BytesProcessed) ATTR_NON_NULL_PTR_ARG(2);

		/**
		 * @brief  Reads the given number of bytes from the endpoint from the given buffer in little endian,
		 *  discarding fully read packets from the host as needed. The last packet is not automatically
		 *  discarded once the remaining bytes has been read; the user is responsible for manually
		 *  discarding the last packet from the host via the @ref Endpoint_ClearOUT() macro.
		 *
		 *  If the BytesProcessed parameter is \c NULL, the entire stream transfer is attempted at once,
		 *  failing or succeeding as a single unit. If the BytesProcessed parameter points to a valid
		 *  storage location, the transfer will instead be performed as a series of chunks. Each time
		 *  the endpoint bank becomes empty while there is still data to process (and after the current
		 *  packet has been acknowledged) the BytesProcessed location will be updated with the total number
		 *  of bytes processed in the stream, and the function will exit with an error code of
		 *  @ref ENDPOINT_RWSTREAM_IncompleteTransfer. This allows for any abort checking to be performed
		 *  in the user code - to continue the transfer, call the function again with identical parameters
		 *  and it will resume until the BytesProcessed value reaches the total transfer length.
		 *
		 *  <b>Single Stream Transfer Example:</b>
		 *  \code
		 *  uint8_t DataStream[512];
		 *  uint8_t ErrorCode;
		 *
		 *  if ((ErrorCode = Endpoint_Read_Stream_LE(DataStream, sizeof(DataStream),
		 *                                           NULL)) != ENDPOINT_RWSTREAM_NoError)
		 *  {
		 *       // Stream failed to complete - check ErrorCode here
		 *  }
		 *  \endcode
		 *
		 *  <b>Partial Stream Transfers Example:</b>
		 *  \code
		 *  uint8_t  DataStream[512];
		 *  uint8_t  ErrorCode;
		 *  uint16_t BytesProcessed;
		 *
		 *  BytesProcessed = 0;
		 *  while ((ErrorCode = Endpoint_Read_Stream_LE(DataStream, sizeof(DataStream),
		 *                                              &BytesProcessed)) == ENDPOINT_RWSTREAM_IncompleteTransfer)
		 *  {
		 *      // Stream not yet complete - do other actions here, abort if required
		 *  }
		 *
		 *  if (ErrorCode != ENDPOINT_RWSTREAM_NoError)
		 *  {
		 *      // Stream failed to complete - check ErrorCode here
		 *  }
		 *  \endcode
		 *
		 *  @note This routine should not be used on CONTROL type endpoints.
		 *
		 *  @param     corenum         ID Number of USB Core to be processed.
		 *  \param[out] Buffer          Pointer to the destination data buffer to write to.
		 *  @param      Length          Number of bytes to send via the currently selected endpoint.
		 *  @param      BytesProcessed  Pointer to a location where the total number of bytes processed in the current
		 *                              transaction should be updated, \c NULL if the entire stream should be read at once.
		 *
		 * @param  Buffer :         Pointer to the destination data buffer to write to
		 * @param  Length :         Number of bytes to send via the currently selected endpoint
		 * @param  BytesProcessed : Pointer to a location where the total number of bytes processed in the current
		 *                          transaction should be updated, NULL if the entire stream should be written at once
		 * @return A value from the @ref Endpoint_Stream_RW_ErrorCodes_t enum
		 */
		uint8_t Endpoint_Read_Stream_LE(uint8_t corenum,
										void *const Buffer,
										uint16_t Length,
										uint16_t *const BytesProcessed) ATTR_NON_NULL_PTR_ARG(2);

		/**
		 * @brief  Reads the given number of bytes from the endpoint from the given buffer in big endian,
		 *  discarding fully read packets from the host as needed. The last packet is not automatically
		 *  discarded once the remaining bytes has been read; the user is responsible for manually
		 *  discarding the last packet from the host via the @ref Endpoint_ClearOUT() macro.
		 *
		 *  @note This routine should not be used on CONTROL type endpoints.
		 *
		 * @param  Buffer :         Pointer to the destination data buffer to write to
		 * @param  Length :         Number of bytes to send via the currently selected endpoint
		 * @param  BytesProcessed : Pointer to a location where the total number of bytes processed in the current
		 *                          transaction should be updated, \c NULL if the entire stream should be read at once
		 * @return A value from the @ref Endpoint_Stream_RW_ErrorCodes_t enum
		 */
		uint8_t Endpoint_Read_Stream_BE(void *const Buffer,
										uint16_t Length,
										uint16_t *const BytesProcessed) ATTR_NON_NULL_PTR_ARG(1);

		/**
		 * @brief  Writes the given number of bytes to the CONTROL type endpoint from the given buffer in little endian,
		 *  sending full packets to the host as needed. The host OUT acknowledgement is not automatically cleared
		 *  in both failure and success states; the user is responsible for manually clearing the setup OUT to
		 *  finalize the transfer via the @ref Endpoint_ClearOUT() macro.
		 *
		 *  @note This function automatically clears the control transfer's status stage. Do not manually attempt
		 *        to clear the status stage when using this routine in a control transaction.
		 *        \n\n
		 *
		 *  @note This routine should only be used on CONTROL type endpoints.
		 *
		 *  \warning Unlike the standard stream read/write commands, the control stream commands cannot be chained
		 *           together; i.e. the entire stream data must be read or written at the one time.
		 *
		 * @param  corenum          ID Number of USB Core to be processed.
		 * @param  Buffer :         Pointer to the source data buffer to read from
		 * @param  Length :         Number of bytes to read for the currently selected endpoint into the buffer
		 * @return A value from the @ref Endpoint_ControlStream_RW_ErrorCodes_t enum
		 */
		uint8_t Endpoint_Write_Control_Stream_LE(uint8_t corenum, const void *const Buffer,
												 uint16_t Length) ATTR_NON_NULL_PTR_ARG(2);

		/**
		 * @brief  Writes the given number of bytes to the CONTROL type endpoint from the given buffer in big endian,
		 *  sending full packets to the host as needed. The host OUT acknowledgement is not automatically cleared
		 *  in both failure and success states; the user is responsible for manually clearing the setup OUT to
		 *  finalize the transfer via the @ref Endpoint_ClearOUT() macro.
		 *
		 *  @note This function automatically clears the control transfer's status stage. Do not manually attempt
		 *        to clear the status stage when using this routine in a control transaction.
		 *        \n\n
		 *
		 *  @note This routine should only be used on CONTROL type endpoints.
		 *
		 *  \warning Unlike the standard stream read/write commands, the control stream commands cannot be chained
		 *           together; i.e. the entire stream data must be read or written at the one time.
		 *
		 * @param  Buffer :         Pointer to the source data buffer to read from
		 * @param  Length :         Number of bytes to read for the currently selected endpoint into the buffer
		 * @return A value from the @ref Endpoint_ControlStream_RW_ErrorCodes_t enum
		 */
		uint8_t Endpoint_Write_Control_Stream_BE(const void *const Buffer,
												 uint16_t Length) ATTR_NON_NULL_PTR_ARG(1);

		/**
		 * @brief  Reads the given number of bytes from the CONTROL endpoint from the given buffer in little endian,
		 *  discarding fully read packets from the host as needed. The device IN acknowledgement is not
		 *  automatically sent after success or failure states; the user is responsible for manually sending the
		 *  setup IN to finalize the transfer via the @ref Endpoint_ClearIN() macro.
		 *
		 *  @note This function automatically clears the control transfer's status stage. Do not manually attempt
		 *        to clear the status stage when using this routine in a control transaction.
		 *        \n\n
		 *
		 *  @note This routine should only be used on CONTROL type endpoints.
		 *
		 *  \warning Unlike the standard stream read/write commands, the control stream commands cannot be chained
		 *           together; i.e. the entire stream data must be read or written at the one time.
		 *
		 * @param  corenum          ID Number of USB Core to be processed.
		 * @param  Buffer :         Pointer to the destination data buffer to write to
		 * @param  Length :         Number of bytes to send via the currently selected endpoint
		 * @return A value from the @ref Endpoint_ControlStream_RW_ErrorCodes_t enum
		 */
		uint8_t Endpoint_Read_Control_Stream_LE(uint8_t corenum, void *const Buffer,
												uint16_t Length) ATTR_NON_NULL_PTR_ARG(2);

		/**
		 * @brief  Reads the given number of bytes from the CONTROL endpoint from the given buffer in big endian,
		 *  discarding fully read packets from the host as needed. The device IN acknowledgement is not
		 *  automatically sent after success or failure states; the user is responsible for manually sending the
		 *  setup IN to finalize the transfer via the @ref Endpoint_ClearIN() macro.
		 *
		 *  @note This function automatically clears the control transfer's status stage. Do not manually attempt
		 *        to clear the status stage when using this routine in a control transaction.
		 *        \n\n
		 *
		 *  @note This routine should only be used on CONTROL type endpoints.
		 *
		 *  \warning Unlike the standard stream read/write commands, the control stream commands cannot be chained
		 *           together; i.e. the entire stream data must be read or written at the one time.
		 *
		 * @param  Buffer :         Pointer to the destination data buffer to write to
		 * @param  Length :         Number of bytes to send via the currently selected endpoint
		 * @return A value from the @ref Endpoint_ControlStream_RW_ErrorCodes_t enum
		 */
		uint8_t Endpoint_Read_Control_Stream_BE(void *const Buffer,
												uint16_t Length) ATTR_NON_NULL_PTR_ARG(1);
		//@}

		/** \name Stream functions for EEPROM source/destination data */
		//@{
		/**
		 * @brief  Endpoint Write EEPROM Stream Little Endian
		 * @param  Buffer :         Pointer to the source data buffer to read from
		 * @param  Length :         Number of bytes to read for the currently selected endpoint into the buffer
		 * @param  BytesProcessed : Pointer to a location where the total number of bytes processed in the current
		 *                          transaction should be updated, \c NULL if the entire stream should be written at once
		 * @return A value from the @ref Endpoint_Stream_RW_ErrorCodes_t enum
		 */
		uint8_t Endpoint_Write_EStream_LE(const void *const Buffer,
										  uint16_t Length,
										  uint16_t *const BytesProcessed) ATTR_NON_NULL_PTR_ARG(1);

		/**
		 * @brief  Endpoint Write EEPROM Stream Big Endian
		 * @param  Buffer :         Pointer to the source data buffer to read from
		 * @param  Length :         Number of bytes to read for the currently selected endpoint into the buffer
		 * @param  BytesProcessed : Pointer to a location where the total number of bytes processed in the current
		 *                          transaction should be updated, \c NULL if the entire stream should be written at once
		 * @return A value from the @ref Endpoint_Stream_RW_ErrorCodes_t enum
		 */
		uint8_t Endpoint_Write_EStream_BE(const void *const Buffer,
										  uint16_t Length,
										  uint16_t *const BytesProcessed) ATTR_NON_NULL_PTR_ARG(1);

		/**
		 * @brief  Endpoint Read EEPROM Stream Little Endian
		 * @param  Buffer :         Pointer to the destination data buffer to write to, located in EEPROM memory space
		 * @param  Length :         Number of bytes to send via the currently selected endpoint
		 * @param  BytesProcessed : Pointer to a location where the total number of bytes processed in the current
		 *                          transaction should be updated, \c NULL if the entire stream should be read at once
		 * @return A value from the @ref Endpoint_Stream_RW_ErrorCodes_t enum
		 */
		uint8_t Endpoint_Read_EStream_LE(void *const Buffer,
										 uint16_t Length,
										 uint16_t *const BytesProcessed) ATTR_NON_NULL_PTR_ARG(1);

		/**
		 * @brief  Endpoint Read EEPROM Stream Big Endian
		 * @param  Buffer :         Pointer to the destination data buffer to write to, located in EEPROM memory space
		 * @param  Length :         Number of bytes to send via the currently selected endpoint
		 * @param  BytesProcessed : Pointer to a location where the total number of bytes processed in the current
		 *                          transaction should be updated, \c NULL if the entire stream should be read at once
		 * @return A value from the @ref Endpoint_Stream_RW_ErrorCodes_t enum
		 */
		uint8_t Endpoint_Read_EStream_BE(void *const Buffer,
										 uint16_t Length,
										 uint16_t *const BytesProcessed) ATTR_NON_NULL_PTR_ARG(1);

		/**
		 * @brief  Endpoint Write Control EEPROM Stream Little Endian
		 *
		 *  @note This function automatically clears the control transfer's status stage. Do not manually attempt
		 *        to clear the status stage when using this routine in a control transaction.
		 *        \n\n
		 *
		 *  @note This routine should only be used on CONTROL type endpoints.
		 *        \n\n
		 *
		 *  \warning Unlike the standard stream read/write commands, the control stream commands cannot be chained
		 *           together; i.e. the entire stream data must be read or written at the one time.
		 *
		 * @param  Buffer :         Pointer to the source data buffer to read from
		 * @param  Length :         Number of bytes to read for the currently selected endpoint into the buffer
		 * @return A value from the @ref Endpoint_ControlStream_RW_ErrorCodes_t enum
		 */
		uint8_t Endpoint_Write_Control_EStream_LE(const void *const Buffer,
												  uint16_t Length) ATTR_NON_NULL_PTR_ARG(1);

		/**
		 * @brief  Endpoint Write Control EEPROM Stream Big Endian
		 *
		 *  @note This function automatically clears the control transfer's status stage. Do not manually attempt
		 *        to clear the status stage when using this routine in a control transaction.
		 *        \n\n
		 *
		 *  @note This routine should only be used on CONTROL type endpoints.
		 *        \n\n
		 *
		 *  \warning Unlike the standard stream read/write commands, the control stream commands cannot be chained
		 *           together; i.e. the entire stream data must be read or written at the one time.
		 *
		 * @param  Buffer :         Pointer to the source data buffer to read from
		 * @param  Length :         Number of bytes to read for the currently selected endpoint into the buffer
		 * @return A value from the @ref Endpoint_ControlStream_RW_ErrorCodes_t enum
		 */
		uint8_t Endpoint_Write_Control_EStream_BE(const void *const Buffer,
												  uint16_t Length) ATTR_NON_NULL_PTR_ARG(1);

		/**
		 * @brief  Endpoint Read Control EEPROM Stream Little Endian
		 *
		 *  @note This function automatically clears the control transfer's status stage. Do not manually attempt
		 *        to clear the status stage when using this routine in a control transaction.
		 *        \n\n
		 *
		 *  @note This routine should only be used on CONTROL type endpoints.
		 *        \n\n
		 *
		 *  \warning Unlike the standard stream read/write commands, the control stream commands cannot be chained
		 *           together; i.e. the entire stream data must be read or written at the one time.
		 *
		 * @param  Buffer :         Pointer to the destination data buffer to write to
		 * @param  Length :         Number of bytes to send via the currently selected endpoint
		 * @return A value from the @ref Endpoint_ControlStream_RW_ErrorCodes_t enum
		 */
		uint8_t Endpoint_Read_Control_EStream_LE(void *const Buffer,
												 uint16_t Length) ATTR_NON_NULL_PTR_ARG(1);

		/**
		 * @brief  Endpoint Read Control EEPROM Stream Big Endian
		 *
		 *  @note This function automatically clears the control transfer's status stage. Do not manually attempt
		 *        to clear the status stage when using this routine in a control transaction.
		 *        \n\n
		 *
		 *  @note This routine should only be used on CONTROL type endpoints.
		 *        \n\n
		 *
		 *  \warning Unlike the standard stream read/write commands, the control stream commands cannot be chained
		 *           together; i.e. the entire stream data must be read or written at the one time.
		 *
		 * @param  Buffer :         Pointer to the destination data buffer to write to
		 * @param  Length :         Number of bytes to send via the currently selected endpoint
		 * @return A value from the @ref Endpoint_ControlStream_RW_ErrorCodes_t enum
		 */
		uint8_t Endpoint_Read_Control_EStream_BE(void *const Buffer,
												 uint16_t Length) ATTR_NON_NULL_PTR_ARG(1);
					//@}
		/**
		 * @brief  Endpoint Write PROGMEM Stream Little Endian
		//@{
		 * @param  Buffer :         Pointer to the source data buffer to read from
		 * @param  Length :         Number of bytes to read for the currently selected endpoint into the buffer
		 * @param  BytesProcessed : Pointer to a location where the total number of bytes processed in the current
		 *                          transaction should be updated, NULL if the entire stream should be written at once.
		 * @return A value from the @ref Endpoint_Stream_RW_ErrorCodes_t enum
		 */
		uint8_t Endpoint_Write_PStream_LE(const void *const Buffer,
										  uint16_t Length,
										  uint16_t *const BytesProcessed) ATTR_NON_NULL_PTR_ARG(1);

		/**
		 * @brief  Endpoint Write PROGMEM Stream Big Endian
		 * @param  Buffer :         Pointer to the source data buffer to read from
		 * @param  Length :         Number of bytes to read for the currently selected endpoint into the buffer
		 * @param  BytesProcessed : Pointer to a location where the total number of bytes processed in the current
		 *                          transaction should be updated, \c NULL if the entire stream should be written at once.
		 * @return A value from the @ref Endpoint_Stream_RW_ErrorCodes_t enum
		 */
		uint8_t Endpoint_Write_PStream_BE(const void *const Buffer,
										  uint16_t Length,
										  uint16_t *const BytesProcessed) ATTR_NON_NULL_PTR_ARG(1);

		/**
		 * @brief  Endpoint Write Control PROGMEM Stream Little Endian
		 * @param  Buffer :         Pointer to the source data buffer to read from
		 * @param  Length :         Number of bytes to read for the currently selected endpoint into the buffer
		 * @return A value from the @ref Endpoint_ControlStream_RW_ErrorCodes_t enum
		 */
		uint8_t Endpoint_Write_Control_PStream_LE(const void *const Buffer,
												  uint16_t Length) ATTR_NON_NULL_PTR_ARG(1);

		/**
		 * @brief  Endpoint Write Control PROGMEM Stream Big Endian
		 * @param  Buffer :         Pointer to the source data buffer to read from
		 * @param  Length :         Number of bytes to read for the currently selected endpoint into the buffer
		 * @return A value from the @ref Endpoint_ControlStream_RW_ErrorCodes_t enum
		 */
		uint8_t Endpoint_Write_Control_PStream_BE(const void *const Buffer,
												  uint16_t Length) ATTR_NON_NULL_PTR_ARG(1);
		//@}

	/* Disable C linkage for C++ Compilers: */
		#if defined(__cplusplus)
			}
		#endif

#endif

/** @} */

