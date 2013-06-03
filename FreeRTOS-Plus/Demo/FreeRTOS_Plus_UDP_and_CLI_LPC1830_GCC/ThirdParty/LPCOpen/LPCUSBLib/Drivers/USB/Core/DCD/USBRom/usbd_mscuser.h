/*
 * @brief Definition of functions exported by ROM based MSC function driver
 *
 * @note
 * Copyright(C) NXP Semiconductors, 2012
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

#include "error.h"
#include "usbd.h"
#include "usbd_msc.h"
#include "usbd_core.h"

#ifndef __MSCUSER_H__
#define __MSCUSER_H__


/** @ingroup Group_USBD_Class
 *  @defgroup USBD_MSC Mass Storage Class (MSC) Function Driver
 *  @section Sec_MSCModDescription Module Description
 *  MSC Class Function Driver module. This module contains an internal implementation of the USB MSC Class.
 *  User applications can use this class driver instead of implementing the MSC class manually
 *  via the low-level USBD_HW and USBD_Core APIs.
 *
 *  This module is designed to simplify the user code by exposing only the required interface needed to interface with
 *  Devices using the USB MSC Class.
 */

/** @brief Mass Storage class function driver initilization parameter data structure.
 *  @ingroup USBD_MSC
 *
 *  @details  This data structure is used to pass initialization parameters to the
 *  Mass Storage class function driver's init function.
 *
 */
typedef struct USBD_MSC_INIT_PARAM
{
  /* memory allocation params */
  uint32_t mem_base;  /**< Base memory location from where the stack can allocate
                      data and buffers. @note The memory address set in this field
                      should be accessible by USB DMA controller. Also this value
                      should be aligned on 4 byte boundary.
                      */
  uint32_t mem_size;  /**< The size of memory buffer which stack can use.
                      @note The \em mem_size should be greater than the size
                      returned by USBD_MSC_API::GetMemSize() routine.*/
  /* mass storage paramas */
  uint8_t*  InquiryStr; /**< Pointer to the 28 character string. This string is
                        sent in response to the SCSI Inquiry command. @note The data
                        pointed by the pointer should be of global scope.
                        */
  uint32_t  BlockCount; /**< Number of blocks present in the mass storage device */
  uint32_t  BlockSize; /**< Block size in number of bytes */
  uint32_t  MemorySize; /**< Memory size in number of bytes */
  /** Pointer to the interface descriptor within the descriptor
  * array (\em high_speed_desc) passed to Init() through @ref USB_CORE_DESCS_T
  * structure. The stack assumes both HS and FS use same BULK endpoints.
  */
  uint8_t* intf_desc;
  /* user defined functions */

 /**
  *  MSC Write callback function.
  *
  *  This function is provided by the application software. This function gets called
  *  when host sends a write command.
  *
  *  @param offset Destination start address.
  *  @param src  Pointer to a pointer to the source of data. Pointer-to-pointer
  *                       is used to implement zero-copy buffers.
  *  @param length  Number of bytes to be written.
  *  @return Nothing.
  *
  */
  void (*MSC_Write)( uint32_t offset, uint8_t** src, uint32_t length);
 /**
  *  MSC Read callback function.
  *
  *  This function is provided by the application software. This function gets called
  *  when host sends a read command.
  *
  *  @param offset Source start address.
  *  @param dst  Pointer to a pointer to the source of data. The MSC function drivers
  *         implemented in stack are written with zero-copy model. Meaning the stack doesn't make an
  *          extra copy of buffer before writing/reading data from USB hardware FIFO. Hence the
  *          parameter is pointer to a pointer containing address buffer (<em>uint8_t** dst</em>).
  *          So that the user application can update the buffer pointer instead of copying data to
  *          address pointed by the parameter. /note The updated buffer address should be accessable
  *          by USB DMA master. If user doesn't want to use zero-copy model, then the user should copy
  *          data to the address pointed by the passed buffer pointer parameter and shouldn't change
  *          the address value.
  *  @param length  Number of bytes to be read.
  *  @return Nothing.
  *
  */
  void (*MSC_Read)( uint32_t offset, uint8_t** dst, uint32_t length);
 /**
  *  MSC Verify callback function.
  *
  *  This function is provided by the application software. This function gets called
  *  when host sends a verify command. The callback function should compare the buffer
  *  with the destination memory at the requested offset and
  *
  *  @param offset Destination start address.
  *  @param buf  Buffer containing the data sent by the host.
  *  @param length  Number of bytes to verify.
  *  @return Returns @ref ErrorCode_t type to indicate success or error condition.
  *          @retval LPC_OK If data in the buffer matches the data at destination
  *          @retval ERR_FAILED  Atleast one byte is different.
  *
  */
  ErrorCode_t (*MSC_Verify)( uint32_t offset, uint8_t buf[], uint32_t length);
  /**
  *  Optional callback function to optimize MSC_Write buffer transfer.
  *
  *  This function is provided by the application software. This function gets called
  *  when host sends SCSI_WRITE10/SCSI_WRITE12 command. The callback function should
  *  update the \em buff_adr pointer so that the stack transfers the data directly
  *  to the target buffer. /note The updated buffer address should be accessable
  *  by USB DMA master. If user doesn't want to use zero-copy model, then the user
  *  should not update the buffer pointer.
  *
  *  @param offset Destination start address.
  *  \param[in,out] buf  Buffer containing the data sent by the host.
  *  @param length  Number of bytes to write.
  *  @return Nothing.
  *
  */
  void (*MSC_GetWriteBuf)( uint32_t offset, uint8_t** buff_adr, uint32_t length);

  /**
  *  Optional user overridable function to replace the default MSC class handler.
  *
  *  The application software could override the default EP0 class handler with their
  *  own by providing the handler function address as this data member of the parameter
  *  structure. Application which like the default handler should set this data member
  *  to zero before calling the USBD_MSC_API::Init().
  *  \n
  *  @note
  *
  *  @param hUsb Handle to the USB device stack.
  *  @param data Pointer to the data which will be passed when callback function is called by the stack.
  *  @param event  Type of endpoint event. See @ref USBD_EVENT_T for more details.
  *  @return The call back should returns @ref ErrorCode_t type to indicate success or error condition.
  *          @retval LPC_OK On success.
  *          @retval ERR_USBD_UNHANDLED  Event is not handled hence pass the event to next in line.
  *          @retval ERR_USBD_xxx  For other error conditions.
  *
  */
  ErrorCode_t (*MSC_Ep0_Hdlr) (USBD_HANDLE_T hUsb, void* data, uint32_t event);

} USBD_MSC_INIT_PARAM_T;

/** @brief MSC class API functions structure.
 *  @ingroup USBD_MSC
 *
 *  This module exposes functions which interact directly with USB device controller hardware.
 *
 */
typedef struct USBD_MSC_API
{
  /** @fn uint32_t GetMemSize(USBD_MSC_INIT_PARAM_T* param)
   *  Function to determine the memory required by the MSC function driver module.
   *
   *  This function is called by application layer before calling pUsbApi->msc->Init(), to allocate memory used
   *  by MSC function driver module. The application should allocate the memory which is accessible by USB
   *  controller/DMA controller.
   *  @note Some memory areas are not accessible by all bus masters.
   *
   *  @param param Structure containing HID function driver module initialization parameters.
   *  @return Returns the required memory size in bytes.
   */
  uint32_t (*GetMemSize)(USBD_MSC_INIT_PARAM_T* param);

  /** @fn ErrorCode_t init(USBD_HANDLE_T hUsb, USBD_MSC_INIT_PARAM_T* param)
   *  Function to initialize MSC function driver module.
   *
   *  This fuction is called by application layer to initialize MSC function driver module.
   *
   *  @param hUsb Handle to the USB device stack.
   *  @param param Structure containing HID function driver module initialization parameters.
   *  @return Returns @ref ErrorCode_t type to indicate success or error condition.
   *          @retval LPC_OK On success
   *          @retval ERR_USBD_BAD_MEM_BUF  Memory buffer passed is not 4-byte
   *              aligned or smaller than required.
   *          @retval ERR_API_INVALID_PARAM2 Either MSC_Write() or MSC_Read() or
   *              MSC_Verify() callbacks are not defined.
   *          @retval ERR_USBD_BAD_INTF_DESC  Wrong interface descriptor is passed.
   *          @retval ERR_USBD_BAD_EP_DESC  Wrong endpoint descriptor is passed.
   */
  ErrorCode_t (*init)(USBD_HANDLE_T hUsb, USBD_MSC_INIT_PARAM_T* param);

} USBD_MSC_API_T;

/*-----------------------------------------------------------------------------
 *  Private functions & structures prototypes
 *-----------------------------------------------------------------------------*/
/** @cond  ADVANCED_API */

typedef struct _MSC_CTRL_T
{
  /* If it's a USB HS, the max packet is 512, if it's USB FS,
  the max packet is 64. Use 512 for both HS and FS. */
  /*ALIGNED(4)*/ uint8_t  BulkBuf[512]; /* Bulk In/Out Buffer */
  /*ALIGNED(4)*/MSC_CBW CBW;                   /* Command Block Wrapper */
  /*ALIGNED(4)*/MSC_CSW CSW;                   /* Command Status Wrapper */

  USB_CORE_CTRL_T*  pUsbCtrl;

  uint32_t Offset;                  /* R/W Offset */
  uint32_t Length;                  /* R/W Length */
  uint32_t BulkLen;                 /* Bulk In/Out Length */
  uint8_t* rx_buf;

  uint8_t BulkStage;               /* Bulk Stage */
  uint8_t if_num;                  /* interface number */
  uint8_t epin_num;                /* BULK IN endpoint number */
  uint8_t epout_num;               /* BULK OUT endpoint number */
  uint32_t MemOK;                  /* Memory OK */

  uint8_t*  InquiryStr;
  uint32_t  BlockCount;
  uint32_t  BlockSize;
  uint32_t  MemorySize;
  /* user defined functions */
  void (*MSC_Write)( uint32_t offset, uint8_t** src, uint32_t length);
  void (*MSC_Read)( uint32_t offset, uint8_t** dst, uint32_t length);
  ErrorCode_t (*MSC_Verify)( uint32_t offset, uint8_t src[], uint32_t length);
  /* optional call back for MSC_Write optimization */
  void (*MSC_GetWriteBuf)( uint32_t offset, uint8_t** buff_adr, uint32_t length);


}USB_MSC_CTRL_T;


/** @endcond */


#endif  /* __MSCUSER_H__ */
