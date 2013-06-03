/*
 * @brief Definition of functions exported by ROM based CDC function driver
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
#include "usbd_cdc.h"

#ifndef __CDCUSER_H__
#define __CDCUSER_H__


/** @ingroup Group_USBD_Class
 *  @defgroup USBD_CDC Communication Device Class (CDC) Function Driver
 *  @section Sec_CDCModDescription Module Description
 *  CDC Class Function Driver module. This module contains an internal implementation of the USB CDC Class.
 *  User applications can use this class driver instead of implementing the CDC class manually
 *  via the low-level USBD_HW and USBD_Core APIs.
 *
 *  This module is designed to simplify the user code by exposing only the required interface needed to interface with
 *  Devices using the USB CDC Class.
 */

/*----------------------------------------------------------------------------
  We need a buffer for incomming data on USB port because USB receives
  much faster than  UART transmits
 *---------------------------------------------------------------------------*/
/* Buffer masks */
#define CDC_BUF_SIZE               (128)               /* Output buffer in bytes (power 2) */
                                                       /* large enough for file transfer */
#define CDC_BUF_MASK               (CDC_BUF_SIZE-1ul)

/** @brief Communication Device Class function driver initilization parameter data structure.
 *  @ingroup USBD_CDC
 *
 *  @details  This data structure is used to pass initialization parameters to the 
 *  Communication Device Class function driver's init function.
 *
 */
typedef struct USBD_CDC_INIT_PARAM
{
  /* memory allocation params */
  uint32_t mem_base;  /**< Base memory location from where the stack can allocate
                      data and buffers. @note The memory address set in this field
                      should be accessible by USB DMA controller. Also this value
                      should be aligned on 4 byte boundary.
                      */
  uint32_t mem_size;  /**< The size of memory buffer which stack can use. 
                      @note The \em mem_size should be greater than the size 
                      returned by USBD_CDC_API::GetMemSize() routine.*/
  /** Pointer to the control interface descriptor within the descriptor
  * array (\em high_speed_desc) passed to Init() through @ref USB_CORE_DESCS_T 
  * structure. The stack assumes both HS and FS use same BULK endpoints. 
  */
  uint8_t* cif_intf_desc;
  /** Pointer to the data interface descriptor within the descriptor
  * array (\em high_speed_desc) passed to Init() through @ref USB_CORE_DESCS_T 
  * structure. The stack assumes both HS and FS use same BULK endpoints. 
  */
  uint8_t* dif_intf_desc;

  /* user defined functions */

  /* required functions */
  /** 
  *  Communication Interface Class specific get request callback function.
  *
  *  This function is provided by the application software. This function gets called 
  *  when host sends CIC management element get requests. The setup packet data (\em pSetup)
  *  is passed to the callback so that application can extract the CIC request type
  *  and other associated data. By default the stack will ssign \em pBuffer pointer
  *  to \em EP0Buff allocated at init. The application code can directly write data 
  *  into this buffer as long as data is less than 64 byte. If more data has to be sent 
  *  then application code should update \em pBuffer pointer and length accordingly.
  *   
  *  
  *  @param hCdc Handle to CDC function driver. 
  *  @param pSetup Pointer to setup packet recived from host. 
  *  @param pBuffer  Pointer to a pointer of data buffer containing request data. 
  *                       Pointer-to-pointer is used to implement zero-copy buffers.
  *  @param length  Amount of data to be sent back to host.
  *  @return The call back should returns @ref ErrorCode_t type to indicate success or error condition.
  *          @retval LPC_OK On success.
  *          @retval ERR_USBD_UNHANDLED  Event is not handled hence pass the event to next in line. 
  *          @retval ERR_USBD_xxx  For other error conditions. 
  *                                             
  */
  ErrorCode_t (*CIC_GetRequest)( USBD_HANDLE_T hHid, USB_SETUP_PACKET* pSetup, uint8_t** pBuffer, uint16_t* length); 
  
  /** 
  *  Communication Interface Class specific set request callback function.
  *
  *  This function is provided by the application software. This function gets called 
  *  when host sends a CIC management element requests. The setup packet data (\em pSetup)
  *  is passed to the callback so that application can extract the CIC request type
  *  and other associated data. If a set request has data associated, then this callback
  *  is called twice. 
  *  (1) First when setup request is recived, at this time application code could update
  *  \em pBuffer pointer to point to the intended destination. The length param is set to 0
  *  so that application code knows this is first time. By default the stack will
  *  assign \em pBuffer pointer to \em EP0Buff allocated at init. Note, if data length is 
  *  greater than 64 bytes and application code doesn't update \em pBuffer pointer the 
  *  stack will send STALL condition to host.
  *  (2) Second when the data is recived from the host. This time the length param is set
  *  with number of data bytes recived.
  *  
  *  @param hCdc Handle to CDC function driver. 
  *  @param pSetup Pointer to setup packet recived from host. 
  *  @param pBuffer  Pointer to a pointer of data buffer containing request data. 
  *                       Pointer-to-pointer is used to implement zero-copy buffers.
  *  @param length  Amount of data copied to destination buffer.
  *  @return The call back should returns @ref ErrorCode_t type to indicate success or error condition.
  *          @retval LPC_OK On success.
  *          @retval ERR_USBD_UNHANDLED  Event is not handled hence pass the event to next in line. 
  *          @retval ERR_USBD_xxx  For other error conditions. 
  *                                             
  */
  ErrorCode_t (*CIC_SetRequest)( USBD_HANDLE_T hCdc, USB_SETUP_PACKET* pSetup, uint8_t** pBuffer, uint16_t length);

  /** 
  *  Communication Device Class specific BULK IN endpoint handler.
  *
  *  The application software should provide the BULK IN endpoint handler.
  *  Applications should transfer data depending on the communication protocol type set in descriptors. 
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
  ErrorCode_t (*CDC_BulkIN_Hdlr) (USBD_HANDLE_T hUsb, void* data, uint32_t event);

  /** 
  *  Communication Device Class specific BULK OUT endpoint handler.
  *
  *  The application software should provide the BULK OUT endpoint handler.
  *  Applications should transfer data depending on the communication protocol type set in descriptors. 
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
  ErrorCode_t (*CDC_BulkOUT_Hdlr) (USBD_HANDLE_T hUsb, void* data, uint32_t event);

  ErrorCode_t (*SendEncpsCmd) (USBD_HANDLE_T hCDC, uint8_t* buffer, uint16_t len);
  ErrorCode_t (*GetEncpsResp) (USBD_HANDLE_T hCDC, uint8_t** buffer, uint16_t* len);
  ErrorCode_t (*SetCommFeature) (USBD_HANDLE_T hCDC, uint16_t feature, uint8_t* buffer, uint16_t len);
  ErrorCode_t (*GetCommFeature) (USBD_HANDLE_T hCDC, uint16_t feature, uint8_t** pBuffer, uint16_t* len);
  ErrorCode_t (*ClrCommFeature) (USBD_HANDLE_T hCDC, uint16_t feature);
  ErrorCode_t (*SetCtrlLineState) (USBD_HANDLE_T hCDC, uint16_t state);
  ErrorCode_t (*SendBreak) (USBD_HANDLE_T hCDC, uint16_t mstime);
  ErrorCode_t (*SetLineCode) (USBD_HANDLE_T hCDC, CDC_LINE_CODING* line_coding);

  /** 
  *  Optional Communication Device Class specific INTERRUPT IN endpoint handler.
  *
  *  The application software should provide the INT IN endpoint handler.
  *  Applications should transfer data depending on the communication protocol type set in descriptors. 
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
  ErrorCode_t (*CDC_InterruptEP_Hdlr) (USBD_HANDLE_T hUsb, void* data, uint32_t event);

  /** 
  *  Optional user overridable function to replace the default CDC class handler.
  *
  *  The application software could override the default EP0 class handler with their
  *  own by providing the handler function address as this data member of the parameter
  *  structure. Application which like the default handler should set this data member
  *  to zero before calling the USBD_CDC_API::Init().
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
  ErrorCode_t (*CDC_Ep0_Hdlr) (USBD_HANDLE_T hUsb, void* data, uint32_t event);

} USBD_CDC_INIT_PARAM_T;

/** @brief CDC class API functions structure.
 *  @ingroup USBD_CDC
 *
 *  This module exposes functions which interact directly with USB device controller hardware.
 *
 */
typedef struct USBD_CDC_API
{
  /** @fn uint32_t GetMemSize(USBD_CDC_INIT_PARAM_T* param)
   *  Function to determine the memory required by the CDC function driver module.
   * 
   *  This function is called by application layer before calling pUsbApi->CDC->Init(), to allocate memory used 
   *  by CDC function driver module. The application should allocate the memory which is accessible by USB
   *  controller/DMA controller. 
   *  @note Some memory areas are not accessible by all bus masters.
   *
   *  @param param Structure containing CDC function driver module initialization parameters.
   *  @return Returns the required memory size in bytes.
   */
  uint32_t (*GetMemSize)(USBD_CDC_INIT_PARAM_T* param);
  
  /** @fn ErrorCode_t init(USBD_HANDLE_T hUsb, USBD_CDC_INIT_PARAM_T* param)
   *  Function to initialize CDC function driver module.
   * 
   *  This fuction is called by application layer to initialize CDC function driver module. 
   *
   *  @param hUsb Handle to the USB device stack. 
   *  @param param Structure containing CDC function driver module initialization parameters.
   *  @return Returns @ref ErrorCode_t type to indicate success or error condition.
   *          @retval LPC_OK On success
   *          @retval ERR_USBD_BAD_MEM_BUF  Memory buffer passed is not 4-byte 
   *              aligned or smaller than required. 
   *          @retval ERR_API_INVALID_PARAM2 Either CDC_Write() or CDC_Read() or
   *              CDC_Verify() callbacks are not defined. 
   *          @retval ERR_USBD_BAD_INTF_DESC  Wrong interface descriptor is passed. 
   *          @retval ERR_USBD_BAD_EP_DESC  Wrong endpoint descriptor is passed. 
   */
  ErrorCode_t (*init)(USBD_HANDLE_T hUsb, USBD_CDC_INIT_PARAM_T* param, USBD_HANDLE_T* phCDC);

  /** @fn ErrorCode_t SendNotification(USBD_HANDLE_T hCdc, uint8_t bNotification, uint16_t data)
   *  Function to initialize CDC function driver module.
   * 
   *  This fuction is called by application layer to initialize CDC function driver module. 
   *
   *  @param hUsb Handle to the USB device stack. 
   *  @param param Structure containing CDC function driver module initialization parameters.
   *  @return Returns @ref ErrorCode_t type to indicate success or error condition.
   *          @retval LPC_OK On success
   *          @retval ERR_USBD_BAD_MEM_BUF  Memory buffer passed is not 4-byte 
   *              aligned or smaller than required. 
   *          @retval ERR_API_INVALID_PARAM2 Either CDC_Write() or CDC_Read() or
   *              CDC_Verify() callbacks are not defined. 
   *          @retval ERR_USBD_BAD_INTF_DESC  Wrong interface descriptor is passed. 
   *          @retval ERR_USBD_BAD_EP_DESC  Wrong endpoint descriptor is passed. 
   */
  ErrorCode_t (*SendNotification)(USBD_HANDLE_T hCdc, uint8_t bNotification, uint16_t data);

} USBD_CDC_API_T;

/*-----------------------------------------------------------------------------
 *  Private functions & structures prototypes
 *-----------------------------------------------------------------------------*/
/** @cond  ADVANCED_API */

typedef struct _CDC_CTRL_T
{
  USB_CORE_CTRL_T*  pUsbCtrl;
  /* notification buffer */
  uint8_t notice_buf[12];
  CDC_LINE_CODING line_coding;
 
  uint8_t cif_num;                 /* control interface number */
  uint8_t dif_num;                 /* data interface number */
  uint8_t epin_num;                /* BULK IN endpoint number */
  uint8_t epout_num;               /* BULK OUT endpoint number */
  uint8_t epint_num;               /* Interrupt IN endpoint number */

  /* user defined functions */
  ErrorCode_t (*SendEncpsCmd) (USBD_HANDLE_T hCDC, uint8_t* buffer, uint16_t len);
  ErrorCode_t (*GetEncpsResp) (USBD_HANDLE_T hCDC, uint8_t** buffer, uint16_t* len);
  ErrorCode_t (*SetCommFeature) (USBD_HANDLE_T hCDC, uint16_t feature, uint8_t* buffer, uint16_t len);
  ErrorCode_t (*GetCommFeature) (USBD_HANDLE_T hCDC, uint16_t feature, uint8_t** pBuffer, uint16_t* len);
  ErrorCode_t (*ClrCommFeature) (USBD_HANDLE_T hCDC, uint16_t feature);
  ErrorCode_t (*SetCtrlLineState) (USBD_HANDLE_T hCDC, uint16_t state);
  ErrorCode_t (*SendBreak) (USBD_HANDLE_T hCDC, uint16_t state);
  ErrorCode_t (*SetLineCode) (USBD_HANDLE_T hCDC, CDC_LINE_CODING* line_coding);

  /* virtual functions */
  ErrorCode_t (*CIC_GetRequest)( USBD_HANDLE_T hCdc, USB_SETUP_PACKET* pSetup, uint8_t** pBuffer, uint16_t* length);
  ErrorCode_t (*CIC_SetRequest)( USBD_HANDLE_T hCdc, USB_SETUP_PACKET* pSetup, uint8_t** pBuffer, uint16_t length);

}USB_CDC_CTRL_T;


/** @endcond */

void UsbdCdc_IO_Buffer_Sync_Task(void);
void UsbdCdc_SendData(uint8_t* buffer, uint32_t cnt);
uint32_t UsbdCdc_RecvData(uint8_t* buffer, uint32_t len);


#endif  /* __CDCUSER_H__ */

