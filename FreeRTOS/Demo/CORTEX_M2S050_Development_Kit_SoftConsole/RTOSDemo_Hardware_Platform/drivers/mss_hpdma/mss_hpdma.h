/*******************************************************************************
 * (c) Copyright 2010-2013 Microsemi SoC Products Group.  All rights reserved.
 * 
 *  SmartFusion2 MSS HPDMA bare metal software driver public API.
 *
 * SVN $Revision: 5583 $
 * SVN $Date: 2013-04-04 12:29:18 +0100 (Thu, 04 Apr 2013) $
 */

/*=========================================================================*//**
  @mainpage SmartFusion2 MSS HPDMA Bare Metal Driver.

  @section intro_sec Introduction
  The SmartFusion2 Microcontroller Subsystem (MSS) includes a High Performance
  Direct Memory Access (HPDMA) controller which performs fast data transfer
  between any MSS memory connected to the AHB bus matrix and MSS DDR-Bridge
  memory. This software driver provides a set of functions for controlling the
  MSS HPDMA as part of a bare metal system where no operating system is
  available. The driver can be adapted for use as part of an operating system
  but the implementation of the adaptation layer between the driver and the
  operating system's driver model is outside the scope of the driver.
  
  @section hw_dependencies Hardware Flow Dependencies
  The configuration of all features of the MSS HPDMA is covered by this driver.
  There are no dependencies on the hardware flow when configuring the MSS HPDMA.
  The base address, register addresses and interrupt number assignment for the
  MSS HPDMA blocks are defined as constants in the SmartFusion2 CMSIS HAL. You
  must ensure that the latest SmartFusion2 CMSIS HAL is included in the project
  settings of the software tool chain used to build your project and that it is
  generated into your project.
  
  @section theory_op Theory of Operation
  The MSS HPDMA driver functions are grouped into the following categories:
    - Initialization of the MSS HPDMA driver and hardware
    - Data transfer control 
    - Data transfer status
    - Interrupt handling
    
  Initialization
  The MSS HPDMA driver is initialized through a call to the MSS_HPDMA_init()
  function. The MSS_HPDMA_init() function must be called before any other MSS
  HPDMA driver functions can be called.
  
  Data Transfer Control
  The driver provides the following functions to control HPDMA data transfers:
    - MSS_HPDMA_start()  – This function starts a HPDMA data transfer. You must
                           provide the source and destination addresses along
                           with transfer size and transfer direction.
    - MSS_HPDMA_pause()  – This function pauses the HPDMA transfer that is
                           currently in progress.
    - MSS_HPDMA_resume() – This function resumes a HPDMA transfer that was
                           previously paused.
    - MSS_HPDMA_abort()  – This function aborts the HPDMA transfer that is
                           currently in progress.
    
  Data Transfer Status
  The status of the HPDMA transfer initiated by the last call to
  MSS_HPDMA_start() can be retrieved using the MSS_HPDMA_get_transfer_status()
  function.
  
  Interrupt Handling
  The MSS_HPDMA_set_handler() function is used to register a handler function
  that will be called by the driver when the HPDMA transfer completes. You must
  create and register a transfer completion handler function to suit your
  application.

 *//*=========================================================================*/
#ifndef MSS_HPDMA_H_
#define MSS_HPDMA_H_

#ifdef __cplusplus
extern "C" {
#endif 

#include "../../CMSIS/m2sxxx.h"

/*-------------------------------------------------------------------------*//**
  The HPDMA_TO_DDR constant is used to specify the data transfer direction. It
  indicates a transfer from memory connected to the AHB bus matrix to MSS
  DDR-Bridge memory. It is used as a parameter by the MSS_HPDMA_start()
  function.
 */
#define HPDMA_TO_DDR        0u

/*-------------------------------------------------------------------------*//**
  The HPDMA_FROM_DDR constant is used to specify the data transfer direction. It
  indicates a transter from MSS DDR-Bridge memory to memory connected to the AHB
  bus matrix. It is used as a parameter by the MSS_HPDMA_start() function.
 */
#define HPDMA_FROM_DDR      1u

/*-------------------------------------------------------------------------*//**
  The hpdma_status_t type is used to communicate the status of the HPDMA
  transfer initiated by the most recent call to HPDMA_start(). It indicates if
  a transfer is still currently in progress or the outcome of the latest
  transfer. This type is returned by the MSS_HPDMA_get_transfer_status()
  function and used as parameter to handler functions registered with the MSS
  HPDMA driver by the application.
  
  - HPDMA_IN_PROGRESS       - A HPDMA transfer is taking place.
  - HPDMA_COMPLETED         - The most recent HPDMA transfer initiated by a call
                              to HPDMA_start() has completed successfully.
  - HPDMA_SOURCE_ERROR      - The most recent HPDMA transfer failed because of a
                              problem with the source address passed to
                              HPDMA_start().
  - HPDMA_DESTINATION_ERROR - The most recent HPDMA transfer failed because of a
                              problem with the destination address passed to
                              HPDMA_start().
  - HPDMA_WORD_ALIGN_ERROR  - The most recent HPDMA transfer failed because the
                              transfer size was not word aligned. This means
                              that the transfer size passed to HPDMA_start() was
                              not a multiple of four.
 */
typedef enum
{
    HPDMA_IN_PROGRESS,
    HPDMA_COMPLETED,
    HPDMA_SOURCE_ERROR,
    HPDMA_DESTINATION_ERROR,
    HPDMA_WORD_ALIGN_ERROR
} hpdma_status_t;

/*-------------------------------------------------------------------------*//**
  This type definition specifies the prototype of a function that can be
  registered with this driver as a HPDMA transfer completion handler function
  through a call to MSS_HPDMA_set_handler(). The HPDMA transfer completion
  handler will be called by the driver when a HPDMA transfer completes. The MSS
  HPDMA driver passes the outcome of the transfer to the completion handler in
  the form of a hpdma_status_t parameter indicating if the transfer was
  successful or the type of error that occurred during the transfer.
 */
typedef void (*mss_hpdma_handler_t)(hpdma_status_t status);

/*-------------------------------------------------------------------------*//**
  The MSS_HPDMA_init() function initializes the MSS HPDMA driver. It resets the
  HPDMA controller. It clears all pending HPDMA interrupts. It initializes
  internal data structures used by the MSS HPDMA driver. It disables interrupts
  related to HPDMA data transfers.

  @param
    This function has no parameters.

  @return
    This function does not return a value.
 */
void
MSS_HPDMA_init
(
    void
);

/*-------------------------------------------------------------------------*//**
  The MSS_HPDMA_start() function starts a HPDMA data transfer. Its parameters
  specify the source and destination addresses of the transfer as well as its
  size and direction. HPDMA data transfers always use DDR memory as the source
  or destination of the transfer. The HPDMA controller transfers data in 32-bit
  chunks located on 32-bit word aligned address boundaries.

  @param src_addr
    The parameter src_addr is the address of the data that will be transferred
    by the HPDMA. This address must be 32-bit word aligned. The memory location
    specified by this address must be located in DDR memory if the transfer_dir
    parameter is set to HPDM_FROM_DDR.

  @param dest_addr
    The parameter dest_addr is the address of the location at which the data
    will be transferred. This address must be 32-bit word aligned. The memory
    location specified by this address must be located in DDR memory if the
    transfer_dir parameter is set to HPDM_TO_DDR.

  @param transfer_size
    The parameter transfer_size specifies the size in bytes of the requested
    transfer. The value of transfer_size must be a multiple of four.

  @param transfer_dir
     The parameter transfer_dir is used for specifying the data transfer
     direction. Allowed values for transfer_dir are as follows:
        - HPDMA_TO_DDR
        - HPDMA_FROM_DDR

  @return
    This function does not return a value.
 */
void
MSS_HPDMA_start
(
    uint32_t src_addr,
    uint32_t dest_addr,
    uint32_t transfer_size,
    uint8_t transfer_dir
);

/*-------------------------------------------------------------------------*//**
  The MSS_HPDMA_pause() function pauses the current HPDMA transfer. The HPDMA
  transfer can be resumed later  by calling MSS_HPDMA_resume().

  @param
    This function has no parameters.
    
  @return
    This function does not return a value.
 */
void
MSS_HPDMA_pause
(
    void
);

/*-------------------------------------------------------------------------*//**
  The MSS_HPDMA_pause() function resumes the current HPDMA transfer after it was
  previously paused through a call to MSS_HPDMA_pause().

  @param
    This function has no parameters.
    
  @return
    This function does not return a value.
 */
void
MSS_HPDMA_resume
(
    void
);

/*-------------------------------------------------------------------------*//**
  The MSS_HPDMA_abort() function aborts the current HPDMA transfer.

  @param
    This function has no parameters.
    
  @return
    This function does not return a value.
 */
void
MSS_HPDMA_abort
(
    void
);

/*-------------------------------------------------------------------------*//**
 The MSS_HPDMA_get_transfer_status() function returns the status of the HPDMA
 transfer initiated by a call to MSS_HPDMA_start(). 

  @param
    This function has no parameters.
    
  @return
    The MSS_HPDMA_get_transfer_status() function returns the status of the HPDMA
    transfer as a value of  type hpdma_status_t. The possible return values are:
        - HPDMA_IN_PROGRESS
        - HPDMA_COMPLETED
        - HPDMA_SOURCE_ERROR
        - HPDMA_DESTINATION_ERROR
        - HPDMA_WORD_ALIGN_ERROR
      
  The example code below demonstrates the use of the
  MSS_HPDMA_get_transfer_status() function to detect the completion of the
  transfer of the content of eNVM into MDDR memory.
  @code
    void copy_envm_to_mddr(void)
    {
        MSS_HPDMA_start(ENVM_BASE_ADDR,
                        MDDR_BASE_ADDR,
                        ENVM_SIZE_BYTE,
                        HPDMA_TO_DDR);
        
        do {
            xfer_state = MSS_HPDMA_get_transfer_status();
        } while(HPDMA_IN_PROGRESS == xfer_state);
    }
  @endcode
 */
hpdma_status_t
MSS_HPDMA_get_transfer_status
(
    void
);

/*-------------------------------------------------------------------------*//**
  The MSS_HPDMA_set_handler() function is used to register a handler function
  that will be called by the driver when the HPDMA transfer completes. You must
  create and register a transfer completion handler function to suit your
  application. The MSS HPDMA driver passes the outcome of the transfer to the
  completion handler in the form of a hpdma_status_t parameter indicating if the
  transfer was successful or the type of error that occurred during the transfer
  if the transfer failed.

  @param handler
    The handler parameter is a pointer to a handler function provided by your
    application. This handler is of type mss_hpdma_handler_t. The handler
    function must take one parameter of type hpdma_status_t and must not return
    a value.

  @return
    This function does not return a value.
    
  This example code demonstrates the use of the MSS_HPDMA_set_handler()
  function:
  @code
    void transfer_complete_handler(hpdma_status_t status);

    volatile uint32_t g_xfer_in_progress = 0;

    void demo_transfer(void)
    {
        MSS_HPDMA_init();
        
        MSS_HPDMA_set_handler(transfer_complete_handler);
        
        g_xfer_in_progress = 1;
        MSS_HPDMA_start((uint32_t)0x20000000,
                        (uint32_t)0x00000000,
                        20,
                        HPDMA_FROM_DDR);
        
        while(g_xfer_in_progress)
        {
            ;
        }
    }

    void transfer_complete_handler(hpdma_status_t status)
    {
        g_xfer_in_progress = 0;
        
        switch(status)
        {
            case HPDMA_COMPLETED:
                display("Transfer complete");
            break;

            case HPDMA_SOURCE_ERROR:
                display("Transfer failed: source error");
            break;

            case HPDMA_DESTINATION_ERROR:
                display("Transfer failed: destination error");
            break;

            case HPDMA_WORD_ALIGN_ERROR:
                display("Transfer failed: word alignment error");
            break;

            default:
                display("Unexpected status");
            break;
        }
    }
  @endcode
 */
void
MSS_HPDMA_set_handler
(
    mss_hpdma_handler_t handler
);

#ifdef __cplusplus
}
#endif

#endif /* MSS_HPDMA_H_ */
