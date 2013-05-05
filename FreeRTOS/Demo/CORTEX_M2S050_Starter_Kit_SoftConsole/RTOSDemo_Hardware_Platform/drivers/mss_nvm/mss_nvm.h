/*******************************************************************************
 * (c) Copyright 2011-2013 Microsemi SoC Products Group.  All rights reserved.
 * 
 * This file contains public APIs for SmartFusion2 eNVM software driver.
 * 
 * SVN $Revision: 5362 $
 * SVN $Date: 2013-03-26 21:37:53 +0000 (Tue, 26 Mar 2013) $
 */
/*=========================================================================*//**
  @mainpage SmartFusion2 MSS eNVM Bare Metal Driver.
  
  @section intro_sec Introduction
  The SmartFusion2 microcontroller subsystem (MSS) includes up to two embedded
  non-volatile memory (eNVM) blocks. Each of these eNVM blocks can be a maximum
  size of 256kB. This software driver provides a set of functions for accessing
  and controlling the MSS eNVM as part of a bare metal system where no operating
  system is available. The driver can be adapted for use as part of an operating
  system, but the implementation of the adaptation layer between the driver and
  the operating system's driver model is outside the scope of the driver.
  
  The MSS eNVM driver provides support for the following features:
    - eNVM write (program) operations.
    - eNVM page unlocking
  The MSS eNVM driver is provided as C source code.

  
  @section configuration Driver Configuration
  The size of the MSS eNVM varies with different SmartFusion2 device types. You
  must only use this driver to access memory locations within the valid MSS eNVM
  address space for the targeted device. The size of the valid MSS eNVM address
  space corresponds to the size of the MSS eNVM in the device. Some pages of the
  MSS eNVM may be write protected by the SmartFusion2 MSS configurator as part
  of the hardware design flow. The driver cannot unlock or write to these
  protected pages.
  The base address, register addresses and interrupt number assignment for the
  MSS eNVM blocks are defined as constants in the SmartFusion2 CMSIS HAL. You
  must ensure that the latest SmartFusion2 CMSIS HAL is included in the project
  settings of the software tool chain used to build your project and that it is
  generated into your project.

  @section theory_op Theory of Operation
  The total amount of eNVM available in a SmartFusion device ranges from 128kB
  to 512kB, provided in one or two physical eNVM blocks. The eNVM blocks are
  divided into pages, with each page holding 128 bytes of data. The MSS eNVM
  driver treats the entire eNVM as a contiguous memory space. It provides write
  access to all pages that are in the valid eNVM address range for the
  SmartFusion device and that are not write-protected. The driver imposes no
  restrictions on writing data across eNVM block or page boundaries. The driver
  supports random access writes to the eNVM memory. 

 *//*=========================================================================*/
#ifndef __MSS_NVM_H
#define __MSS_NVM_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/******************************************************************************/
/* Public definitions                                                         */
/******************************************************************************/
/*******************************************************************************
 * Page Locking constants:
 */
/*
 * Indicates that the NVM_write() function should not lock the addressed pages
 * after programming the data.
 */
#define NVM_DO_NOT_LOCK_PAGE    0u

/*
 * Indicates that the NVM_write() function should lock the addressed pages after
 * programming the data.
 */
#define NVM_LOCK_PAGE           1u

/*******************************************************************************
  The nvm_status_t enumeration specifies the possible return values from the
  NVM_write() and NVM_unlock() functions.
  
    NVM_SUCCESS:
      Indicates that the programming was successful.
        
    NVM_PROTECTION_ERROR:
      Indicates that the operation could not be completed because of a
      protection error. This happens when attempting to program a page that was
      set as protected in the hardware flow.
      
    NVM_VERIFY_FAILURE:
      Indicates that one of the verify operations failed.
      
    NVM_PAGE_LOCK_ERROR:
      Indicates that the operation could not complete because one of the pages
      is locked. This may happen if the page was locked during a previous call
      to NVM_write() or if the page was locked in the hardware design flow.
      
    NVM_WRITE_THRESHOLD_ERROR:
      Indicates that the NVM maximum number of programming cycles has been
      reached.
      
    NVM_IN_USE_BY_OTHER_MASTER:
      Indicates that some other MSS AHB Bus Matrix master is accessing the NVM.
      This could be due to the FPGA logic or the system controller programming
      the NVM.
      
    NVM_INVALID_PARAMETER:
      Indicates that one of more of the function parameters has an invalid
      value. This is typically  returned when attempting to write or unlock more
      eNVM than is available on  the device.
 */
typedef enum nvm_status
{
    NVM_SUCCESS = 0,
    NVM_PROTECTION_ERROR,
    NVM_VERIFY_FAILURE,
    NVM_PAGE_LOCK_ERROR,
    NVM_WRITE_THRESHOLD_ERROR,
    NVM_IN_USE_BY_OTHER_MASTER,
    NVM_INVALID_PARAMETER
} nvm_status_t;

/******************************************************************************/
/* Public variables                                                           */
/******************************************************************************/


/******************************************************************************/
/* Public function declarations                                               */
/******************************************************************************/

/***************************************************************************//**
  The NVM_write() function is used to program (or write) data into the eNVM.
  This function treats the two eNVM blocks contiguously, so a total of 512kB of
  memory can be accessed linearly. The start address and end address of the
  memory range to be programmed do not need to be page aligned. This function
  supports programming of data that spans multiple pages. This function is a
  blocking function.
  Note: The NVM_write() function performs a verify operation on each page 
        programmed to ensure the eNVM is programmed with the expected data.

  @param start_addr
    The start_addr parameter is the byte aligned start address in the eNVM
    address space, to which the data is to be programmed.

  @param pidata
    The pidata parameter is the byte aligned start address of the input data.

  @param length
    The length parameter is the number of bytes of data to be programmed.

  @param lock_page
    The lock_page parameter specifies whether the pages that are programmed
    must be locked or not once programmed. Locking the programmed pages prevents
    them from being overwritten by mistake. Subsequent programming of these
    pages will require the pages to be unlocked prior to calling NVM_write().
    Allowed values for lock_page are:
        - NVM_DO_NOT_LOCK_PAGE
        - NVM_LOCK_PAGE
        
  @return
    This function returns NVM_SUCCESS on successful execution. 
    It returns one of the following error codes if the programming of the eNVM
    fails:
        - NVM_PROTECTION_ERROR
        - NVM_VERIFY_FAILURE
        - NVM_PAGE_LOCK_ERROR
        - NVM_WRITE_THRESHOLD_ERROR
        - NVM_IN_USE_BY_OTHER_MASTER
        - NVM_INVALID_PARAMETER
        
  Example:
  @code
    uint8_t idata[815] = {"Z"};
    status = NVM_write(0x0, idata, sizeof(idata), NVM_DO_NOT_LOCK_PAGE);
  @endcode
 */
nvm_status_t 
NVM_write
(
    uint32_t start_addr,
    const uint8_t * pidata,
    uint32_t  length,
    uint32_t  lock_page
);

/***************************************************************************//**
  The NVM_unlock() function is used to unlock the eNVM pages for a specified
  range of eNVM addresses in preparation for writing data into the unlocked
  locations. This function treats the two eNVM blocks contiguously, so a total
  of 512kB of memory can be accessed linearly. The start address and end address
  of the memory range to be unlocked do not need to be page aligned. This
  function supports unlocking of an eNVM address range that spans multiple
  pages. This function is a blocking function.

  @param start_addr
    The start_addr parameter is the byte aligned start address, in the eNVM
    address space, of the memory range to be unlocked.
    
  @param length
    The length parameter is the size in bytes of the memory range to be
    unlocked.

  @return
    This function returns NVM_SUCCESS on successful execution. 
    It returns one of the following error codes if the unlocking of the eNVM fails:
        - NVM_PROTECTION_ERROR
        - NVM_VERIFY_FAILURE
        - NVM_PAGE_LOCK_ERROR
        - NVM_WRITE_THRESHOLD_ERROR
        - NVM_IN_USE_BY_OTHER_MASTER
        - NVM_INVALID_PARAMETER
        
  The example code below demonstrates the intended use of the NVM_unlock()
  function:
  @code
    int program_locked_nvm(uint32_t target_addr, uint32_t length)
    {
        nvm_status_t status;
        int success = 0;
        
        status = NVM_unlock(target_addr, length);
        if(NVM_SUCCESS == status)
        {
            status = NVM_write(target_addr, buffer, length, NVM_LOCK_PAGE);
            if(NVM_SUCCESS == status)
            {
                success = 1; 
            }
        }
        return success;
    }
  @endcode
 */
nvm_status_t
NVM_unlock
(
    uint32_t start_addr,
    uint32_t length
);

#ifdef __cplusplus
}
#endif

#endif /* __MSS_NVM_H */


