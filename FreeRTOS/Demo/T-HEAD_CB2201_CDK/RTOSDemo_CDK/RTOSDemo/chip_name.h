/*
 * Description : chip_name.h - Define the system configuration such as:
 * 1 CPU base config
 * 2 memory & IO base address 
 * 3 flash size & address
 * 4 interrupt resource for the soc.
 *
 * Copyright (C) : Hangzhou C-SKY Microsystems Co.,LTD.
 * Date:   2016-08-22
 */

#ifndef __INCLUDE_CHIP_NAME_H__
#define __INCLUDE_CHIP_NAME_H__

typedef enum IRQn
{
/* ----------------------  CK801CM0 Specific Interrupt Numbers  --------------------- */
  CORET_IRQn = 0,
} IRQn_Type;

/* Configuration of the CK80# Processor and Core Peripherals */
/* ToDo: set the defines according your Device                                                    */
/* ToDo: define the correct core revision
         __CK801_REV if your device is a CK801 device
         __CK802_REV if your device is a CK802 device
         __CK803S_REV if your device is a CK803S device                                           */
#define __NVIC_PRIO_BITS          2         /*!< Number of Bits used for Priority Levels          */
#define __Vendor_SysTickConfig    0         /*!< Set to 1 if different SysTick Config is used     */
#define __MGU_PRESENT             0         /*!< MGU present or not                               */

/* Soft reset address */
#define  __RESET_CONST           0xabcd1234

/**********************************************
 * Config CPU
 * Define the attribute for your CPU
 *********************************************/
//#include "CSICORE_CK802.H"

/*******************************
 * Config IO base address
 ******************************/


#endif /* __INCLUDE_CHIP_NAME_H__ */
