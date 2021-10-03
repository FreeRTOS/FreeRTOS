/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * @file hw_memory.h
 * @author Microchip-FPGA Embedded Systems Solutions
 *
 *
 * Note 1: This file should not be edited. If you need to modify a parameter
 * without going through regenerating using the MSS Configurator Libero flow 
 * or editing the associated xml file
 * the following method is recommended: 

 * 1. edit the following file 
 * boards/your_board/platform_config/mpfs_hal_config/mss_sw_config.h

 * 2. define the value you want to override there.
 * (Note: There is a commented example in the platform directory)

 * Note 2: The definition in mss_sw_config.h takes precedence, as
 * mss_sw_config.h is included prior to the generated header files located in
 * boards/your_board/fpga_design_config
 *
 */

#ifndef HW_MEMORY_H_
#define HW_MEMORY_H_


#ifdef __cplusplus
extern  "C" {
#endif

#if !defined (LIBERO_SETTING_RESET_VECTOR_HART0)
/*Reset vector hart0 */
#define LIBERO_SETTING_RESET_VECTOR_HART0    0x20220000
#define LIBERO_SETTING_RESET_VECTOR_HART0_SIZE    0x4    /* Length of memory block*/ 
#endif
#if !defined (LIBERO_SETTING_RESET_VECTOR_HART1)
/*Reset vector hart1 */
#define LIBERO_SETTING_RESET_VECTOR_HART1    0x20220000
#define LIBERO_SETTING_RESET_VECTOR_HART1_SIZE    0x4    /* Length of memory block*/ 
#endif
#if !defined (LIBERO_SETTING_RESET_VECTOR_HART2)
/*Reset vector hart2 */
#define LIBERO_SETTING_RESET_VECTOR_HART2    0x20220000
#define LIBERO_SETTING_RESET_VECTOR_HART2_SIZE    0x4    /* Length of memory block*/ 
#endif
#if !defined (LIBERO_SETTING_RESET_VECTOR_HART3)
/*Reset vector hart3 */
#define LIBERO_SETTING_RESET_VECTOR_HART3    0x20220000
#define LIBERO_SETTING_RESET_VECTOR_HART3_SIZE    0x4    /* Length of memory block*/ 
#endif
#if !defined (LIBERO_SETTING_RESET_VECTOR_HART4)
/*Reset vector hart4 */
#define LIBERO_SETTING_RESET_VECTOR_HART4    0x20220000
#define LIBERO_SETTING_RESET_VECTOR_HART4_SIZE    0x4    /* Length of memory block*/ 
#endif
#if !defined (LIBERO_SETTING_DDR_32_CACHE)
/*example instance of memory */
#define LIBERO_SETTING_DDR_32_CACHE    0x80000000
#define LIBERO_SETTING_DDR_32_CACHE_SIZE    0x100000    /* Length of memory block*/ 
#endif
#if !defined (LIBERO_SETTING_DDR_32_NON_CACHE)
/*example instance */
#define LIBERO_SETTING_DDR_32_NON_CACHE    0xC0000000
#define LIBERO_SETTING_DDR_32_NON_CACHE_SIZE    0x100000    /* Length of memory block*/ 
#endif
#if !defined (LIBERO_SETTING_DDR_64_CACHE)
/*64 bit address  */
#define LIBERO_SETTING_DDR_64_CACHE    0x1000000000
#define LIBERO_SETTING_DDR_64_CACHE_SIZE    0x100000    /* Length of memory block*/ 
#endif
#if !defined (LIBERO_SETTING_DDR_64_NON_CACHE)
/*64 bit address  */
#define LIBERO_SETTING_DDR_64_NON_CACHE    0x1400000000
#define LIBERO_SETTING_DDR_64_NON_CACHE_SIZE    0x100000    /* Length of memory block*/ 
#endif
#if !defined (LIBERO_SETTING_DDR_32_WCB)
/*example instance */
#define LIBERO_SETTING_DDR_32_WCB    0xD0000000
#define LIBERO_SETTING_DDR_32_WCB_SIZE    0x100000    /* Length of memory block*/ 
#endif
#if !defined (LIBERO_SETTING_DDR_64_WCB)
/*64 bit address  */
#define LIBERO_SETTING_DDR_64_WCB    0x1800000000
#define LIBERO_SETTING_DDR_64_WCB_SIZE    0x100000    /* Length of memory block*/ 
#endif
#if !defined (LIBERO_SETTING_RESERVED_SNVM)
/*Offset and size of reserved sNVM. (Not available to MSS) */
#define LIBERO_SETTING_RESERVED_SNVM    0x00000000
#define LIBERO_SETTING_RESERVED_SNVM_SIZE    0x00000000    /* Length of memory block*/ 
#endif
#if !defined (LIBERO_SETTING_RESERVED_ENVM)
/*Offset and size of reserved eNVM  (Not available to MSS) */
#define LIBERO_SETTING_RESERVED_ENVM    0x00000000
#define LIBERO_SETTING_RESERVED_ENVM_SIZE    0x00000000    /* Length of memory block*/ 
#endif

#ifdef __cplusplus
}
#endif


#endif /* #ifdef HW_MEMORY_H_ */

