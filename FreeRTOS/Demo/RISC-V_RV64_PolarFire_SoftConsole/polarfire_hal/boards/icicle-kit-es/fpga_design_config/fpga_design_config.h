/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * @file fpga_design_config.h
 * @author Embedded Software
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

#ifndef FPGA_DESIGN_CONFIG_H_
#define FPGA_DESIGN_CONFIG_H_

#define  LIBERO_SETTING_MSS_CONFIGURATOR_VERSION                    "2021.1"
#define  LIBERO_SETTING_DESIGN_NAME                                 "ICICLE_MSS"
#define  LIBERO_SETTING_MPFS_PART                                   "MPFS250T_ES"
#define  LIBERO_SETTING_GENERATION_DATE                             "04-11-2021_22:30:25"
#define  LIBERO_SETTING_XML_VERSION                                 "0.5.3"
#define  LIBERO_SETTING_XML_VERSION_MAJOR                           0
#define  LIBERO_SETTING_XML_VERSION_MINOR                           5
#define  LIBERO_SETTING_XML_VERSION_PATCH                           3
#define  LIBERO_SETTING_HEADER_GENERATOR_VERSION                    "0.6.3"
#define  LIBERO_SETTING_HEADER_GENERATOR_VERSION_MAJOR              0
#define  LIBERO_SETTING_HEADER_GENERATOR_VERSION_MINOR              6
#define  LIBERO_SETTING_HEADER_GENERATOR_VERSION_PATCH              3

#include "memory_map/hw_memory.h"
#include "memory_map/hw_apb_split.h"
#include "memory_map/hw_cache.h"
#include "memory_map/hw_pmp_hart0.h"
#include "memory_map/hw_pmp_hart1.h"
#include "memory_map/hw_pmp_hart2.h"
#include "memory_map/hw_pmp_hart3.h"
#include "memory_map/hw_pmp_hart4.h"
#include "memory_map/hw_mpu_fic0.h"
#include "memory_map/hw_mpu_fic1.h"
#include "memory_map/hw_mpu_fic2.h"
#include "memory_map/hw_mpu_crypto.h"
#include "memory_map/hw_mpu_gem0.h"
#include "memory_map/hw_mpu_gem1.h"
#include "memory_map/hw_mpu_usb.h"
#include "memory_map/hw_mpu_mmc.h"
#include "memory_map/hw_mpu_scb.h"
#include "memory_map/hw_mpu_trace.h"
#include "io/hw_mssio_mux.h"
#include "io/hw_hsio_mux.h"
#include "sgmii/hw_sgmii_tip.h"
#include "ddr/hw_ddr_options.h"
#include "ddr/hw_ddr_io_bank.h"
#include "ddr/hw_ddr_mode.h"
#include "ddr/hw_ddr_off_mode.h"
#include "ddr/hw_ddr_segs.h"
#include "ddr/hw_ddrc.h"
#include "clocks/hw_mss_clks.h"
#include "clocks/hw_clk_sysreg.h"
#include "clocks/hw_clk_mss_pll.h"
#include "clocks/hw_clk_sgmii_pll.h"
#include "clocks/hw_clk_ddr_pll.h"
#include "clocks/hw_clk_mss_cfm.h"
#include "clocks/hw_clk_sgmii_cfm.h"
#include "general/hw_gen_peripherals.h"

#ifdef __cplusplus
extern  "C" {
#endif

/* No content in this file, used for referencing header */

#ifdef __cplusplus
}
#endif


#endif /* #ifdef FPGA_DESIGN_CONFIG_H_ */

