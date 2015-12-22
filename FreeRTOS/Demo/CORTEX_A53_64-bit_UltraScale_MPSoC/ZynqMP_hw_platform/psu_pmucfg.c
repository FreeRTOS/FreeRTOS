/******************************************************************************
 *
 * (c) Copyright 2014 Xilinx, Inc. All rights reserved.
 *
 * This file contains confidential and proprietary information  of Xilinx, Inc.
 * and is protected under U.S. and  international copyright and other
 * intellectual property  laws.
 *
 * DISCLAIMER
 * This disclaimer is not a license and does not grant any  rights to the
 * materials distributed herewith. Except as  otherwise provided in a valid
 * license issued to you by  Xilinx, and to the maximum extent permitted by
 * applicable law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND  WITH ALL
 * FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES  AND CONDITIONS, EXPRESS,
 * IMPLIED, OR STATUTORY, INCLUDING  BUT NOT LIMITED TO WARRANTIES OF
 * MERCHANTABILITY, NON-  INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE;
 * and
 * (2) Xilinx shall not be liable (whether in contract or tort,  including
 * negligence, or under any other theory of liability) for any loss or damage
 * of any kind or nature  related to, arising under or in connection with these
 * materials, including for any direct, or any indirect,  special, incidental,
 * or consequential loss or damage  (including loss of data, profits,
 * goodwill, or any type of  loss or damage suffered as a result of any
 * action brought  by a third party) even if such damage or loss was
 * reasonably foreseeable or Xilinx had been advised of the  possibility
 * of the same.
 *
 * CRITICAL APPLICATIONS
 * Xilinx products are not designed or intended to be fail-  safe, or for use
 * in any application requiring fail-safe  performance, such as life-support
 * or safety devices or  systems, Class III medical devices, nuclear
 * facilities,  applications related to the deployment of airbags, or any
 * other applications that could lead to death, personal  injury, or severe
 * property or environmental damage  (individually and collectively,
 * "Critical  Applications"). Customer assumes the sole risk and  liability
 * of any use of Xilinx products in Critical  Applications, subject only to
 * applicable laws and  regulations governing limitations on product liability.
 *
 * THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS  PART
 * OF THIS FILE AT ALL TIMES.
 *
 ******************************************************************************/
/*
  PMU - PCW handoff file
  Auto generated file from PCW-Vivado tools to be consumed in PMU firmware  
*/

#define XPFW_CFG_MASTER_PMU                   0 
#define XPFW_CFG_MASTER_CSU                   1
#define XPFW_CFG_MASTER_APU                   2
#define XPFW_CFG_MASTER_RPU_0                 3
#define XPFW_CFG_MASTER_RPU_1                 4
#define XPFW_CFG_MASTER_USB0                  5
#define XPFW_CFG_MASTER_USB1                  6
#define XPFW_CFG_MASTER_ENET0                 7
#define XPFW_CFG_MASTER_ENET1                 8
#define XPFW_CFG_MASTER_ENET2                 9
#define XPFW_CFG_MASTER_ENET3                 10
#define XPFW_CFG_MASTER_DAP                   11
#define XPFW_CFG_MASTER_ADMA                  12
#define XPFW_CFG_MASTER_SD0                   13
#define XPFW_CFG_MASTER_SD1                   14
#define XPFW_CFG_MASTER_NAND                  15
#define XPFW_CFG_MASTER_QSPI                  16
#define XPFW_CFG_MASTER_SATA                  17
#define XPFW_CFG_MASTER_GPU                   18
#define XPFW_CFG_MASTER_CORESIGHT             19
#define XPFW_CFG_MASTER_PCIE                  20 
#define XPFW_CFG_MASTER_DP                    21 
#define XPFW_CFG_MASTER_GDMA                  22 
#define XPFW_CFG_MASTER_AF0                   23 
#define XPFW_CFG_MASTER_AF1                   24 
#define XPFW_CFG_MASTER_AF2                   25 
#define XPFW_CFG_MASTER_AF3                   26 
#define XPFW_CFG_MASTER_AF4                   27 
#define XPFW_CFG_MASTER_AF5                   28 
#define XPFW_CFG_MASTER_AFILPD                29
#define XPFW_CFG_MASTER_MAX                   30 

#define XPFW_CFG_SLAVE_UART0                  0 
#define XPFW_CFG_SLAVE_UART1                  1 
#define XPFW_CFG_SLAVE_I2C0                   2 
#define XPFW_CFG_SLAVE_I2C1                   3 
#define XPFW_CFG_SLAVE_SPI0                   4 
#define XPFW_CFG_SLAVE_SPI1                   5 
#define XPFW_CFG_SLAVE_CAN0                   6 
#define XPFW_CFG_SLAVE_CAN1                   7 
#define XPFW_CFG_SLAVE_GPIO0                  8 
#define XPFW_CFG_SLAVE_ENET0                  9 
#define XPFW_CFG_SLAVE_ENET1                  10 
#define XPFW_CFG_SLAVE_ENET2                  11 
#define XPFW_CFG_SLAVE_ENET3                  12 
#define XPFW_CFG_SLAVE_NAND0                  13 
#define XPFW_CFG_SLAVE_TTC0                   14 
#define XPFW_CFG_SLAVE_TTC1                   15 
#define XPFW_CFG_SLAVE_TTC2                   16 
#define XPFW_CFG_SLAVE_TTC3                   17 
#define XPFW_CFG_SLAVE_WDT0                   18 
#define XPFW_CFG_SLAVE_SD0                    19 
#define XPFW_CFG_SLAVE_SD1                    10 
#define XPFW_CFG_SLAVE_USB0                   11 
#define XPFW_CFG_SLAVE_USB1                   12 
#define XPFW_CFG_SLAVE_IOUSLCR0               13 
#define XPFW_CFG_SLAVE_CSU0                   14 
#define XPFW_CFG_SLAVE_LPD_SLCR               15 
#define XPFW_CFG_SLAVE_LPD_GPV                16 
#define XPFW_CFG_SLAVE_USB3_0                 17 
#define XPFW_CFG_SLAVE_USB3_1                 18 
#define XPFW_CFG_SLAVE_QSPI0                  19 
#define XPFW_CFG_SLAVE_DDR                    20 
#define XPFW_CFG_SLAVE_OCM                    21 
#define XPFW_CFG_SLAVE_PMU_GLREG              22 
#define XPFW_CFG_SLAVE_MAX                    23 
 
 
/* MASTER LIST
 Shared resources like DDR will be powered off by the PMUFW, if no active user for such a resource is present. In order to be able to determine whether no user is present, 
 PMUFW needs to be aware of all possible users. These include:
 1.  APU  / Independent A53s
 2.  RPU lockstep/independent
 3.  PL Soft-Cores
 So a list of all active Masters in the System should be exported to PMU FW */
 unsigned int XPFW_ConfigActMasters[XPFW_CFG_MASTER_MAX] = { 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1}; 

/* SLAVE LIST
 It is expected that unused resources are statically turned off by the FSBL during boot. Everything else that is used during run-time needs to be known to the
 PMUFW in order to execute PM-related functionality on it. So a list of all active slaves on the system should be exported to the PMU FW */
 unsigned int XPFW_ConfigActSlaves[XPFW_CFG_SLAVE_MAX] = { 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1}; 

/* Ownership Information
 PMU_Master_Slave_Isolation[C_MASTER_PSS_CORTEX_APU][PSS_DDR_0] = 1 */
unsigned int XPFW_ConfigTable[XPFW_CFG_MASTER_MAX][XPFW_CFG_SLAVE_MAX] = {
                                                                             1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,   // E.g APU   - > DDR, SD0, ENET0 
                                                                             1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,   // E.g RPU_0 - > DDR, SD0, ENET0 
                                                                             1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,   // E.g RPU_1 - > DDR, ENET0 
                                                                             1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,                         
                                                                             1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,                        
                                                                             1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,                       
                                                                             1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,                      
                                                                             1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,                     
                                                                             1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,                    
                                                                             1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,                    
                                                                             1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,                    
                                                                             1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,                    
                                                                             1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,                    
                                                                             1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,                    
                                                                             1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,                    
                                                                             1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,                    
                                                                             1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,                    
                                                                             1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,                    
                                                                             1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,                    
                                                                             1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,                    
                                                                             1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,                    
                                                                             1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,                    
                                                                             1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1                    
                                                                           };

/* Safety Monitor test case to be done */
