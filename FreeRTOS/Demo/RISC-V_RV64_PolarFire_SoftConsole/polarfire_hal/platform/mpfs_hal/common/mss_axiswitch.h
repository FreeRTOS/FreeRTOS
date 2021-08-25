/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software
 *
 */
/*=========================================================================*//**

 *//*=========================================================================*/
#ifndef __MSS_AXISW_H_
#define __MSS_AXISW_H_ 1


#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/***************************************************************************//**

 */

typedef enum {
    MSS_AXISW_FIC0_RD_CHAN    = 0x000,
    MSS_AXISW_FIC0_WR_CHAN,
    MSS_AXISW_FIC1_RD_CHAN,
    MSS_AXISW_FIC1_WR_CHAN,
    MSS_AXISW_FIC2_RD_CHAN,
    MSS_AXISW_FIC2_WR_CHAN,
    MSS_AXISW_ATHENA_RD_CHAN,
    MSS_AXISW_ATHENA_WR_CHAN,
    MSS_AXISW_GEM0_RD_CHAN,
    MSS_AXISW_GEM0_WR_CHAN,
    MSS_AXISW_GEM1_RD_CHAN,
    MSS_AXISW_GEM1_WR_CHAN,
    MSS_AXISW_MMC_RD_CHAN,
    MSS_AXISW_MMC_WR_CHAN,
    MSS_AXISW_USB_RD_CHAN,
    MSS_AXISW_USB_WR_CHAN,
    MSS_AXISW_SCB_RD_CHAN,
    MSS_AXISW_SCB_WR_CHAN,
    MSS_AXISW_CPLEX_D0_RD_CHAN,
    MSS_AXISW_CPLEX_D0_WR_CHAN,
    MSS_AXISW_CPLEX_D1_RD_CHAN,
    MSS_AXISW_CPLEX_D1_WR_CHAN,
    MSS_AXISW_CPLEX_F0_RD_CHAN,
    MSS_AXISW_CPLEX_F0_WR_CHAN,
    MSS_AXISW_CPLEX_F1_RD_CHAN,
    MSS_AXISW_CPLEX_F1_WR_CHAN,
    MSS_AXISW_CPLEX_NC_RD_CHAN,
    MSS_AXISW_CPLEX_NC_WR_CHAN,
    MSS_AXISW_TRACE_RD_CHAN,
    MSS_AXISW_TRACE_WR_CHAN,
} mss_axisw_mport_t;


typedef enum {
    MSS_AXISW_BURSTINESS_EN    = 0x00,
    MSS_AXISW_PEAKRT_XCTRT,
    MSS_AXISW_QOS_VAL,
    MSS_AXISW_SLV_RDY,
} mss_axisw_cmd_t;

typedef enum {
    MSS_AXISW_MASTER_RD_CHAN    = 0x00,
    MSS_AXISW_MASTER_WR_CHAN    = 0x01,
} mss_axisw_mchan_t;

/*
The Peak rate and transaction rates are encoded as follows.
1000_0000_0000          1/2
0100_0000_0000          1/4
0010_0000_0000          1/8
0001_0000_0000          1/16
0000_1000_0000          1/32
0000_0100_0000          1/64
0000_0010_0000          1/128
0000_0001_0000          1/256
0000_0000_1000          1/512
0000_0000_0100          1/1024
0000_0000_0010          1/2048
0000_0000_0001          1/4096

Programming the transaction rate as 0000_0000_0000 disables token generation and
traffic is not regulated based on the tokens.

Programming the peak rate as 0000_0000_0000 disables the peak rate control logic and
traffic is not regulated by the peak rate logic.
*/
typedef enum {
    MSS_AXISW_TXNRATE_BY4096    = 0x001,
    MSS_AXISW_TXNRATE_BY2098    = 0x002,
    MSS_AXISW_TXNRATE_BY1024    = 0x004,
    MSS_AXISW_TXNRATE_BY512     = 0x008,
    MSS_AXISW_TXNRATE_BY256     = 0x010,
    MSS_AXISW_TXNRATE_BY128     = 0x020,
    MSS_AXISW_TXNRATE_BY64      = 0x040,
    MSS_AXISW_TXNRATE_BY32      = 0x080,
    MSS_AXISW_TXNRATE_BY16      = 0x100,
    MSS_AXISW_TXNRATE_BY8       = 0x200,
    MSS_AXISW_TXNRATE_BY4       = 0x400,
    MSS_AXISW_TXNRATE_BY2       = 0x800,
    MSS_AXISW_TXNRATE_DISABLE      = 0x0,
} mss_axisw_rate_t;

#define AXISW_CMD_EN                        31U
#define AXISW_CMD_EN_MASK                   (uint32_t)(0x01U << AXISW_CMD_EN)

#define AXISW_CMD_RW                        30U
#define AXISW_CMD_RW_MASK                   (uint32_t)(0x01U << AXISW_CMD_RW)

#define AXISW_CMD_SWRST                     29U
#define AXISW_CMD_SWRST_MASK                (uint32_t)(0x01U << AXISW_CMD_SWRST)

#define AXISW_CMD_ERR                       28U
#define AXISW_CMD_ERR_MASK                  (uint32_t)(0x01U << AXISW_CMD_ERR)

//#define AXISW_CMD_MPORT                   8U
//#define AXISW_CMD_MPORT_MASK              (0x0F << AXISW_CMD_MPORT)

#define AXISW_CMD_RWCHAN                    7U
#define AXISW_CMD_RWCHAN_MASK               (uint32_t)(0x1F << AXISW_CMD_RWCHAN)

#define AXISW_CMD_CMD                       0U
#define AXISW_CMD_CMD_MASK                  (0x01U << AXISW_CMD_CMD)

#define AXISW_DATA_PEAKRT                   20U
#define AXISW_DATA_PEAKRT_MASK              (0xFFFU << AXISW_DATA_PEAKRT)

#define AXISW_DATA_XCTRT                    4U
#define AXISW_DATA_XCTRT_MASK               (0xFFFU << AXISW_DATA_XCTRT)

#define AXISW_DATA_BURSTI                   16U
#define AXISW_DATA_BURSTI_MASK              (0xFFU << AXISW_DATA_BURSTI)

#define AXISW_DATA_QOSVAL                   0U
#define AXISW_DATA_QOSVAL_MASK              (0xFU << AXISW_DATA_QOSVAL)

typedef struct
{
    __IO uint32_t  VID;
    __IO uint32_t  HWCFG;
    __IO uint32_t  CMD;
    __IO uint32_t  DATA;
} AXISW_TypeDef;


#define AXISW                               ((AXISW_TypeDef*)0x20004000UL)


uint32_t MSS_AXISW_get_hwcfg(void);
uint32_t MSS_AXISW_get_vid(void);
uint32_t MSS_AXISW_write_qos_val(mss_axisw_mport_t master_port_num,
                                               uint32_t data);
uint32_t MSS_AXISW_read_qos_val(mss_axisw_mport_t master_port_num,
                                              uint32_t* rd_data);
uint32_t MSS_AXISW_write_rate(mss_axisw_mport_t master_port_num,
                                            mss_axisw_rate_t peak_rate,
                                            mss_axisw_rate_t xct_rate);
uint32_t MSS_AXISW_read_rate(mss_axisw_mport_t master_port_num,
                                          mss_axisw_rate_t* peak_rate,
                                          mss_axisw_rate_t* xct_rate);
int32_t MSS_AXISW_write_burstiness(mss_axisw_mport_t master_port_num,
                                                  uint32_t burstiness_val,
                                                  uint32_t regulator_en);
uint32_t MSS_AXISW_read_burstiness(mss_axisw_mport_t master_port_num,
                                                uint32_t* burstiness_val);
uint32_t MSS_AXISW_write_slave_ready(mss_axisw_mport_t master_port_num,
                                                   uint8_t slave_ready_en);
uint32_t MSS_AXISW_read_slave_ready(mss_axisw_mport_t master_port_num,
                                                  uint8_t* slave_ready_en);


#ifdef __cplusplus
}
#endif

#endif /* __MSS_AXISW_H_ */

