/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 *
 * MPFS HAL Embedded Software
 *
 */
/*******************************************************************************
 * @file mss_axiswitch.c
 * @author Microchip-FPGA Embedded Systems Solutions
 * @brief PolarFire SoC MSS AXI switch configuration
 *
 */

#include <stddef.h>
#include <stdint.h>
#include "mpfs_hal/mss_hal.h"

#ifdef __cplusplus
extern "C" {
#endif

/*Returns the value of AXI_HW_CFG_REG register*/
uint32_t MSS_AXISW_get_hwcfg(void)
{
    return (AXISW->HWCFG);
}

/*Returns the value of AXI_VERSION_ID_REG register*/
uint32_t MSS_AXISW_get_vid(void)
{
    return (AXISW->VID);
}

/*Performs write operation on the AXI SWITCH APB interface,
 * Parameters:
 * master_port_num = AXI Master Port number. See Enum mss_axisw_mport_t above.


 Note: QoS values are programmable through registers only for AXI3 configurations.
 We have AXI4 so the QoS value programming should not be attempted.
 IF you try to write/read QoS value you will get return value =1 (AXI_ERR_BIT)

 Burstiness peak rate and transaction rate can be configured using other APIs.

  data: QoS value to be programmed
 return value: As received form AXI_ERR_BIT in CMD register.

 * */
uint32_t MSS_AXISW_write_qos_val(mss_axisw_mport_t master_port_num,
                                               uint32_t data)
{
    while(AXISW->CMD & AXISW_CMD_EN_MASK);  /*make sure previous command completed*/

    AXISW->DATA = data & AXISW_DATA_QOSVAL_MASK;  /*only valid values of bits[3:0]*/

    AXISW->CMD = (AXISW_CMD_RW_MASK |
                 (master_port_num << AXISW_CMD_RWCHAN) |
                 MSS_AXISW_QOS_VAL |
                 AXISW_CMD_EN_MASK);

    while(AXISW->CMD & AXISW_CMD_EN_MASK);    /*Wait for command to complete*/

    return ((AXISW->CMD & AXISW_CMD_ERR_MASK) >> AXISW_CMD_ERR);   /*return error bit value*/
}

/*Performs read operation on the AXI SWITCH APB interface,
 * Parameters:
 * master_port_num = AXI Master Port number. See Enum mss_axisw_mport_t above.
 *
 * Note: QoS values are programmable through registers only for AXI3 configurations.
 We have AXI4 so the QoS value programming should not be attempted.
 IF you try to write/read QoS value you will get return value =1 (AXI_ERR_BIT)
 *
 * returns the data returned by AXI SWITCH read operation for QoS command
 *
 * return value: As received form AXI_ERR_BIT in CMD register.
 */
uint32_t MSS_AXISW_read_qos_val(mss_axisw_mport_t master_port_num,
                                              uint32_t* rd_data)
{

    while(AXISW->CMD & AXISW_CMD_EN_MASK);

    AXISW->CMD &= ~(AXISW_CMD_RW_MASK);  /*Clear read/write bit*/

    AXISW->CMD = ((master_port_num << AXISW_CMD_RWCHAN) | (MSS_AXISW_QOS_VAL) | AXISW_CMD_EN_MASK);

    while(AXISW->CMD & AXISW_CMD_EN_MASK);

    *rd_data = AXISW->DATA & AXISW_DATA_QOSVAL_MASK;

    return ((AXISW->CMD & AXISW_CMD_ERR_MASK) >> AXISW_CMD_ERR);   /*return error bit value*/
}

/* Programs the peak rate and transaction rate value for the given master port
 read/write address channel

 NOTE: Peak rate and transaction rate are programmed simultaneously in one command.
 So we must make sure that both desired valid values must be provided.

* return value: As received form AXI_ERR_BIT in CMD register.

*/
uint32_t MSS_AXISW_write_rate(mss_axisw_mport_t master_port_num,
                                            mss_axisw_rate_t peak_rate,
                                            mss_axisw_rate_t xct_rate)
{
    while(AXISW->CMD & AXISW_CMD_EN_MASK);  /*make sure previous command completed*/
    AXISW->DATA = ((peak_rate) << AXISW_DATA_PEAKRT) | ((xct_rate) << AXISW_DATA_XCTRT) ;

    AXISW->CMD = (AXISW_CMD_RW_MASK |
                 (master_port_num << AXISW_CMD_RWCHAN) |
                 (MSS_AXISW_PEAKRT_XCTRT) |
                 AXISW_CMD_EN_MASK);

    while(AXISW->CMD & AXISW_CMD_EN_MASK);    /*Wait for command to complete*/

    return ((AXISW->CMD & AXISW_CMD_ERR_MASK) >> AXISW_CMD_ERR);   /*return error bit value*/
}

/* Reads the peak rate and transaction rate value for the given master port
read/write address channel
peak_rate: returns the value of peak rate
xct_rate: returns the value of transaction rate
return value: As received form AXI_ERR_BIT in CMD register.

*/
uint32_t MSS_AXISW_read_rate(mss_axisw_mport_t master_port_num,
                                          mss_axisw_rate_t* peak_rate,
                                          mss_axisw_rate_t* xct_rate)
{
    uint32_t temp = 0u;
    while(AXISW->CMD & AXISW_CMD_EN_MASK);

    AXISW->CMD &= ~(AXISW_CMD_RW_MASK);  /*Clear read/write and command EN bit*/

    AXISW->CMD = ((master_port_num << AXISW_CMD_RWCHAN) |
                 (MSS_AXISW_PEAKRT_XCTRT) |
                 AXISW_CMD_EN_MASK);

    while(AXISW->CMD & AXISW_CMD_EN_MASK);

    temp = AXISW->DATA;

    *peak_rate = (temp & AXISW_DATA_PEAKRT_MASK) >> AXISW_DATA_PEAKRT;
    *xct_rate = (temp & AXISW_DATA_XCTRT_MASK) >> AXISW_DATA_XCTRT;

    return ((AXISW->CMD & AXISW_CMD_ERR_MASK) >> AXISW_CMD_ERR);   /*return error bit value*/
}

/* Programs the burstiness value for the given master port read/write address channel

burstiness_val: burstiness value to be programmed
NOTE: Burstiness value formula as mentioned in AXISW document is Burstiness = DataReg[23:16] + 1

regulator_en: QoS regulator Enable 1= enable, 0 = disable

* return value: As received form AXI_ERR_BIT in CMD register.
*/
int32_t MSS_AXISW_write_burstiness(mss_axisw_mport_t master_port_num,
                                                  uint32_t burstiness_val,
                                                  uint32_t regulator_en)
{

    while(AXISW->CMD & AXISW_CMD_EN_MASK);  /*make sure previous command completed*/

    /*Write burstiness value and enable burstiness regulator.
     * Burstiness_val=0 is not valid.
    Burstiness value formula as mentioned in AXISW document is Burstiness = DataReg[23:16] + 1*/

    if(burstiness_val == 0)
    {
    	return -1;
    }
    else
    {
        AXISW->DATA = ((burstiness_val - 1u) << AXISW_DATA_BURSTI) | (regulator_en & 0x01);
    }

    AXISW->CMD = (AXISW_CMD_RW_MASK |
                 (master_port_num << AXISW_CMD_RWCHAN) |
                 (MSS_AXISW_BURSTINESS_EN) |
                 AXISW_CMD_EN_MASK);

    while(AXISW->CMD & AXISW_CMD_EN_MASK);      /*Wait for command to complete*/

    return ((AXISW->CMD & AXISW_CMD_ERR_MASK) >> AXISW_CMD_ERR);   /*return error bit value*/
}

/* Reads the burstiness value for the given master port read/write address channel

burstiness_val: Return parameter bit 23:16 shows the burstiness value.
NOTE: Burstiness value formula as mentioned in AXISW document is Burstiness = DataReg[23:16] + 1

* return value: As received form AXI_ERR_BIT in CMD register.
*/
uint32_t MSS_AXISW_read_burstiness(mss_axisw_mport_t master_port_num,
                                                uint32_t* burstiness_val)
{
    while(AXISW->CMD & AXISW_CMD_EN_MASK);

    AXISW->CMD &= ~(AXISW_CMD_RW_MASK);  /*Clear read/write and command EN bit*/

    AXISW->CMD = ((master_port_num << AXISW_CMD_RWCHAN) |
                 (MSS_AXISW_BURSTINESS_EN) |
                 AXISW_CMD_EN_MASK);

    while(AXISW->CMD & AXISW_CMD_EN_MASK);

    *burstiness_val = ((AXISW->DATA & AXISW_DATA_BURSTI_MASK) >> AXISW_DATA_BURSTI) + 1u;

    return ((AXISW->CMD & AXISW_CMD_ERR_MASK) >> AXISW_CMD_ERR);   /*return error bit value*/
}

uint32_t MSS_AXISW_write_slave_ready(mss_axisw_mport_t master_port_num,
                                                   uint8_t slave_ready_en)
{
    while(AXISW->CMD & AXISW_CMD_EN_MASK);  /*make sure previous command completed*/

    AXISW->DATA = slave_ready_en & 0x01;  /*only valid value of bit0*/

    AXISW->CMD = (AXISW_CMD_RW_MASK |
                 (master_port_num << AXISW_CMD_RWCHAN) |
                 MSS_AXISW_SLV_RDY |
                 AXISW_CMD_EN_MASK);

    while(AXISW->CMD & AXISW_CMD_EN_MASK);    /*Wait for command to complete*/

    return ((AXISW->CMD & AXISW_CMD_ERR_MASK) >> AXISW_CMD_ERR);   /*return error bit value*/
}

/*Performs read operation on the AXI SWITCH APB interface,
 * Parameters:
 * master_port_num = AXI Master Port number. See Enum mss_axisw_mport_t above.
 *
 *
 * slave_ready_en: returns the data returned by AXI SWITCH read operation for slave ready command
 * return value: As received form AXI_ERR_BIT in CMD register.
 *
 */
uint32_t MSS_AXISW_read_slave_ready(mss_axisw_mport_t master_port_num,
                                                  uint8_t* slave_ready_en)
{

    while(AXISW->CMD & AXISW_CMD_EN_MASK);

    AXISW->CMD &= ~(AXISW_CMD_RW_MASK);  /*Clear read/write bit*/

    AXISW->CMD = ((master_port_num << AXISW_CMD_RWCHAN) |
                 (MSS_AXISW_SLV_RDY) |
                 AXISW_CMD_EN_MASK);

    while(AXISW->CMD & AXISW_CMD_EN_MASK);

    *slave_ready_en = AXISW->DATA & 0x01;

    return ((AXISW->CMD & AXISW_CMD_ERR_MASK) >> AXISW_CMD_ERR);   /*return error bit value*/
}

#ifdef __cplusplus
}
#endif


