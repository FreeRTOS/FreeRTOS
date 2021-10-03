/*******************************************************************************
 * Copyright 2019-2021 Microchip FPGA Embedded Systems Solutions.
 *
 */

#include <stdint.h>
#include <stdio.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#include "mpfs_hal/mss_hal.h"
#include "mss_cfm.h"

/***************************************************************************//**
 * See mss_cfm.h for description of this function.
 */
uint8_t MSS_CFM_control_start(void)
{

    /* Writing a 1, to this causes measurement circuitry to start. */
    CFM_REG->controlReg |= 1;

    return (CFM_REG->controlReg & CFM_CONTROL_REG_START_MASK);

}


uint8_t MSS_CFM_control_stop(void)
{

    /* Writing a 1, to this causes measurement circuitry to start. */
    CFM_REG->controlReg |= (1 << CFM_CONTROL_REG_STOP_BITS_SHIFT);

    return (CFM_REG->controlReg & CFM_CONTROL_REG_START_MASK);

}



cfm_error_id_t MSS_CLF_clk_configuration(
        uint8_t clkSel,
        uint8_t refsel0,
        uint8_t refsel1,
        uint8_t monSEL,
        uint8_t monEN
    )
{

    /* Reset the register. */
    CFM_REG->clkselReg = 0;

    /* Some error checking on configuration values. */
    if(clkSel > CFM_CLK_SEL_MASK)
        return ERROR_INVALID_CLK_SELECTION_GROUP;

    if(refsel0 > CFM_CLK_REFSEL0_MASK)
        return ERROR_INVALID_REF_SEL0;

    if(refsel1 > CFM_CLK_REFSEL1_MASK)
        return ERROR_INVALID_REF_SEL1;

    if(monSEL > CFM_CLK_MONSEL_MASK)
        return ERROR_INVALID_CHANNEL_DRIVE_CLK_MONITOR;


    CFM_REG->clkselReg |= (clkSel & CFM_CLK_SEL_MASK);

    if(refsel0)
        CFM_REG->clkselReg |= (uint32_t)(refsel0 << CFM_CLK_REFSEL0SHIFT);

    if(refsel1)
        CFM_REG->clkselReg |= (uint32_t)(refsel1 << CFM_CLK_REFSEL1SHIFT);

    if(monSEL)
        CFM_REG->clkselReg |= (uint32_t)(monSEL << CFM_CLK_MONSEL_SHIFT);


    if(monEN)
        CFM_REG->clkselReg |= (uint32_t)(monEN << CFM_CLK_MONEN_SHIFT);


    return CFM_OK;

}


void MSS_CFM_runtime_register(uint32_t  referenceCount)
{

    /*Sets how many runtime reference clock cycles the frequency and time
     * measurement shold be made for.. */
    CFM_REG->runtimeReg = (referenceCount & CFM_RUNTIME_REG_MASK);

    return;
}


void MSS_CFM_channel_mode(cfmChannelMode  chMode)
{


    uint32_t chConfiguration = 0;

    chConfiguration |= (chMode.channel0 & CFM_CHANNEL_MODE_MASK) << CFM_CH0_SHIFT_MASK;
    chConfiguration |= (chMode.channel1 & CFM_CHANNEL_MODE_MASK) << CFM_CH1_SHIFT_MASK;
    chConfiguration |= (chMode.channel2 & CFM_CHANNEL_MODE_MASK) << CFM_CH2_SHIFT_MASK;
    chConfiguration |= (chMode.channel3 & CFM_CHANNEL_MODE_MASK) << CFM_CH3_SHIFT_MASK;
    chConfiguration |= (chMode.channel4 & CFM_CHANNEL_MODE_MASK) << CFM_CH4_SHIFT_MASK;
    chConfiguration |= (chMode.channel5 & CFM_CHANNEL_MODE_MASK) << CFM_CH5_SHIFT_MASK;
    chConfiguration |= (chMode.channel6 & CFM_CHANNEL_MODE_MASK) << CFM_CH6_SHIFT_MASK;
    chConfiguration |= (chMode.channel7 & CFM_CHANNEL_MODE_MASK) << CFM_CH7_SHIFT_MASK;

    CFM_REG->modelReg = chConfiguration;


    return;
}

cfm_error_id_t MSS_CFM_get_count(cfm_count_id_t ch, uint32_t *count)
{

    if(count == NULL)
        return ERROR_NULL_VALUE;

    *count = 0;

    if(CFM_REG->controlReg & CFM_CONTROL_REG_BUSY_MASK)
        return ERROR_INVALID_CFM_BUSY;

    switch(ch)
    {
        case CFM_COUNT_0:
            *count = CFM_REG->count0;
            break;

        case CFM_COUNT_1:
            *count = CFM_REG->count1;
            break;

        case CFM_COUNT_2:
            *count = CFM_REG->count2;
            break;

        case CFM_COUNT_3:
            *count = CFM_REG->count3;
            break;

        case CFM_COUNT_4:
            *count = CFM_REG->count4;
            break;

        case CFM_COUNT_5:
            *count = CFM_REG->count5;
            break;

        case CFM_COUNT_6:
            *count = CFM_REG->count6;
            break;

        case CFM_COUNT_7:
            *count = CFM_REG->count7;
            break;

        default:
            return 11;


    }

    return CFM_OK;

}
