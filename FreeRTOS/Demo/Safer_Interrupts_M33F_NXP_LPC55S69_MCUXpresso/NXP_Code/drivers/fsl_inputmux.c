/*
 * Copyright (c) 2016, Freescale Semiconductor, Inc.
 * Copyright 2016-2021 NXP
 * All rights reserved.
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

#include "fsl_inputmux.h"

/*******************************************************************************
 * Definitions
 ******************************************************************************/

/* Component ID definition, used by tools. */
#ifndef FSL_COMPONENT_ID
#define FSL_COMPONENT_ID "platform.drivers.inputmux"
#endif

/*******************************************************************************
 * Code
 ******************************************************************************/

/*!
 * brief	Initialize INPUTMUX peripheral.

 * This function enables the INPUTMUX clock.
 *
 * param base Base address of the INPUTMUX peripheral.
 *
 * retval None.
 */
void INPUTMUX_Init(INPUTMUX_Type *base)
{
#if !(defined(FSL_SDK_DISABLE_DRIVER_CLOCK_CONTROL) && FSL_SDK_DISABLE_DRIVER_CLOCK_CONTROL)
#if defined(FSL_FEATURE_INPUTMUX_HAS_NO_INPUTMUX_CLOCK_SOURCE) && FSL_FEATURE_INPUTMUX_HAS_NO_INPUTMUX_CLOCK_SOURCE
    CLOCK_EnableClock(kCLOCK_Sct);
    CLOCK_EnableClock(kCLOCK_Dma);
#else
    CLOCK_EnableClock(kCLOCK_InputMux);
#endif /* FSL_FEATURE_INPUTMUX_HAS_NO_INPUTMUX_CLOCK_SOURCE */
#endif /* FSL_SDK_DISABLE_DRIVER_CLOCK_CONTROL */
}

/*!
 * brief Attaches a signal
 *
 * This function gates the INPUTPMUX clock.
 *
 * param base Base address of the INPUTMUX peripheral.
 * param index Destination peripheral to attach the signal to.
 * param connection Selects connection.
 *
 * retval None.
 */
void INPUTMUX_AttachSignal(INPUTMUX_Type *base, uint32_t index, inputmux_connection_t connection)
{
    uint32_t pmux_id;
    uint32_t output_id;

    /* extract pmux to be used */
    pmux_id = ((uint32_t)(connection)) >> PMUX_SHIFT;
    /*  extract function number */
    output_id = ((uint32_t)(connection)) & ((1UL << PMUX_SHIFT) - 1U);
    /* programm signal */
    *(volatile uint32_t *)(((uint32_t)base) + pmux_id + (index * 4U)) = output_id;
}

#if defined(FSL_FEATURE_INPUTMUX_HAS_SIGNAL_ENA)
/*!
 * brief Enable/disable a signal
 *
 * This function gates the INPUTPMUX clock.
 *
 * param base Base address of the INPUTMUX peripheral.
 * param signal Enable signal register id and bit offset.
 * param enable Selects enable or disable.
 *
 * retval None.
 */
void INPUTMUX_EnableSignal(INPUTMUX_Type *base, inputmux_signal_t signal, bool enable)
{
    uint32_t ena_id;
    uint32_t ena_id_mask = (1UL << (32U - ENA_SHIFT)) - 1U;
    uint32_t bit_offset;

#if defined(FSL_FEATURE_INPUTMUX_HAS_CHANNEL_MUX) && FSL_FEATURE_INPUTMUX_HAS_CHANNEL_MUX
    uint32_t chmux_offset;
    uint32_t chmux_value;

    /* Only enable need to update channel mux */
    if (enable && ((((uint32_t)signal) & (1UL << CHMUX_AVL_SHIFT)) != 0U))
    {
        chmux_offset = (((uint32_t)signal) >> CHMUX_OFF_SHIFT) & ((1UL << (CHMUX_AVL_SHIFT - CHMUX_OFF_SHIFT)) - 1UL);
        chmux_value  = (((uint32_t)signal) >> CHMUX_VAL_SHIFT) & ((1UL << (CHMUX_OFF_SHIFT - CHMUX_VAL_SHIFT)) - 1UL);
        *(volatile uint32_t *)(((uint32_t)base) + chmux_offset) = chmux_value;
    }
    ena_id_mask = (1UL << (CHMUX_VAL_SHIFT - ENA_SHIFT)) - 1U;
#endif
    /* extract enable register to be used */
    ena_id = (((uint32_t)signal) >> ENA_SHIFT) & ena_id_mask;
    /* extract enable bit offset */
    bit_offset = ((uint32_t)signal) & ((1UL << ENA_SHIFT) - 1U);
    /* set signal */
    if (enable)
    {
        *(volatile uint32_t *)(((uint32_t)base) + ena_id) |= (1UL << bit_offset);
    }
    else
    {
        *(volatile uint32_t *)(((uint32_t)base) + ena_id) &= ~(1UL << bit_offset);
    }
}
#endif

/*!
 * brief	Deinitialize INPUTMUX peripheral.

 * This function disables the INPUTMUX clock.
 *
 * param base Base address of the INPUTMUX peripheral.
 *
 * retval None.
 */
void INPUTMUX_Deinit(INPUTMUX_Type *base)
{
#if !(defined(FSL_SDK_DISABLE_DRIVER_CLOCK_CONTROL) && FSL_SDK_DISABLE_DRIVER_CLOCK_CONTROL)
#if defined(FSL_FEATURE_INPUTMUX_HAS_NO_INPUTMUX_CLOCK_SOURCE) && FSL_FEATURE_INPUTMUX_HAS_NO_INPUTMUX_CLOCK_SOURCE
    CLOCK_DisableClock(kCLOCK_Sct);
    CLOCK_DisableClock(kCLOCK_Dma);
#else
    CLOCK_DisableClock(kCLOCK_InputMux);
#endif /* FSL_FEATURE_INPUTMUX_HAS_NO_INPUTMUX_CLOCK_SOURCE */
#endif /* FSL_SDK_DISABLE_DRIVER_CLOCK_CONTROL */
}
