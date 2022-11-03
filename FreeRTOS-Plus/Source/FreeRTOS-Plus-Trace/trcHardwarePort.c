/*
 * Trace Recorder for Tracealyzer v4.6.0
 * Copyright 2021 Percepio AB
 * www.percepio.com
 *
 * SPDX-License-Identifier: Apache-2.0
 *
 * The hardware abstraction layer for the trace recorder.
 */

#include <trcRecorder.h>

#if (TRC_USE_TRACEALYZER_RECORDER == 1)

/* If using DWT timestamping (default on ARM Cortex-M3, M4 and M7), make sure the DWT unit is initialized. */
#if ((TRC_CFG_HARDWARE_PORT == TRC_HARDWARE_PORT_ARM_Cortex_M) && (defined (__CORTEX_M) && (__CORTEX_M >= 0x03)))
#if (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING)
#ifndef TRC_CFG_ARM_CM_USE_SYSTICK

void xTraceHardwarePortInitCortexM()
{
	/* Make sure the DWT registers are unlocked, in case the debugger doesn't do this. */
	TRC_REG_ITM_LOCKACCESS = TRC_ITM_LOCKACCESS_UNLOCK;

	/* Make sure DWT is enabled is enabled, if supported */
	TRC_REG_DEMCR |= TRC_DEMCR_TRCENA;

	do
	{
		/* Verify that DWT is supported */
		if (TRC_REG_DEMCR == 0)
		{
			/* This function is called on Cortex-M3, M4 and M7 devices to initialize
			the DWT unit, assumed present. The DWT cycle counter is used for timestamping.

			If the below error is produced, the DWT unit does not seem to be available.

			In that case, define the macro TRC_CFG_ARM_CM_USE_SYSTICK in your build
			to use SysTick timestamping instead, or define your own timestamping by
			setting TRC_CFG_HARDWARE_PORT to TRC_HARDWARE_PORT_APPLICATION_DEFINED
			and make the necessary definitions, as explained in trcHardwarePort.h.*/

			xTraceError(TRC_ERROR_DWT_NOT_SUPPORTED);
			break;
		}

		/* Verify that DWT_CYCCNT is supported */
		if (TRC_REG_DWT_CTRL & TRC_DWT_CTRL_NOCYCCNT)
		{
			/* This function is called on Cortex-M3, M4 and M7 devices to initialize
			the DWT unit, assumed present. The DWT cycle counter is used for timestamping.

			If the below error is produced, the cycle counter does not seem to be available.

			In that case, define the macro TRC_CFG_ARM_CM_USE_SYSTICK in your build
			to use SysTick timestamping instead, or define your own timestamping by
			setting TRC_CFG_HARDWARE_PORT to TRC_HARDWARE_PORT_APPLICATION_DEFINED
			and make the necessary definitions, as explained in trcHardwarePort.h.*/

			xTraceError(TRC_ERROR_DWT_CYCCNT_NOT_SUPPORTED);
			break;
		}

		/* Reset the cycle counter */
		TRC_REG_DWT_CYCCNT = 0;

		/* Enable the cycle counter */
		TRC_REG_DWT_CTRL |= TRC_DWT_CTRL_CYCCNTENA;

	} while (0);	/* breaks above jump here */
}
#endif /* TRC_CFG_ARM_CM_USE_SYSTICK */

#endif /* (TRC_CFG_RECORDER_MODE == TRC_RECORDER_MODE_STREAMING) */
#endif /* ((TRC_CFG_HARDWARE_PORT == TRC_HARDWARE_PORT_ARM_Cortex_M) && (defined (__CORTEX_M) && (__CORTEX_M >= 0x03))) */

#if ((TRC_CFG_HARDWARE_PORT == TRC_HARDWARE_PORT_ARM_CORTEX_A9) || (TRC_CFG_HARDWARE_PORT == TRC_HARDWARE_PORT_XILINX_ZyncUltraScaleR5) || (TRC_CFG_HARDWARE_PORT == TRC_HARDWARE_PORT_CYCLONE_V_HPS))

#define CS_TYPE_NONE 0
#define CS_TYPE_TASK 1
#define CS_TYPE_ISR_MASK_CHANGED 2
#define CS_TYPE_ISR_MASK_NOT_CHANGED 3

#define CS_TYPE_INVALID 0xFFFFFFFF

int cortex_a9_r5_enter_critical(void)
{
	uint32_t cs_type = CS_TYPE_INVALID;

    if ((prvGetCPSR() & 0x001F) == 0x13) // CSPR (ASPR) mode = SVC
    {
    	/* Executing in an ISR other than the context-switch (where interrupts might have been enabled, motivating a critical section). */
    	if (ulPortSetInterruptMask() == pdTRUE)
    	{
    		cs_type = CS_TYPE_ISR_MASK_NOT_CHANGED;
    	}
    	else
    	{
    		cs_type = CS_TYPE_ISR_MASK_CHANGED;
    	}
    }
    else if (pxTraceRecorderData->uiTraceSystemState == TRC_STATE_IN_TASKSWITCH)
    {
    	// In the context-switch code. All interrupts are already masked here, so don't modify the mask.
    	cs_type = CS_TYPE_NONE;
    }
    else if (pxTraceRecorderData->uiTraceSystemState != TRC_STATE_IN_TASKSWITCH)
    {
    	// Not within ISR or task-switch context, use a regular critical section.
    	vPortEnterCritical();
    	cs_type = CS_TYPE_TASK;
    }

	return cs_type;
}

void cortex_a9_r5_exit_critical(int cs_type)
{
	switch (cs_type)
	{
		case CS_TYPE_TASK:
			vPortExitCritical();
			break;

		case CS_TYPE_ISR_MASK_CHANGED:
			vPortClearInterruptMask(pdFALSE);	// pdFALSE means it will reset the IRQ mask.
			break;

		case CS_TYPE_ISR_MASK_NOT_CHANGED:
		case CS_TYPE_NONE:
			// No action in these two cases.
			break;

		default:
			// Error, should not be possible;
			for (;;);
	}
}
#endif /* ((TRC_CFG_HARDWARE_PORT == TRC_HARDWARE_PORT_ARM_CORTEX_A9) || (TRC_CFG_HARDWARE_PORT == TRC_HARDWARE_PORT_XILINX_ZyncUltraScaleR5)) */

#endif /* (TRC_USE_TRACEALYZER_RECORDER == 1) */
