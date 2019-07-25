/******************************************************************************
 *
 * Copyright 2013 Altera Corporation. All Rights Reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 
 * 1. Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following disclaimer.
 * 
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 * 
 * 3. The name of the author may not be used to endorse or promote products
 * derived from this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE, ARE DISCLAIMED. IN NO
 * EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS;
 * OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR
 * OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
 * ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * 
 ******************************************************************************/

#include "alt_16550_uart.h"
#include "alt_clock_manager.h"
#include "socal/alt_rstmgr.h"
#include "socal/alt_uart.h"
#include "socal/hps.h"
#include "socal/socal.h"

/////

#define ALT_16550_HANDLE_DATA_UART_ENABLED_MSK   (1UL << 31)
#define ALT_16550_HANDLE_DATA_DIVISOR_VALUE_GET(value) (value & 0xffff)

#define ALT_ALTERA_16550_CPR_OFST        (0xF4)
#define ALT_ALTERA_16550_CPR_ADDR(base)  ALT_CAST(void *, (ALT_CAST(char *, (base)) + ALT_ALTERA_16550_CPR_OFST))
#define ALT_ALTERA_16550_CPR_FIFO_MODE_GET(value) (((value) >> 16) & 0xff)
#define ALT_ALTERA_16550_CPR_AFCE_MODE_SET_MSK (1 << 4)

/////

// Remove these macros as part of case:123835.
#define ALT_UART_IER_DLH_VALUE_SET(value) ((value) & 0xff)
#define ALT_UART_IER_DLH_ETBEI_DLH1_SET_MSK ALT_UART_IER_DLH_ETBEI_DLHL_SET_MSK

/////

//
// Helper function which resets the UART and if requested, initializes the UART
// to the default settings. Currently the default settings are:
//  - 8 databits
//  - no parity
//  - 1 stopbit
//  - 57600 baudrate
// The reset routines depends on the hardware implementation of the UART.
//

// This helper is needed because the regular alt_read_word(src) essentially
// resolves to "*(volatile uint32_t *)src". As there is no assignment, this
// could potentially be optimized away. With the helper, the actual register
// read should occur and be returned (and subsequently discarded).
static inline uint32_t alt_read_word_helper(const void * addr)
{
    return alt_read_word(addr);
}

//
// Helper function write the divisor in hardware.
//
static ALT_STATUS_CODE alt_16550_write_divisor_helper(ALT_16550_HANDLE_t * handle,
                                                      uint32_t divisor)
{
    // Validate the divisor parameter.
    if (divisor > 0xffff)
    {
        // This should never happen as it is verified in divisor_set.
        return ALT_E_ERROR;
    }

    switch (handle->device)
    {
    case ALT_16550_DEVICE_SOCFPGA_UART0:
    case ALT_16550_DEVICE_SOCFPGA_UART1:
    case ALT_16550_DEVICE_ALTERA_16550_UART:
        // Set LCR::DLAB (Line Control Register :: Divisor Latch Access Bit)
        alt_setbits_word(ALT_UART_LCR_ADDR(handle->location), ALT_UART_LCR_DLAB_SET_MSK);

        // Write DLL (Divisor Latch Low).
        alt_write_word(ALT_UART_RBR_THR_DLL_ADDR(handle->location), ALT_UART_RBR_THR_DLL_VALUE_SET(divisor));

        // Write DLH (Divisor Latch High).
        alt_write_word(ALT_UART_IER_DLH_ADDR(handle->location), ALT_UART_IER_DLH_VALUE_SET(divisor >> 8));

        // Clear LCR::DLAB (Line Control Register :: Divisor Latch Access Bit)
        alt_clrbits_word(ALT_UART_LCR_ADDR(handle->location), ALT_UART_LCR_DLAB_SET_MSK);

        break;

    default:
        return ALT_E_ERROR;
    }

    // Update the enabled state in the handle data.
    if (divisor != 0)
    {
        handle->data |= ALT_16550_HANDLE_DATA_UART_ENABLED_MSK;
    }
    else
    {
        handle->data &= ~ALT_16550_HANDLE_DATA_UART_ENABLED_MSK;
    }

    return ALT_E_SUCCESS;
}

//
// Helper function to reset the UART.
//
static ALT_STATUS_CODE alt_16550_reset_helper(ALT_16550_HANDLE_t * handle, bool enable_init)
{
    switch (handle->device)
    {
    case ALT_16550_DEVICE_SOCFPGA_UART0:
    case ALT_16550_DEVICE_SOCFPGA_UART1:
        // Write SRR::UR (Shadow Reset Register :: UART Reset)
        alt_write_word(ALT_UART_SRR_ADDR(handle->location), ALT_UART_SRR_UR_SET_MSK);

        // Read the MSR to work around case:119085.
        alt_read_word_helper(ALT_UART_MSR_ADDR(handle->location));
        break;

    case ALT_16550_DEVICE_ALTERA_16550_UART:
        alt_16550_write_divisor_helper(handle, 0); // Disable UART
        alt_16550_int_disable_all(handle);         // Disable interrupts
        alt_16550_fifo_disable(handle);            // Disable FIFOs
        alt_write_word(ALT_UART_MCR_ADDR(handle->location), 0); // 0 -> MCR (AFCE, LP, OUT2, OUT1, RTS, DTR)
        break;

    default:
        return ALT_E_ERROR;
    }

    // If we are initializing (as opposed to just uninitializing)
    if (enable_init)
    {
        ALT_STATUS_CODE status;

        // Set bit IER::PTIME (Interrupt Enable Register :: Programmable THRE Mode Enable)
        alt_setbits_word(ALT_UART_IER_DLH_ADDR(handle->location), ALT_UART_IER_DLH_PTIME_DLH7_SET_MSK);

        // Set the line configuration to use 8-N-1.
        status = alt_16550_line_config_set(handle, ALT_16550_DATABITS_8,
                                                   ALT_16550_PARITY_DISABLE,
                                                   ALT_16550_STOPBITS_1);
        if (status != ALT_E_SUCCESS)
        {
            return status;
        }

        uint32_t divisor = ALT_16550_HANDLE_DATA_DIVISOR_VALUE_GET(handle->data);
        if (divisor == 0)
        {
            // Set the default baudrate to 57600.
            status = alt_16550_baudrate_set(handle, ALT_16550_BAUDRATE_57600);
            if (status != ALT_E_SUCCESS)
            {
                return status;
            }
        }
    }

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_16550_init(ALT_16550_DEVICE_t device,
                               void * location,
                               alt_freq_t clock_freq,
                               ALT_16550_HANDLE_t * handle)
{
    handle->device = device;
    handle->data   = 0;
    handle->fcr    = 0;

    switch (device)
    {
    case ALT_16550_DEVICE_SOCFPGA_UART0:
    case ALT_16550_DEVICE_SOCFPGA_UART1:
        // The ALT_CLK_L4_SP is required for all SoCFPGA UARTs. Check that it's enabled.
        if (alt_clk_is_enabled(ALT_CLK_L4_SP) != ALT_E_TRUE)
        {
            return ALT_E_BAD_CLK;
        }
        else
        {
            ALT_STATUS_CODE status;
            status = alt_clk_freq_get(ALT_CLK_L4_SP, &handle->clock_freq);
            if (status != ALT_E_SUCCESS)
            {
                return status;
            }

            if (device == ALT_16550_DEVICE_SOCFPGA_UART0)
            {
                handle->location = ALT_UART0_ADDR;

                // Bring UART0 out of reset.
                alt_clrbits_word(ALT_RSTMGR_PERMODRST_ADDR, ALT_RSTMGR_PERMODRST_UART0_SET_MSK);
            }
            else // device == ALT_16550_DEVICE_SOCFPGA_UART1
            {
                handle->location = ALT_UART1_ADDR;

                // Bring UART1 out of reset.
                alt_clrbits_word(ALT_RSTMGR_PERMODRST_ADDR, ALT_RSTMGR_PERMODRST_UART1_SET_MSK);
            } 

            // Verify the UCR (UART Component Version)
            uint32_t ucr = alt_read_word(ALT_UART_UCV_ADDR(handle->location));
            if (ucr != ALT_UART_UCV_UART_COMPONENT_VER_RESET)
            {
                return ALT_E_ERROR;
            }
        }
        break;
    case ALT_16550_DEVICE_ALTERA_16550_UART:
        handle->location   = location;
        handle->clock_freq = clock_freq;
        break;
    default:
        return ALT_E_BAD_ARG;
    }

    return alt_16550_reset_helper(handle, true);
}

ALT_STATUS_CODE alt_16550_uninit(ALT_16550_HANDLE_t * handle)
{
    switch (handle->device)
    {
    case ALT_16550_DEVICE_SOCFPGA_UART0:
        alt_setbits_word(ALT_RSTMGR_PERMODRST_ADDR, ALT_RSTMGR_PERMODRST_UART0_SET_MSK);
        return ALT_E_SUCCESS;
    case ALT_16550_DEVICE_SOCFPGA_UART1:
        alt_setbits_word(ALT_RSTMGR_PERMODRST_ADDR, ALT_RSTMGR_PERMODRST_UART1_SET_MSK);
        return ALT_E_SUCCESS;
    case ALT_16550_DEVICE_ALTERA_16550_UART:
    default:
        return alt_16550_reset_helper(handle, false);
    }
}

ALT_STATUS_CODE alt_16550_reset(ALT_16550_HANDLE_t * handle)
{
    return alt_16550_reset_helper(handle, true);
}

ALT_STATUS_CODE alt_16550_enable(ALT_16550_HANDLE_t * handle)
{
    // Write the divisor cached in the handle data to the divisor registers.
    // This will effectively enable the UART.
    return alt_16550_write_divisor_helper(handle,
                                          ALT_16550_HANDLE_DATA_DIVISOR_VALUE_GET(handle->data));
}

ALT_STATUS_CODE alt_16550_disable(ALT_16550_HANDLE_t * handle)
{
    // Write 0 to the divisor the divisor registers. This will effectively
    // disable the UART.
    return alt_16550_write_divisor_helper(handle, 0);
}

ALT_STATUS_CODE alt_16550_read(ALT_16550_HANDLE_t * handle,
                               char * item)
{
    // Verify that the UART is enabled
    if (!(handle->data & ALT_16550_HANDLE_DATA_UART_ENABLED_MSK))
    {
        return ALT_E_ERROR;
    }

    // Verify that the FIFO is disabled
    if (handle->fcr & ALT_UART_FCR_FIFOE_SET_MSK)
    {
        return ALT_E_ERROR;
    }

    switch (handle->device)
    {
    case ALT_16550_DEVICE_SOCFPGA_UART0:
    case ALT_16550_DEVICE_SOCFPGA_UART1:
    case ALT_16550_DEVICE_ALTERA_16550_UART:
        // Read the RBR (Receive Buffer Register) into *item.
        *item = ALT_UART_RBR_THR_DLL_VALUE_GET(alt_read_word(ALT_UART_RBR_THR_DLL_ADDR(handle->location)));
        break;
    default:
        return ALT_E_ERROR;
    }
    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_16550_write(ALT_16550_HANDLE_t * handle,
                                char item)
{
    // Verify that the UART is enabled
    if (!(handle->data & ALT_16550_HANDLE_DATA_UART_ENABLED_MSK))
    {
        return ALT_E_ERROR;
    }

    // Verify that the FIFO is disabled
    if (handle->fcr & ALT_UART_FCR_FIFOE_SET_MSK)
    {
        return ALT_E_ERROR;
    }

    switch (handle->device)
    {
    case ALT_16550_DEVICE_SOCFPGA_UART0:
    case ALT_16550_DEVICE_SOCFPGA_UART1:
    case ALT_16550_DEVICE_ALTERA_16550_UART:
        // Write the buffer into the THR (Transmit Holding Register)
        alt_write_word(ALT_UART_RBR_THR_DLL_ADDR(handle->location), item);
        break;
    default:
        return ALT_E_ERROR;
    }

    return ALT_E_SUCCESS;
}

/////

ALT_STATUS_CODE alt_16550_fifo_enable(ALT_16550_HANDLE_t * handle)
{
    switch (handle->device)
    {
    case ALT_16550_DEVICE_SOCFPGA_UART0:
    case ALT_16550_DEVICE_SOCFPGA_UART1:
    case ALT_16550_DEVICE_ALTERA_16550_UART:
        // Set FCR::FIFOE (FIFO Control Register :: FIFO Enable) bit.
        handle->fcr |= ALT_UART_FCR_FIFOE_SET_MSK;
        alt_write_word(ALT_UART_FCR_ADDR(handle->location), handle->fcr);
        break;
    default:
        return ALT_E_ERROR;
    }

    // No need to reset / clear the FIFOs. This is done automatically when
    // FCR::FIFOE is changed.
    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_16550_fifo_disable(ALT_16550_HANDLE_t * handle)
{
    switch (handle->device)
    {
    case ALT_16550_DEVICE_SOCFPGA_UART0:
    case ALT_16550_DEVICE_SOCFPGA_UART1:
    case ALT_16550_DEVICE_ALTERA_16550_UART:
        // Clear FCR::FIFOE (FIFO Control Register :: FIFO Enable) bit.
        handle->fcr &= ~ALT_UART_FCR_FIFOE_SET_MSK;
        alt_write_word(ALT_UART_FCR_ADDR(handle->location), handle->fcr);
        break;
    default:
        return ALT_E_ERROR;
    }

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_16550_fifo_read(ALT_16550_HANDLE_t * handle,
                                    char * buffer,
                                    size_t count)
{
    // Verify that the UART is enabled
    if (!(handle->data & ALT_16550_HANDLE_DATA_UART_ENABLED_MSK))
    {
        return ALT_E_ERROR;
    }

    // Verify that the FIFO is enabled
    if (!(handle->fcr & ALT_UART_FCR_FIFOE_SET_MSK))
    {
        return ALT_E_ERROR;
    }

    switch (handle->device)
    {
    case ALT_16550_DEVICE_SOCFPGA_UART0:
    case ALT_16550_DEVICE_SOCFPGA_UART1:
    case ALT_16550_DEVICE_ALTERA_16550_UART:
        // Read the RBR (Receive Buffer Register) into the buffer
        for (size_t i = 0; i < count; ++i)
        {
            buffer[i] = ALT_UART_RBR_THR_DLL_VALUE_GET(alt_read_word(ALT_UART_RBR_THR_DLL_ADDR(handle->location)));
        }
        break;
    default:
        return ALT_E_ERROR;
    }

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_16550_fifo_write(ALT_16550_HANDLE_t * handle,
                                     const char * buffer,
                                     size_t count)
{
    // Verify that the UART is enabled
    if (!(handle->data & ALT_16550_HANDLE_DATA_UART_ENABLED_MSK))
    {
        return ALT_E_ERROR;
    }

    // Verify that the FIFO is enabled
    if (!(handle->fcr & ALT_UART_FCR_FIFOE_SET_MSK))
    {
        return ALT_E_ERROR;
    }

    switch (handle->device)
    {
    case ALT_16550_DEVICE_SOCFPGA_UART0:
    case ALT_16550_DEVICE_SOCFPGA_UART1:
    case ALT_16550_DEVICE_ALTERA_16550_UART:
        // Write the buffer into the THR (Transmit Holding Register)
        for (size_t i = 0; i < count; ++i)
        {
            alt_write_word(ALT_UART_RBR_THR_DLL_ADDR(handle->location), buffer[i]);
        }
        break;
    default:
        return ALT_E_ERROR;
    }

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_16550_fifo_clear_rx(ALT_16550_HANDLE_t * handle)
{
    // Verify that the FIFO is enabled
    if (!(handle->fcr & ALT_UART_FCR_FIFOE_SET_MSK))
    {
        return ALT_E_ERROR;
    }

    switch (handle->device)
    {
    case ALT_16550_DEVICE_SOCFPGA_UART0:
    case ALT_16550_DEVICE_SOCFPGA_UART1:
        // Write SRR::RFR (Shadow Reset Register :: Receiver FIFO Reset) bit.
        alt_write_word(ALT_UART_SRR_ADDR(handle->location), ALT_UART_SRR_RFR_SET_MSK);
        break;
    case ALT_16550_DEVICE_ALTERA_16550_UART:
        // Write FCR::RFIFOR (FIFO Control Register :: Receiver FIFO Reset) bit.
        alt_write_word(ALT_UART_FCR_ADDR(handle->location), handle->fcr | ALT_UART_FCR_RFIFOR_SET_MSK);
        break;
    default:
        return ALT_E_ERROR;
    }

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_16550_fifo_clear_tx(ALT_16550_HANDLE_t * handle)
{
    // Verify that the FIFO is enabled
    if (!(handle->fcr & ALT_UART_FCR_FIFOE_SET_MSK))
    {
        return ALT_E_ERROR;
    }

    switch (handle->device)
    {
    case ALT_16550_DEVICE_SOCFPGA_UART0:
    case ALT_16550_DEVICE_SOCFPGA_UART1:
        // Write SRR::XFR (Shadow Reset Register :: Xmitter FIFO Reset) bit.
        alt_write_word(ALT_UART_SRR_ADDR(handle->location), ALT_UART_SRR_XFR_SET_MSK);
        break;
    case ALT_16550_DEVICE_ALTERA_16550_UART:
        // Write FCR::XFIFOR (FIFO Control Register :: Xmitter FIFO Reset) bit.
        alt_write_word(ALT_UART_FCR_ADDR(handle->location), handle->fcr | ALT_UART_FCR_XFIFOR_SET_MSK);
        break;
    default:
        return ALT_E_ERROR;
    }

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_16550_fifo_clear_all(ALT_16550_HANDLE_t * handle)
{
    // Verify that the FIFO is enabled
    if (!(handle->fcr & ALT_UART_FCR_FIFOE_SET_MSK))
    {
        return ALT_E_ERROR;
    }

    switch (handle->device)
    {
    case ALT_16550_DEVICE_SOCFPGA_UART0:
    case ALT_16550_DEVICE_SOCFPGA_UART1:
        // Write SRR::(RFR | XFR)
        //   (Shadow Reset Register :: (Receiver FIFO Reset | Xmitter FIFO Reset)) bits.
        alt_write_word(ALT_UART_SRR_ADDR(handle->location),
                       ALT_UART_SRR_RFR_SET_MSK | ALT_UART_SRR_XFR_SET_MSK);
        break;
    case ALT_16550_DEVICE_ALTERA_16550_UART:
        // Write FCR::(RFIFOR |XFIFOR)
        //   (FIFO Control Register :: (Receiver FIFO Reset | Xmitter FIFO Reset)) bits.
        alt_write_word(ALT_UART_FCR_ADDR(handle->location),
                       handle->fcr | ALT_UART_FCR_RFIFOR_SET_MSK | ALT_UART_FCR_XFIFOR_SET_MSK);
        break;
    default:
        return ALT_E_ERROR;
    }

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_16550_fifo_size_get_rx(ALT_16550_HANDLE_t * handle,
                                           uint32_t * size)
{
    switch (handle->device)
    {
    case ALT_16550_DEVICE_SOCFPGA_UART0:
    case ALT_16550_DEVICE_SOCFPGA_UART1:
        // Read the CPR::FIFO_Mod (Component Parameter Register :: FIFO Mode).
        // The FIFO size is 16x this value.
        *size = ALT_UART_CPR_FIFO_MOD_GET(alt_read_word(ALT_UART_CPR_ADDR(handle->location))) << 4;
        break;
    case ALT_16550_DEVICE_ALTERA_16550_UART:
        // Altera 16550 Compatible Soft UARTs have a configurable size and is
        // stored in the CPR::FIFO_Mode (Component Parameter Register :: FIFO Depth).
        *size = ALT_ALTERA_16550_CPR_FIFO_MODE_GET(alt_read_word(ALT_ALTERA_16550_CPR_ADDR(handle->location))) << 4;
        break;
    default:
        return ALT_E_ERROR;
    }

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_16550_fifo_size_get_tx(ALT_16550_HANDLE_t * handle,
                                           uint32_t * size)
{
    switch (handle->device)
    {
    case ALT_16550_DEVICE_SOCFPGA_UART0:
    case ALT_16550_DEVICE_SOCFPGA_UART1:
        // Read the CPR::FIFO_Mod (Component Parameter Register :: FIFO Mode).
        // The FIFO size is 16x this value.
        *size = ALT_UART_CPR_FIFO_MOD_GET(alt_read_word(ALT_UART_CPR_ADDR(handle->location))) << 4;
        break;
    case ALT_16550_DEVICE_ALTERA_16550_UART:
        // Altera 16550 Compatible Soft UARTs have a configurable size and is
        // stored in the CPR::FIFO_Mode (Component Parameter Register :: FIFO Depth).
        // The FIFO size is 16x this value.
        *size = ALT_ALTERA_16550_CPR_FIFO_MODE_GET(alt_read_word(ALT_ALTERA_16550_CPR_ADDR(handle->location))) << 4;
        break;
    default:
        return ALT_E_ERROR;
    }

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_16550_fifo_level_get_rx(ALT_16550_HANDLE_t * handle,
                                            uint32_t * level)
{
    // Verify that the FIFO is enabled
    if (!(handle->fcr & ALT_UART_FCR_FIFOE_SET_MSK))
    {
        return ALT_E_ERROR;
    }

    switch (handle->device)
    {
    case ALT_16550_DEVICE_SOCFPGA_UART0:
    case ALT_16550_DEVICE_SOCFPGA_UART1:
        // Read RFL (Receive FIFO Level).
        *level = alt_read_word(ALT_UART_RFL_ADDR(handle->location));
        break;
    case ALT_16550_DEVICE_ALTERA_16550_UART:
        // RFL not implemented. Return 0.
        *level = 0;
        break;
    default:
        return ALT_E_ERROR;
    }

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_16550_fifo_level_get_tx(ALT_16550_HANDLE_t * handle,
                                            uint32_t * level)
{
    // Verify that the FIFO is enabled
    if (!(handle->fcr & ALT_UART_FCR_FIFOE_SET_MSK))
    {
        return ALT_E_ERROR;
    }

    switch (handle->device)
    {
    case ALT_16550_DEVICE_SOCFPGA_UART0:
    case ALT_16550_DEVICE_SOCFPGA_UART1:
        // Read TFL (Transmit FIFO Level).
        *level = alt_read_word(ALT_UART_TFL_ADDR(handle->location));
        break;
    case ALT_16550_DEVICE_ALTERA_16550_UART:
        // TFL not implemented. Return 0.
        *level = 0;
        break;
    default:
        return ALT_E_ERROR;
    }

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_16550_fifo_trigger_set_rx(ALT_16550_HANDLE_t * handle,
                                              ALT_16550_FIFO_TRIGGER_RX_t trigger)
{
    // Verify that the FIFO is enabled
    if (!(handle->fcr & ALT_UART_FCR_FIFOE_SET_MSK))
    {
        return ALT_E_ERROR;
    }

    // Verify triggering parameter
    switch (trigger)
    {
    case ALT_16550_FIFO_TRIGGER_RX_ANY:
    case ALT_16550_FIFO_TRIGGER_RX_QUARTER_FULL:
    case ALT_16550_FIFO_TRIGGER_RX_HALF_FULL:
    case ALT_16550_FIFO_TRIGGER_RX_ALMOST_FULL:
        break;
    default:
        return ALT_E_BAD_ARG;
    }

    switch (handle->device)
    {
    case ALT_16550_DEVICE_SOCFPGA_UART0:
    case ALT_16550_DEVICE_SOCFPGA_UART1:
    case ALT_16550_DEVICE_ALTERA_16550_UART:
        // Update FCR::RT (FIFO Control Register :: Receiver Trigger)
        handle->fcr &= ~ALT_UART_FCR_RT_SET_MSK;
        handle->fcr |= ALT_UART_FCR_RT_SET(trigger);
        alt_write_word(ALT_UART_FCR_ADDR(handle->location), handle->fcr);
        break;
    default:
        return ALT_E_ERROR;
    }

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_16550_fifo_trigger_set_tx(ALT_16550_HANDLE_t * handle,
                                              ALT_16550_FIFO_TRIGGER_TX_t trigger)
{
    // Verify that the FIFO is enabled
    if (!(handle->fcr & ALT_UART_FCR_FIFOE_SET_MSK))
    {
        return ALT_E_ERROR;
    }

    // Verify triggering parameter
    switch (trigger)
    {
    case ALT_16550_FIFO_TRIGGER_TX_EMPTY:
    case ALT_16550_FIFO_TRIGGER_TX_ALMOST_EMPTY:
    case ALT_16550_FIFO_TRIGGER_TX_QUARTER_FULL:
    case ALT_16550_FIFO_TRIGGER_TX_HALF_FULL:
        break;
    default:
        return ALT_E_BAD_ARG;
    }

    switch (handle->device)
    {
    case ALT_16550_DEVICE_SOCFPGA_UART0:
    case ALT_16550_DEVICE_SOCFPGA_UART1:
    case ALT_16550_DEVICE_ALTERA_16550_UART:
        // Update FCR::TET (FIFO Control Register :: Transmit Empty Trigger)
        handle->fcr &= ~ALT_UART_FCR_TET_SET_MSK;
        handle->fcr |= ALT_UART_FCR_TET_SET(trigger);
        alt_write_word(ALT_UART_FCR_ADDR(handle->location), handle->fcr);
        break;
    default:
        return ALT_E_ERROR;
    }

    return ALT_E_SUCCESS;
}

/////

ALT_STATUS_CODE alt_16550_baudrate_get(ALT_16550_HANDLE_t * handle,
                                       uint32_t * baudrate)
{
    // Query the divisor cached in the handle data
    uint32_t divisor = ALT_16550_HANDLE_DATA_DIVISOR_VALUE_GET(handle->data);

    // The divisor should never be zero. It is set to allow for a baud of 57600
    // on initialization and a valid value is checked at
    // alt_16550_divisor_set(). We do not check for users altering the data in
    // the handle structure.

    // Formula for calculating the baudrate:
    //    baudrate = clock / (16 * divisor)

    *baudrate = (handle->clock_freq >> 4) / divisor;

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_16550_baudrate_set(ALT_16550_HANDLE_t * handle,
                                       uint32_t baudrate)
{
    if (baudrate == 0)
    {
        return ALT_E_ARG_RANGE;
    }

    // Formula for calculating the divisor:
    //    baudrate = clock / (16 * divisor)
    // => baudrate * 16 * divisor = clock
    // => divisor = clock / (baudrate * 16)
    // => divisor = (clock / 16) / baudrate

    // Add half of the denominator to address rounding errors.
    uint32_t divisor = ((handle->clock_freq + (8 * baudrate)) / (16 * baudrate));

    // Check for divisor range is in alt_16550_divisor_set().
    return alt_16550_divisor_set(handle, divisor);
}

ALT_STATUS_CODE alt_16550_divisor_get(ALT_16550_HANDLE_t * handle,
                                      uint32_t * divisor)
{
    // Just read the divisor portion of the handle data.
    *divisor = ALT_16550_HANDLE_DATA_DIVISOR_VALUE_GET(handle->data);

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_16550_divisor_set(ALT_16550_HANDLE_t * handle,
                                      uint32_t divisor)
{
    // Verify divisor value is in range.
    if ((divisor > 0xffff) || (divisor == 0))
    {
        return ALT_E_ARG_RANGE;
    }

    // Set the divisor portion of the handle data.
    handle->data &= ~(0xffff);
    handle->data |= divisor;

    // Even if the UART is enabled, don't do anything. It is documented that
    // the change will take effect when the UART move to the enabled state.

    return ALT_E_SUCCESS;
}

/////

static ALT_STATUS_CODE alt_16550_ier_mask_set_helper(ALT_16550_HANDLE_t * handle, uint32_t setmask)
{
    switch (handle->device)
    {
    case ALT_16550_DEVICE_SOCFPGA_UART0:
    case ALT_16550_DEVICE_SOCFPGA_UART1:
    case ALT_16550_DEVICE_ALTERA_16550_UART:
        // Set bit in IER (Interrupt Enable Register)
        alt_setbits_word(ALT_UART_IER_DLH_ADDR(handle->location), setmask);
        break;
    default:
        return ALT_E_ERROR;
    }

    return ALT_E_SUCCESS;
}

static ALT_STATUS_CODE alt_16550_ier_mask_clr_helper(ALT_16550_HANDLE_t * handle, uint32_t setmask)
{
    switch (handle->device)
    {
    case ALT_16550_DEVICE_SOCFPGA_UART0:
    case ALT_16550_DEVICE_SOCFPGA_UART1:
    case ALT_16550_DEVICE_ALTERA_16550_UART:
        // Clear bit in IER (Interrupt Enable Register)
        alt_clrbits_word(ALT_UART_IER_DLH_ADDR(handle->location), setmask);
        break;
    default:
        return ALT_E_ERROR;
    }

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_16550_int_enable_rx(ALT_16550_HANDLE_t * handle)
{
    // Set the IER::ERBFI (Interrupt Enable Register :: Enable Receive Buffer Full Interrupt) bit.
    return alt_16550_ier_mask_set_helper(handle, ALT_UART_IER_DLH_ERBFI_DLH0_SET_MSK);
}

ALT_STATUS_CODE alt_16550_int_disable_rx(ALT_16550_HANDLE_t * handle)
{
    // Clear the IER::ERBFI (Interrupt Enable Register :: Enable Receive Buffer Full Interrupt) bit.
    return alt_16550_ier_mask_clr_helper(handle, ALT_UART_IER_DLH_ERBFI_DLH0_SET_MSK);
}

ALT_STATUS_CODE alt_16550_int_enable_tx(ALT_16550_HANDLE_t * handle)
{
    // Set the IER::ETBEI (Interrupt Enable Register :: Enable Transmit Buffer Empty Interrupt) bit.
    return alt_16550_ier_mask_set_helper(handle, ALT_UART_IER_DLH_ETBEI_DLH1_SET_MSK);
}

ALT_STATUS_CODE alt_16550_int_disable_tx(ALT_16550_HANDLE_t * handle)
{
    // Clear the IER::ETBEI (Interrupt Enable Register :: Enable Transmit Buffer Empty Interrupt) bit.
    return alt_16550_ier_mask_clr_helper(handle, ALT_UART_IER_DLH_ETBEI_DLH1_SET_MSK);
}

ALT_STATUS_CODE alt_16550_int_enable_line(ALT_16550_HANDLE_t * handle)
{
    // Set the IER::ELSI (Interrupt Enable Register :: Enable Line Status Interrupt) bit.
    return alt_16550_ier_mask_set_helper(handle, ALT_UART_IER_DLH_ELSI_DHL2_SET_MSK);
}

ALT_STATUS_CODE alt_16550_int_disable_line(ALT_16550_HANDLE_t * handle)
{
    // Clear the IER::ELSI (Interrupt Enable Register :: Enable Line Status Interrupt) bit.
    return alt_16550_ier_mask_clr_helper(handle, ALT_UART_IER_DLH_ELSI_DHL2_SET_MSK);
}

ALT_STATUS_CODE alt_16550_int_enable_modem(ALT_16550_HANDLE_t * handle)
{
    // Set the IER::EDSSI (Interrupt Enable Register :: Enable Modem Status Interrupt) bit.
    return alt_16550_ier_mask_set_helper(handle, ALT_UART_IER_DLH_EDSSI_DHL3_SET_MSK);
}

ALT_STATUS_CODE alt_16550_int_disable_modem(ALT_16550_HANDLE_t * handle)
{
    // Clear the IER::EDSSI (Interrupt Enable Register :: Enable Modem Status Interrupt) bit.
    return alt_16550_ier_mask_clr_helper(handle, ALT_UART_IER_DLH_EDSSI_DHL3_SET_MSK);
}

ALT_STATUS_CODE alt_16550_int_disable_all(ALT_16550_HANDLE_t * handle)
{
    // Clear the IER::(ERBFI | ETBEI | ELSI | EDSSI)
    //   (Interrupt Enable Register :: (Enable Receive Buffer Full Interrupt   |
    //                                  Enable Transmit Buffer Empty Interrupt |
    //                                  Enable Line Status Interrupt           |
    //                                  Enable Modem Status Interrupt)) bits
    return alt_16550_ier_mask_clr_helper(handle, ALT_UART_IER_DLH_ERBFI_DLH0_SET_MSK |
                                                 ALT_UART_IER_DLH_ETBEI_DLH1_SET_MSK |
                                                 ALT_UART_IER_DLH_ELSI_DHL2_SET_MSK  |
                                                 ALT_UART_IER_DLH_EDSSI_DHL3_SET_MSK);
}

ALT_STATUS_CODE alt_16550_int_status_get(ALT_16550_HANDLE_t * handle,
                                         ALT_16550_INT_STATUS_t * status)
{
    switch (handle->device)
    {
    case ALT_16550_DEVICE_SOCFPGA_UART0:
    case ALT_16550_DEVICE_SOCFPGA_UART1:
    case ALT_16550_DEVICE_ALTERA_16550_UART:
        // Read IIR::IID (Interrupt Identity Register :: Interrupt ID)
        *status = (ALT_16550_INT_STATUS_t) ALT_UART_IIR_ID_GET(alt_read_word(ALT_UART_IIR_ADDR(handle->location)));
        break;
    default:
        return ALT_E_ERROR;
    }

    return ALT_E_SUCCESS;
}

/////

ALT_STATUS_CODE alt_16550_line_config_set(ALT_16550_HANDLE_t * handle,
                                          ALT_16550_DATABITS_t databits,
                                          ALT_16550_PARITY_t parity,
                                          ALT_16550_STOPBITS_t stopbits)
{
    // Validate the databits parameter.
    switch (databits)
    {
    case ALT_16550_DATABITS_5:
    case ALT_16550_DATABITS_6:
    case ALT_16550_DATABITS_7:
    case ALT_16550_DATABITS_8:
        break;
    default:
        return ALT_E_ERROR;
    }

    // Validate the parity parameter.
    switch (parity)
    {
    case ALT_16550_PARITY_DISABLE:
    case ALT_16550_PARITY_ODD:
    case ALT_16550_PARITY_EVEN:
        break;
    default:
        return ALT_E_ERROR;
    }

    // Validate the stopbits parameter.
    switch (stopbits)
    {
    case ALT_16550_STOPBITS_1:
    case ALT_16550_STOPBITS_2:
        break;
    default:
        return ALT_E_ERROR;
    }

    // LCR (Line Control Register) cache.
    uint32_t lcr = 0;

    switch (handle->device)
    {
    case ALT_16550_DEVICE_SOCFPGA_UART0:
    case ALT_16550_DEVICE_SOCFPGA_UART1:
    case ALT_16550_DEVICE_ALTERA_16550_UART:

        // Configure the number of databits
        lcr |= ALT_UART_LCR_DLS_SET(databits);

        // Configure the number of stopbits
        lcr |= ALT_UART_LCR_STOP_SET(stopbits);

        // Configure the parity
        if (parity != ALT_16550_PARITY_DISABLE)
        {
            // Enable parity in LCR
            lcr |= ALT_UART_LCR_PEN_SET_MSK;

            if (parity == ALT_16550_PARITY_EVEN)
            {
                // Enable even parity in LCR; otherwise it's odd parity.
                lcr |= ALT_UART_LCR_EPS_SET_MSK;
            }
        }

        // Update LCR (Line Control Register)
        alt_replbits_word(ALT_UART_LCR_ADDR(handle->location), 
                          ALT_UART_LCR_DLS_SET_MSK
                        | ALT_UART_LCR_STOP_SET_MSK
                        | ALT_UART_LCR_PEN_SET_MSK
                        | ALT_UART_LCR_EPS_SET_MSK,
                        lcr);

        break;

    default:
        return ALT_E_ERROR;
    }

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_16550_line_break_enable(ALT_16550_HANDLE_t * handle)
{
    switch (handle->device)
    {
    case ALT_16550_DEVICE_SOCFPGA_UART0:
    case ALT_16550_DEVICE_SOCFPGA_UART1:
    case ALT_16550_DEVICE_ALTERA_16550_UART:
        // Set the LCR::Break (Line Control Register :: Break) bit.
        alt_setbits_word(ALT_UART_LCR_ADDR(handle->location), ALT_UART_LCR_BREAK_SET_MSK);
        break;

    default:
        return ALT_E_ERROR;
    }

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_16550_line_break_disable(ALT_16550_HANDLE_t * handle)
{
    switch (handle->device)
    {
    case ALT_16550_DEVICE_SOCFPGA_UART0:
    case ALT_16550_DEVICE_SOCFPGA_UART1:
    case ALT_16550_DEVICE_ALTERA_16550_UART:
        // Clear the LCR::Break (Line Control Register :: Break) bit.
        alt_clrbits_word(ALT_UART_LCR_ADDR(handle->location), ALT_UART_LCR_BREAK_SET_MSK);
        break;

    default:
        return ALT_E_ERROR;
    }


    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_16550_line_status_get(ALT_16550_HANDLE_t * handle,
                                          uint32_t * status)
{
    switch (handle->device)
    {
    case ALT_16550_DEVICE_SOCFPGA_UART0:
    case ALT_16550_DEVICE_SOCFPGA_UART1:
    case ALT_16550_DEVICE_ALTERA_16550_UART:
        // Read the LSR (Line Status Register).
        *status = alt_read_word(ALT_UART_LSR_ADDR(handle->location));
        break;
    default:
        return ALT_E_ERROR;
    }

    return ALT_E_SUCCESS;
}

/////

static ALT_STATUS_CODE alt_16550_mcr_mask_set_helper(ALT_16550_HANDLE_t * handle,
                                                     uint32_t setmask)
{
    switch (handle->device)
    {
    case ALT_16550_DEVICE_SOCFPGA_UART0:
    case ALT_16550_DEVICE_SOCFPGA_UART1:
    case ALT_16550_DEVICE_ALTERA_16550_UART:
        // Set the bit in MCR (Modem Control Register).
        alt_setbits_word(ALT_UART_MCR_ADDR(handle->location), setmask);
        break;
    default:
        return ALT_E_ERROR;
    }

    return ALT_E_SUCCESS;
}

static ALT_STATUS_CODE alt_16550_mcr_mask_clr_helper(ALT_16550_HANDLE_t * handle, uint32_t setmask)
{
    switch (handle->device)
    {
    case ALT_16550_DEVICE_SOCFPGA_UART0:
    case ALT_16550_DEVICE_SOCFPGA_UART1:
    case ALT_16550_DEVICE_ALTERA_16550_UART:
        // Clear the bit in MCR (Modem Control Register).
        alt_clrbits_word(ALT_UART_MCR_ADDR(handle->location), setmask);
        break;
    default:
        return ALT_E_ERROR;
    }

    return ALT_E_SUCCESS;
}

ALT_STATUS_CODE alt_16550_flowcontrol_enable(ALT_16550_HANDLE_t * handle)
{
    // Verify that the FIFO is enabled
    if (!(handle->fcr & ALT_UART_FCR_FIFOE_SET_MSK))
    {
        return ALT_E_ERROR;
    }

    // For the Altera 16550 Compatible Soft UART, check that Hardware Flowcontrol is enabled.
    if (handle->device == ALT_16550_DEVICE_ALTERA_16550_UART)
    {
        // Read the CPR::AFCE_Mode (Component Parameter Register :: Auto Flow Control mode) bit.
        uint32_t cpr = alt_read_word(ALT_ALTERA_16550_CPR_ADDR(handle->location));
        if (!(ALT_ALTERA_16550_CPR_AFCE_MODE_SET_MSK & cpr))
        {
            return ALT_E_ERROR;
        }
    }

    // Set MCR::AFCE (Modem Control Register :: Automatic FlowControl Enable) bit.
    return alt_16550_mcr_mask_set_helper(handle, ALT_UART_MCR_AFCE_SET_MSK);
}

ALT_STATUS_CODE alt_16550_flowcontrol_disable(ALT_16550_HANDLE_t * handle)
{
    // Clear MCR::AFCE (Modem Control Register :: Automatic FlowControl Enable) bit.
    return alt_16550_mcr_mask_clr_helper(handle, ALT_UART_MCR_AFCE_SET_MSK);
}

ALT_STATUS_CODE alt_16550_loopback_enable(ALT_16550_HANDLE_t * handle)
{
    // Loopback is not implemented in the Altera 16550 Compatible Soft UART.
    if (handle->device == ALT_16550_DEVICE_ALTERA_16550_UART)
    {
        return ALT_E_ERROR;
    }

    // Set MCR::Loopback (Modem Control Register :: Loopback) bit.
    return alt_16550_mcr_mask_set_helper(handle, ALT_UART_MCR_LOOPBACK_SET_MSK);
}

ALT_STATUS_CODE alt_16550_loopback_disable(ALT_16550_HANDLE_t * handle)
{
    // Clear MCR::Loopback (Modem Control Register :: Loopback) bit.
    return alt_16550_mcr_mask_clr_helper(handle, ALT_UART_MCR_LOOPBACK_SET_MSK);
}

ALT_STATUS_CODE alt_16550_modem_enable_out1(ALT_16550_HANDLE_t * handle)
{
    // Set MCR::Out1 (Modem Control Register :: Out1) bit.
    return alt_16550_mcr_mask_set_helper(handle, ALT_UART_MCR_OUT1_SET_MSK);
}

ALT_STATUS_CODE alt_16550_modem_disable_out1(ALT_16550_HANDLE_t * handle)
{
    // Clear MCR::Out1 (Modem Control Register :: Out1) bit.
    return alt_16550_mcr_mask_clr_helper(handle, ALT_UART_MCR_OUT1_SET_MSK);
}

ALT_STATUS_CODE alt_16550_modem_enable_out2(ALT_16550_HANDLE_t * handle)
{
    // Set MCR::Out2 (Modem Control Register :: Out2) bit.
    return alt_16550_mcr_mask_set_helper(handle, ALT_UART_MCR_OUT2_SET_MSK);
}

ALT_STATUS_CODE alt_16550_modem_disable_out2(ALT_16550_HANDLE_t * handle)
{
    // Clear MCR::Out2 (Modem Control Register :: Out2) bit.
    return alt_16550_mcr_mask_clr_helper(handle, ALT_UART_MCR_OUT2_SET_MSK);
}

ALT_STATUS_CODE alt_16550_modem_enable_rts(ALT_16550_HANDLE_t * handle)
{
    // Set MCR::RTS (Modem Control Register :: Request To Send) bit.
    return alt_16550_mcr_mask_set_helper(handle, ALT_UART_MCR_RTS_SET_MSK);
}

ALT_STATUS_CODE alt_16550_modem_disable_rts(ALT_16550_HANDLE_t * handle)
{
    // Clear MCR::RTS (Modem Control Register :: Request To Send) bit.
    return alt_16550_mcr_mask_clr_helper(handle, ALT_UART_MCR_RTS_SET_MSK);
}

ALT_STATUS_CODE alt_16550_modem_enable_dtr(ALT_16550_HANDLE_t * handle)
{
    // Set MCR::DTR (Modem Control Register :: Data Terminal Ready) bit.
    return alt_16550_mcr_mask_set_helper(handle, ALT_UART_MCR_DTR_SET_MSK);
}

ALT_STATUS_CODE alt_16550_modem_disable_dtr(ALT_16550_HANDLE_t * handle)
{
    // Clear MCR::DTR (Modem Control Register :: Data Terminal Ready) bit.
    return alt_16550_mcr_mask_clr_helper(handle, ALT_UART_MCR_DTR_SET_MSK);
}

ALT_STATUS_CODE alt_16550_modem_status_get(ALT_16550_HANDLE_t * handle,
                                          uint32_t * status)
{
    switch (handle->device)
    {
    case ALT_16550_DEVICE_SOCFPGA_UART0:
    case ALT_16550_DEVICE_SOCFPGA_UART1:
    case ALT_16550_DEVICE_ALTERA_16550_UART:
        // Read the MSR (Modem Status Register).
        *status = alt_read_word(ALT_UART_MSR_ADDR(handle->location));
        break;
    default:
        return ALT_E_ERROR;
    }

    return ALT_E_SUCCESS;
}
