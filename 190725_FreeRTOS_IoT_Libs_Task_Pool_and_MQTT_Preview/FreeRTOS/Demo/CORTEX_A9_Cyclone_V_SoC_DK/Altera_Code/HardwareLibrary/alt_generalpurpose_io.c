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
* EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
* EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT
* OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
* INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
* CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING
* IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY
* OF SUCH DAMAGE.
*
******************************************************************************/

#include    <stdint.h>
#include    <stdlib.h>
#include    <stdbool.h>

#include    "socal/hps.h"
#include    "socal/socal.h"
#include    "socal/alt_gpio.h"
#include    "socal/alt_rstmgr.h"
#include    "hwlib.h"
#include    "alt_generalpurpose_io.h"


/****************************************************************************************/
/******************************* Useful local definitions *******************************/
/****************************************************************************************/

#define     ALT_GPIO_EOPA       ALT_GPIO_1BIT_28
#define     ALT_GPIO_EOPB       ALT_GPIO_1BIT_57
#define     ALT_GPIO_EOPC       ALT_HLGPI_15
#define     ALT_GPIO_BITMASK    0x1FFFFFFF

            // expands the zero or one bit to the 29-bit GPIO word
#define     ALT_GPIO_ALLORNONE(tst)  ((uint32_t) ((tst == 0) ? 0 : ALT_GPIO_BITMASK))


/****************************************************************************************/
/* alt_gpio_init() initializes the GPIO modules 										*/
/****************************************************************************************/

ALT_STATUS_CODE alt_gpio_init(void)
{
		// put GPIO modules into system manager reset if not already there
	alt_gpio_uninit();
		// release GPIO modules from system reset (w/ two-instruction delay)
	alt_replbits_word(ALT_RSTMGR_PERMODRST_ADDR, ALT_RSTMGR_PERMODRST_GPIO0_SET_MSK |
			ALT_RSTMGR_PERMODRST_GPIO1_SET_MSK |
			ALT_RSTMGR_PERMODRST_GPIO2_SET_MSK, 0);
	return ALT_E_SUCCESS;
}


/****************************************************************************************/
/* alt_gpio_uninit() uninitializes the GPIO modules			     				       	*/
/****************************************************************************************/

ALT_STATUS_CODE alt_gpio_uninit(void)
{
	// put all GPIO modules into system manager reset
	alt_replbits_word(ALT_RSTMGR_PERMODRST_ADDR, ALT_RSTMGR_PERMODRST_GPIO0_SET_MSK |
			ALT_RSTMGR_PERMODRST_GPIO1_SET_MSK |
			ALT_RSTMGR_PERMODRST_GPIO2_SET_MSK,
			ALT_GPIO_BITMASK);
	return ALT_E_SUCCESS;
}


/****************************************************************************************/
/* alt_gpio_port_datadir_set() sets the specified GPIO data bits to use the data        */
/* direction(s) specified. 0 = input (default). 1 = output.                             */
/****************************************************************************************/

ALT_STATUS_CODE alt_gpio_port_datadir_set(ALT_GPIO_PORT_t gpio_pid,
        uint32_t mask, uint32_t config)
{
    volatile uint32_t   *addr;

    if ((mask & ~ALT_GPIO_BITMASK) || (config & ~ALT_GPIO_BITMASK))  { return ALT_E_ERROR; }
    if (gpio_pid == ALT_GPIO_PORTA)      { addr = ALT_GPIO0_SWPORTA_DDR_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTB) { addr = ALT_GPIO1_SWPORTA_DDR_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTC) { addr = ALT_GPIO2_SWPORTA_DDR_ADDR; }
    else { return ALT_E_BAD_ARG; }

    alt_replbits_word(addr, mask, config);
    return ALT_E_SUCCESS;
}


/****************************************************************************************/
/*  alt_gpio_port_datadir_get() returns the data direction configuration of selected    */
/* bits of the designated GPIO module.                                                  */
/****************************************************************************************/

uint32_t alt_gpio_port_datadir_get(ALT_GPIO_PORT_t gpio_pid,
        uint32_t mask)
{
    volatile uint32_t   *addr;

    if (gpio_pid == ALT_GPIO_PORTA)      { addr = ALT_GPIO0_SWPORTA_DDR_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTB) { addr = ALT_GPIO1_SWPORTA_DDR_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTC) { addr = ALT_GPIO2_SWPORTA_DDR_ADDR; }
    else { return 0; }

    return alt_read_word(addr) & mask;
}


/****************************************************************************************/
/* alt_gpio_port_data_write() sets the GPIO data outputs of the specified GPIO module   */
/* to a one or zero. Actual outputs are only set if the data direction for that bit(s)  */
/* has previously been set to configure them as output(s).                              */
/****************************************************************************************/

ALT_STATUS_CODE alt_gpio_port_data_write(ALT_GPIO_PORT_t gpio_pid,
        uint32_t mask, uint32_t val)
{
    volatile uint32_t   *addr;

    if ((mask & ~ALT_GPIO_BITMASK) || (val & ~ALT_GPIO_BITMASK))  { return ALT_E_ERROR; }
    if (gpio_pid == ALT_GPIO_PORTA)      { addr = ALT_GPIO0_SWPORTA_DR_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTB) { addr = ALT_GPIO1_SWPORTA_DR_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTC) { addr = ALT_GPIO2_SWPORTA_DR_ADDR; }
    else { return ALT_E_BAD_ARG; }

    alt_replbits_word(addr, mask, val);
    return ALT_E_SUCCESS;
}


/****************************************************************************************/
/* alt_gpio_port_data_read() returns the value of the data inputs of the specified      */
/* GPIO module. Data direction for these bits must have been previously set to inputs.  */
/****************************************************************************************/

#if (!ALT_GPIO_DATAREAD_TEST_MODE)
    /* This is the production code version. For software unit testing, set the      */
    /* ALT_GPIO_DATAREAD_TEST_MODE flag to true in the makefile, which will compile */
    /* the GPIO test software version of alt_gpio_port_data_read() instead.         */

uint32_t alt_gpio_port_data_read(ALT_GPIO_PORT_t gpio_pid, uint32_t mask)
{
    volatile uint32_t   *addr;

    if (gpio_pid == ALT_GPIO_PORTA)      { addr = ALT_GPIO0_EXT_PORTA_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTB) { addr = ALT_GPIO1_EXT_PORTA_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTC) { addr = ALT_GPIO2_EXT_PORTA_ADDR; }
    else { return 0; }

    return alt_read_word(addr) & mask;
}
#endif


/****************************************************************************************/
/* alt_gpio_port_int_type_set() sets selected signals of the specified GPIO port to     */
/* be either level-sensitive ( =0) or edge-triggered ( =1).                             */
/****************************************************************************************/

ALT_STATUS_CODE alt_gpio_port_int_type_set(ALT_GPIO_PORT_t gpio_pid,
        uint32_t mask, uint32_t config)
{
    volatile uint32_t   *addr;

    if ((mask & ~ALT_GPIO_BITMASK) || (config & ~ALT_GPIO_BITMASK))  { return ALT_E_ERROR; }
    if (gpio_pid == ALT_GPIO_PORTA)      { addr = ALT_GPIO0_INTTYPE_LEVEL_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTB) { addr = ALT_GPIO1_INTTYPE_LEVEL_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTC) { addr = ALT_GPIO2_INTTYPE_LEVEL_ADDR; }
    else { return ALT_E_BAD_ARG; }

    alt_replbits_word(addr, mask, config);
    return ALT_E_SUCCESS;
}


/****************************************************************************************/
/* alt_gpio_port_int_type_get() returns the interrupt configuration (edge-triggered or  */
/* level-triggered) for the specified signals of the specified GPIO module.             */
/****************************************************************************************/

uint32_t alt_gpio_port_int_type_get(ALT_GPIO_PORT_t gpio_pid,
        uint32_t mask)
{
    volatile uint32_t   *addr;

    if (gpio_pid == ALT_GPIO_PORTA)      { addr = ALT_GPIO0_INTTYPE_LEVEL_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTB) { addr = ALT_GPIO1_INTTYPE_LEVEL_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTC) { addr = ALT_GPIO2_INTTYPE_LEVEL_ADDR; }
    else { return 0; }

    return alt_read_word(addr) & mask;
}


/****************************************************************************************/
/* alt_gpio_port_int_pol_set() sets the interrupt polarity of the signals of the        */
/* specified GPIO register (when used as inputs) to active-high ( =0) or active-low     */
/* ( =1).                                                                               */
/****************************************************************************************/

ALT_STATUS_CODE alt_gpio_port_int_pol_set(ALT_GPIO_PORT_t gpio_pid,
        uint32_t mask, uint32_t config)
{
    volatile uint32_t   *addr;

    if ((mask & ~ALT_GPIO_BITMASK) || (config & ~ALT_GPIO_BITMASK))  { return ALT_E_ERROR; }
    if (gpio_pid == ALT_GPIO_PORTA)      { addr = ALT_GPIO0_INT_POL_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTB) { addr = ALT_GPIO1_INT_POL_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTC) { addr = ALT_GPIO2_INT_POL_ADDR; }
    else { return ALT_E_BAD_ARG; }

    alt_replbits_word(addr, mask, config);
    return ALT_E_SUCCESS;
}


/****************************************************************************************/
/* alt_gpio_port_int_pol_get() returns the active-high or active-low polarity           */
/* configuration for the possible interrupt sources of the specified GPIO module.       */
/* 0 = The interrupt polarity for this bit is set to active-low mode. 1 = The           */
/* interrupt polarity for this bit is set to active-highmode.                           */
/****************************************************************************************/

uint32_t alt_gpio_port_int_pol_get(ALT_GPIO_PORT_t gpio_pid,
        uint32_t mask)
{
    volatile uint32_t   *addr;

    if (gpio_pid == ALT_GPIO_PORTA)      { addr = ALT_GPIO0_INT_POL_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTB) { addr = ALT_GPIO1_INT_POL_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTC) { addr = ALT_GPIO2_INT_POL_ADDR; }
    else { return 0; }

    return alt_read_word(addr) & mask;
}


/****************************************************************************************/
/* alt_gpio_port_debounce_set() sets the debounce configuration for input signals of    */
/* the specified GPIO module. 0 - Debounce is not selected for this signal (default).   */
/* 1 - Debounce is selected for this signal.                                            */
/****************************************************************************************/

ALT_STATUS_CODE alt_gpio_port_debounce_set(ALT_GPIO_PORT_t gpio_pid,
        uint32_t mask, uint32_t config)
{
    volatile uint32_t   *addr;

    if ((mask & ~ALT_GPIO_BITMASK) || (config & ~ALT_GPIO_BITMASK))  { return ALT_E_ERROR; }
    if (gpio_pid == ALT_GPIO_PORTA)      { addr = ALT_GPIO0_DEBOUNCE_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTB) { addr = ALT_GPIO1_DEBOUNCE_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTC) { addr = ALT_GPIO2_DEBOUNCE_ADDR; }
    else { return ALT_E_BAD_ARG; }

    alt_replbits_word(addr, mask, config);
    return ALT_E_SUCCESS;
}


/****************************************************************************************/
/* alt_gpio_port_debounce_get() returns the debounce configuration for the input        */
/* signals of the specified GPIO register. 0 - Debounce is not selected for this        */
/* signal. 1 - Debounce is selected for this signal.                                    */
/****************************************************************************************/

uint32_t alt_gpio_port_debounce_get(ALT_GPIO_PORT_t gpio_pid,
        uint32_t mask)
{
    volatile uint32_t   *addr;

    if (gpio_pid == ALT_GPIO_PORTA)      { addr = ALT_GPIO0_DEBOUNCE_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTB) { addr = ALT_GPIO1_DEBOUNCE_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTC) { addr = ALT_GPIO2_DEBOUNCE_ADDR; }
    else { return 0; }

    return alt_read_word(addr) & mask;
}


/****************************************************************************************/
/* alt_gpio_port_sync_set() sets the synchronization configuration for the signals of   */
/* the specified GPIO register. This allows for synchronizing level-sensitive           */
/* interrupts to the internal clock signal. This is a port-wide option that controls    */
/* all level-sensitive interrupt signals of that GPIO port.                             */
/****************************************************************************************/

ALT_STATUS_CODE alt_gpio_port_sync_set(ALT_GPIO_PORT_t gpio_pid, uint32_t config)
{
    volatile uint32_t   *addr;

    config = (config != 0) ? 1 : 0;
    if (gpio_pid == ALT_GPIO_PORTA)      { addr = ALT_GPIO0_LS_SYNC_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTB) { addr = ALT_GPIO1_LS_SYNC_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTC) { addr = ALT_GPIO2_LS_SYNC_ADDR; }
    else { return ALT_E_BAD_ARG; }

    alt_write_word(addr, config);
    return ALT_E_SUCCESS;
}


/****************************************************************************************/
/* alt_gpio_port_sync_get() returns the synchronization configuration for the signals   */
/* of the specified GPIO register. This allows for synchronizing level-sensitive        */
/* interrupts to the internal clock signal. This is a port-wide option that controls    */
/* all level-sensitive interrupt signals of that GPIO port.                             */
/****************************************************************************************/

ALT_STATUS_CODE alt_gpio_port_sync_get(ALT_GPIO_PORT_t gpio_pid)
{
    volatile uint32_t   *addr;

    if (gpio_pid == ALT_GPIO_PORTA)      { addr = ALT_GPIO0_LS_SYNC_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTB) { addr = ALT_GPIO1_LS_SYNC_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTC) { addr = ALT_GPIO2_LS_SYNC_ADDR; }
    else { return ALT_E_BAD_ARG; }         // error

    return (alt_read_word(addr) != 0) ? ALT_E_TRUE : ALT_E_FALSE;
}


/****************************************************************************************/
/* alt_gpio_port_config() configures a group of GPIO signals with the same parameters.  */
/* Allows for configuring all parameters of a given port at one time.                   */
/****************************************************************************************/

ALT_STATUS_CODE alt_gpio_port_config(ALT_GPIO_PORT_t gpio_pid,
        uint32_t mask, ALT_GPIO_PIN_DIR_t dir, ALT_GPIO_PIN_TYPE_t type,
        ALT_GPIO_PIN_POL_t pol, ALT_GPIO_PIN_DEBOUNCE_t debounc,
        uint32_t data)
{
    ALT_STATUS_CODE     ret;

        // set all affected GPIO bits to inputs
    ret = alt_gpio_port_datadir_set(gpio_pid, mask, ALT_GPIO_ALLORNONE(ALT_GPIO_PIN_INPUT));
                // the ALT_GPIO_ALLORNONE() macro expands the zero or one bit to the 29-bit GPIO word

        // set trigger type
    if (ret == ALT_E_SUCCESS)
    {
        ret = alt_gpio_port_int_type_set(gpio_pid, mask, ALT_GPIO_ALLORNONE(type));
    }

        // set polarity
    if (ret == ALT_E_SUCCESS)
    {
        alt_gpio_port_int_pol_set(gpio_pid, mask, ALT_GPIO_ALLORNONE(pol));
    }

        // set debounce
    if (ret == ALT_E_SUCCESS)
    {
        alt_gpio_port_debounce_set(gpio_pid, mask, ALT_GPIO_ALLORNONE(debounc));
    }

        // set data output(s)
    if (ret == ALT_E_SUCCESS)
    {
        alt_gpio_port_data_write(gpio_pid, mask, ALT_GPIO_ALLORNONE(data));
    }

    if (ret == ALT_E_SUCCESS)
    {
        // set data direction of one or more bits to select output
        ret = alt_gpio_port_datadir_set(gpio_pid, mask, ALT_GPIO_ALLORNONE(dir));
    }

    return ret;
}


/****************************************************************************************/
/* Enables the specified GPIO data register interrupts.                                 */
/****************************************************************************************/

ALT_STATUS_CODE alt_gpio_port_int_enable(ALT_GPIO_PORT_t gpio_pid, uint32_t config)
{
    volatile uint32_t   *addr;

    if (config & ~ALT_GPIO_BITMASK)      { return ALT_E_ERROR; }
    if (gpio_pid == ALT_GPIO_PORTA)      { addr = ALT_GPIO0_INTEN_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTB) { addr = ALT_GPIO1_INTEN_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTC) { addr = ALT_GPIO2_INTEN_ADDR; }
    else { return ALT_E_BAD_ARG; }

    alt_replbits_word(addr, config, UINT32_MAX);
    return ALT_E_SUCCESS;
}


/****************************************************************************************/
/* Disables the specified GPIO data module interrupts.                                  */
/****************************************************************************************/

ALT_STATUS_CODE alt_gpio_port_int_disable(ALT_GPIO_PORT_t gpio_pid, uint32_t config)
{
    volatile uint32_t   *addr;

    if (config & ~ALT_GPIO_BITMASK)      { return ALT_E_ERROR; }
    if (gpio_pid == ALT_GPIO_PORTA)      { addr = ALT_GPIO0_INTEN_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTB) { addr = ALT_GPIO1_INTEN_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTC) { addr = ALT_GPIO2_INTEN_ADDR; }
    else { return ALT_E_BAD_ARG; }

    alt_replbits_word(addr, config, 0);
    return ALT_E_SUCCESS;
}



/****************************************************************************************/
/* Get the current state of the specified GPIO port interrupts enables.                 */
/****************************************************************************************/

uint32_t alt_gpio_port_int_enable_get(ALT_GPIO_PORT_t gpio_pid)
{
    volatile uint32_t   *addr;

    if (gpio_pid == ALT_GPIO_PORTA)      { addr = ALT_GPIO0_INTEN_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTB) { addr = ALT_GPIO1_INTEN_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTC) { addr = ALT_GPIO2_INTEN_ADDR; }
    else { return 0; }

    return alt_read_word(addr);
}


/****************************************************************************************/
/* Masks or unmasks selected interrupt source bits of the data register of the          */
/* specified GPIO module. Uses a second bit mask to determine which signals may be      */
/* changed by this call.                                                                */
/****************************************************************************************/

ALT_STATUS_CODE alt_gpio_port_int_mask_set(ALT_GPIO_PORT_t gpio_pid,
        uint32_t mask, uint32_t val)
{
    volatile uint32_t   *addr;

    if ((mask & ~ALT_GPIO_BITMASK) || (val & ~ALT_GPIO_BITMASK))  { return ALT_E_ERROR; }
    if (gpio_pid == ALT_GPIO_PORTA)      { addr = ALT_GPIO0_INTMSK_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTB) { addr = ALT_GPIO1_INTMSK_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTC) { addr = ALT_GPIO2_INTMSK_ADDR; }
    else { return ALT_E_BAD_ARG; }         // argument error

    alt_replbits_word(addr, mask, val);
    return ALT_E_SUCCESS;
}


/****************************************************************************************/
/* Returns the interrupt source mask of the specified GPIO module.                      */
/****************************************************************************************/

uint32_t alt_gpio_port_int_mask_get(ALT_GPIO_PORT_t gpio_pid)
{
    volatile uint32_t   *addr;

    if (gpio_pid == ALT_GPIO_PORTA)      { addr = ALT_GPIO0_INTMSK_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTB) { addr = ALT_GPIO1_INTMSK_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTC) { addr = ALT_GPIO2_INTMSK_ADDR; }
    else { return 0; }         // error

    return alt_read_word(addr);
}


/****************************************************************************************/
/* alt_gpio_port_int_status_get() returns the interrupt pending status of all signals   */
/* of the specified GPIO register.                                                      */
/****************************************************************************************/

uint32_t alt_gpio_port_int_status_get(ALT_GPIO_PORT_t gpio_pid)
{
    volatile uint32_t   *addr;

    if (gpio_pid == ALT_GPIO_PORTA)      { addr = ALT_GPIO0_INTSTAT_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTB) { addr = ALT_GPIO1_INTSTAT_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTC) { addr = ALT_GPIO2_INTSTAT_ADDR; }
    else { return 0; }         // error

    return alt_read_word(addr);
}


/****************************************************************************************/
/* Clear the interrupt pending status of selected signals of the specified GPIO         */
/* register.                                                                            */
/****************************************************************************************/

ALT_STATUS_CODE alt_gpio_port_int_status_clear(ALT_GPIO_PORT_t gpio_pid,
        uint32_t clrmask)
{
    volatile uint32_t   *addr;

    if (clrmask & ~ALT_GPIO_BITMASK)      { return ALT_E_ERROR; }
    if (gpio_pid == ALT_GPIO_PORTA)      { addr = ALT_GPIO0_INTSTAT_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTB) { addr = ALT_GPIO1_INTSTAT_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTC) { addr = ALT_GPIO2_INTSTAT_ADDR; }
    else { return ALT_E_BAD_ARG; }         // argument error

    alt_write_word(addr, clrmask);
    return ALT_E_SUCCESS;
}


/****************************************************************************************/
/*  alt_gpio_port_idcode_get() returns the ID code of the specified GPIO module.        */
/****************************************************************************************/

uint32_t alt_gpio_port_idcode_get(ALT_GPIO_PORT_t gpio_pid)
{
    volatile uint32_t   *addr;

    if (gpio_pid == ALT_GPIO_PORTA)      { addr = ALT_GPIO0_ID_CODE_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTB) { addr = ALT_GPIO1_ID_CODE_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTC) { addr = ALT_GPIO2_ID_CODE_ADDR; }
    else { return 0; }

    return alt_read_word(addr);
}


/****************************************************************************************/
/* alt_gpio_port_ver_get() returns the version code of the specified GPIO module.       */
/****************************************************************************************/

uint32_t alt_gpio_port_ver_get(ALT_GPIO_PORT_t gpio_pid)
{
    volatile uint32_t   *addr;

    if (gpio_pid == ALT_GPIO_PORTA)      { addr = ALT_GPIO0_VER_ID_CODE_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTB) { addr = ALT_GPIO1_VER_ID_CODE_ADDR; }
    else if (gpio_pid == ALT_GPIO_PORTC) { addr = ALT_GPIO2_VER_ID_CODE_ADDR; }
    else { return 0; }

    return alt_read_word(addr);
}


/****************************************************************************************/
/* alt_gpio_bit_config() configures one bit (signal) of the GPIO ports.                 */
/****************************************************************************************/

ALT_STATUS_CODE alt_gpio_bit_config(ALT_GPIO_1BIT_t signal_num,
        ALT_GPIO_PIN_DIR_t dir, ALT_GPIO_PIN_TYPE_t type,
        ALT_GPIO_PIN_POL_t pol, ALT_GPIO_PIN_DEBOUNCE_t debounce,
        ALT_GPIO_PIN_DATA_t data)
{
    ALT_GPIO_PORT_t     pid;
    uint32_t            mask;

    pid = alt_gpio_bit_to_pid(signal_num);
    mask = 0x1 << alt_gpio_bit_to_port_pin(signal_num);
    return alt_gpio_port_config(pid, mask, dir, type, pol, debounce, data);
}


/****************************************************************************************/
/* Returns the configuration parameters of a given GPIO bit.                            */
/****************************************************************************************/

ALT_STATUS_CODE alt_gpio_bitconfig_get(ALT_GPIO_1BIT_t signal_num,
        ALT_GPIO_CONFIG_RECORD_t *config)
{
    ALT_STATUS_CODE     ret = ALT_E_ERROR;
    ALT_GPIO_PORT_t     pid;
    uint32_t            mask, shift;

    if ((config != NULL) && (signal_num != ALT_END_OF_GPIO_SIGNALS) && (signal_num <= ALT_LAST_VALID_GPIO_BIT))
    {
        pid = alt_gpio_bit_to_pid(signal_num);
        shift = alt_gpio_bit_to_port_pin(signal_num);
        if ((pid != ALT_GPIO_PORT_UNKNOWN) && (shift <= ALT_GPIO_BIT_MAX))
        {
            config->signal_number = signal_num;
            mask = 0x00000001 << shift;
            config->direction = (alt_gpio_port_datadir_get(pid, mask) == 0) ? ALT_GPIO_PIN_INPUT : ALT_GPIO_PIN_OUTPUT;
            config->type = (alt_gpio_port_int_type_get(pid, mask) == 0) ? ALT_GPIO_PIN_LEVEL_TRIG_INT : ALT_GPIO_PIN_EDGE_TRIG_INT;

            // save the following data whatever the state of config->direction
            config->polarity = (alt_gpio_port_int_pol_get(pid, mask) == 0) ? ALT_GPIO_PIN_ACTIVE_LOW : ALT_GPIO_PIN_ACTIVE_HIGH;
            config->debounce = (alt_gpio_port_debounce_get(pid, mask) == 0) ? ALT_GPIO_PIN_NODEBOUNCE : ALT_GPIO_PIN_DEBOUNCE;
            config->data = (alt_gpio_port_data_read(pid, mask) == 0) ? ALT_GPIO_PIN_DATAZERO : ALT_GPIO_PIN_DATAONE;
            ret = ALT_E_SUCCESS;
        }
    }
    return ret;
}


/****************************************************************************************/
/* alt_gpio_group_config() configures a list of GPIO bits. The GPIO bits do not have    */
/* to be configured the same, as was the case for the mask version of this function,    */
/* alt_gpio_port_config(). Each bit may be configured differently and bits may be       */
/* listed in any order.                                                                 */
/****************************************************************************************/

ALT_STATUS_CODE alt_gpio_group_config(ALT_GPIO_CONFIG_RECORD_t* config_array, uint32_t len)
{
    ALT_STATUS_CODE         ret = ALT_E_ERROR;

    if (config_array != NULL)
    {
        if (config_array->signal_number == ALT_END_OF_GPIO_SIGNALS) { ret = ALT_E_SUCCESS; }
            // catches the condition where the pointers are good, but the
            // first index is the escape character - which isn't an error
        else
        {
            for (; (len-- > 0) && (config_array->signal_number != ALT_END_OF_GPIO_SIGNALS) && (config_array != NULL); config_array++)
            {
                ret = alt_gpio_bit_config(config_array->signal_number,
                        config_array->direction, config_array->type, config_array->polarity,
                        config_array->debounce, config_array->data);
                if ((config_array->direction == ALT_GPIO_PIN_OUTPUT) && (ret == ALT_E_SUCCESS))
                {
                    // if the pin is set to be an output, set it to the correct value
                    alt_gpio_port_data_write(alt_gpio_bit_to_pid(config_array->signal_number),
                             0x1 << alt_gpio_bit_to_port_pin(config_array->signal_number),
                             ALT_GPIO_ALLORNONE(config_array->data));
                        // ret should retain the value returned by alt_gpio_bit_config() above
                        // and should not be changed by the alt_gpio_port_data_write() call.
                }
                if (((ret != ALT_E_SUCCESS) && (config_array->signal_number <= ALT_LAST_VALID_GPIO_BIT))
                    || ((ret == ALT_E_SUCCESS) && (config_array->signal_number > ALT_LAST_VALID_GPIO_BIT)))
                {
                    ret = ALT_E_ERROR;
                    break;
                }
            }
        }
    }
    return ret;
}


/****************************************************************************************/
/* Returns a list of the pin signal indices and the associated configuration settings   */
/* (data direction, interrupt type, polarity, debounce, and synchronization) of that    */
/* list of signals. Only the signal indices in the first field of each configuration    */
/* record need be filled in. This function will fill in all the other fields of the     */
/* configuration record, returning all configuration parameters in the array. A signal  */
/* number index in the array equal to ALT_END_OF_GPIO_SIGNALS (-1) also terminates the  */
/* function.                                                                            */
/****************************************************************************************/

ALT_STATUS_CODE alt_gpio_group_config_get(ALT_GPIO_CONFIG_RECORD_t *config_array,
        uint32_t len)
{
    ALT_STATUS_CODE     ret = ALT_E_ERROR;

    if ((config_array != NULL) && (config_array->signal_number == ALT_END_OF_GPIO_SIGNALS))
    {
        ret = ALT_E_SUCCESS;
    }
    else
    {
        for ( ; (len > 0) && (config_array != NULL) && (config_array->signal_number != ALT_END_OF_GPIO_SIGNALS)
                    && (config_array->signal_number <= ALT_LAST_VALID_GPIO_BIT); len--)
        {
            ret = alt_gpio_bitconfig_get(config_array->signal_number, config_array);
            config_array++;
            if (ret != ALT_E_SUCCESS) { break; }
        }
    }
    return ret;
}

/****************************************************************************************/
/* Another way to return a configuration list. The difference between this version and  */
/* alt_gpio_group_config_get() is that this version follows a separate list of signal   */
/* indices instead of having the signal list provided in the first field of the         */
/* configuration records in the array. This function will fill in the fields of the     */
/* configuration record, returning all configuration parameters in the array. A signal  */
/* number index in the array equal to ALT_END_OF_GPIO_SIGNALS (-1) also terminates      */
/* operation.                                                                           */
/****************************************************************************************/

ALT_STATUS_CODE alt_gpio_group_config_get2(ALT_GPIO_1BIT_t* pinid_array,
        ALT_GPIO_CONFIG_RECORD_t *config_array, uint32_t len)
{
    ALT_STATUS_CODE     ret = ALT_E_ERROR;

    if ((config_array != NULL) && (pinid_array != NULL) && (*pinid_array == ALT_END_OF_GPIO_SIGNALS))
    {
        ret = ALT_E_SUCCESS;
        // catches the condition where the pointers are good, but the
        // first index is the escape character - which isn't an error
    }
    else
    {
        for ( ;(len > 0) && (pinid_array != NULL) && (*pinid_array != ALT_END_OF_GPIO_SIGNALS) && (config_array != NULL); len--)
        {
            ret = alt_gpio_bitconfig_get(*pinid_array, config_array);
            config_array++;
            pinid_array++;
            if (ret != ALT_E_SUCCESS) { break; }
        }
    }
    return ret;
}


/****************************************************************************************/
/* A useful utility function. Extracts the GPIO port ID from the supplied GPIO Signal   */
/* Index Number.                                                                        */
/****************************************************************************************/

ALT_GPIO_PORT_t alt_gpio_bit_to_pid(ALT_GPIO_1BIT_t pin_num)
{
    ALT_GPIO_PORT_t     pid = ALT_GPIO_PORT_UNKNOWN;

    if (pin_num <= ALT_GPIO_EOPA) { pid = ALT_GPIO_PORTA; }
    else if (pin_num <= ALT_GPIO_EOPB) { pid = ALT_GPIO_PORTB; }
    else if (pin_num <= ALT_GPIO_EOPC) { pid = ALT_GPIO_PORTC; }
    return pid;
}


/****************************************************************************************/
/* A useful utility function. Extracts the GPIO signal (pin) mask from the supplied     */
/* GPIO Signal Index Number.                                                           */
/****************************************************************************************/

ALT_GPIO_PORTBIT_t alt_gpio_bit_to_port_pin(ALT_GPIO_1BIT_t pin_num)
{
    if (pin_num <= ALT_GPIO_EOPA) {}
    else if (pin_num <= ALT_GPIO_EOPB) { pin_num -= (ALT_GPIO_EOPA + 1); }
    else if (pin_num <= ALT_GPIO_EOPC) { pin_num -= (ALT_GPIO_EOPB + 1); }
    else { return ALT_END_OF_GPIO_PORT_SIGNALS; }
    return (ALT_GPIO_PORTBIT_t) pin_num;
}


/****************************************************************************************/
/* A useful utility function. Extracts the GPIO Signal Index Number from the supplied   */
/* GPIO port ID and signal mask. If passed a bitmask composed of more than one signal,  */
/* the signal number of the lowest bitmask presented is returned.                       */
/****************************************************************************************/

ALT_GPIO_1BIT_t alt_gpio_port_pin_to_bit(ALT_GPIO_PORT_t pid,
        uint32_t bitmask)
{
    uint32_t    i;

    for (i=0; i <= ALT_GPIO_BITNUM_MAX ;i++)
    {
        if (bitmask & 0x00000001)
        {
            if (pid == ALT_GPIO_PORTA) {}
            else if (pid == ALT_GPIO_PORTB) { i += ALT_GPIO_EOPA + 1; }
            else if (pid == ALT_GPIO_PORTC) { i += ALT_GPIO_EOPB + 1; }
            else { return ALT_END_OF_GPIO_SIGNALS; }
            return (ALT_GPIO_1BIT_t) i;
        }
        bitmask >>= 1;
    }
    return ALT_END_OF_GPIO_SIGNALS;
}

