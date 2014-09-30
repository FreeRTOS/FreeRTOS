/*! \file
 *  Altera - GPIO Module
 */

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

#ifndef __ALT_GPIO_H__
#define __ALT_GPIO_H__

#include <stdint.h>
#include "hwlib.h"

#ifdef __cplusplus
extern "C" {
#endif  /* __cplusplus */

#define     ALT_GPIO_BITMASK                0x1FFFFFFF

/* If the GPIO special test mode flag was not defined in the makefile,   */
    /* set the ALT_GPIO_DATAREAD_TEST_MODE flag to false to specify that     */
    /* the production code version of alt_gpio_port_data_read() is included. */
    /* If the flag is defined as true in the makefile, then the test version */
    /* located in the test code file is substituted instead of the version   */
    /* in this file.                                                         */
#ifndef     ALT_GPIO_DATAREAD_TEST_MODE
#define     ALT_GPIO_DATAREAD_TEST_MODE     false
#endif

/******************************************************************************/
/*! \addtogroup ALT_GPIO_API The General Purpose Input/Output Manager API
 *
 * This module defines the General Purpose Input/Output Manager API for
 * accessing, configuring, and controlling the General Purpose Input/Output
 * Manager resources. These include both the general-purpose GPIO signals and
 * the input-only GPI signals that are shared with the DDR interface.\n \n
 * The GPIO API presents two views or perspectives of the GPIO signals. The first
 * is to view the GPIO signals in a traditional way, as separate GPIO ports
 * each comprised of a number of GPIO bits. The second perspective is of a
 * unified flat view that presents the GPIO and GPI signals as a set of indexed
 * bits, a view that allows the programmer to mostly ignore the port and pin
 * hardware configuration and read/write/configure the GPIO and GPI signals
 * independently of the underlying hardware implementation.
 *
 * @{
 */

/******************************************************************************/
/*! \addtogroup ALT_GPIO_API_CONFIG General-Purpose IO Configuration Functions
 *
 * This functional group contains functions to control, configure and manage
 * the general-purpose IO signals as individual signals or as groups of signals.
 * This group of functions can operate on multiple bits within the same GPIO
 * port and accepts a bit mask to specify which bits an operation will operate on.
 * Other bits within the same GPIO port are not changed.
 *
 * This example shows how multiple drivers or applications can use this feature
 * to easily prevent conflict while accessing the same GPIO port:
 * \verbatim
 #define DRIVER_0_GPIO_MSK   0x0010FF03;
 #define DRIVER_1_GPIO_MSK   0x002000F8;
 #define DRIVER_2_GPIO_MSK   0x03C00004;
 #define DRIVER_3_GPIO_MSK   0x000F0000;

    alt_gpio_port_data_write(ALT_GPIO_PORTA, DRIVER_0_GPIO_MSK, init_val0);
    alt_gpio_port_data_write(ALT_GPIO_PORTA, DRIVER_1_GPIO_MSK, init_val1);
    alt_gpio_port_data_write(ALT_GPIO_PORTA, DRIVER_2_GPIO_MSK, init_val2);
    alt_gpio_port_data_write(ALT_GPIO_PORTA, DRIVER_3_GPIO_MSK, init_val3);
    alt_gpio_port_int_type_set(ALT_GPIO_PORTA, DRIVER_1_GPIO_MSK, config_val1);
 \endverbatim
 *
 *  @{
 */
/******************************************************************************/
/*!
 * This type definition enumerates the data direction (input or output) of
 * the GPIO signals.
 */

typedef enum ALT_GPIO_PIN_DIR_e
{
    /*! # */
    ALT_GPIO_PIN_INPUT,
    /*! # */
    ALT_GPIO_PIN_OUTPUT
} ALT_GPIO_PIN_DIR_t;

/******************************************************************************/
/*!
 * This type definition enumerates the type of interrupt source
 * (level-triggered or edge-triggered) of the GPIO signals.
 */

typedef enum ALT_GPIO_PIN_TYPE_e
{
    /*! # */
    ALT_GPIO_PIN_LEVEL_TRIG_INT,
    /*! # */
    ALT_GPIO_PIN_EDGE_TRIG_INT
} ALT_GPIO_PIN_TYPE_t;

/******************************************************************************/
/*!
 * This type definition enumerates the polarity of the interrupt sources
 * (falling-edge or rising-edge for edge-triggered interrupts, active-low or
 * active-high for level-triggered interrupts) of the GPIO signals.
 */

typedef enum ALT_GPIO_PIN_POL_e
{
    /*! Indicates active-low for level-triggered interrupts and
     * falling-edge for edge-triggered interrupts */
    ALT_GPIO_PIN_ACTIVE_LOW,

    /*! Indicates active-high for level-triggered interrupts and
     * rising-edge for edge-triggered interrupt */
    ALT_GPIO_PIN_ACTIVE_HIGH
} ALT_GPIO_PIN_POL_t;

/******************************************************************************/
/*!
 * This type definition enumerates whether or not the debounce metastability
 * flip-flops are inserted or not. These are used to debounce signals presented
 * to the GPIO inputs. A signal must be steady for two periods of the
 * gpio_db_clk clock before it is considered valid. The frequency of the
 * gpio_db_clk clock may be set using the Clock Manager API.
 */

typedef enum ALT_GPIO_PIN_DEBOUNCE_e
{
    /*! # */
    ALT_GPIO_PIN_NODEBOUNCE,
    /*! # */
    ALT_GPIO_PIN_DEBOUNCE
} ALT_GPIO_PIN_DEBOUNCE_t;

/******************************************************************************/
/*!
 * This type definition enumerates whether or not level-sensitive interrupts
 * are synchronized to the internal pclk_intr clock. It has no effect for GPIO
 * signals that are selected as outputs, or if the interrupt is not enabled,
 * or if the interrupt is set to be edge-triggered. This is a port-wide option.
 */

typedef enum ALT_GPIO_PIN_SYNC_e
{
    /*! # */
    ALT_GPIO_PIN_NOSYNC,
    /*! # */
    ALT_GPIO_PIN_SYNC
} ALT_GPIO_PIN_SYNC_t;

/******************************************************************************/
/*!
 * This type definition enumerates the possible data states of the GPIO bits.
 */

typedef enum ALT_GPIO_PIN_DATA_e
{
    /*! # */
    ALT_GPIO_PIN_DATAZERO,
    /*! # */
    ALT_GPIO_PIN_DATAONE
} ALT_GPIO_PIN_DATA_t;


/******************************************************************************/
/*!
 * This type definition enumerates the GPIO ports that the GPIO manager
 * handles.
 */

typedef enum ALT_GPIO_PORT_e
{
    /*!
     * \b Port \b A - 29-bit GPIO port A.
     */
    ALT_GPIO_PORTA,

    /*!
     * \b Port \b B - 29-bit GPIO port B.
     */
    ALT_GPIO_PORTB,

    /*!
     * \b Port \b C - 29-bit GPIO port C. \n 13 bits are used for GPIO signals,
     *                14 bits are used for GPI-only signals that are shared
     *                with the DDR interface, 2 bits are not used. Some signals
     *                may not be connected on some versions. See the relevant
     *                pin mux data.
     */
    ALT_GPIO_PORTC,

    /*!
     * \b Unknown \b Port - Used to indicate an error.
     */
    ALT_GPIO_PORT_UNKNOWN
} ALT_GPIO_PORT_t;


/******************************************************************************/
/*!
 * This type definition enumerates the individual bits within the GPIO ports
 * used by the GPIO manager. The bit-ordering must match the hardware
 * bit-ordering. Since the ordering and packing of bitfields is not
 * standardized in C/C++, the following are defined as masks. \n
 * For example, to set bits 3 and 4 of GPIO port B outputs (assuming the bits
 * had previously been set to outputs), the user could use the syntax: \par
 * \b alt_gpio_port_data_write(\b ALT_GPIO_PORTB, \b ALT_GPIO_BIT3 \b | \b
 * ALT_GPIO_BIT4);
 */

typedef enum ALT_GPIO_PORTBIT_e
{
    /*! # */
    ALT_GPIO_BIT0 = ALT_TWO_TO_POW0,
    /*! # */
    ALT_GPIO_BIT1 = ALT_TWO_TO_POW1,
    /*! # */
    ALT_GPIO_BIT2 = ALT_TWO_TO_POW2,
    /*! # */
    ALT_GPIO_BIT3 = ALT_TWO_TO_POW3,
    /*! # */
    ALT_GPIO_BIT4 = ALT_TWO_TO_POW4,
    /*! # */
    ALT_GPIO_BIT5 = ALT_TWO_TO_POW5,
    /*! # */
    ALT_GPIO_BIT6 = ALT_TWO_TO_POW6,
    /*! # */
    ALT_GPIO_BIT7 = ALT_TWO_TO_POW7,
    /*! #  */
    ALT_GPIO_BIT8 = ALT_TWO_TO_POW8,
    /*! # */
    ALT_GPIO_BIT9 = ALT_TWO_TO_POW9,
    /*! # */
    ALT_GPIO_BIT10 = ALT_TWO_TO_POW10,
    /*! # */
    ALT_GPIO_BIT11 = ALT_TWO_TO_POW11,
    /*! # */
    ALT_GPIO_BIT12 = ALT_TWO_TO_POW12,
    /*! # */
    ALT_GPIO_BIT13 = ALT_TWO_TO_POW13,
    /*! # */
    ALT_GPIO_BIT14 = ALT_TWO_TO_POW14,
    /*! # */
    ALT_GPIO_BIT15 = ALT_TWO_TO_POW15,
    /*! # */
    ALT_GPIO_BIT16 = ALT_TWO_TO_POW16,
    /*! # */
    ALT_GPIO_BIT17 = ALT_TWO_TO_POW17,
    /*! # */
    ALT_GPIO_BIT18 = ALT_TWO_TO_POW18,
    /*! # */
    ALT_GPIO_BIT19 = ALT_TWO_TO_POW19,
    /*! # */
    ALT_GPIO_BIT20 = ALT_TWO_TO_POW20,
    /*! # */
    ALT_GPIO_BIT21 = ALT_TWO_TO_POW21,
    /*! # */
    ALT_GPIO_BIT22 = ALT_TWO_TO_POW22,
    /*! # */
    ALT_GPIO_BIT23 = ALT_TWO_TO_POW23,
    /*! # */
    ALT_GPIO_BIT24 = ALT_TWO_TO_POW24,
    /*! # */
    ALT_GPIO_BIT25 = ALT_TWO_TO_POW25,
    /*! # */
    ALT_GPIO_BIT26 = ALT_TWO_TO_POW26,
    /*! # */
    ALT_GPIO_BIT27 = ALT_TWO_TO_POW27,
    /*! # */
    ALT_GPIO_BIT28 = ALT_TWO_TO_POW28,
    ALT_GPIO_BIT29 = ALT_TWO_TO_POW29,              /* Not currently used */
    ALT_GPIO_BIT30 = ALT_TWO_TO_POW30,              /* Not currently used */
    ALT_GPIO_BIT31 = (int32_t) (1UL<<31),           /* Not currently used */

    ALT_GPIO_BITNUM_MAX = (28),
    ALT_GPIO_BIT_MAX = (1 << ALT_GPIO_BITNUM_MAX),
    ALT_END_OF_GPIO_PORT_SIGNALS = (32)
} ALT_GPIO_PORTBIT_t;



/******************************************************************************/
/*!
 * Initialize the GPIO modules before use
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_gpio_init(void);

/******************************************************************************/
/*!
 * Uninitialize the GPIO modules & return to reset state
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 */
ALT_STATUS_CODE alt_gpio_uninit(void);

/******************************************************************************/
/*!
 * Sets the specified GPIO data bits to use the data direction(s)
 * specified.
 *
 *
 * \param       gpio_pid
 *              The GPIO port identifier.
 * \param       mask
 *              The group of bits (where mask bits equal one) to apply this
 *              operation to. Other bits (where mask bits equal zero) are
 *              not changed. Specify mask = ALT_GPIO_BITMASK (0x1FFFFFFF) to
 *              configure all data direction bits of the port.
 * \param       config
 *              The data-directions of the bits to be set in this operation.
 *              Individual bits are: \n \b 0 - Use as an input (default). \n
 *              \b 1 - Use as an output.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   Bad input argument.
 */
ALT_STATUS_CODE alt_gpio_port_datadir_set(ALT_GPIO_PORT_t gpio_pid,
        uint32_t mask, uint32_t config);

/******************************************************************************/
/*!
 * Returns the data direction configuration of selected bits of the
 * specified GPIO module.
 *
 * \param       gpio_pid
 *              The GPIO port identifier.
 * \param       mask
 *              The group of bits (where mask bits equal one) to read and
 *              return. Other bits (where mask bits equal zero) are returned
 *              as zero. Specify mask = ALT_GPIO_BITMASK (0x1FFFFFFF) to
 *              return all data direction bits of the port.
 *
 * \retval      uint32_t \n Individual bits are: \n \b 0 - The signal is
 *              configured as an input.
 *              \n \b 1 - The signal is configured as an output.
 *
 */
uint32_t alt_gpio_port_datadir_get(ALT_GPIO_PORT_t gpio_pid,
        uint32_t mask);

/******************************************************************************/
/*!
 * Sets the GPIO data outputs of the specified GPIO module to a logic one or
 * zero. Outputs are only set if the data direction for those bits is also
 * set to configure them as outputs.
 *
 * \param       gpio_pid
 *              The GPIO port identifier.
 * \param       mask
 *              The group of bits (mask bits equal one) to apply this
 *              operation to. Other bits (mask bits equal zero) are
 *              not changed.
 * \param       val
 *              The 32-bit word to write to the GPIO outputs. Only the 29 LSBs
 *              are used. Setting the three MSBs causes an error.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   Bad input argument.
 */
ALT_STATUS_CODE alt_gpio_port_data_write(ALT_GPIO_PORT_t gpio_pid,
        uint32_t mask, uint32_t val);

/******************************************************************************/
/*!
 * Returns the value of the data inputs of the specified GPIO module. This is
 * the current logic value of the pin, whether set to be an input or an output.
 * \n If a given signal is set to be an output, this input value can be read to
 * determine if the pin is grounded, pulled high, or is floating.
 *
 * \param       gpio_pid
 *              The GPIO port identifier.
 * \param       mask
 *              The group of bits (where mask bits equal one) to return. Other
 *              bits (where mask bits equal zero) are returned as zero. Specify
 *              mask = ALT_GPIO_BITMASK (0x1FFFFFFF) to return all data bits of
 *              the port.
 *
 * \retval      uint32_t   The current value of the GPIO module input signals.
 */
uint32_t alt_gpio_port_data_read(ALT_GPIO_PORT_t gpio_pid, uint32_t mask);


/*! @} */
/******************************************************************************/
/*! \addtogroup ALT_GPIO_INT General-Purpose IO Interrupt Functions
 *
 * This functional group contains functions to control and manage the
 * interrupts of the General-Purpose IO modules.
 *
 * @{
 */
/******************************************************************************/
/*!
 * Sets edge-triggered or level-triggered interrupt configuration for the
 * specified signals of the specified GPIO module.
 *
 *
 * \param       gpio_pid
 *              The GPIO port identifier.
 * \param       mask
 *              The group of bits (where mask bits equal one) to apply this
 *              operation to. Other bits (where mask bits equal zero) are
 *              not changed. Specify mask = ALT_GPIO_BITMASK (0x1FFFFFFF) to
 *              configure all interrupt type bits of the port.
 * \param       config
 *              The interrupt configuration to write. Individual bits
 *              are: \n \b 0 - Set the
 *              interrupt for this bit to be level-sensitive (default). \n \b
 *              1 - Set the interrupt for this bit to be edge-sensitive.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   Invalid input data.
 */
ALT_STATUS_CODE alt_gpio_port_int_type_set(ALT_GPIO_PORT_t gpio_pid,
        uint32_t mask, uint32_t config);

/******************************************************************************/
/*!
 * Returns the interrupt configuration (edge-triggered or level-triggered) for
 * the specified bits of the specified GPIO module.
 *
 * \param       gpio_pid
 *              The GPIO port identifier.
 * \param       mask
 *              The group of bits (where mask bits equal one) to return. Other
 *              bits (where mask bits equal zero) are returned as zero. Specify
 *              mask = ALT_GPIO_BITMASK (0x1FFFFFFF) to return all configuration
 *              bits of the port.
 * \retval      uint32_t
 *              The current interrupt source configuration. Individual bits
 *              are: \n \b 0 - The interrupt for this bit is set to be
 *              level-sensitive. \n \b 1 -
 *              The interrupt for this bit is set to be edge-sensitive.
 *
 */
uint32_t alt_gpio_port_int_type_get(ALT_GPIO_PORT_t gpio_pid,
        uint32_t mask);

/******************************************************************************/
/*!
 * Sets the interrupt polarity of the signals of the specified GPIO register
 * (when used as inputs) to active-high or active-low (for level-sensitive
 * interrupts) or to rising-edge or falling-edge (for edge-sensitive interrupts).
 *
 * \param       gpio_pid
 *              The GPIO port identifier.
 * \param       mask
 *              The group of bits (where mask bits equal one) to apply this
 *              operation to. Other bits (where mask bits equal zero) are
 *              not changed.
 * \param       config
 *              The interrupt polarity configuration to set. Individual bits
 *              are: \n \b 0 - Set the interrupt polarity for this bit to
 *              active-low or falling-edge mode (default). \n \b 1 - Set the
 *              interrupt polarity for this bit to active-high or rising-edge mode.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   Invalid input data.
 */
ALT_STATUS_CODE alt_gpio_port_int_pol_set(ALT_GPIO_PORT_t gpio_pid,
        uint32_t mask, uint32_t config);

/******************************************************************************/
/*!
 * Returns the active-high or active-low polarity configuration for the
 * possible interrupt sources of the specified GPIO module.
 *
 *
 * \param       gpio_pid
 *              The GPIO port identifier.
 * \param       mask
 *              The group of bits (where mask bits equal one) to return. Other
 *              bits (where mask bits equal zero) are returned as zero. Specify
 *              mask = ALT_GPIO_BITMASK (0x1FFFFFFF) to return all the
 *              configuration bits of the port.
 *
 * \retval      uint32_t
 *              The current polarity configuration. Individual bits are: \n
 *              \b 0 = The interrupt polarity for this bit is set to
 *              active-low or falling-edge mode. \n \b 1 = The interrupt
 *              polarity for this bit is set to active-high or rising-edge mode.
 *
 */
uint32_t alt_gpio_port_int_pol_get(ALT_GPIO_PORT_t gpio_pid,
        uint32_t mask);


/*! @} */
/******************************************************************************/
/*! \addtogroup ALT_GPIO_API_CONFIG General-Purpose IO Configuration Functions
 *
 * @{
 */
/******************************************************************************/
/*!
 * Sets the debounce configuration for input signals of the specified GPIO
 * module. If debounce is selected, metastability flip-flops are inserted to
 * debounce signals presented to the GPIO inputs. A signal must be steady for
 * two periods of the gpio_db_clk clock before it is considered valid. The
 * frequency of the gpio_db_clk clock may be set using the Clock Manager API.
 *
 * \param       gpio_pid
 *              The GPIO port identifier.
 * \param       mask
 *              The group of bits (where mask bits equal one) to apply this
 *              operation to. Other bits (where mask bits equal zero) are
 *              not changed. Specify mask = ALT_GPIO_BITMASK (0x1FFFFFFF) to
 *              configure the debounce setting for all bits of the port.
 * \param       config
 *              The debounce configuration to set. Individual bits are: \n
 *              \b 0 - Debounce is not selected for this signal (default). \n
 *              \b 1 - Debounce is selected for this signal.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   Invalid input data.
 */
ALT_STATUS_CODE alt_gpio_port_debounce_set(ALT_GPIO_PORT_t gpio_pid,
        uint32_t mask, uint32_t config);

/******************************************************************************/
/*!
 * Returns the debounce configuration for the input signals of the specified
 * GPIO register. If debounce is selected, metastability flip-flops are
 * inserted to debounce signals presented to the GPIO inputs.
 *
 * \param       gpio_pid
 *              The GPIO port identifier.
 * \param       mask
 *              The group of bits (where mask bits equal one) to return. Other
 *              bits (where mask bits equal zero) are returned as zero. Specify
 *              mask = ALT_GPIO_BITMASK (0x1FFFFFFF) to return all debounce
 *              configuration bits of the port.
 *
 * \retval      uint32_t
 *              The current debounce configuration.Individual bits are: \n
 *              \b 0 - Debounce is not selected for this signal. \n \b 1 -
 *              Debounce is selected for this signal.
 *
 */
uint32_t alt_gpio_port_debounce_get(ALT_GPIO_PORT_t gpio_pid,
        uint32_t mask);

/******************************************************************************/
/*!
 * Sets the synchronization configuration for the signals of the specified
 * GPIO register. This allows for synchronizing level-sensitive interrupts to
 * an internal clock signal. This is a port-wide option that controls all
 * level-sensitive interrupt signals of that GPIO port.
 *
 * \param       gpio_pid
 *              The GPIO port identifier.
 * \param       config
 *              \n \b Any \b non-zero \b value - Synchronize to internal clock signal.
 *              \n \b Zero - Do not synchronize to internal clock signal.
 *
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   Invalid input data.
 */
ALT_STATUS_CODE alt_gpio_port_sync_set(ALT_GPIO_PORT_t gpio_pid,
        uint32_t config);

/******************************************************************************/
/*!
 *
 * Returns the synchronization configuration for the signals of the
 * specified GPIO register. This allows for synchronizing level-sensitive
 * interrupts to the internal clock signal. This is a port-wide option that
 * controls all level-sensitive interrupt signals of that GPIO port.
 *
 * \param       gpio_pid
 *              The GPIO port identifier.


 * \retval      ALT_E_TRUE      Synchronization to clock is enabled for
 *                              level-sensitive interrupts.
 * \retval      ALT_E_FALSE     Synchronization to clock is disabled for
 *                              level-sensitive interrupts.
 * \retval      ALT_E_BAD_ARG   Invalid input argument.
 */
ALT_STATUS_CODE alt_gpio_port_sync_get(ALT_GPIO_PORT_t gpio_pid);

/******************************************************************************/
/*!
 * Configures a group of GPIO signals with identical setup parameters. Allows
 * for configuring all parameters of a given port at one time.
 *
 * \param       gpio_pid
 *              The GPIO port identifier.
 * \param       mask
 *              The group of bits to apply this operation to. Other bits (mask
 *              set to zero) are not changed.
 * \param       dir
 *              Data direction.
 * \param       type
 *              Edge-triggered or level-triggered interrupts.
 * \param       pol
 *              Active-high or active-low polarity.
 * \param       debounc
 *              Debounce signals or not.
 * \param       data
 *              Set the data output to this value.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   Invalid input argument.

 */
ALT_STATUS_CODE alt_gpio_port_config(ALT_GPIO_PORT_t gpio_pid,
        uint32_t mask, ALT_GPIO_PIN_DIR_t dir, ALT_GPIO_PIN_TYPE_t type,
        ALT_GPIO_PIN_POL_t pol, ALT_GPIO_PIN_DEBOUNCE_t debounc,
        uint32_t data);

/*! @} */
/******************************************************************************/
/*! \addtogroup ALT_GPIO_INT General-Purpose IO Interrupt Functions
 *
 *  @{
 */
/******************************************************************************/
/*!
 * Enables the specified GPIO data input interrupts.
 *
 *
 * \param       gpio_pid
 *              The GPIO port identifier.
 * \param       config
 *              Individual bit interrupt enables \n
 *              \b 0 - Interrupt disabled. \n
 *              \b 1 - Interrupt enabled.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   Bad input argument.
 */
ALT_STATUS_CODE alt_gpio_port_int_enable(ALT_GPIO_PORT_t gpio_pid, uint32_t config);

/******************************************************************************/
/*!
 * Disables the specified GPIO data module interrupt.
 *
 *
 * \param       gpio_pid
 *              The GPIO port identifier.
 * \param       config
 *              Individual bit interrupt enables \n
 *              \b 0 - Interrupt disabled. \n
 *              \b 1 - Interrupt enabled.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   Bad input argument.
 */
ALT_STATUS_CODE alt_gpio_port_int_disable(ALT_GPIO_PORT_t gpio_pid, uint32_t config);

/******************************************************************************/
/*!
 *  Returns the current state of the specified GPIO port interrupts enables.
 *
 * \param       gpio_pid
 *              The GPIO port identifier.
 *
 * \retval      uint32_t
 *              The interrupt enable configuration that was read. Individual bits
 *              are: \n \b 0 = The interrupt for this bit is not enabled. \n \b
 *              1 = The interrupt for this bit is enabled.
 */
uint32_t alt_gpio_port_int_enable_get(ALT_GPIO_PORT_t gpio_pid);


/******************************************************************************/
/*!
 * Masks or unmasks selected interrupt source bits of the data register of
 * the specified GPIO module. Uses a second bit mask to determine which
 * signals may be changed by this call.
 *
 *
 * \param       gpio_pid
 *              The GPIO port identifier.
 * \param       mask
 *              Which bits to change among the port \n \b 0 =
 *              Do not change this bit. \n \b 1 = Allow this bit to change.
 * \param       val
 *              The interrupt mask to write. Individual bits are: \n \b 0 =
 *              Do not mask the interrupt for this bit (default). \n \b 1 =
 *              Mask the interrupt for this bit.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   Invalid input data.
 */
ALT_STATUS_CODE alt_gpio_port_int_mask_set(ALT_GPIO_PORT_t gpio_pid,
        uint32_t mask, uint32_t val);

/******************************************************************************/
/*!
 * Returns the interrupt mask of the specified GPIO module.
 *
 *
 * \param       gpio_pid
 *              The GPIO port identifier.
 *
 * \retval      uint32_t
 *              The interrupt mask that was read. Individual bits are: \n
 *              \b 0 = The interrupt for this bit is not masked. \n \b 1 = The
 *              interrupt for this bit is masked.
 *
 */
uint32_t alt_gpio_port_int_mask_get(ALT_GPIO_PORT_t gpio_pid);

/******************************************************************************/
/*!
 * Returns the interrupt pending status of all signals of the specified GPIO
 * register.
 *
 *
 * \param       gpio_pid
 *              The GPIO port identifier.

 * \retval      uint32_t
 *              The current interrupt pending status. Individual bits are: \n
 *              \b 0 - The interrupt for this bit is not pending. \n \b 1 -
 *              The interrupt for this bit is pending.
 *
 */
uint32_t alt_gpio_port_int_status_get(ALT_GPIO_PORT_t gpio_pid);

/******************************************************************************/
/*!
 * Clear the interrupt pending status of selected signals of the
 * specified GPIO register.
 *
 *
 * \param       gpio_pid
 *              The GPIO port identifier.
 * \param       clrmask
 *              The interrupt bits to clear. Individual bits are: \n \b 0 -
 *              The interrupt for this bit will not be changed. \n \b 1 -
 *              The interrupt for this bit will be cleared.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   Invalid input data.
 */
ALT_STATUS_CODE alt_gpio_port_int_status_clear(ALT_GPIO_PORT_t gpio_pid,
        uint32_t clrmask);

/*! @} */

/******************************************************************************/
/*! \addtogroup ALT_GPIO_BITVIEW General-Purpose IO via Bit Index
 *
 * This functional group presents a perspective of the General-Purpose IO
 * signals as individual GPIO and GPI bits spread across a number of signals
 * across several GPIO ports. This allows the programmer the freedom to generally
 * ignore the underlying port and signal structure of the GPIO hardware if
 * desired.
 *
 * @{
 */
/******************************************************************************/
/*!
 * This type definition enumerates the individual bits as one flat array spread
 * across the multiple GPIO ports handled by the GPIO manager. The bit-ordering
 * must match the hardware bit-ordering.
 *
 */
typedef enum ALT_GPIO_1BIT_e
{
    /*! # */
    ALT_GPIO_1BIT_0,
    /*! # */
    ALT_GPIO_1BIT_1,
    /*! # */
    ALT_GPIO_1BIT_2,
    /*! # */
    ALT_GPIO_1BIT_3,
    /*! # */
    ALT_GPIO_1BIT_4,
    /*! # */
    ALT_GPIO_1BIT_5,
    /*! # */
    ALT_GPIO_1BIT_6,
    /*! # */
    ALT_GPIO_1BIT_7,
    /*! # */
    ALT_GPIO_1BIT_8,
    /*! # */
    ALT_GPIO_1BIT_9,
    /*! # */
    ALT_GPIO_1BIT_10,
    /*! # */
    ALT_GPIO_1BIT_11,
    /*! # */
    ALT_GPIO_1BIT_12,
    /*! # */
    ALT_GPIO_1BIT_13,
    /*! # */
    ALT_GPIO_1BIT_14,
    /*! # */
    ALT_GPIO_1BIT_15,
    /*! # */
    ALT_GPIO_1BIT_16,
    /*! # */
    ALT_GPIO_1BIT_17,
    /*! # */
    ALT_GPIO_1BIT_18,
    /*! # */
    ALT_GPIO_1BIT_19,
    /*! # */
    ALT_GPIO_1BIT_20,
    /*! # */
    ALT_GPIO_1BIT_21,
    /*! # */
    ALT_GPIO_1BIT_22,
    /*! # */
    ALT_GPIO_1BIT_23,
    /*! # */
    ALT_GPIO_1BIT_24,
    /*! # */
    ALT_GPIO_1BIT_25,
    /*! # */
    ALT_GPIO_1BIT_26,
    /*! # */
    ALT_GPIO_1BIT_27,
    /*! # */
    ALT_GPIO_1BIT_28,
    /*! # */
    ALT_GPIO_1BIT_29,
    /*! # */
    ALT_GPIO_1BIT_30,
    /*! # */
    ALT_GPIO_1BIT_31,
    /*! # */
    ALT_GPIO_1BIT_32,
    /*! # */
    ALT_GPIO_1BIT_33,
    /*! # */
    ALT_GPIO_1BIT_34,
    /*! # */
    ALT_GPIO_1BIT_35,
    /*! # */
    ALT_GPIO_1BIT_36,
    /*! # */
    ALT_GPIO_1BIT_37,
    /*! # */
    ALT_GPIO_1BIT_38,
    /*! # */
    ALT_GPIO_1BIT_39,
    /*! # */
    ALT_GPIO_1BIT_40,
    /*! # */
    ALT_GPIO_1BIT_41,
    /*! # */
    ALT_GPIO_1BIT_42,
    /*! # */
    ALT_GPIO_1BIT_43,
    /*! # */
    ALT_GPIO_1BIT_44,
    /*! # */
    ALT_GPIO_1BIT_45,
    /*! # */
    ALT_GPIO_1BIT_46,
    /*! # */
    ALT_GPIO_1BIT_47,
    /*! # */
    ALT_GPIO_1BIT_48,
    /*! # */
    ALT_GPIO_1BIT_49,
    /*! # */
    ALT_GPIO_1BIT_50,
    /*! # */
    ALT_GPIO_1BIT_51,
    /*! # */
    ALT_GPIO_1BIT_52,
    /*! # */
    ALT_GPIO_1BIT_53,
    /*! # */
    ALT_GPIO_1BIT_54,
    /*! # */
    ALT_GPIO_1BIT_55,
    /*! # */
    ALT_GPIO_1BIT_56,
    /*! # */
    ALT_GPIO_1BIT_57,
    /*! # */
    ALT_GPIO_1BIT_58,
    /*! # */
    ALT_GPIO_1BIT_59,
    /*! # */
    ALT_GPIO_1BIT_60,
    /*! # */
    ALT_GPIO_1BIT_61,
    /*! # */
    ALT_GPIO_1BIT_62,
    /*! # */
    ALT_GPIO_1BIT_63,
    /*! # */
    ALT_GPIO_1BIT_64,
    /*! # */
    ALT_GPIO_1BIT_65,
    /*! # */
    ALT_GPIO_1BIT_66,
    /*! # */
    ALT_GPIO_1BIT_67,        /* Not bonded out on some versions */
    /*! # */
    ALT_GPIO_1BIT_68,        /* Not bonded out on some versions */
    /*! # */
    ALT_GPIO_1BIT_69,        /* Not bonded out on some versions */

    /*! The last of the input/output bits */
    ALT_GPIO_1BIT_70,        /* Not bonded out on some versions */


    /*! This and the following signals are not present on all SoCs. \n
     * If present, the selection between their use as 14 General-purpose inputs or
     * use as 14 DDR interface signals is made in the IOCSR (IO Configuration Shift
     * Register) and software to make this selection is in the IO Manager API. If
     * they are present, they are restricted to using the same power supply voltage
     * as the SDRAM module.*/
    ALT_HLGPI_0,        /* Not bonded out on some versions */
    /*! # */
    ALT_HLGPI_1,        /* Not bonded out on some versions */
    /*! # */
    ALT_HLGPI_2,        /* Not bonded out on some versions */
    /*! # */
    ALT_HLGPI_3,        /* Not bonded out on some versions */
    /*! # */
    ALT_HLGPI_4,        /* Not bonded out on some versions */
    /*! # */
    ALT_HLGPI_5,        /* Not bonded out on some versions */
    /*! # */
    ALT_HLGPI_6,        /* Not bonded out on some versions */
    /*! # */
    ALT_HLGPI_7,        /* Not bonded out on some versions */
    /*! # */
    ALT_HLGPI_8,        /* Not bonded out on some versions */
    /*! # */
    ALT_HLGPI_9,        /* Not bonded out on some versions */
    /*! # */
    ALT_HLGPI_10,       /* Not bonded out on some versions */
    /*! # */
    ALT_HLGPI_11,       /* Not bonded out on some versions */
    /*! # */
    ALT_HLGPI_12,       /* Not bonded out on some versions */
    /*! # */
    ALT_HLGPI_13,       /* Not bonded out on some versions */

    ALT_HLGPI_14,       /* Not bonded out */

    ALT_HLGPI_15,       /* Not bonded out */

    ALT_GPIO_INVALID,
    ALT_END_OF_GPIO_SIGNALS = -1,
    ALT_LAST_VALID_GPIO_BIT = ALT_HLGPI_15
} ALT_GPIO_1BIT_t;


/******************************************************************************/
/*!
 * This configuration record definition is used for configuring bits and
 * groups of bits of the GPIO interface.
 */
typedef struct ALT_GPIO_CONFIG_RECORD_s
{
    /*!
     * The index number of the signal to configure. */
    ALT_GPIO_1BIT_t             signal_number;
    /*!
     * The data direction of the signal. */
    ALT_GPIO_PIN_DIR_t          direction;
    /*!
     * Edge-triggered or level triggered interrupts. */
    ALT_GPIO_PIN_TYPE_t         type;
    /*!
     * Active-high or active-low trigger for the interrupt. */
    ALT_GPIO_PIN_POL_t          polarity;
    /*!
     * Enable or disable GPIO debounce capability. */
    ALT_GPIO_PIN_DEBOUNCE_t     debounce;
    /*!
     * If the signal is an output, the data value to be output. */
    ALT_GPIO_PIN_DATA_t         data;
} ALT_GPIO_CONFIG_RECORD_t;

/******************************************************************************/
/*!
 * This pin record type definition is comprised of the signal index and
 * associated input or output data.
 */
typedef struct ALT_GPIO_PIN_RECORD_s
{
    /*!
     * The index number of the signal. */
    ALT_GPIO_1BIT_t         signal_number;
    /*!
     * Data - zero or one. */
    ALT_GPIO_PIN_DATA_t     val;
} ALT_GPIO_PIN_RECORD_t;

/*! @} */

/******************************************************************************/
/*! \addtogroup ALT_GPIO_BITVIEW General-Purpose IO via Bit Index
 *
 * @{
 */
/******************************************************************************/
/*!
 * Configures all parameters for one bit (signal) of the GPIO ports.
 *
 * \param       signal_num
 *              The GPIO port signal index.
 * \param       dir
 *              The data direction for this signal.
 * \param       type
 *              Edge-triggered or Level-triggered interrupt for this signal.
 * \param       pol
 *              Active-high or active-low interrupt polarity for this signal.
 * \param       debounce
 *              Enable the debounce flip-flops for this signal or not.
 * \param       data
 *              If the GPIO signal is set to be an output, set it to
 *              this value
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   Invalid input argument.
 */
ALT_STATUS_CODE alt_gpio_bit_config(ALT_GPIO_1BIT_t signal_num,
        ALT_GPIO_PIN_DIR_t dir, ALT_GPIO_PIN_TYPE_t type,
        ALT_GPIO_PIN_POL_t pol, ALT_GPIO_PIN_DEBOUNCE_t debounce,
        ALT_GPIO_PIN_DATA_t data);

/******************************************************************************/
/*!
 * Returns the configuration parameters of a given GPIO bit.
 *
 * \param       signal_num
 *              The GPIO port signal index.
 * \param       config
 *              Pointer to a single GPIO_CONFIG_RECORD_s configuration record.
 *              The fields of this configuration record are filled in
 *              by the function.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   Invalid input argument.

 */
ALT_STATUS_CODE alt_gpio_bitconfig_get(ALT_GPIO_1BIT_t signal_num,
        ALT_GPIO_CONFIG_RECORD_t *config);

/******************************************************************************/
/*!
 * Configures a list of GPIO bits. The GPIO bits do not have to be
 * configured the same, as was the case for the mask version of this function,
 * alt_gpio_port_config(). Each bit may be configured differently and bits may
 * be listed in any order.
 *
 * \param       config_array
 *              Pointer to an array of GPIO_CONFIG_RECORD_s configuration
 *              records. These definitions contain all the parameters
 *              needed to set up the listed pins. All or
 *              any subset of the GPIO signals can be configured. Signals do
 *              not have to be listed in numerical order or be unique. If a
 *              signal number is listed multiple times, the last configuration
 *              listed is used. \n Configuration terminates either when \b len
 *              signals have been configured or if the next signal number index
 *              in the array is equal to \b ALT_END_OF_GPIO_SIGNALS (-1).
 *
 * \param       len
 *              Length of array to configure.
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   Invalid input argument.

 */
ALT_STATUS_CODE alt_gpio_group_config(ALT_GPIO_CONFIG_RECORD_t* config_array,
        uint32_t len);

/******************************************************************************/
/*!
 * Returns a list of the pin signal indices and the associated configuration
 * settings (data direction, interrupt type, polarity, and debounce) of that
 * list of signals.
 *
 * \param       config_array
 *              Pointer to an array of ALT_GPIO_CONFIG_RECORD_t configuration
 *              records. Only the signal indices in the first field of each
 *              configuration record need be filled in. This function will
 *              fill in all the other fields of the configuration record,
 *              returning all configuration parameters in the array.
 *              Signals do not have to be listed in numerical order or be
 *              unique. If a signal number is listed multiple times, the
 *              configuration record will contain multiple entries for
 *              that signal. \n Configuration reading terminates either when
 *              \b len signal configurations have been read or if the next
 *              signal number index in the array is equal to
 *              \b ALT_END_OF_GPIO_SIGNALS (-1).
 * \param       len
 *              Length of configuration array to read and return.
 *
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   Invalid input argument.

 */
ALT_STATUS_CODE alt_gpio_group_config_get(ALT_GPIO_CONFIG_RECORD_t *config_array,
        uint32_t len);

/******************************************************************************/
/*!
 * Returns a list of the pin signal indices and the associated configuration
 * settings (data direction, interrupt type, polarity, and debounce) of that
 * list of signals. The difference between this version and
 * alt_gpio_group_config_get() is this version follows a separate list of
 * signal indices instead of having the signal list provided in the first
 * field of the configuration records in the array.
 *
 * \param       pinid_array
 *              Pointer to a list of signal index numbers. These indices
 *              are copied to the first field of each configuration record
 *              in the returned array.
 * \param       config_array
 *              Pointer to an array of ALT_GPIO_CONFIG_RECORD_t configuration
 *              records. This function will fill in the fields of the
 *              configuration record, returning all configuration parameters
 *              in the array. Signals do not have to be listed in numerical
 *              order or be unique. If a signal number is listed multiple
 *              times, the configuration record array will contain multiple
 *              identical entries for that signal. \n Configuration reading
 *              terminates either when \b len signal configurations have been
 *              read or if the next signal number index in the array is equal
 *              to \b ALT_END_OF_GPIO_SIGNALS (-1).
 * \param       len
 *              Length of configuration array to read.
 *
 *
 * \retval      ALT_E_SUCCESS   The operation was successful.
 * \retval      ALT_E_ERROR     The operation failed.
 * \retval      ALT_E_BAD_ARG   Invalid input argument.
 *
 */
ALT_STATUS_CODE alt_gpio_group_config_get2(ALT_GPIO_1BIT_t* pinid_array,
        ALT_GPIO_CONFIG_RECORD_t *config_array, uint32_t len);


/*! @} */
/******************************************************************************/
/*! \addtogroup ALT_GPIO_UTILITY General-Purpose IO Utility Functions
 *
 * These are useful utility functions for the general-purpose input & output
 * module.
 *
 * @{ */
/******************************************************************************/
/*!
 * Returns the ID code of the specified GPIO module.
 *
 * \param       gpio_pid
 *              The GPIO port identifier.
 *
 *
 * \retval      uint32_t    The component code of the module, GPIO_MODULE_IDCODE.
 */
uint32_t alt_gpio_port_idcode_get(ALT_GPIO_PORT_t gpio_pid);

/******************************************************************************/
/*!
 * Returns the version code of the specified GPIO module.
 *
 * \param       gpio_pid
 *              The GPIO port identifier.
 *
 *
 * \retval      uint32_t      The encoded revision number of the module.
 */
uint32_t alt_gpio_port_ver_get(ALT_GPIO_PORT_t gpio_pid);


/******************************************************************************/
/*!
 * Extracts the GPIO port ID from the supplied GPIO Signal Index Number.
 */
ALT_GPIO_PORT_t alt_gpio_bit_to_pid(ALT_GPIO_1BIT_t pin_num);


/******************************************************************************/
/*!
 * Extracts the GPIO signal (pin) offset from the supplied GPIO Signal Index
 * Number.
 *  */
ALT_GPIO_PORTBIT_t alt_gpio_bit_to_port_pin(ALT_GPIO_1BIT_t pin_num);

/******************************************************************************/
/*!
 * Extracts the GPIO Signal Index Number from the supplied GPIO port ID and
 * signal mask. If passed a bitmask composed of more than one signal, the
 * signal number of the lowest bit in the bitmask presented is returned.
 *
 */
ALT_GPIO_1BIT_t alt_gpio_port_pin_to_bit(ALT_GPIO_PORT_t pid,
        uint32_t bitmask);


/*! @} */
/*! @} */

#ifdef __cplusplus
}
#endif  /* __cplusplus */
#endif  /* __ALT_GPIO_H__ */
