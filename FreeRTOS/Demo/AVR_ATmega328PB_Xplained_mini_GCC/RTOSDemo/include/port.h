

/**
 * \file
 *
 * \brief Tinymega Port related support
 *
 (c) 2018 Microchip Technology Inc. and its subsidiaries.

    Subject to your compliance with these terms,you may use this software and
    any derivatives exclusively with Microchip products.It is your responsibility
    to comply with third party license terms applicable to your use of third party
    software (including open source software) that may accompany Microchip software.

    THIS SOFTWARE IS SUPPLIED BY MICROCHIP "AS IS". NO WARRANTIES, WHETHER
    EXPRESS, IMPLIED OR STATUTORY, APPLY TO THIS SOFTWARE, INCLUDING ANY IMPLIED
    WARRANTIES OF NON-INFRINGEMENT, MERCHANTABILITY, AND FITNESS FOR A
    PARTICULAR PURPOSE.

    IN NO EVENT WILL MICROCHIP BE LIABLE FOR ANY INDIRECT, SPECIAL, PUNITIVE,
    INCIDENTAL OR CONSEQUENTIAL LOSS, DAMAGE, COST OR EXPENSE OF ANY KIND
    WHATSOEVER RELATED TO THE SOFTWARE, HOWEVER CAUSED, EVEN IF MICROCHIP HAS
    BEEN ADVISED OF THE POSSIBILITY OR THE DAMAGES ARE FORESEEABLE. TO THE
    FULLEST EXTENT ALLOWED BY LAW, MICROCHIP'S TOTAL LIABILITY ON ALL CLAIMS IN
    ANY WAY RELATED TO THIS SOFTWARE WILL NOT EXCEED THE AMOUNT OF FEES, IF ANY,
    THAT YOU HAVE PAID DIRECTLY TO MICROCHIP FOR THIS SOFTWARE.
 *
 */

#ifndef PORT_INCLUDED
#define PORT_INCLUDED

#ifdef __cplusplus
extern "C" {
#endif

#include <compiler.h>
#include <stdint.h>
#include <stdbool.h>
#include <compiler.h>

enum port_pull_mode {
	PORT_PULL_OFF,
	PORT_PULL_UP,
};

enum port_dir {
	PORT_DIR_IN,
	PORT_DIR_OUT,
	PORT_DIR_OFF,
};

/**
 * \brief Set PORTB pin pull mode
 *
 * Configure pin to pull up, down or disable pull mode, supported pull
 * modes are defined by device used
 *
 * \param[in] pin       The pin number in PORTB
 * \param[in] pull_mode Pin pull mode
 */
static inline void PORTB_set_pin_pull_mode(const uint8_t pin, const enum port_pull_mode pull_mode)
{

	if (pull_mode == PORT_PULL_UP) {

		DDRB &= ~(1 << pin);

		PORTB |= 1 << pin;
	} else if (pull_mode == PORT_PULL_OFF) {

		PORTB &= ~(1 << pin);
	}
}

/**
 * \brief Set PORTB data direction
 *
 * Select if the port pins selected by mask data direction is input, output
 * or disabled.
 *
 * \param[in] mask      Bit mask where 1 means apply direction setting to the
 *                      corresponding pin
 * \param[in] direction PORT_DIR_IN  = Data direction in
 *                      PORT_DIR_OUT = Data direction out
 *                      PORT_DIR_OFF = Disables the pin
 *                      (low power state)
 */
static inline void PORTB_set_port_dir(const uint8_t mask, const enum port_dir direction)
{
	switch (direction) {
	case PORT_DIR_IN:
		DDRB &= ~mask;
		break;
	case PORT_DIR_OUT:
		DDRB |= mask;
		break;
	case PORT_DIR_OFF:
		DDRB &= ~mask;

		PORTB |= mask;
		break;
	default:
		break;
	}
}

/**
 * \brief Set PORTB single pin data direction
 *
 * Select if the pin data direction is input, output or disabled.
 * If disabled state is not possible, this function throws an assert.
 *
 * \param[in] pin       The pin number within PORTB (0..7)
 * \param[in] direction PORT_DIR_IN  = Data direction in
 *                      PORT_DIR_OUT = Data direction out
 *                      PORT_DIR_OFF = Disables the pin
 *                      (low power state)
 */
static inline void PORTB_set_pin_dir(const uint8_t pin, const enum port_dir direction)
{
	switch (direction) {
	case PORT_DIR_IN:
		DDRB &= ~(1 << pin);
		break;
	case PORT_DIR_OUT:
		DDRB |= 1 << pin;
		break;
	case PORT_DIR_OFF:
		DDRB &= ~(1 << pin);

		PORTB |= 1 << pin;
		break;
	default:
		break;
	}
}

/**
 * \brief Set PORTB level
 *
 * Sets output level on the pins defined by the bit mask
 *
 * \param[in] mask  Bit mask where 1 means apply port level to the corresponding
 *                  pin
 * \param[in] level true  = Pin levels set to "high" state
 *                  false = Pin levels set to "low" state
 */
static inline void PORTB_set_port_level(const uint8_t mask, const bool level)
{
	if (level) {
		PORTB |= mask;
	} else {
		PORTB &= ~mask;
	}
}

/**
 * \brief Set PORTB level
 *
 * Sets output level on a pin
 *
 * \param[in] pin       The pin number for device
 * \param[in] level true  = Pin level set to "high" state
 *                  false = Pin level set to "low" state
 */
static inline void PORTB_set_pin_level(const uint8_t pin, const bool level)
{
	if (level) {
		PORTB |= 1 << pin;
	} else {
		PORTB &= ~(1 << pin);
	}
}

/**
 * \brief Toggle out level on pins
 *
 * Toggle the pin levels on pins defined by bit mask
 *
 * \param[in] port  Ports are grouped into groups of maximum 32 pins,
 *                  PORT_PORTA = group 0, PORT_PORTB = group 1, etc
 * \param[in] mask  Bit mask where 1 means toggle pin level to the corresponding
 *                  pin
 */
static inline void PORTB_toggle_port_level(const uint8_t mask)
{
	PINB = mask;
}

/**
 * \brief Toggle output level on pin
 *
 * Toggle the pin levels on pin
 *
 * \param[in] pin       The pin number for device
 */
static inline void PORTB_toggle_pin_level(const uint8_t pin)
{
	PINB = 1 << pin;
}

/**
 * \brief Get input level on pins
 *
 * Read the input level on pins connected to a port
 *
 * \param[in] port  Ports are grouped into groups of maximum 32 pins,
 *                  PORT_PORTA = group 0, PORT_PORTB = group 1, etc
 */
static inline uint8_t PORTB_get_port_level(volatile uint8_t *port)
{
	return PINB;
}

/**
 * \brief Get level on pin
 *
 * Reads the level on a pin connected to a port
 *
 * \param[in] pin       The pin number for device
 */
static inline bool PORTB_get_pin_level(const uint8_t pin)
{
	return PINB & (1 << pin);
}

/**
 * \brief Write value to PORTB
 *
 * Write directly to the entire port register.
 *
 * \param[in] value   Value to write
 */
static inline void PORTB_write_port(const uint8_t value)
{
	PORTB = value;
}

/**
 * \brief Set PORTC pin pull mode
 *
 * Configure pin to pull up, down or disable pull mode, supported pull
 * modes are defined by device used
 *
 * \param[in] pin       The pin number in PORTC
 * \param[in] pull_mode Pin pull mode
 */
static inline void PORTC_set_pin_pull_mode(const uint8_t pin, const enum port_pull_mode pull_mode)
{

	if (pull_mode == PORT_PULL_UP) {

		DDRC &= ~(1 << pin);

		PORTC |= 1 << pin;
	} else if (pull_mode == PORT_PULL_OFF) {

		PORTC &= ~(1 << pin);
	}
}

/**
 * \brief Set PORTC data direction
 *
 * Select if the port pins selected by mask data direction is input, output
 * or disabled.
 *
 * \param[in] mask      Bit mask where 1 means apply direction setting to the
 *                      corresponding pin
 * \param[in] direction PORT_DIR_IN  = Data direction in
 *                      PORT_DIR_OUT = Data direction out
 *                      PORT_DIR_OFF = Disables the pin
 *                      (low power state)
 */
static inline void PORTC_set_port_dir(const uint8_t mask, const enum port_dir direction)
{
	switch (direction) {
	case PORT_DIR_IN:
		DDRC &= ~mask;
		break;
	case PORT_DIR_OUT:
		DDRC |= mask;
		break;
	case PORT_DIR_OFF:
		DDRC &= ~mask;

		PORTC |= mask;
		break;
	default:
		break;
	}
}

/**
 * \brief Set PORTC single pin data direction
 *
 * Select if the pin data direction is input, output or disabled.
 * If disabled state is not possible, this function throws an assert.
 *
 * \param[in] pin       The pin number within PORTC (0..7)
 * \param[in] direction PORT_DIR_IN  = Data direction in
 *                      PORT_DIR_OUT = Data direction out
 *                      PORT_DIR_OFF = Disables the pin
 *                      (low power state)
 */
static inline void PORTC_set_pin_dir(const uint8_t pin, const enum port_dir direction)
{
	switch (direction) {
	case PORT_DIR_IN:
		DDRC &= ~(1 << pin);
		break;
	case PORT_DIR_OUT:
		DDRC |= 1 << pin;
		break;
	case PORT_DIR_OFF:
		DDRC &= ~(1 << pin);

		PORTC |= 1 << pin;
		break;
	default:
		break;
	}
}

/**
 * \brief Set PORTC level
 *
 * Sets output level on the pins defined by the bit mask
 *
 * \param[in] mask  Bit mask where 1 means apply port level to the corresponding
 *                  pin
 * \param[in] level true  = Pin levels set to "high" state
 *                  false = Pin levels set to "low" state
 */
static inline void PORTC_set_port_level(const uint8_t mask, const bool level)
{
	if (level) {
		PORTC |= mask;
	} else {
		PORTC &= ~mask;
	}
}

/**
 * \brief Set PORTC level
 *
 * Sets output level on a pin
 *
 * \param[in] pin       The pin number for device
 * \param[in] level true  = Pin level set to "high" state
 *                  false = Pin level set to "low" state
 */
static inline void PORTC_set_pin_level(const uint8_t pin, const bool level)
{
	if (level) {
		PORTC |= 1 << pin;
	} else {
		PORTC &= ~(1 << pin);
	}
}

/**
 * \brief Toggle out level on pins
 *
 * Toggle the pin levels on pins defined by bit mask
 *
 * \param[in] port  Ports are grouped into groups of maximum 32 pins,
 *                  PORT_PORTA = group 0, PORT_PORTB = group 1, etc
 * \param[in] mask  Bit mask where 1 means toggle pin level to the corresponding
 *                  pin
 */
static inline void PORTC_toggle_port_level(const uint8_t mask)
{
	PINC = mask;
}

/**
 * \brief Toggle output level on pin
 *
 * Toggle the pin levels on pin
 *
 * \param[in] pin       The pin number for device
 */
static inline void PORTC_toggle_pin_level(const uint8_t pin)
{
	PINC = 1 << pin;
}

/**
 * \brief Get input level on pins
 *
 * Read the input level on pins connected to a port
 *
 * \param[in] port  Ports are grouped into groups of maximum 32 pins,
 *                  PORT_PORTA = group 0, PORT_PORTB = group 1, etc
 */
static inline uint8_t PORTC_get_port_level(volatile uint8_t *port)
{
	return PINC;
}

/**
 * \brief Get level on pin
 *
 * Reads the level on a pin connected to a port
 *
 * \param[in] pin       The pin number for device
 */
static inline bool PORTC_get_pin_level(const uint8_t pin)
{
	return PINC & (1 << pin);
}

/**
 * \brief Write value to PORTC
 *
 * Write directly to the entire port register.
 *
 * \param[in] value   Value to write
 */
static inline void PORTC_write_port(const uint8_t value)
{
	PORTC = value;
}

/**
 * \brief Set PORTD pin pull mode
 *
 * Configure pin to pull up, down or disable pull mode, supported pull
 * modes are defined by device used
 *
 * \param[in] pin       The pin number in PORTD
 * \param[in] pull_mode Pin pull mode
 */
static inline void PORTD_set_pin_pull_mode(const uint8_t pin, const enum port_pull_mode pull_mode)
{

	if (pull_mode == PORT_PULL_UP) {

		DDRD &= ~(1 << pin);

		PORTD |= 1 << pin;
	} else if (pull_mode == PORT_PULL_OFF) {

		PORTD &= ~(1 << pin);
	}
}

/**
 * \brief Set PORTD data direction
 *
 * Select if the port pins selected by mask data direction is input, output
 * or disabled.
 *
 * \param[in] mask      Bit mask where 1 means apply direction setting to the
 *                      corresponding pin
 * \param[in] direction PORT_DIR_IN  = Data direction in
 *                      PORT_DIR_OUT = Data direction out
 *                      PORT_DIR_OFF = Disables the pin
 *                      (low power state)
 */
static inline void PORTD_set_port_dir(const uint8_t mask, const enum port_dir direction)
{
	switch (direction) {
	case PORT_DIR_IN:
		DDRD &= ~mask;
		break;
	case PORT_DIR_OUT:
		DDRD |= mask;
		break;
	case PORT_DIR_OFF:
		DDRD &= ~mask;

		PORTD |= mask;
		break;
	default:
		break;
	}
}

/**
 * \brief Set PORTD single pin data direction
 *
 * Select if the pin data direction is input, output or disabled.
 * If disabled state is not possible, this function throws an assert.
 *
 * \param[in] pin       The pin number within PORTD (0..7)
 * \param[in] direction PORT_DIR_IN  = Data direction in
 *                      PORT_DIR_OUT = Data direction out
 *                      PORT_DIR_OFF = Disables the pin
 *                      (low power state)
 */
static inline void PORTD_set_pin_dir(const uint8_t pin, const enum port_dir direction)
{
	switch (direction) {
	case PORT_DIR_IN:
		DDRD &= ~(1 << pin);
		break;
	case PORT_DIR_OUT:
		DDRD |= 1 << pin;
		break;
	case PORT_DIR_OFF:
		DDRD &= ~(1 << pin);

		PORTD |= 1 << pin;
		break;
	default:
		break;
	}
}

/**
 * \brief Set PORTD level
 *
 * Sets output level on the pins defined by the bit mask
 *
 * \param[in] mask  Bit mask where 1 means apply port level to the corresponding
 *                  pin
 * \param[in] level true  = Pin levels set to "high" state
 *                  false = Pin levels set to "low" state
 */
static inline void PORTD_set_port_level(const uint8_t mask, const bool level)
{
	if (level) {
		PORTD |= mask;
	} else {
		PORTD &= ~mask;
	}
}

/**
 * \brief Set PORTD level
 *
 * Sets output level on a pin
 *
 * \param[in] pin       The pin number for device
 * \param[in] level true  = Pin level set to "high" state
 *                  false = Pin level set to "low" state
 */
static inline void PORTD_set_pin_level(const uint8_t pin, const bool level)
{
	if (level) {
		PORTD |= 1 << pin;
	} else {
		PORTD &= ~(1 << pin);
	}
}

/**
 * \brief Toggle out level on pins
 *
 * Toggle the pin levels on pins defined by bit mask
 *
 * \param[in] port  Ports are grouped into groups of maximum 32 pins,
 *                  PORT_PORTA = group 0, PORT_PORTB = group 1, etc
 * \param[in] mask  Bit mask where 1 means toggle pin level to the corresponding
 *                  pin
 */
static inline void PORTD_toggle_port_level(const uint8_t mask)
{
	PIND = mask;
}

/**
 * \brief Toggle output level on pin
 *
 * Toggle the pin levels on pin
 *
 * \param[in] pin       The pin number for device
 */
static inline void PORTD_toggle_pin_level(const uint8_t pin)
{
	PIND = 1 << pin;
}

/**
 * \brief Get input level on pins
 *
 * Read the input level on pins connected to a port
 *
 * \param[in] port  Ports are grouped into groups of maximum 32 pins,
 *                  PORT_PORTA = group 0, PORT_PORTB = group 1, etc
 */
static inline uint8_t PORTD_get_port_level(volatile uint8_t *port)
{
	return PIND;
}

/**
 * \brief Get level on pin
 *
 * Reads the level on a pin connected to a port
 *
 * \param[in] pin       The pin number for device
 */
static inline bool PORTD_get_pin_level(const uint8_t pin)
{
	return PIND & (1 << pin);
}

/**
 * \brief Write value to PORTD
 *
 * Write directly to the entire port register.
 *
 * \param[in] value   Value to write
 */
static inline void PORTD_write_port(const uint8_t value)
{
	PORTD = value;
}

/**
 * \brief Set PORTE pin pull mode
 *
 * Configure pin to pull up, down or disable pull mode, supported pull
 * modes are defined by device used
 *
 * \param[in] pin       The pin number in PORTE
 * \param[in] pull_mode Pin pull mode
 */
static inline void PORTE_set_pin_pull_mode(const uint8_t pin, const enum port_pull_mode pull_mode)
{

	if (pull_mode == PORT_PULL_UP) {

		DDRE &= ~(1 << pin);

		PORTE |= 1 << pin;
	} else if (pull_mode == PORT_PULL_OFF) {

		PORTE &= ~(1 << pin);
	}
}

/**
 * \brief Set PORTE data direction
 *
 * Select if the port pins selected by mask data direction is input, output
 * or disabled.
 *
 * \param[in] mask      Bit mask where 1 means apply direction setting to the
 *                      corresponding pin
 * \param[in] direction PORT_DIR_IN  = Data direction in
 *                      PORT_DIR_OUT = Data direction out
 *                      PORT_DIR_OFF = Disables the pin
 *                      (low power state)
 */
static inline void PORTE_set_port_dir(const uint8_t mask, const enum port_dir direction)
{
	switch (direction) {
	case PORT_DIR_IN:
		DDRE &= ~mask;
		break;
	case PORT_DIR_OUT:
		DDRE |= mask;
		break;
	case PORT_DIR_OFF:
		DDRE &= ~mask;

		PORTE |= mask;
		break;
	default:
		break;
	}
}

/**
 * \brief Set PORTE single pin data direction
 *
 * Select if the pin data direction is input, output or disabled.
 * If disabled state is not possible, this function throws an assert.
 *
 * \param[in] pin       The pin number within PORTE (0..7)
 * \param[in] direction PORT_DIR_IN  = Data direction in
 *                      PORT_DIR_OUT = Data direction out
 *                      PORT_DIR_OFF = Disables the pin
 *                      (low power state)
 */
static inline void PORTE_set_pin_dir(const uint8_t pin, const enum port_dir direction)
{
	switch (direction) {
	case PORT_DIR_IN:
		DDRE &= ~(1 << pin);
		break;
	case PORT_DIR_OUT:
		DDRE |= 1 << pin;
		break;
	case PORT_DIR_OFF:
		DDRE &= ~(1 << pin);

		PORTE |= 1 << pin;
		break;
	default:
		break;
	}
}

/**
 * \brief Set PORTE level
 *
 * Sets output level on the pins defined by the bit mask
 *
 * \param[in] mask  Bit mask where 1 means apply port level to the corresponding
 *                  pin
 * \param[in] level true  = Pin levels set to "high" state
 *                  false = Pin levels set to "low" state
 */
static inline void PORTE_set_port_level(const uint8_t mask, const bool level)
{
	if (level) {
		PORTE |= mask;
	} else {
		PORTE &= ~mask;
	}
}

/**
 * \brief Set PORTE level
 *
 * Sets output level on a pin
 *
 * \param[in] pin       The pin number for device
 * \param[in] level true  = Pin level set to "high" state
 *                  false = Pin level set to "low" state
 */
static inline void PORTE_set_pin_level(const uint8_t pin, const bool level)
{
	if (level) {
		PORTE |= 1 << pin;
	} else {
		PORTE &= ~(1 << pin);
	}
}

/**
 * \brief Toggle out level on pins
 *
 * Toggle the pin levels on pins defined by bit mask
 *
 * \param[in] port  Ports are grouped into groups of maximum 32 pins,
 *                  PORT_PORTA = group 0, PORT_PORTB = group 1, etc
 * \param[in] mask  Bit mask where 1 means toggle pin level to the corresponding
 *                  pin
 */
static inline void PORTE_toggle_port_level(const uint8_t mask)
{
	PINE = mask;
}

/**
 * \brief Toggle output level on pin
 *
 * Toggle the pin levels on pin
 *
 * \param[in] pin       The pin number for device
 */
static inline void PORTE_toggle_pin_level(const uint8_t pin)
{
	PINE = 1 << pin;
}

/**
 * \brief Get input level on pins
 *
 * Read the input level on pins connected to a port
 *
 * \param[in] port  Ports are grouped into groups of maximum 32 pins,
 *                  PORT_PORTA = group 0, PORT_PORTB = group 1, etc
 */
static inline uint8_t PORTE_get_port_level(volatile uint8_t *port)
{
	return PINE;
}

/**
 * \brief Get level on pin
 *
 * Reads the level on a pin connected to a port
 *
 * \param[in] pin       The pin number for device
 */
static inline bool PORTE_get_pin_level(const uint8_t pin)
{
	return PINE & (1 << pin);
}

/**
 * \brief Write value to PORTE
 *
 * Write directly to the entire port register.
 *
 * \param[in] value   Value to write
 */
static inline void PORTE_write_port(const uint8_t value)
{
	PORTE = value;
}

#ifdef __cplusplus
}
#endif

#endif /* PORT_INCLUDED */
