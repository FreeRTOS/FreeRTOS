/**
 * \file
 *
 * \brief I2C Master driver example.
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

#include <atmel_start.h>
#include <i2c_types.h>
#include <i2c_simple_master.h>
#include <utils/atomic.h>

#define slave_adr 0x4f
#define slave_reg_adr 0x0

uint8_t read_data[2];

/** Structure passed into read_handler to describe the actions to be performed by the handler */
typedef struct {
	uint8_t *data;
	uint8_t  size;
} transfer_descriptor_t;

/** This callback is called when the initial write of the pointer register has finished.
    This callback controls the second phase of the I2C transaction, the read of the
    targeted register after a REPEATED START.
*/
i2c_operations_t I2C_0_read_handler(void *d)
{
	transfer_descriptor_t *desc = (transfer_descriptor_t *)d;
	I2C_0_set_buffer((void *)desc->data, desc->size);
	// Set callback to terminate transfer and send STOP after read is complete
	I2C_0_set_data_complete_callback(i2c_cb_return_stop, NULL);
	return i2c_restart_read; // Send REPEATED START before read
}

/** Performs the following transfer sequence:
1. Send SLA+W, Data1
2. Send RepeatedStart, SLA+R, Read Data1, Read Data2
3. Send Stop

This transfer sequence is typically done to first write to the slave the address in
the slave to read from, thereafter to read N bytes from this address.
*/
i2c_error_t I2C_0_do_transfer(uint8_t adr, uint8_t *data, uint8_t size)
{
	/* timeout is used to get out of twim_release, when there is no device connected to the bus*/
	uint16_t              timeout = I2C_TIMEOUT;
	transfer_descriptor_t d       = {data, size};

	while (I2C_BUSY == I2C_0_open(slave_adr) && --timeout)
		; // sit here until we get the bus..
	if (!timeout)
		return I2C_BUSY;

	// This callback specifies what to do after the first write operation has completed
	// The parameters to the callback are bundled together in the aggregate data type d.
	I2C_0_set_data_complete_callback(I2C_0_read_handler, &d);
	// If we get an address NACK, then try again by sending SLA+W
	I2C_0_set_address_nack_callback(i2c_cb_restart_write, NULL);
	// Transmit specified number of bytes
	I2C_0_set_buffer((void *)&adr, 1);
	// Start a Write operation
	I2C_0_master_operation(false);
	timeout = I2C_TIMEOUT;
	while (I2C_BUSY == I2C_0_close() && --timeout)
		; // sit here until finished.
	if (!timeout)
		return I2C_FAIL;

	return I2C_NOERR;
}

uint8_t I2C_0_test_i2c_master(void)
{

	I2C_0_do_transfer(slave_reg_adr, read_data, 2);
	// If we get here, everything was OK
	return 1;
}
