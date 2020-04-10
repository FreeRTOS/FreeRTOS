/**
 * \file
 *
 * \brief I2C Simple master driver.
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

/**
 * \defgroup doc_driver_i2c_simple_master I2C Simple Master Driver
 * \ingroup doc_driver_i2c
 *
 * \section doc_driver_i2c_simple_master_rev Revision History
 * - v0.0.0.1 Initial Commit
 *
 *@{
 */

#include <i2c_master.h>
#include <i2c_simple_master.h>

static i2c_operations_t I2C_0_wr1RegCompleteHandler(void *p)
{
	I2C_0_set_buffer(p, 1);
	I2C_0_set_data_complete_callback(NULL, NULL);
	return i2c_continue;
}

i2c_error_t I2C_0_write1ByteRegister(i2c_address_t address, uint8_t reg, uint8_t data)
{
	/* timeout is used to get out of twim_release, when there is no device connected to the bus*/
	uint16_t timeout = I2C_TIMEOUT;

	while (I2C_BUSY == I2C_0_open(address) && --timeout)
		; // sit here until we get the bus..
	if (!timeout)
		return I2C_BUSY;
	I2C_0_set_data_complete_callback(I2C_0_wr1RegCompleteHandler, &data);
	I2C_0_set_buffer(&reg, 1);
	I2C_0_set_address_nack_callback(i2c_cb_restart_write, NULL); // NACK polling?
	I2C_0_master_write();
	timeout = I2C_TIMEOUT;
	while (I2C_BUSY == I2C_0_close() && --timeout)
		; // sit here until finished.
	if (!timeout)
		return I2C_FAIL;

	return I2C_NOERR;
}

i2c_error_t I2C_0_writeNBytes(i2c_address_t address, void *data, size_t len)
{
	/* timeout is used to get out of twim_release, when there is no device connected to the bus*/
	uint16_t timeout = I2C_TIMEOUT;

	while (I2C_BUSY == I2C_0_open(address) && --timeout)
		; // sit here until we get the bus..
	if (!timeout)
		return I2C_BUSY;
	I2C_0_set_buffer(data, len);
	I2C_0_set_address_nack_callback(i2c_cb_restart_write, NULL); // NACK polling?
	I2C_0_master_write();
	timeout = I2C_TIMEOUT;
	while (I2C_BUSY == I2C_0_close() && --timeout)
		; // sit here until finished.
	if (!timeout)
		return I2C_FAIL;

	return I2C_NOERR;
}

static i2c_operations_t I2C_0_rd1RegCompleteHandler(void *p)
{
	I2C_0_set_buffer(p, 1);
	I2C_0_set_data_complete_callback(NULL, NULL);
	return i2c_restart_read;
}

uint8_t I2C_0_read1ByteRegister(i2c_address_t address, uint8_t reg)
{
	uint8_t     d2 = 42;
	i2c_error_t e;
	int         x;

	for (x = 2; x != 0; x--) {
		while (!I2C_0_open(address))
			; // sit here until we get the bus..
		I2C_0_set_data_complete_callback(I2C_0_rd1RegCompleteHandler, &d2);
		I2C_0_set_buffer(&reg, 1);
		I2C_0_set_address_nack_callback(i2c_cb_restart_write, NULL); // NACK polling?
		I2C_0_master_write();
		while (I2C_BUSY == (e = I2C_0_close()))
			; // sit here until finished.
		if (e == I2C_NOERR)
			break;
	}

	return d2;
}

static i2c_operations_t I2C_0_rd2RegCompleteHandler(void *p)
{
	I2C_0_set_buffer(p, 2);
	I2C_0_set_data_complete_callback(NULL, NULL);
	return i2c_restart_read;
}

uint16_t I2C_0_read2ByteRegister(i2c_address_t address, uint8_t reg)
{
	// result is little endian
	uint16_t result;

	while (!I2C_0_open(address))
		; // sit here until we get the bus..
	I2C_0_set_data_complete_callback(I2C_0_rd2RegCompleteHandler, &result);
	I2C_0_set_buffer(&reg, 1);
	I2C_0_set_address_nack_callback(i2c_cb_restart_write, NULL); // NACK polling?
	I2C_0_master_write();
	while (I2C_BUSY == I2C_0_close())
		; // sit here until finished.

	return (result << 8 | result >> 8);
}

/****************************************************************/
static i2c_operations_t I2C_0_wr2RegCompleteHandler(void *p)
{
	I2C_0_set_buffer(p, 2);
	I2C_0_set_data_complete_callback(NULL, NULL);
	return i2c_continue;
}

i2c_error_t I2C_0_write2ByteRegister(i2c_address_t address, uint8_t reg, uint16_t data)
{
	/* timeout is used to get out of twim_release, when there is no device connected to the bus*/
	uint16_t timeout = I2C_TIMEOUT;

	while (I2C_BUSY == I2C_0_open(address) && --timeout)
		; // sit here until we get the bus..
	if (!timeout)
		return I2C_BUSY;
	I2C_0_set_data_complete_callback(I2C_0_wr2RegCompleteHandler, &data);
	I2C_0_set_buffer(&reg, 1);
	I2C_0_set_address_nack_callback(i2c_cb_restart_write, NULL); // NACK polling?
	I2C_0_master_write();
	timeout = I2C_TIMEOUT;
	while (I2C_BUSY == I2C_0_close() && --timeout)
		; // sit here until finished.
	if (!timeout)
		return I2C_FAIL;

	return I2C_NOERR;
}

/****************************************************************/
typedef struct {
	size_t len;
	char * data;
} I2C_0_buf_t;

static i2c_operations_t I2C_0_rdBlkRegCompleteHandler(void *p)
{
	I2C_0_set_buffer(((I2C_0_buf_t *)p)->data, ((I2C_0_buf_t *)p)->len);
	I2C_0_set_data_complete_callback(NULL, NULL);
	return i2c_restart_read;
}

i2c_error_t I2C_0_readDataBlock(i2c_address_t address, uint8_t reg, void *data, size_t len)
{
	/* timeout is used to get out of twim_release, when there is no device connected to the bus*/
	uint16_t timeout = I2C_TIMEOUT;
	// result is little endian
	I2C_0_buf_t d;
	d.data = data;
	d.len  = len;

	while (I2C_BUSY == I2C_0_open(address) && --timeout)
		; // sit here until we get the bus..
	if (!timeout)
		return I2C_BUSY;
	I2C_0_set_data_complete_callback(I2C_0_rdBlkRegCompleteHandler, &d);
	I2C_0_set_buffer(&reg, 1);
	I2C_0_set_address_nack_callback(i2c_cb_restart_write, NULL); // NACK polling?
	I2C_0_master_write();
	timeout = I2C_TIMEOUT;
	while (I2C_BUSY == I2C_0_close() && --timeout)
		; // sit here until finished.
	if (!timeout)
		return I2C_FAIL;

	return I2C_NOERR;
}

i2c_error_t I2C_0_readNBytes(i2c_address_t address, void *data, size_t len)
{
	/* timeout is used to get out of twim_release, when there is no device connected to the bus*/
	uint16_t timeout = I2C_TIMEOUT;

	while (I2C_BUSY == I2C_0_open(address) && --timeout)
		; // sit here until we get the bus..
	if (!timeout)
		return I2C_BUSY;
	I2C_0_set_buffer(data, len);
	I2C_0_master_read();
	timeout = I2C_TIMEOUT;
	while (I2C_BUSY == I2C_0_close() && --timeout)
		; // sit here until finished.
	if (!timeout)
		return I2C_FAIL;

	return I2C_NOERR;
}
