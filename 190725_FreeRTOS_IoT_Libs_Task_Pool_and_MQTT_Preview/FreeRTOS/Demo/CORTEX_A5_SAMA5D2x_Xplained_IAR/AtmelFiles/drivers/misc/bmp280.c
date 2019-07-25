/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2015, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

/**
  * \file
  *
  * Implementation BMP280 driver.
  *
  */

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "board.h"
#include "chip.h"
#include "math.h"
#include "misc/bmp280.h"
#include "peripherals/pio.h"
#include "peripherals/twid.h"
#include "peripherals/twi.h"
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <assert.h>

/*------------------------------------------------------------------------------
 *         Local definitions
 *----------------------------------------------------------------------------*/

#define EPSILON (1e-10)

/*------------------------------------------------------------------------------
 *         Local functions
 *----------------------------------------------------------------------------*/

static uint8_t _bmp280_read(struct _bmp280* bmp280, uint8_t* buffer, uint32_t len)
{
	struct _buffer in = {
		.data = buffer,
		.size = len
	};
	return (uint8_t)twid_transfert(bmp280->twid, &in, 0, twid_finish_transfert_callback, 0);
}

static uint8_t _bmp280_write(struct _bmp280* bmp280, const uint8_t* buffer, uint32_t len)
{
	struct _buffer out = {
		.data = (uint8_t*)buffer,
		.size = len
	};
	return (uint8_t)twid_transfert(bmp280->twid, 0, &out, twid_finish_transfert_callback, 0);
}

/*------------------------------------------------------------------------------
 *         Global functions
 *----------------------------------------------------------------------------*/

/* Write the data to the given register
 *
 * Param addr -> Address of the register
 *       data -> The data from the register
 *       len -> no of bytes to read
 *
 * Return results of bus communication function
 *	@retval 0 -> Success
 *	@retval -1 -> Error
 */
uint8_t bmp280_write_register(struct _bmp280* bmp280, uint8_t addr, uint8_t* pdata, uint8_t len)
{
	/* variable used to return communication result*/
	uint8_t com_rslt = ERROR;

	/* check the bmp280 struct pointer as NULL*/
	if (bmp280 == BMP280_NULL)
		return E_BMP280_NULL_PTR;
	else {
		bmp280->twid->iaddr = addr;
		bmp280->twid->isize = 1;
		com_rslt = _bmp280_write(bmp280, pdata, len);
	}
	return com_rslt;
}

/* Reads the data from the given register
 *
 * Param addr -> Address of the register
 *	 data -> The data from the register
 *	 len -> no of bytes to read
 *
 * Return results of bus communication function
 *	@retval 0 -> Success
 *	@retval -1 -> Error
 */
uint8_t bmp280_read_register(struct _bmp280* bmp280, uint8_t addr, uint8_t* pdata, uint8_t len)
{
	/* variable used to return communication result*/
	uint8_t com_rslt = ERROR;

	/* check the bmp280 struct pointer as NULL*/
	if (bmp280 == BMP280_NULL)
		return E_BMP280_NULL_PTR;
	else {
		bmp280->twid->iaddr = addr;
		bmp280->twid->isize = 1;
		com_rslt = _bmp280_read(bmp280, pdata, len);
	}
	return com_rslt;
}

/*
 * Read uncompensated temperature in the registers
 * 0xFA, 0xFB and 0xFC
 * 0xFA -> MSB -> bit from 0 to 7
 * 0xFB -> LSB -> bit from 0 to 7
 * 0xFC -> LSB -> bit from 4 to 7
 *
 * Param uncT : The uncompensated temperature.
 *
 * Return results of bus communication function
 *       0 -> Success
 *	-1 -> Error
 */
uint8_t bmp280_read_uncompensed_temperature (struct _bmp280* bmp280, int32_t* uncT)
{
	/* variable used to return communication result*/
	uint8_t com_rslt = ERROR;
	/* Array holding the MSB and LSb value
	   dt[0] - Temperature MSB
	   dt[1] - Temperature LSB
	   dt[2] - Temperature LSB
	*/
	uint8_t dt[3] = {0};

	/* check the bmp280 struct pointer as NULL*/
	if (bmp280 == BMP280_NULL)
		return E_BMP280_NULL_PTR;
	else {
		/* read temperature data */
		bmp280->twid->iaddr = BMP280_TEMPERATURE_MSB_REG;
		bmp280->twid->isize = 1;
		com_rslt = _bmp280_read(bmp280, &dt[0], 3);
		*uncT = (int32_t)((((uint32_t) (dt[0])) << 12) |
				  (((uint32_t)(dt[1])) << 4) | ((uint32_t)dt[2] >> 4));
	}
	return com_rslt;
}

/* Reads actual temperature from uncompensated temperature
 * Returns the value in 0.01 degree Centigrade
 * Output value of "5123" equals 51.23 DegC.
 *
 * param uncT : value of uncompensated temperature
 *
 * return Actual temperature output as s32
 */
int32_t bmp280_compensate_temperatureC (struct _bmp280* bmp280, int32_t uncT)
{
	int32_t x1 = 0;
	int32_t x2 = 0;
	int32_t temperature = 0;

	/* calculate true temperature*/
	x1  = ((((uncT >> 3) - ((int32_t)bmp280->calpar.dig_T1
				<< 1))) * ((int32_t)bmp280->calpar.dig_T2)) >> 11;
	x2  = (((((uncT >> 4) - ((int32_t)bmp280->calpar.dig_T1)) *
		 ((uncT >> 4) - ((int32_t)bmp280->calpar.dig_T1)))
		>> 12) * ((int32_t)bmp280->calpar.dig_T3)) >> 14;
	bmp280->calpar.t_fine = x1 + x2;
	temperature  = (bmp280->calpar.t_fine * BMP280_DEC_TRUE_TEMP_5 +
			BMP280_DEC_TRUE_TEMP_128) >> 8;
	return temperature;
}

/* Read uncompensated pressure.
 * in the registers 0xF7, 0xF8 and 0xF9
 * 0xF7 -> MSB -> bit from 0 to 7
 * 0xF8 -> LSB -> bit from 0 to 7
 * 0xF9 -> LSB -> bit from 4 to 7
 *
 * param uncP : The value of uncompensated pressure
 *
 * return results of bus communication function
 *       0 -> Success
 *	-1 -> Error
 */
uint8_t bmp280_read_uncompensed_pressure (struct _bmp280* bmp280, int32_t* uncP)
{
	/* variable used to return communication result*/
	uint8_t com_rslt = ERROR;
	/* Array holding the MSB and LSb value
	   dt[0] - Pressure MSB
	   dt[1] - Pressure LSB
	   dt[2] - Pressure LSB
	*/
	uint8_t dt[3] = {0};

	/* check the bmp280 struct pointer as NULL*/
	if (bmp280 == BMP280_NULL)
		return  E_BMP280_NULL_PTR;
	else {
		bmp280->twid->iaddr = BMP280_PRESSURE_MSB_REG;
		bmp280->twid->isize = 1;
		com_rslt = _bmp280_read(bmp280, &dt[0], 3);
		*uncP = (int32_t)((((uint32_t)(dt[0])) << 12) |
				  (((uint32_t)(dt[1])) << 4) | ((uint32_t)dt[2] >> 4));
	}
	return com_rslt;
}

/*
 * Reads actual pressure from uncompensated pressure and returns the value in
 * Pascal(Pa)
 *
 * Note: Output value of "96386" equals 96386 Pa = 963.86 hPa = 963.86 millibar
 *
 * Param  uncP: value of uncompensated pressure
 *
 * Return Returns the Actual pressure out put as s32
 */
uint32_t  bmp280_compensate_pressureP (struct _bmp280* bmp280, int32_t uncP)
{
	int32_t x1 = 0;
	int32_t x2 = 0;
	uint32_t pressure = 0;

	/* calculate true pressure*/
	x1 = (((int32_t)bmp280->calpar.t_fine) >> 1) - (int32_t)BMP280_DEC_TRUE_PRES_64000;
	x2 = (((x1 >> 2) * (x1 >> 2)) >> 11) * ((int32_t)bmp280->calpar.dig_P6);
	x2 = x2 + ((x1 * ((int32_t)bmp280->calpar.dig_P5)) << 1);
	x2 = (x2 >> 2) + (((int32_t)bmp280->calpar.dig_P4) << 16);
	x1 = (((bmp280->calpar.dig_P3 * (((x1 >> 2) * (x1 >> 2)) >> 13)) >> 3) +
	      ((((int32_t)bmp280->calpar.dig_P2) * x1) >> 1)) >> 18;
	x1 = ((((BMP280_DEC_TRUE_PRES_32768 + x1)) * ((int32_t)bmp280->calpar.dig_P1)) >> 15);
	pressure = (((uint32_t)(((int32_t)BMP280_DEC_TRUE_PRES_1048576) - uncP) -
		     (x2 >> 12))) * BMP280_DEC_TRUE_PRES_3125;

	if (pressure < BMP280_HEX_TRUE_PRES_8M)
		/* Avoid exception caused by division by zero */
		if (x1 != 0)
			pressure = (pressure << 1) / ((uint32_t)x1);
		else
			return 0;
	else
		/* Avoid exception caused by division by zero */
		if (x1 != 0)
			pressure = (pressure / (uint32_t)x1) * BMP280_DEC_TRUE_PRES_2;
		else
			return 0;

	x1 = (((int32_t)bmp280->calpar.dig_P9)* ((int32_t)(((pressure>>3)* (pressure>>3))>>13)))>>12 ;
	x2 = (((int32_t)(pressure >> 2))*((int32_t)bmp280->calpar.dig_P8))>>13;
	pressure = (uint32_t)((int32_t)pressure + ((x1 + x2 + bmp280->calpar.dig_P7)>>4));

	return pressure;
}


/*
 * Reads uncompensated pressure and temperature
 *
 * Param uncP: The value of uncompensated pressure.
 *       uncT: The value of uncompensated temperature.
 *
 * Return results of bus communication function
 *	0 -> Success
 *	-1 -> Error
 */
uint8_t bmp280_read_uncompensed_pressure_temperature (struct _bmp280* bmp280, int32_t* uncP, int32_t* uncT)
{
	/* variable used to return communication result*/
	uint8_t com_rslt = ERROR;

	/* Array holding the temperature and pressure data
	   dt[0] - Pressure MSB
	   dt[1] - Pressure LSB
	   dt[2] - Pressure LSB
	   dt[3] - Temperature MSB
	   dt[4] - Temperature LSB
	   dt[5] - Temperature LSB
	*/
	uint8_t dt[6] = {0};

	/* check the bmp280 struct pointer as NULL*/
	if (bmp280 == BMP280_NULL)
		return  E_BMP280_NULL_PTR;
	else {
		bmp280->twid->iaddr = BMP280_PRESSURE_MSB_REG;
		bmp280->twid->isize = 1;
		com_rslt = _bmp280_read(bmp280, &dt[0], 6);
		/*Pressure*/
		*uncP = (int32_t)((((uint32_t)(dt[0]))<<12) | (((uint32_t)(dt[1]))<<4) | ((uint32_t)dt[2]>>4));
		/* Temperature */
		*uncT = (int32_t)((((uint32_t)(dt[3]))<<12) | (((uint32_t)(dt[4]))<<4) | ((uint32_t)dt[5]>>4));
	}
	return com_rslt;
}

/*
 * Reads the true pressure and temperature
 *
 * Param pressure : The value of compensated pressure.
 *       temperature : The value of compensated temperature.
 *
 * Return results of bus communication function
 *	0 -> Success
 *	-1 -> Error
 */

uint8_t bmp280_read_pressure_temperature (struct _bmp280* bmp280, uint32_t* pressure, int32_t* temperature)
{
	/* variable used to return communication result*/
	uint8_t com_rslt = ERROR;
	int32_t uncP = 0;
	int32_t uncT = 0;

	/* check the bmp280 struct pointer as NULL*/
	if (bmp280 == BMP280_NULL)
		return  E_BMP280_NULL_PTR;
	else {
		/* read uncompensated pressure and temperature*/
		com_rslt = bmp280_read_uncompensed_pressure_temperature(bmp280, &uncP, &uncT);
		/* read true pressure and temperature*/
		*temperature = bmp280_compensate_temperatureC(bmp280, uncT);
		*pressure = bmp280_compensate_pressureP(bmp280, uncP);
	}
	return com_rslt;
}

/*
 * Calibration parameters used for calculation in the registers
 *
 *  parameter | Register address |   bit
 *------------|------------------|----------------
 *	dig_T1    |  0x88 and 0x89   | from 0 : 7 to 8: 15
 *	dig_T2    |  0x8A and 0x8B   | from 0 : 7 to 8: 15
 *	dig_T3    |  0x8C and 0x8D   | from 0 : 7 to 8: 15
 *	dig_P1    |  0x8E and 0x8F   | from 0 : 7 to 8: 15
 *	dig_P2    |  0x90 and 0x91   | from 0 : 7 to 8: 15
 *	dig_P3    |  0x92 and 0x93   | from 0 : 7 to 8: 15
 *	dig_P4    |  0x94 and 0x95   | from 0 : 7 to 8: 15
 *	dig_P5    |  0x96 and 0x97   | from 0 : 7 to 8: 15
 *	dig_P6    |  0x98 and 0x99   | from 0 : 7 to 8: 15
 *	dig_P7    |  0x9A and 0x9B   | from 0 : 7 to 8: 15
 *	dig_P8    |  0x9C and 0x9D   | from 0 : 7 to 8: 15
 *	dig_P9    |  0x9E and 0x9F   | from 0 : 7 to 8: 15
 *
 * Return results of bus communication function
 *	0 -> Success
 *	-1 -> Error
 */
uint8_t bmp280_get_calpar (struct _bmp280* bmp280)
{
	/* variable used to return communication result*/
	uint8_t com_rslt = ERROR;
	uint8_t dt[26] = {0};

	/* check the bmp280 struct pointer as NULL*/
	if (bmp280 == BMP280_NULL)
		return  E_BMP280_NULL_PTR;
	else {
		bmp280->twid->iaddr = BMP280_DIG_T1_LSB_REG;
		bmp280->twid->isize = 1;
		com_rslt = _bmp280_read(bmp280, &dt[0], 24);
		/* read calibration values*/
		bmp280->calpar.dig_T1 = (uint16_t)((((uint16_t)((uint8_t)dt[1])) << 8) | dt[0]);
		bmp280->calpar.dig_T2 = (int16_t)((((int16_t)((int8_t)dt[3])) << 8) | dt[2]);
		bmp280->calpar.dig_T3 = (int16_t)((((int16_t)((int8_t)dt[5])) << 8) | dt[4]);
		bmp280->calpar.dig_P1 = (uint16_t)((((uint16_t)((uint8_t)dt[7])) << 8) | dt[6]);
		bmp280->calpar.dig_P2 = (int16_t)((((int16_t)((int8_t)dt[9])) << 8) | dt[8]);
		bmp280->calpar.dig_P3 = (int16_t)((((int16_t)((int8_t)dt[11])) << 8) | dt[10]);
		bmp280->calpar.dig_P4 = (int16_t)((((int16_t)((int8_t)dt[13])) << 8) | dt[12]);
		bmp280->calpar.dig_P5 = (int16_t)((((int16_t)((int8_t)dt[15])) << 8) | dt[14]);
		bmp280->calpar.dig_P6 = (int16_t)((((int16_t)((int8_t)dt[17])) << 8) | dt[16]);
		bmp280->calpar.dig_P7 = (int16_t)((((int16_t)((int8_t)dt[19])) << 8) | dt[18]);
		bmp280->calpar.dig_P8 = (int16_t)((((int16_t)((int8_t)dt[21])) << 8) | dt[20]);
		bmp280->calpar.dig_P9 = (int16_t)((((int16_t)((int8_t)dt[23])) << 8) | dt[22]);
	}
	return com_rslt;
}

/* Get the temperature oversampling setting in the register 0xF4
 * bits from 5 to 7
 *
 *        value             | Temperature oversampling
 *  ------------------------|------------------------------
 *       0x00               |  Skipped
 *       0x01               |  BMP280_OVERSAMP_1X
 *       0x02               |  BMP280_OVERSAMP_2X
 *       0x03               |  BMP280_OVERSAMP_4X
 *       0x04               |  BMP280_OVERSAMP_8X
 *       0x05,0x06 and 0x07 |  BMP280_OVERSAMP_16X
 *
 * Param: value :The value of temperature over sampling
 *
 * Return results of bus communication function
 *	@retval 0 -> Success
 *	@retval -1 -> Error
 */
uint8_t bmp280_get_overs_temp (struct _bmp280* bmp280, uint8_t* value)
{
	/* variable used to return communication result*/
	uint8_t com_rslt = ERROR;
	uint8_t data = 0;

	/* check the bmp280 struct pointer as NULL*/
	if (bmp280 == BMP280_NULL)
		return  E_BMP280_NULL_PTR;
	else {
		/* read temperature over sampling*/
		bmp280->twid->iaddr = BMP280_CTRL_MEAS_REG_OVRS_TEMP__REG;
		bmp280->twid->isize = 1;
		com_rslt = _bmp280_read(bmp280, &data, 1);
		*value = BMP280_GET_BITSLICE(data, BMP280_CTRL_MEAS_REG_OVRS_TEMP);
		/* assign temperature oversampling*/
		bmp280->overs_temp = *value;
	}
	return com_rslt;
}

/* Set the temperature oversampling setting in the register 0xF4
 * bits from 5 to 7
 *
 *        value             | Temperature oversampling
 *  ------------------------|------------------------------
 *       0x00               |  Skipped
 *       0x01               |  BMP280_OVERSAMP_1X
 *       0x02               |  BMP280_OVERSAMP_2X
 *       0x03               |  BMP280_OVERSAMP_4X
 *       0x04               |  BMP280_OVERSAMP_8X
 *       0x05,0x06 and 0x07 |  BMP280_OVERSAMP_16X
 *
 * Param: value :The value of temperature over sampling
 *
 * Return results of bus communication function
 *	@retval 0 -> Success
 *	@retval -1 -> Error
 */
uint8_t bmp280_set_overs_temp (struct _bmp280* bmp280, uint8_t value)
{
	/* variable used to return communication result*/
	uint8_t com_rslt = ERROR;
	uint8_t data = 0;

	/* check the bmp280 struct pointer as NULL*/
	if (bmp280 == BMP280_NULL)
		return  E_BMP280_NULL_PTR;
	else {
		bmp280->twid->iaddr = BMP280_CTRL_MEAS_REG_OVRS_TEMP__REG;
		bmp280->twid->isize = 1;
		com_rslt = _bmp280_read(bmp280, &data, 1);
		if (com_rslt == SUCCESS) {
			/* write over sampling*/
			data = BMP280_SET_BITSLICE(data, BMP280_CTRL_MEAS_REG_OVRS_TEMP, value);
			bmp280->twid->iaddr = BMP280_CTRL_MEAS_REG_OVRS_TEMP__REG;
			bmp280->twid->isize = 1;
			com_rslt = _bmp280_write(bmp280, &data, 1);
			bmp280->overs_temp = value;
		}
	}
	return com_rslt;
}

/* Get the pressure oversampling setting in the register 0xF4
 * bits from 2 to 4
 *
 *        value             | Pressure oversampling
 *  ------------------------|------------------------------
 *       0x00               |  Skipped
 *       0x01               |  BMP280_OVERSAMP_1X
 *       0x02               |  BMP280_OVERSAMP_2X
 *       0x03               |  BMP280_OVERSAMP_4X
 *       0x04               |  BMP280_OVERSAMP_8X
 *       0x05,0x06 and 0x07 |  BMP280_OVERSAMP_16X
 *
 * Param:  value : The value of pressure over sampling
 *
 * Return results of bus communication function
 *	@retval 0 -> Success
 *	@retval -1 -> Error
 */
uint8_t bmp280_get_overs_pres (struct _bmp280* bmp280, uint8_t* value)
{
	/* variable used to return communication result*/
	uint8_t com_rslt = ERROR;
	uint8_t data = 0;

	/* check the bmp280 struct pointer as NULL*/
	if (bmp280 == BMP280_NULL)
		return  E_BMP280_NULL_PTR;
	else {
		/* read pressure over sampling */
		bmp280->twid->iaddr = BMP280_CTRL_MEAS_REG_OVRS_PRES__REG;
		bmp280->twid->isize = 1;
		com_rslt = _bmp280_read(bmp280, &data, 1);
		*value = BMP280_GET_BITSLICE(data, BMP280_CTRL_MEAS_REG_OVRS_PRES);
		bmp280->overs_pres = *value;
	}
	return com_rslt;
}

/* Set the pressure oversampling setting in the register 0xF4
 * bits from 2 to 4
 *
 *        value             | Pressure oversampling
 *  ------------------------|------------------------------
 *       0x00               |  Skipped
 *       0x01               |  BMP280_OVERSAMP_1X
 *       0x02               |  BMP280_OVERSAMP_2X
 *       0x03               |  BMP280_OVERSAMP_4X
 *       0x04               |  BMP280_OVERSAMP_8X
 *       0x05,0x06 and 0x07 |  BMP280_OVERSAMP_16X
 *
 * Param:  value : The value of pressure over sampling
 *
 * Return results of bus communication function
 *	@retval 0 -> Success
 *	@retval -1 -> Error
 */
uint8_t bmp280_set_overs_pres (struct _bmp280* bmp280, uint8_t value)
{
	/* variable used to return communication result*/
	uint8_t com_rslt = ERROR;
	uint8_t data = 0;

	/* check the bmp280 struct pointer as NULL*/
	if (bmp280 == BMP280_NULL)
		return  E_BMP280_NULL_PTR;
	else {
		bmp280->twid->iaddr = BMP280_CTRL_MEAS_REG_OVRS_PRES__REG;
		bmp280->twid->isize = 1;
		com_rslt = _bmp280_read(bmp280, &data, 1);
		if (com_rslt == SUCCESS) {
			/* write pressure over sampling */
			data = BMP280_SET_BITSLICE(data, BMP280_CTRL_MEAS_REG_OVRS_PRES, value);
			bmp280->twid->iaddr = BMP280_CTRL_MEAS_REG_OVRS_PRES__REG;
			bmp280->twid->isize = 1;
			com_rslt = _bmp280_write(bmp280, &data, 1);
			bmp280->overs_pres = value;
		}
	}
	return com_rslt;
}

/* Get the operational Mode from the sensor in the register 0xF4 bit 0 and 1
 *
 * Param: power_mode : The value of power mode value
 *  value            |   Power mode
 * ------------------|------------------
 *	0x00             | BMP280_SLEEP_MODE
 *	0x01 and 0x02    | BMP280_FORCED_MODE
 *	0x03             | BMP280_NORMAL_MODE
 *
 * Return results of bus communication function
 *	@retval 0 -> Success
 *	@retval -1 -> Error
 */
uint8_t bmp280_get_power_mode(struct _bmp280* bmp280, uint8_t* power_mode)
{
	/* variable used to return communication result*/
	uint8_t com_rslt = ERROR;
	uint8_t mode = 0;

	/* check the bmp280 struct pointer as NULL*/
	if (bmp280 == BMP280_NULL)
		return  E_BMP280_NULL_PTR;
	else {
		/* read the power mode*/
		bmp280->twid->iaddr = BMP280_CTRL_MEAS_REG_POWER_MODE__REG;
		bmp280->twid->isize = 1;
		com_rslt = _bmp280_read(bmp280, &mode, 1);
		*power_mode = BMP280_GET_BITSLICE(mode, BMP280_CTRL_MEAS_REG_POWER_MODE);
	}
	return com_rslt;
}

/* Set the operational Mode from the sensor in the register 0xF4 bit 0 and 1
 *
 * Param: power_mode : The value of power mode value
 *  value            |   Power mode
 * ------------------|------------------
 *	0x00             | BMP280_SLEEP_MODE
 *	0x01 and 0x02    | BMP280_FORCED_MODE
 *	0x03             | BMP280_NORMAL_MODE
 *
 * Return results of bus communication function
 *	@retval 0 -> Success
 *	@retval -1 -> Error
 */
uint8_t bmp280_set_power_mode (struct _bmp280* bmp280, uint8_t power_mode)
{
	/* variable used to return communication result*/
	uint8_t com_rslt = ERROR;
	uint8_t mode = 0;

	/* check the bmp280 struct pointer as NULL*/
	if (bmp280 == BMP280_NULL)
		return  E_BMP280_NULL_PTR;
	else
	{
		if (power_mode < 4) {
			/* write the power mode*/
			mode = (bmp280->overs_temp << 5) + (bmp280->overs_pres << 2) + power_mode;
			bmp280->twid->iaddr = BMP280_CTRL_MEAS_REG_POWER_MODE__REG;
			bmp280->twid->isize = 1;
			com_rslt = _bmp280_write(bmp280, &mode, 1);
		}
		else {
			com_rslt = E_BMP280_OUT_OF_RANGE;
		}
	}
	return com_rslt;
}

/* Reset the sensor
 * The value 0xB6 is written to the 0xE0 register the device is reset using the
 * complete power-on-reset procedure.
 * Softreset can be easily set using bmp280_set_softreset().
 *
 * Note Usage Hint : bmp280_set_softreset()
 * Return results of bus communication function
 *	@retval 0 -> Success
 *	@retval -1 -> Error
 */
uint8_t bmp280_set_soft_rst (struct _bmp280* bmp280)
{
	/* variable used to return communication result*/
	uint8_t com_rslt = ERROR;
	uint8_t data = BMP280_SOFT_RESET_CODE;

	/* check the bmp280 struct pointer as NULL*/
	if (bmp280 == BMP280_NULL)
		return  E_BMP280_NULL_PTR;
	else {
		/* write soft reset */
		bmp280->twid->iaddr = BMP280_RST_REG;
		bmp280->twid->isize = 1;
		com_rslt = _bmp280_write(bmp280, &data, 1);
	}
	return com_rslt;
}

/* Get the sensor SPI mode(communication type) in the register 0xF5 bit 0
 *
 * Param: enable_disable : The spi3 enable or disable state
 *    value    | Description
 *  -----------|---------------
 *     0       | Disable
 *     1       | Enable
 *
 * Return results of bus communication function
 *	@retval 0 -> Success
 *	@retval -1 -> Error
 */
uint8_t bmp280_get_spi3 (struct _bmp280* bmp280, uint8_t* enable_disable)
{
	/* variable used to return communication result*/
	uint8_t com_rslt = ERROR;
	uint8_t data = 0;

	/* check the bmp280 struct pointer as NULL*/
	if (bmp280 == BMP280_NULL)
		return  E_BMP280_NULL_PTR;
	else {
		bmp280->twid->iaddr = BMP280_CONFIG_REG_SPI3_ENABLE__REG;
		bmp280->twid->isize = 1;
		com_rslt = _bmp280_read(bmp280, &data, 1);
		*enable_disable = BMP280_GET_BITSLICE(data, BMP280_CONFIG_REG_SPI3_ENABLE);
	}
	return com_rslt;
}

/* Set the sensor SPI mode(communication type) in the register 0xF5 bit 0
 *
 * Param: enable_disable : The spi3 enable or disable state
 *    value    | Description
 *  -----------|---------------
 *     0       | Disable
 *     1       | Enable
 *
 * Return results of bus communication function
 *	@retval 0 -> Success
 *	@retval -1 -> Error
 */
uint8_t bmp280_set_spi3 (struct _bmp280* bmp280, uint8_t enable_disable)
{
	/* variable used to return communication result*/
	uint8_t com_rslt = ERROR;
	uint8_t data = 0;

	/* check the bmp280 struct pointer as NULL*/
	if (bmp280 == BMP280_NULL)
		return  E_BMP280_NULL_PTR;
	else {
		bmp280->twid->iaddr = BMP280_CONFIG_REG_SPI3_ENABLE__REG;
		bmp280->twid->isize = 1;
		com_rslt = _bmp280_read(bmp280, &data, 1);
		if (com_rslt == SUCCESS) {
			data = BMP280_SET_BITSLICE(data, BMP280_CONFIG_REG_SPI3_ENABLE, enable_disable);
			bmp280->twid->iaddr = BMP280_CONFIG_REG_SPI3_ENABLE__REG;
			bmp280->twid->isize = 1;
			com_rslt = _bmp280_write(bmp280, &data, 1);
		}
	}
	return com_rslt;
}

/* Reads filter setting in the register 0xF5 bit 3 and 4
 *
 * Param value : The value of filter coefficient
 *	value	    |	Filter coefficient
 * -------------|-------------------------
 *	0x00        | BMP280_FILTER_COEFF_OFF
 *	0x01        | BMP280_FILTER_COEFF_2
 *	0x02        | BMP280_FILTER_COEFF_4
 *	0x03        | BMP280_FILTER_COEFF_8
 *	0x04        | BMP280_FILTER_COEFF_16
 *
 * Return results of bus communication function
 *	@retval 0 -> Success
 *	@retval -1 -> Error
 */
uint8_t bmp280_get_filter (struct _bmp280* bmp280, uint8_t *value)
{
	/* variable used to return communication result*/
	uint8_t com_rslt = ERROR;
	uint8_t data = 0;

	/* check the bmp280 struct pointer as NULL*/
	if (bmp280 == BMP280_NULL)
		return  E_BMP280_NULL_PTR;
	else {
		/* read filter*/
		bmp280->twid->iaddr = BMP280_CONFIG_REG_FILTER__REG;
		bmp280->twid->isize = 1;
		com_rslt = _bmp280_read(bmp280, &data, 1);
		*value = BMP280_GET_BITSLICE(data, BMP280_CONFIG_REG_FILTER);
	}
	return com_rslt;
}

/* Write filter setting in the register 0xF5 bit 3 and 4
 *
 * Param value : The value of filter coefficient
 *	value	    |	Filter coefficient
 * -------------|-------------------------
 *	0x00        | BMP280_FILTER_COEFF_OFF
 *	0x01        | BMP280_FILTER_COEFF_2
 *	0x02        | BMP280_FILTER_COEFF_4
 *	0x03        | BMP280_FILTER_COEFF_8
 *	0x04        | BMP280_FILTER_COEFF_16
 *
 * Return results of bus communication function
 *	@retval 0 -> Success
 *	@retval -1 -> Error
 */
uint8_t bmp280_set_filter (struct _bmp280* bmp280, uint8_t value)
{
	uint8_t com_rslt = SUCCESS;
	uint8_t data = 0;

	/* check the bmp280 struct pointer as NULL*/
	if (bmp280 == BMP280_NULL)
		return  E_BMP280_NULL_PTR;
	else {
		/* write filter*/
		bmp280->twid->iaddr = BMP280_CONFIG_REG_FILTER__REG;
		bmp280->twid->isize = 1;
		com_rslt = _bmp280_read(bmp280, &data, 1);
		if (com_rslt == SUCCESS) {
			data = BMP280_SET_BITSLICE(data, BMP280_CONFIG_REG_FILTER, value);
			bmp280->twid->iaddr = BMP280_CONFIG_REG_FILTER__REG;
			bmp280->twid->isize = 1;
			com_rslt = _bmp280_write(bmp280, &data, 1);
		}
	}
	return com_rslt;
}

/* Read the standby duration time from the sensor in the register 0xF5 bit 5 to 7
 *
 * Param standby_durn : The standby duration time value.
 *  value     |  standby duration
 * -----------|--------------------
 *    0x00    | BMP280_STANDBYTIME_1_MS
 *    0x01    | BMP280_STANDBYTIME_63_MS
 *    0x02    | BMP280_STANDBYTIME_125_MS
 *    0x03    | BMP280_STANDBYTIME_250_MS
 *    0x04    | BMP280_STANDBYTIME_500_MS
 *    0x05    | BMP280_STANDBYTIME_1000_MS
 *    0x06    | BMP280_STANDBYTIME_2000_MS
 *    0x07    | BMP280_STANDBYTIME_4000_MS
 *
 * Return results of bus communication function
 *	@retval 0 -> Success
 *	@retval -1 -> Error
 */
uint8_t bmp280_get_standby_durn(struct _bmp280* bmp280, uint8_t* standby_durn)
{
	/* variable used to return communication result*/
	uint8_t com_rslt = ERROR;
	uint8_t data = 0;

	/* check the bmp280 struct pointer as NULL*/
	if (bmp280 == BMP280_NULL)
		return  E_BMP280_NULL_PTR;
	else {
		/* read the standby duration*/
		bmp280->twid->iaddr = BMP280_CONFIG_REG_STANDBY_DURN__REG;
		bmp280->twid->isize = 1;
		com_rslt = _bmp280_read(bmp280, &data, 1);
		*standby_durn = BMP280_GET_BITSLICE(data, BMP280_CONFIG_REG_STANDBY_DURN);
	}
	return com_rslt;
}

/* Read the standby duration time from the sensor in the register 0xF5 bit 5 to 7
 *
 * Note Normal mode comprises an automated perpetual cycling between an (active)
 *      Measurement period and an (inactive) standby period.
 * Note The standby time is determined by the contents of the register t_sb.
 *	Standby time can be set using BME280_STANDBYTIME_125_MS.
 * Note bme280_set_standby_durN(BME280_STANDBYTIME_125_MS)
 *
 * Param standby_durn : The standby duration time value.
 *  value     |  standby duration
 * -----------|--------------------
 *    0x00    | BMP280_STANDBYTIME_1_MS
 *    0x01    | BMP280_STANDBYTIME_63_MS
 *    0x02    | BMP280_STANDBYTIME_125_MS
 *    0x03    | BMP280_STANDBYTIME_250_MS
 *    0x04    | BMP280_STANDBYTIME_500_MS
 *    0x05    | BMP280_STANDBYTIME_1000_MS
 *    0x06    | BMP280_STANDBYTIME_2000_MS
 *    0x07    | BMP280_STANDBYTIME_4000_MS
 *
 *  @return results of bus communication function
 *	@retval 0 -> Success
 *	@retval -1 -> Error
 */
uint8_t bmp280_set_standby_durn (struct _bmp280* bmp280, uint8_t standby_durn)
{
	/* variable used to return communication result*/
	uint8_t com_rslt = ERROR;
	uint8_t data = 0;

	/* check the bmp280 struct pointer as NULL*/
	if (bmp280 == BMP280_NULL)
		return  E_BMP280_NULL_PTR;
	else {
		/* write the standby duration*/
		bmp280->twid->iaddr = BMP280_CONFIG_REG_STANDBY_DURN__REG;
		bmp280->twid->isize = 1;
		com_rslt = _bmp280_read(bmp280, &data, 1);
		if (com_rslt == SUCCESS) {
			data = BMP280_SET_BITSLICE(data, BMP280_CONFIG_REG_STANDBY_DURN, standby_durn);
			bmp280->twid->iaddr = BMP280_CONFIG_REG_STANDBY_DURN__REG;
			bmp280->twid->isize = 1;
			com_rslt = _bmp280_write(bmp280, &data, 1);
		}
	}
	return com_rslt;
}

/* Write the working mode of the sensor
 *
 * Param work_mode : The value of work mode
 *   value      |  mode
 * -------------|-------------
 *    0         | BMP280_ULTRA_LOW_POWER_MODE
 *    1         | BMP280_LOW_POWER_MODE
 *    2         | BMP280_STANDARD_RESOLUTION_MODE
 *    3         | BMP280_HIGH_RESOLUTION_MODE
 *    4         | BMP280_ULTRA_HIGH_RESOLUTION_MODE
 *
 * Return results of bus communication function
 *	@retval 0 -> Success
 *	@retval -1 -> Error
 */
uint8_t bmp280_set_work_mode (struct _bmp280* bmp280, uint8_t work_mode)
{
	/* variable used to return communication result*/
	uint8_t com_rslt = ERROR;
	uint8_t data = 0;

	/* check the bmp280 struct pointer as NULL*/
	if (bmp280 == BMP280_NULL)
		return  E_BMP280_NULL_PTR;
	else {
		if (work_mode <= 4) {
			bmp280->twid->iaddr = BMP280_CTRL_MEAS_REG;
			bmp280->twid->isize = 1;
			com_rslt = _bmp280_read(bmp280, &data, 1);
			if (com_rslt == SUCCESS)
			{
				switch (work_mode) {
					/* write work mode*/
				case BMP280_ULTRA_LOW_POWER_MODE:
					bmp280->overs_temp = BMP280_ULTRALOWPOWER_OVRS_TEMP;
					bmp280->overs_pres = BMP280_ULTRALOWPOWER_OVRS_PRES;
					break;
				case BMP280_LOW_POWER_MODE:
					bmp280->overs_temp = BMP280_LOWPOWER_OVRS_TEMP;
					bmp280->overs_pres = BMP280_LOWPOWER_OVRS_PRES;
					break;
				case BMP280_STANDARD_RESOLUTION_MODE:
					bmp280->overs_temp = BMP280_STANDARDRESOLUTION_OVRS_TEMP;
					bmp280->overs_pres = BMP280_STANDARDRESOLUTION_OVRS_PRES;
					break;
				case BMP280_HIGH_RESOLUTION_MODE:
					bmp280->overs_temp = BMP280_HIGHRESOLUTION_OVRS_TEMP;
					bmp280->overs_pres = BMP280_HIGHRESOLUTION_OVRS_PRES;
					break;
				case BMP280_ULTRA_HIGH_RESOLUTION_MODE:
					bmp280->overs_temp = BMP280_ULTRAHIGHRESOLUTION_OVRS_TEMP;
					bmp280->overs_pres = BMP280_ULTRAHIGHRESOLUTION_OVRS_PRES;
					break;
				}
				data = BMP280_SET_BITSLICE(data, BMP280_CTRL_MEAS_REG_OVRS_TEMP, bmp280->overs_temp);
				data = BMP280_SET_BITSLICE(data, BMP280_CTRL_MEAS_REG_OVRS_PRES, bmp280->overs_pres);
				bmp280->twid->iaddr = BMP280_CTRL_MEAS_REG;
				bmp280->twid->isize = 1;
				com_rslt = _bmp280_write(bmp280, &data, 1);
			}
		}
		else {
			com_rslt = E_BMP280_OUT_OF_RANGE;
		}
	}
	return com_rslt;
}

/* Read both uncompensated pressure and temperature in forced mode
 *
 * Param  uncP: The value of uncompensated pressure.
 *        uncT: The value of uncompensated temperature
 *
 * Return results of bus communication function
 *	@retval 0 -> Success
 *	@retval -1 -> Error
 */
uint8_t bmp280_get_forced_uncP_temperature(struct _bmp280* bmp280, int32_t* uncP, int32_t* uncT)
{
	/* variable used to return communication result*/
	uint8_t com_rslt = ERROR;
	uint8_t data = 0;
	uint8_t waittime = 0;

	/* check the bmp280 struct pointer as NULL*/
	if (bmp280 == BMP280_NULL)
		return  E_BMP280_NULL_PTR;
	else {
		/* read pressure and temperature*/
		data = (bmp280->overs_temp << 5) + (bmp280->overs_pres << 2) + BMP280_FORCED_MODE;
		bmp280->twid->iaddr = BMP280_CTRL_MEAS_REG;
		bmp280->twid->isize = 1;
		com_rslt = _bmp280_write(bmp280, &data, 1);
		bmp280_compute_wait_time(bmp280, &waittime);
		bmp280->delay_msec(waittime);
		com_rslt += bmp280_read_uncompensed_pressure_temperature(bmp280, uncP, uncT);
	}
	return com_rslt;
}


#ifdef BMP280_ENABLE_FLOAT
/* Read actual temperature from uncompensated temperature
 *
 * Note Returns the value in Degree centigrade
 *      Output value of "51.23" equals 51.23 DegC.
 *
 * Param uncT : value of uncompensated temperature
 *
 * Return Actual temperature in floating point
 */
double bmp280_compensate_T_double(struct _bmp280* bmp280, int32_t uncT)
{
	double x1 = 0;
	double x2 = 0;
	double temperature = 0;

	x1 = (((double)uncT) / BMP280_FLOAT_TRUE_TEMP_16384 -
	      ((double)bmp280->calpar.dig_T1) / BMP280_FLOAT_TRUE_TEMP_1024) *
		((double)bmp280->calpar.dig_T2);
	x2 = ((((double)uncT) / BMP280_FLOAT_TRUE_TEMP_131072 -
	       ((double)bmp280->calpar.dig_T1) / BMP280_FLOAT_TRUE_TEMP_8192) *
	      (((double)uncT) / BMP280_FLOAT_TRUE_TEMP_131072 -
	       ((double)bmp280->calpar.dig_T1) / BMP280_FLOAT_TRUE_TEMP_8192)) *
		((double)bmp280->calpar.dig_T3);
	bmp280->calpar.t_fine = (int32_t)(x1 + x2);
	temperature  = (x1 + x2) / BMP280_FLOAT_TRUE_TEMP_5120;
	return temperature;
}

/* Reads actual pressure from uncompensated pressure and returns pressure in
 * Pa as double.
 *
 * Note Output value of "96386.2" equals 96386.2 Pa = 963.862 hPa.
 *
 * Param uncP : value of uncompensated pressure
 *
 * Return Actual pressure in floating point
 */
double bmp280_compensate_P_double(struct _bmp280* bmp280, int32_t uncP)
{
	double x1 = 0;
	double x2 = 0;
	double pressure = 0;

	x1 = ((double)bmp280->calpar.t_fine / BMP280_FLOAT_TRUE_PRES_2) -
		BMP280_FLOAT_TRUE_PRES_64000;
	x2 = x1 * x1 * ((double)bmp280->calpar.dig_P6) /
		BMP280_FLOAT_TRUE_PRES_32768;
	x2 = x2 + x1 * ((double)bmp280->calpar.dig_P5)
		* BMP280_FLOAT_TRUE_PRES_2;
	x2 = (x2 / BMP280_FLOAT_TRUE_PRES_4) + ((double)bmp280->calpar.dig_P4)
		* BMP280_FLOAT_TRUE_PRES_65536;
	x1 = (((double)bmp280->calpar.dig_P3) * x1 * x1
	      / BMP280_FLOAT_TRUE_PRES_524288 + ((double)bmp280->calpar.dig_P2) * x1)
		/ BMP280_FLOAT_TRUE_PRES_524288;
	x1 = (BMP280_FLOAT_TRUE_PRES_1 + x1 / BMP280_FLOAT_TRUE_PRES_32768) *
		((double)bmp280->calpar.dig_P1);
	pressure = BMP280_FLOAT_TRUE_PRES_1048576 - (double)uncP;
	/* Avoid exception caused by division by zero */
	if (fabs(x1) >= EPSILON)
		pressure = (pressure - (x2 / BMP280_FLOAT_TRUE_PRES_4096)) *
			BMP280_FLOAT_TRUE_PRES_6250 / x1;
	else
		return BMP280_FLOAT_TRUE_PRES_0;
	x1 = ((double)bmp280->calpar.dig_P9) * pressure * pressure /
		BMP280_FLOAT_TRUE_PRES_2147483648;
	x2 = pressure * ((double)bmp280->calpar.dig_P8) / BMP280_FLOAT_TRUE_PRES_32768;
	pressure = pressure + (x1 + x2 + ((double)bmp280->calpar.dig_P7))
		/ BMP280_FLOAT_TRUE_PRES_1_6;

	return pressure;
}
#endif


#if defined(BMP280_ENABLE_INT64) && defined(BMP280_64BITSUPPORT_PRESENT)
/* Read actual pressure from uncompensated pressure
 *
 * Note returns the value in Pa as unsigned 32 bit integer in Q24.8 format
 * (24 integer bits and 8 fractional bits). Output value of "24674867"
 * represents 24674867 / 256 = 96386.2 Pa = 963.862 hPa
 *
 * Param uncP : value of uncompensated pressure
 *
 * Return actual pressure as 64bit output
 */
uint32_t bmp280_compensate_P_int64(struct _bmp280* bmp280, int32_t uncP)
{
	int64_t x1_s64r = 0;
	int64_t x2_s64r = 0;
	int64_t pressure = 0;

	x1_s64r = ((int64_t)bmp280->calpar.t_fine) -
		BMP280_TRUE_PRES_128000;
	x2_s64r = x1_s64r * x1_s64r * (int64_t)bmp280->calpar.dig_P6;
	x2_s64r = x2_s64r + ((x1_s64r * (int64_t)bmp280->calpar.dig_P5) << 17);
	x2_s64r = x2_s64r + (((int64_t)bmp280->calpar.dig_P4) << 35);
	x1_s64r = ((x1_s64r * x1_s64r * (int64_t)bmp280->calpar.dig_P3) >> 8) +
		((x1_s64r * (int64_t)bmp280->calpar.dig_P2) << 12);
	x1_s64r = (((((int64_t)BMP280_TRUE_PRES_1) << 47) + x1_s64r)) *
		((int64_t)bmp280->calpar.dig_P1) >> 33;
	pressure = BMP280_TRUE_PRES_1048576 - uncP;

	if (x1_s64r != 0)
#if defined __KERNEL__
	pressure = div64_s64((((pressure << 31) - x2_s64r)
						  * BMP280_TRUE_PRES_3125), x1_s64r);
#else
	pressure = (((pressure << 31) - x2_s64r)
				* BMP280_TRUE_PRES_3125) / x1_s64r;
#endif
	else
		return 0;

	x1_s64r = (((int64_t)bmp280->calpar.dig_P9) * (pressure >> 13) *
		   (pressure >> 13)) >> 25;
	x2_s64r = (((int64_t)bmp280->calpar.dig_P8) * pressure) >> 19;
	pressure = ((pressure + x1_s64r + x2_s64r)	>> 8) +
		(((int64_t)bmp280->calpar.dig_P7) << 4);
	return (uint32_t)pressure;
}
#endif

/* Computing waiting time for sensor data read
 *
 * Param delaytimer: The value of delay time
 *
 * Return 0
 */
uint8_t bmp280_compute_wait_time (struct _bmp280* bmp280, uint8_t* delaytimer)
{
	/* variable used to return communication result*/
	uint8_t com_rslt = SUCCESS;

	*delaytimer = (T_INIT_MAX + T_MEASURE_PER_OSRS_MAX *
		       (((1 << bmp280->overs_temp) >> 1) +
			((1 << bmp280->overs_pres) >> 1)) +
		       (bmp280->overs_pres ? T_SETUP_PRESSURE_MAX : 0) + 15) / 16;
	return com_rslt;
}

/*
 *	Read ID and Calibration parameters
 *  Return results of bus communication function
 *	0 -> Success
 *	-1 -> Error
 */
uint8_t bmp280_read_id_get_calib_param (struct _bmp280* bmp280)
{
	/* variable used to return communication result*/
	uint8_t com_rslt;
	uint8_t data = 0;

	/* read chip id */
	bmp280->twid->iaddr = BMP280_CHIP_ID_REG;
	bmp280->twid->isize = 1;
	com_rslt = _bmp280_read(bmp280, &data, 1);
	bmp280->chip_id = data;
	if ( data != BMP280_CHIP_ID ) {
		printf(" -E- Error Chip ID : 0x%x \n\r", data);
		com_rslt = ERROR;
	}
	else {
		printf(" -I- Chip ID: 0x%x \n\r", data);
		/* readout bmp280 calibration parameter structure */
		com_rslt += bmp280_get_calpar(bmp280);
	}
	return com_rslt;
}

// End of file
