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
/*! \file bmp280.h
    \brief BMP280 Sensor Driver Support Header File */

#ifndef __BMP280_H__
#define __BMP280_H__

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include <stdint.h>

/*----------------------------------------------------------------------------
 *        Definition
 *----------------------------------------------------------------------------*/

#define BMP280_64BITSUPPORT_PRESENT

/********************************************/
/**\name	ENABLE FLATING OUTPUT      */
/**************************************/

// If the user wants to support floating point calculations, please set the following define.
#define BMP280_ENABLE_FLOAT

// If the user wants to support 64 bit integer calculation (needed for optimal pressure accuracy)
// please set the following definition. If int64 calculation is not wanted (e.g. because it would include
// large libraries), please do not set the definition.
#define BMP280_ENABLE_INT64

/****************************************/
/**\name	DELAY       */
/****************************************/

// defines the return parameter type of the BMP280_DELAY_FUNCTION
#define BMP280_DELAY_RETURN_TYPE void

// defines the calling parameter types of the BMP280_DELAY_FUNCTION
#define BMP280_DELAY_PARAM_TYPES uint16_t

/***************************************************************/
/**\name	GET AND SET BITSLICE FUNCTIONS       */
/***************************************************************/

/* never change this line */
#define BMP280_DELAY_FUNC(delay_in_msec) delay_func(delay_in_msec)

#define BMP280_GET_BITSLICE(regvar, bitname) ((regvar & bitname##__MSK) >> bitname##__POS)

#define BMP280_SET_BITSLICE(regvar, bitname, val) ((regvar & ~bitname##__MSK) | ((val<<bitname##__POS)&bitname##__MSK))

/***************************************************************/
/**\name	COMMON USED CONSTANTS       */
/***************************************************************/
/* Constants */
#define BMP280_NULL             0
#define	BMP280_INIT_VALUE		0

/************************************************/
/**\name	ERROR CODES      */
/************************************************/
#define	SUCCESS			  		((uint8_t)0)
#define ERROR       			((uint8_t)0xFF)
#define E_BMP280_NULL_PTR       ((uint8_t)ERROR-1)
#define E_BMP280_COMM_RES       ((uint8_t)ERROR-2)
#define E_BMP280_OUT_OF_RANGE   ((uint8_t)ERROR-3)

/************************************************/
/**\name	I2C ADDRESS DEFINITION       */
/***********************************************/
#define BMP280_I2C_ADDRESS1                     0x76
#define BMP280_I2C_ADDRESS2                     0x77
/************************************************/
/**\name	POWER MODE DEFINITION       */
/***********************************************/
/* Sensor Specific constants */
#define BMP280_SLEEP_MODE                       0x00
#define BMP280_FORCED_MODE                      0x01
#define BMP280_NORMAL_MODE                      0x03
#define BMP280_SOFT_RESET_CODE                  0xB6
/************************************************/
/**\name	STANDBY TIME DEFINITION       */
/***********************************************/
#define BMP280_STANDBY_TIME_1_MS                0x00
#define BMP280_STANDBY_TIME_63_MS               0x01
#define BMP280_STANDBY_TIME_125_MS              0x02
#define BMP280_STANDBY_TIME_250_MS              0x03
#define BMP280_STANDBY_TIME_500_MS              0x04
#define BMP280_STANDBY_TIME_1000_MS             0x05
#define BMP280_STANDBY_TIME_2000_MS             0x06
#define BMP280_STANDBY_TIME_4000_MS             0x07
/************************************************/
/**\name	OVERSAMPLING DEFINITION       */
/***********************************************/
#define BMP280_OVERSAMPLING_SKIPPED             0x00
#define BMP280_OVERSAMP_1X                      0x01
#define BMP280_OVERSAMP_2X                      0x02
#define BMP280_OVERSAMP_4X                      0x03
#define BMP280_OVERSAMP_8X                      0x04
#define BMP280_OVERSAMP_16X                     0x05
/************************************************/
/**\name	WORKING MODE DEFINITION       */
/***********************************************/
#define BMP280_ULTRA_LOW_POWER_MODE              0x00
#define BMP280_LOW_POWER_MODE	                0x01
#define BMP280_STANDARD_RESOLUTION_MODE         0x02
#define BMP280_HIGH_RESOLUTION_MODE             0x03
#define BMP280_ULTRA_HIGH_RESOLUTION_MODE       0x04

#define BMP280_ULTRALOWPOWER_OVRS_PRES          BMP280_OVERSAMP_1X
#define BMP280_ULTRALOWPOWER_OVRS_TEMP          BMP280_OVERSAMP_1X

#define BMP280_LOWPOWER_OVRS_PRES	        	BMP280_OVERSAMP_2X
#define BMP280_LOWPOWER_OVRS_TEMP	        	BMP280_OVERSAMP_1X

#define BMP280_STANDARDRESOLUTION_OVRS_PRES     BMP280_OVERSAMP_4X
#define BMP280_STANDARDRESOLUTION_OVRS_TEMP     BMP280_OVERSAMP_1X

#define BMP280_HIGHRESOLUTION_OVRS_PRES         BMP280_OVERSAMP_8X
#define BMP280_HIGHRESOLUTION_OVRS_TEMP         BMP280_OVERSAMP_1X

#define BMP280_ULTRAHIGHRESOLUTION_OVRS_PRES    BMP280_OVERSAMP_16X
#define BMP280_ULTRAHIGHRESOLUTION_OVRS_TEMP    BMP280_OVERSAMP_2X
/************************************************/
/**\name	FILTER DEFINITION       */
/***********************************************/
#define BMP280_FILTER_COEFF_OFF					0x00
#define BMP280_FILTER_COEFF_2                   0x01
#define BMP280_FILTER_COEFF_4                   0x02
#define BMP280_FILTER_COEFF_8                   0x03
#define BMP280_FILTER_COEFF_16                  0x04
/************************************************/
/**\name	DELAY TIME DEFINITION       */
/***********************************************/
#define T_INIT_MAX	                        	20      /* 20/16 = 1.25 ms */
#define T_MEASURE_PER_OSRS_MAX					37      /* 37/16 = 2.3125 ms*/
#define T_SETUP_PRESSURE_MAX					10      /* 10/16 = 0.625 ms */
/************************************************/
/**\name	CALIBRATION PARAMETERS DEFINITION       */
/***********************************************/
/*calibration parameters */
#define BMP280_DIG_T1_LSB_REG                   0x88
#define BMP280_DIG_T1_MSB_REG                   0x89
#define BMP280_DIG_T2_LSB_REG                   0x8A
#define BMP280_DIG_T2_MSB_REG                   0x8B
#define BMP280_DIG_T3_LSB_REG                   0x8C
#define BMP280_DIG_T3_MSB_REG                   0x8D
#define BMP280_DIG_P1_LSB_REG                   0x8E
#define BMP280_DIG_P1_MSB_REG                   0x8F
#define BMP280_DIG_P2_LSB_REG                   0x90
#define BMP280_DIG_P2_MSB_REG                   0x91
#define BMP280_DIG_P3_LSB_REG                   0x92
#define BMP280_DIG_P3_MSB_REG                   0x93
#define BMP280_DIG_P4_LSB_REG                   0x94
#define BMP280_DIG_P4_MSB_REG                   0x95
#define BMP280_DIG_P5_LSB_REG                   0x96
#define BMP280_DIG_P5_MSB_REG                   0x97
#define BMP280_DIG_P6_LSB_REG                   0x98
#define BMP280_DIG_P6_MSB_REG                   0x99
#define BMP280_DIG_P7_LSB_REG                   0x9A
#define BMP280_DIG_P7_MSB_REG                   0x9B
#define BMP280_DIG_P8_LSB_REG                   0x9C
#define BMP280_DIG_P8_MSB_REG                   0x9D
#define BMP280_DIG_P9_LSB_REG                   0x9E
#define BMP280_DIG_P9_MSB_REG                   0x9F
/************************************************/
/**\name	REGISTER ADDRESS DEFINITION       */
/***********************************************/
#define BMP280_CHIP_ID_REG                      0xD0  /*Chip ID Register */
#define BMP280_RST_REG                          0xE0  /*Softreset Register */
#define BMP280_STAT_REG                         0xF3  /*Status Register */
#define BMP280_CTRL_MEAS_REG                    0xF4  /*Ctrl Measure Register */
#define BMP280_CONFIG_REG                       0xF5  /*Configuration Register */
#define BMP280_PRESSURE_MSB_REG                 0xF7  /*Pressure MSB Register */
#define BMP280_PRESSURE_LSB_REG                 0xF8  /*Pressure LSB Register */
#define BMP280_PRESSURE_XLSB_REG                0xF9  /*Pressure XLSB Register */
#define BMP280_TEMPERATURE_MSB_REG              0xFA  /*Temperature MSB Reg */
#define BMP280_TEMPERATURE_LSB_REG              0xFB  /*Temperature LSB Reg */
#define BMP280_TEMPERATURE_XLSB_REG             0xFC  /*Temperature XLSB Reg */
/************************************************/
/**\name	BIT LENGTH,POSITION AND MASK DEFINITION      */
/***********************************************/
/* Status Register */
#define BMP280_STATUS_REG_MEASURING__POS        3
#define BMP280_STATUS_REG_MEASURING__MSK        0x08
#define BMP280_STATUS_REG_MEASURING__LEN        1
#define BMP280_STATUS_REG_MEASURING__REG        BMP280_STAT_REG

#define BMP280_STATUS_REG_IM_UPDATE__POS        0
#define BMP280_STATUS_REG_IM_UPDATE__MSK        0x01
#define BMP280_STATUS_REG_IM_UPDATE__LEN        1
#define BMP280_STATUS_REG_IM_UPDATE__REG        BMP280_STAT_REG
/************************************************/
/**\name	BIT LENGTH,POSITION AND MASK DEFINITION
FOR TEMPERATURE OVERSAMPLING */
/***********************************************/
/* Control Measurement Register */
#define BMP280_CTRL_MEAS_REG_OVRS_TEMP__POS     5
#define BMP280_CTRL_MEAS_REG_OVRS_TEMP__MSK     0xE0
#define BMP280_CTRL_MEAS_REG_OVRS_TEMP__LEN     3
#define BMP280_CTRL_MEAS_REG_OVRS_TEMP__REG     \
BMP280_CTRL_MEAS_REG
/************************************************/
/**\name	BIT LENGTH,POSITION AND MASK DEFINITION
FOR PRESSURE OVERSAMPLING */
/***********************************************/
#define BMP280_CTRL_MEAS_REG_OVRS_PRES__POS     2
#define BMP280_CTRL_MEAS_REG_OVRS_PRES__MSK     0x1C
#define BMP280_CTRL_MEAS_REG_OVRS_PRES__LEN     3
#define BMP280_CTRL_MEAS_REG_OVRS_PRES__REG     \
BMP280_CTRL_MEAS_REG
/************************************************/
/**\name	BIT LENGTH,POSITION AND MASK DEFINITION
FOR POWER MODE */
/***********************************************/
#define BMP280_CTRL_MEAS_REG_POWER_MODE__POS    0
#define BMP280_CTRL_MEAS_REG_POWER_MODE__MSK    0x03
#define BMP280_CTRL_MEAS_REG_POWER_MODE__LEN    2
#define BMP280_CTRL_MEAS_REG_POWER_MODE__REG    BMP280_CTRL_MEAS_REG
/************************************************/
/**\name	BIT LENGTH,POSITION AND MASK DEFINITION
FOR STANDBY DURATION */
/***********************************************/
/* Configuration Register */
#define BMP280_CONFIG_REG_STANDBY_DURN__POS     5
#define BMP280_CONFIG_REG_STANDBY_DURN__MSK     0xE0
#define BMP280_CONFIG_REG_STANDBY_DURN__LEN     3
#define BMP280_CONFIG_REG_STANDBY_DURN__REG     BMP280_CONFIG_REG
/************************************************/
/**\name	BIT LENGTH,POSITION AND MASK DEFINITION
FOR IIR FILTER */
/***********************************************/
#define BMP280_CONFIG_REG_FILTER__POS           2
#define BMP280_CONFIG_REG_FILTER__MSK           0x1C
#define BMP280_CONFIG_REG_FILTER__LEN           3
#define BMP280_CONFIG_REG_FILTER__REG           BMP280_CONFIG_REG
/************************************************/
/**\name	BIT LENGTH,POSITION AND MASK DEFINITION
FOR SPI ENABLE*/
/***********************************************/
#define BMP280_CONFIG_REG_SPI3_ENABLE__POS      0
#define BMP280_CONFIG_REG_SPI3_ENABLE__MSK      0x01
#define BMP280_CONFIG_REG_SPI3_ENABLE__LEN      1
#define BMP280_CONFIG_REG_SPI3_ENABLE__REG      BMP280_CONFIG_REG
/************************************************/
/**\name	BIT LENGTH,POSITION AND MASK DEFINITION
FOR PRESSURE AND TEMPERATURE DATA REGISTERS */
/***********************************************/
/* Data Register */
#define BMP280_PRESSURE_XLSB_REG__POS           4
#define BMP280_PRESSURE_XLSB_REG__MSK           0xF0
#define BMP280_PRESSURE_XLSB_REG__LEN           4
#define BMP280_PRESSURE_XLSB_REG__REG           BMP280_PRESSURE_XLSB_REG

#define BMP280_TEMPERATURE_XLSB_REG__POS        4
#define BMP280_TEMPERATURE_XLSB_REG__MSK        0xF0
#define BMP280_TEMPERATURE_XLSB_REG__LEN        4
#define BMP280_TEMPERATURE_XLSB_REG__REG        BMP280_TEMPERATURE_XLSB_REG

/****************************************************/
/**\name	ARRAY PARAMETERS      */
/***************************************************/
#define LSB_ZERO	0
#define MSB_ONE		1
#define LSB_TWO		2
#define MSB_THREE	3
#define LSB_FOUR	4
#define MSB_FIVE	5
#define LSB_SIX		6
#define MSB_SEVEN	7
/****************************************************/
/**\name	TRUE TEMPERATURE CALUCULATION PARAMETERS  */
/***************************************************/
#define BMP280_DEC_TRUE_TEMP_5           5
#define BMP280_DEC_TRUE_TEMP_128         128
/****************************************************/
/**\name	TRUE PRESSURE CALUCULATION PARAMETERS  */
/***************************************************/
#define BMP280_DEC_TRUE_PRES_64000		64000
#define BMP280_DEC_TRUE_PRES_2	        2
#define BMP280_DEC_TRUE_PRES_32768		32768
#define BMP280_DEC_TRUE_PRES_1048576	1048576
#define BMP280_DEC_TRUE_PRES_3125		3125
#define BMP280_HEX_TRUE_PRES_8M	        0x80000000

/****************************************************/
/**\name	TRUE TEMPERATURE CALCULATION FLOAT RETURN  */
/***************************************************/
#define BMP280_FLOAT_TRUE_TEMP_16384	16384.0
#define BMP280_FLOAT_TRUE_TEMP_1024		1024.0
#define BMP280_FLOAT_TRUE_TEMP_131072	131072.0
#define BMP280_FLOAT_TRUE_TEMP_8192		8192.0
#define BMP280_FLOAT_TRUE_TEMP_5120		5120.0

/****************************************************/
/**\name	TRUE PRESSURE CALCULATION FLOAT RETURN  */
/***************************************************/
#define	BMP280_FLOAT_TRUE_PRES_1		1.0
#define	BMP280_FLOAT_TRUE_PRES_0		0.0
#define	BMP280_FLOAT_TRUE_PRES_2		2.0
#define	BMP280_FLOAT_TRUE_PRES_4		4.0
#define	BMP280_FLOAT_TRUE_PRES_1_6		16.0
#define	BMP280_FLOAT_TRUE_PRES_64000	64000.0
#define	BMP280_FLOAT_TRUE_PRES_32768	32768.0
#define	BMP280_FLOAT_TRUE_PRES_65536	65536.0
#define	BMP280_FLOAT_TRUE_PRES_524288	524288.0
#define	BMP280_FLOAT_TRUE_PRES_1048576	1048576.0
#define	BMP280_FLOAT_TRUE_PRES_4096		4096.0
#define	BMP280_FLOAT_TRUE_PRES_6250		6250.0
#define	BMP280_FLOAT_TRUE_PRES_2147483648  2147483648.0

/****************************************************/
/**\name	TRUE PRESSURE CALUCULATION 64BIT RETURN  */
/***************************************************/
#define BMP280_TRUE_PRES_128000	    128000
#define BMP280_TRUE_PRES_1048576	1048576
#define BMP280_TRUE_PRES_3125		3125
#define BMP280_TRUE_PRES_1			1

/**************************************************************/
/**\name	CHIP ID                        */
/**************************************************************/
#define BMP280_CHIP_ID				0x58

/**************************************************************/
/**\name	STRUCTURE DEFINITIONS                         */
/**************************************************************/
// This structure holds all device specific calibration parameters
struct _bmp280_calib_par
{
  uint16_t dig_T1;      /**<calibration T1 data*/
  int16_t dig_T2;       /**<calibration T2 data*/
  int16_t dig_T3;       /**<calibration T3 data*/
  uint16_t dig_P1;      /**<calibration P1 data*/
  int16_t dig_P2;       /**<calibration P2 data*/
  int16_t dig_P3;       /**<calibration P3 data*/
  int16_t dig_P4;       /**<calibration P4 data*/
  int16_t dig_P5;       /**<calibration P5 data*/
  int16_t dig_P6;       /**<calibration P6 data*/
  int16_t dig_P7;       /**<calibration P7 data*/
  int16_t dig_P8;       /**<calibration P8 data*/
  int16_t dig_P9;       /**<calibration P9 data*/
  int32_t t_fine;       /**<calibration t_fine data*/
};

// This structure holds BMP280 initialization parameters
struct _bmp280
{
	struct _twi_desc* twid;

	struct _bmp280_calib_par calpar;	/**<calibration data*/
	uint8_t chip_id;                    /**< chip id of the sensor*/
	uint8_t dev_addr;                   /**< device address of the sensor*/
	uint8_t overs_temp;                 /**< temperature over sampling*/
	uint8_t overs_pres;                 /**< pressure over sampling*/
	void(*delay_msec)(uint16_t);        /**< delay function pointer*/
};

/**************************************************************/
/**\name	FUNCTION DECLARATIONS                         */
/**************************************************************/

static uint8_t _bmp280_read(struct _bmp280* bmp280, uint8_t* buffer, uint32_t len);
static uint8_t _bmp280_write(struct _bmp280* bmp280, const uint8_t* buffer, uint32_t len);

uint8_t bmp280_write_register(struct _bmp280* bmp280, uint8_t addr, uint8_t* pdata, uint8_t len);
uint8_t bmp280_read_register(struct _bmp280* bmp280, uint8_t addr, uint8_t* pdata, uint8_t len);

uint8_t bmp280_read_uncompensed_temperature (struct _bmp280* bmp280, int32_t* uncT);
int32_t bmp280_compensate_temperatureC (struct _bmp280* bmp280, int32_t uncT);
uint8_t bmp280_read_uncompensed_pressure (struct _bmp280* bmp280, int32_t* uncP);
uint32_t  bmp280_compensate_pressureP (struct _bmp280* bmp280, int32_t uncP);
uint8_t bmp280_read_uncompensed_pressure_temperature (struct _bmp280* bmp280, int32_t* uncP, int32_t* uncT);
uint8_t bmp280_read_pressure_temperature (struct _bmp280* bmp280, uint32_t* pressure, int32_t* temperature);
uint8_t bmp280_get_calpar (struct _bmp280* bmp280);
uint8_t bmp280_get_overs_temp (struct _bmp280* bmp280, uint8_t* value);
uint8_t bmp280_set_overs_temp (struct _bmp280* bmp280, uint8_t value);
uint8_t bmp280_get_overs_pres (struct _bmp280* bmp280, uint8_t* value);
uint8_t bmp280_set_overs_pres (struct _bmp280* bmp280, uint8_t value);
uint8_t bmp280_get_power_mode(struct _bmp280* bmp280, uint8_t* power_mode);
uint8_t bmp280_set_power_mode (struct _bmp280* bmp280, uint8_t power_mode);
uint8_t bmp280_set_soft_rst (struct _bmp280* bmp280);
uint8_t bmp280_get_spi3 (struct _bmp280* bmp280, uint8_t* enable_disable);
uint8_t bmp280_set_spi3 (struct _bmp280* bmp280, uint8_t enable_disable);
uint8_t bmp280_get_filter (struct _bmp280* bmp280, uint8_t *value);
uint8_t bmp280_set_filter (struct _bmp280* bmp280, uint8_t value);
uint8_t bmp280_get_standby_durn(struct _bmp280* bmp280, uint8_t* standby_durn);
uint8_t bmp280_set_standby_durn (struct _bmp280* bmp280, uint8_t standby_durn);
uint8_t bmp280_set_work_mode (struct _bmp280* bmp280, uint8_t work_mode);
uint8_t bmp280_get_forced_uncP_temperature(struct _bmp280* bmp280, int32_t* uncP, int32_t* uncT);

uint8_t bmp280_read_id_get_calib_param (struct _bmp280* bmp280);

/**************************************************************/
/**\name	FUNCTION FOR TRUE TEMPERATURE CALCULATION   */
/**************************************************************/

#ifdef BMP280_ENABLE_FLOAT
	double bmp280_compensate_T_double(struct _bmp280* bmp280, int32_t uncT);
	double bmp280_compensate_P_double(struct _bmp280* bmp280, int32_t uncP);
#endif

#if defined(BMP280_ENABLE_INT64) && defined(BMP280_64BITSUPPORT_PRESENT)
  uint32_t bmp280_compensate_P_int64(struct _bmp280* bmp280, int32_t uncP);
#endif

/**************************************************************/
/**\name	FUNCTION FOR DELAY CALCULATION DURING FORCEMODE  */
/**************************************************************/

uint8_t bmp280_compute_wait_time (struct _bmp280* bmp280, uint8_t* delaytimer);

//------------------------------------------------------------------------------
//------------------------------------------------------------------------------
//------------------------------------------------------------------------------
#endif
