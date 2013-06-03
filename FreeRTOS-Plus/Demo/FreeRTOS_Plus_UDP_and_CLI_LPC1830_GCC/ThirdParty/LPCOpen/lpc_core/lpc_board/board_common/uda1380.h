/*
 * @brief UDA1380 Audio Codec header
 *
 * @note
 * Copyright(C) NXP Semiconductors, 2012
 * All rights reserved.
 *
 * @par
 * Software that is described herein is for illustrative purposes only
 * which provides customers with programming information regarding the
 * LPC products.  This software is supplied "AS IS" without any warranties of
 * any kind, and NXP Semiconductors and its licensor disclaim any and
 * all warranties, express or implied, including all implied warranties of
 * merchantability, fitness for a particular purpose and non-infringement of
 * intellectual property rights.  NXP Semiconductors assumes no responsibility
 * or liability for the use of the software, conveys no license or rights under any
 * patent, copyright, mask work right, or any other intellectual property rights in
 * or to any products. NXP Semiconductors reserves the right to make changes
 * in the software without notification. NXP Semiconductors also makes no
 * representation or warranty that such application will be suitable for the
 * specified use without further testing or modification.
 *
 * @par
 * Permission to use, copy, modify, and distribute this software and its
 * documentation is hereby granted, under NXP Semiconductors' and its
 * licensor's relevant copyrights in the software, without fee, provided that it
 * is used in conjunction with NXP Semiconductors microcontrollers.  This
 * copyright, permission, and disclaimer notice must appear in all copies of
 * this code.
 */

#ifndef __UDA1380_H_
#define __UDA1380_H_

/** @defgroup BOARD_COMMON_UDA1380 BOARD: UDA1380 Audio codec interface module
 * UDA1380 Audio codec interface module, the module registers are accessed
 * using I2C. The board which uses this module must define #UDA1380_I2C_BUS to #I2C0
 * , #I2C1, etc, based on which I2C bus is connected to UDA1380. All the
 * functions in this modules assumes that the I2C interrupt for #UDA1380_I2C_BUS
 * is enabled and ::Chip_I2C_MasterStateHandler(#UDA1380_I2C_BUS) is called from the
 * ISR. If the functions are to be used in polling mode the caller must replace
 * the event handler to Chip_I2C_EventHandlerPolling(), by using API
 * Chip_I2C_SetMasterEventHandler(). A macro #I2CDEV_UDA1380_ADDR must be defined
 * to the appropriate slave address of UDA1380 audio codec.
 * @ingroup BOARD_Common
 * @{
 */

/* UDA1380 Registers */
#define UDA_EVALM_CLK          0x00
#define UDA_BUS_CTRL           0x01
#define UDA_POWER_CTRL         0x02
#define UDA_ANALOG_CTRL        0x03
#define UDA_HPAMP_CTRL         0x04
#define UDA_MASTER_VOL_CTRL    0x10
#define UDA_MIXER_VOL_CTRL     0x11
#define UDA_MODE_CTRL          0x12
#define UDA_MUTE_CTRL          0x13
#define UDA_MIXER_FILTER_CTRL  0x14
#define UDA_DEC_VOL_CTRL       0x20
#define UDA_PGA_CTRL           0x21
#define UDA_ADC_CTRL           0x22
#define UDA_AGC_CTRL           0x23
#define UDA_TOTAL_REG          0x24

/** Evalutation mode and clock setting register bits */
#define EVCLK_EV2             (1 << 15)
#define EVCLK_EV1             (1 << 14)
#define EVCLK_EV0             (1 << 13)
#define EVCLK_EN_ADC          (1 << 11)
#define EVCLK_EN_DEC          (1 << 10)
#define EVCLK_EN_DAC          (1 << 9)
#define EVCLK_EN_INT          (1 << 8)
#define EVCLK_ADC_CLK         (1 << 5)
#define EVCLK_DAC_CLK         (1 << 4)
#define EVCLK_SYS_DIV1        (1 << 3)
#define EVCLK_SYS_DIV0        (1 << 2)
#define EVCLK_PLL1            (1 << 1)
#define EVCLK_PLL0            (1 << 0)

/** UDA1380 register default values */
#define UDA1380_REG_EVALCLK_DEFAULT_VALUE    (0xF << 8 | 0x3 << 4 | 1 << 1)
#define UDA1380_REG_I2S_DEFAULT_VALUE        0x0000

#define UDA1380_REG_PWRCTRL_DEFAULT_VALUE    (1 << 15 | 1 << 13 | 1 << 10 | 1 << 8 | 1 << 6 | 1 << 4 | 0x0F)
#define UDA1380_REG_ANAMIX_DEFAULT_VALUE     0x0000
#define UDA1380_REG_HEADAMP_DEFAULT_VALUE    ( 1 << 9 | 2)

#define UDA1380_REG_MSTRVOL_DEFAULT_VALUE    0x0000
#define UDA1380_REG_MIXVOL_DEFAULT_VALUE     0x0000
#define UDA1380_REG_MODEBBT_DEFAULT_VALUE    0x0000
#define UDA1380_REG_MSTRMUTE_DEFAULT_VALUE   (2 << 8 | 2)
#define UDA1380_REG_MIXSDO_DEFAULT_VALUE     0x0000

#define UDA1380_REG_DECVOL_DEFAULT_VALUE     0xE4E4	/* Decrease Volume -28dB */
#define UDA1380_REG_PGA_DEFAULT_VALUE        0x0000
#define UDA1380_REG_ADC_DEFAULT_VALUE        0x0001	/* Apply 0bB VGA Gain, enable DC Filter */
#define UDA1380_REG_AGC_DEFAULT_VALUE        0x0000

#define UDA1380_REG_L3_DEFAULT_VALUE         0x0000

/* UDA1380 Audio input selection */
#define UDA1380_LINE_IN   0			/**< LINE_IN_L in left stream, LINE_IN_R in Right stream */
#define UDA1380_MIC_IN_L  (1 << 2)	/**< MIC audio in Left stream, Line_IN_R in Right stream */
#define UDA1380_MIC_IN_LR (3 << 2)	/**< MIC audio in Left & Right stream */

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @def UDA1380_U8(val)
 * Convert a 16 bit register value to 2 x 8 bit values that could be written
 * to the I2C bus in an efficient way.
 */
#define UDA1380_U8(val)        (((val) >> 8) & 0xFF), ((val) & 0xFF)

/**
 * @brief	Write a 16-bit value to UDA Register
 * @param	reg		: Register to which @a val be written
 * @param	val		: 16-Bit value to be written
 * @return	Nothing
 */
void UDA1380_REG_Write(uint8_t reg, uint16_t val);

/**
 * @brief	Read a 16-bit value from UDA1380 codec register
 * @param	reg		: Register from which the value to be read
 * @return	Returns the value read from the register
 */
uint16_t UDA1380_REG_Read(uint8_t reg);

/**
 * @brief	Writes a value to a UDA register, read back and verify the value
 * @param	reg		: Register to which the value be written
 * @param	val		: Value to be written
 * @return	1 On success, 0 on failure
 */
int UDA1380_REG_WriteVerify(uint8_t reg, uint16_t val);

/**
 * @brief	Write multiple value to UDA1380 registers
 * @param	buff	: Pointer to buffer (See note section)
 * @param	len		: Number of bytes in buff
 * @return	1 on Success, 0 on failure
 * @note	buff[0] must be the address of the register to which
 * the first data i.e, buff[1], buff[2] be written, the next bytes
 * buff[3], buff[4] be written to register buff[0]+1 and so on.
 */
int UDA1380_REG_WriteMult(const uint8_t *buff, int len);

/**
 * @brief	Verify values in multiple UDA1380 registers
 * @param	reg		: Starting register from which data be read
 * @param	value	: Pointer to memory which contains values to be compared
 * @param	buff	: Pointer to memory to which data be read
 * @param	len		: Length of bytes in value @a buff
 * @return	1 on Success & Data is valid, 0 on Failure
 */
int UDA1380_REG_VerifyMult(uint8_t reg, const uint8_t *value, uint8_t *buff, int len);

/**
 * @brief	Initialize UDA1380 to its default state
 * @param	input	: Audio input source (Must be one of  #UDA1380_LINE_IN
 *                    or #UDA1380_MIC_IN_L or #UDA1380_MIC_IN_LR)
 * @return	1 on Success and 0 on failure
 */
int UDA1380_Init(int input);


#ifdef __cplusplus
}
#endif

/**
 * @}
 */
#endif /* __UDA1380_H_ */
