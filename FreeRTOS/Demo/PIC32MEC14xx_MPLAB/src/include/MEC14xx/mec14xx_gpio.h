/*****************************************************************************
* Copyright 2014 Microchip Technology Inc. and its subsidiaries.
* You may use this software and any derivatives exclusively with
* Microchip products.
* THIS SOFTWARE IS SUPPLIED BY MICROCHIP "AS IS".
* NO WARRANTIES, WHETHER EXPRESS, IMPLIED OR STATUTORY, APPLY TO THIS SOFTWARE,
* INCLUDING ANY IMPLIED WARRANTIES OF NON-INFRINGEMENT, MERCHANTABILITY,
* AND FITNESS FOR A PARTICULAR PURPOSE, OR ITS INTERACTION WITH MICROCHIP
* PRODUCTS, COMBINATION WITH ANY OTHER PRODUCTS, OR USE IN ANY APPLICATION.
* IN NO EVENT WILL MICROCHIP BE LIABLE FOR ANY INDIRECT, SPECIAL, PUNITIVE,
* INCIDENTAL OR CONSEQUENTIAL LOSS, DAMAGE, COST OR EXPENSE OF ANY KIND
* WHATSOEVER RELATED TO THE SOFTWARE, HOWEVER CAUSED, EVEN IF MICROCHIP HAS
* BEEN ADVISED OF THE POSSIBILITY OR THE DAMAGES ARE FORESEEABLE.
* TO THE FULLEST EXTENT ALLOWED BY LAW, MICROCHIP'S TOTAL LIABILITY ON ALL
* CLAIMS IN ANY WAY RELATED TO THIS SOFTWARE WILL NOT EXCEED THE AMOUNT OF
* FEES, IF ANY, THAT YOU HAVE PAID DIRECTLY TO MICROCHIP FOR THIS SOFTWARE.
* MICROCHIP PROVIDES THIS SOFTWARE CONDITIONALLY UPON YOUR ACCEPTANCE
* OF THESE TERMS.
*****************************************************************************/


/** @file mec14xx_gpio.h
 *MEC14xx GPIO definitions
 */
/** @defgroup MEC14xx Peripherals GPIO
 */

#ifndef _MEC14XX_GPIO_H
#define _MEC14XX_GPIO_H

#include <stdint.h>
#include "mec14xx.h"


#ifdef __cplusplus
 extern "C" {
#endif 

#define NUM_GPIO_PORTS (MEC14xx_NUM_GPIO_BANKS)
#define MAX_NUM_GPIO (NUM_GPIO_PORTS * 32)

#define GPIO_PORT_A_BITMAP (0x7FFFFFFFul)   // GPIO_0000 to GPIO_0037
#define GPIO_PORT_B_BITMAP (0x00FFFFFFul)   // GPIO_0040 to GPIO_0077
#define GPIO_PORT_C_BITMAP (0x7FFFFFFFul)   // GPIO_0100 to GPIO_0137
#define GPIO_PORT_D_BITMAP (0x7FFFFFFFul)   // GPIO_0140 to GPIO_0177


#define GPIO_PORT_A_DRVSTR_BITMAP   (0x7FFFFFFEul)
#define GPIO_PORT_B_DRVSTR_BITMAP   (0x006FFFFFul)
#define GPIO_PORT_C_DRVSTR_BITMAP   (0x7FFFFFFFul)
#define GPIO_PORT_D_DRVSTR_BITMAP   (0x007FFFFFul)


//
// Control 
//
#define GPIO_CTRL_RSVD_MASK     (0xFEFEC000UL)
//
#define GPIO_PUD_BITPOS         (0)
#define GPIO_PUD_BLEN           (2)
#define GPIO_PUD_MASK           (0x03UL << (GPIO_PUD_BITPOS))
#define GPIO_PUD_NONE           (0x00)
#define GPIO_PUD_PU             (0x01)
#define GPIO_PUD_PD             (0x02)
#define GPIO_PUD_NONE2          (0x03)
//
#define GPIO_PWRG_BITPOS        (2)
#define GPIO_PWRG_BLEN          (2)
#define GPIO_PWRG_MASK          (0x03UL << (GPIO_PWRG_BITPOS))
#define GPIO_PWRG_V3_S5         (0x00UL << (GPIO_PWRG_BITPOS))
#define GPIO_PWRG_VCC_MAIN      (0x01UL << (GPIO_PWRG_BITPOS))
#define GPIO_PWRG_V3_DUAL       (0x02UL << (GPIO_PWRG_BITPOS))
#define GPIO_PWRG_UNPWRD        (0x03UL << (GPIO_PWRG_BITPOS))
//
#define GPIO_INTDET_BITPOS      (4)
#define GPIO_INTDET_BLEN        (4)
#define GPIO_INTDET_MASK        (0x0FUL << (GPIO_INTDET_BITPOS))
#define GPIO_INTDET_LVL_LOW     (0x00UL << (GPIO_INTDET_BITPOS)) 
#define GPIO_INTDET_LVL_HI      (0x01UL << (GPIO_INTDET_BITPOS)) 
#define GPIO_INTDET_DISABLE     (0x04UL << (GPIO_INTDET_BITPOS)) 
#define GPIO_INTDET_RISE_EDG    (0x0DUL << (GPIO_INTDET_BITPOS)) 
#define GPIO_INTDET_FALL_EDG    (0x0EUL << (GPIO_INTDET_BITPOS)) 
#define GPIO_INTDET_BOTH_EDG    (0x0FUL << (GPIO_INTDET_BITPOS)) 
//
#define GPIO_BUFFTYPE_BITPOS    (8)
#define GPIO_BUFFTYPE_BLEN      (1)
#define GPIO_BUFFTYPE_PUSHPULL  (0x00UL << (GPIO_BUFFTYPE_BITPOS))
#define GPIO_BUFFTYPE_OPENDRAIN (0x01UL << (GPIO_BUFFTYPE_BITPOS))
//
#define GPIO_DIR_BITPOS         (9)
#define GPIO_DIR_BLEN           (1)
#define GPIO_DIR_MASK           (0x01UL << (GPIO_DIR_BITPOS))
#define GPIO_DIR_INPUT          (0x00UL << (GPIO_DIR_BITPOS))
#define GPIO_DIR_OUTPUT         (0x01UL << (GPIO_DIR_BITPOS))
//
#define GPIO_PARWEN_BITPOS      (10)
#define GPIO_PARWEN_BLEN        (1)
#define GPIO_PARWEN_DIS         (0x00UL << (GPIO_PARWEN_BITPOS))
#define GPIO_PARWEN_EN          (0x01UL << (GPIO_PARWEN_BITPOS))
//
#define GPIO_POLARITY_BITPOS    (11)
#define GPIO_POLARITY_BLEN      (1)
#define GPIO_POLARITY_NON_INV   (0x00UL << (GPIO_POLARITY_BITPOS))
#define GPIO_POLARITY_INV       (0x01UL << (GPIO_POLARITY_BITPOS))
//
#define GPIO_MUX_BITPOS         (12)
#define GPIO_MUX_BLEN           (2)
#define GPIO_MUX_MASK           (0x0FUL << (GPIO_MUX_BITPOS))
#define GPIO_MUX_GPIO           (0x00UL << (GPIO_MUX_BITPOS)) 
#define GPIO_MUX_FUNC1          (0x01UL << (GPIO_MUX_BITPOS)) 
#define GPIO_MUX_FUNC2          (0x02UL << (GPIO_MUX_BITPOS)) 
#define GPIO_MUX_FUNC3          (0x03UL << (GPIO_MUX_BITPOS)) 
//
#define GPIO_OUTPUT_BITPOS      (16)
#define GPIO_OUTPUT_BLEN        (1)
#define GPIO_OUTPUT_0           (0x00UL << (GPIO_OUTPUT_BITPOS))
#define GPIO_OUTPUT_1           (0x01UL << (GPIO_OUTPUT_BITPOS))
#define GP_OUTPUT_0             (0x00UL)    // Byte or Bit-banding usage
#define GP_OUTPUT_1             (0x01UL)
//
#define GPIO_PADIN_BITPOS       (24)
#define GPIO_PADIN_BLEN         (1)
#define GPIO_PADIN_LOW          (0x00UL << (GPIO_PADIN_BITPOS))
#define GPIO_PADIN_HI           (0x01UL << (GPIO_PADIN_BITPOS))
#define GP_PADIN_LO             (0x00UL)    // Byte or Bit-banding usage
#define GP_PADIN_HI             (0x01UL)

#define GPIO_PIN_LOW            (0UL)
#define GPIO_PIN_HIGH           (1UL)

//
// Drive Strength
// For GPIO pins that implement drive strength each pin 
// has a 32-bit register containing bit fields  for 
// slew rate and buffer current strength
//
#define GPIO_DRV_STR_OFFSET     (0x0500ul)
#define GPIO_DRV_SLEW_BITPOS    (0ul)
#define GPIO_DRV_SLEW_MASK      (1ul << GPIO_DRV_SLEW_BITPOS)
#define GPIO_DRV_SLEW_SLOW      (0ul << GPIO_DRV_SLEW_BITPOS)
#define GPIO_DRV_SLEW_FAST      (1ul << GPIO_DRV_SLEW_BITPOS)
#define GPIO_DRV_STR_BITPOS     (4ul)
#define GPIO_DRV_STR_LEN        (2ul)
#define GPIO_DRV_STR_MASK       (0x03ul << GPIO_DRV_STR_BITPOS)
#define GPIO_DRV_STR_2MA        (0ul << GPIO_DRV_STR_BITPOS)
#define GPIO_DRV_STR_4MA        (1ul << GPIO_DRV_STR_BITPOS)
#define GPIO_DRV_STR_8MA        (2ul << GPIO_DRV_STR_BITPOS)
#define GPIO_DRV_STR_12MA       (3ul << GPIO_DRV_STR_BITPOS)

/*****************************************************************************
 * GPIO API
 ****************************************************************************/
#define GPIO_PORTA          (0u)
#define GPIO_PORTB          (1u)
#define GPIO_PORTC          (2u)
#define GPIO_PORTD          (3u)
#define GPIO_PORTE          (4u)
#define GPIO_MAX_PORT       (5u)


/*
 * GPIO Functionality
 */

typedef enum gpio_id_t
{
    GPIO_0000_ID,     // 00h: Begin Port A
    GPIO_0001_ID,
    GPIO_0002_ID,
    GPIO_0003_ID,
    GPIO_0004_ID,
    GPIO_0005_ID,
    GPIO_0006_ID,
    GPIO_0007_ID,
    //
    GPIO_0010_ID,    // 08h
    GPIO_0011_ID,
    GPIO_0012_ID,
    GPIO_0013_ID,
    GPIO_0014_ID,
    GPIO_0015_ID,
    GPIO_0016_ID,
    GPIO_0017_ID,
    //
    GPIO_0020_ID,    // 10h
    GPIO_0021_ID,
    GPIO_0022_ID,
    GPIO_0023_ID,
    GPIO_0024_ID,
    GPIO_0025_ID,
    GPIO_0026_ID,
    GPIO_0027_ID,
    //
    GPIO_0030_ID,    // 18h
    GPIO_0031_ID,
    GPIO_0032_ID,
    GPIO_0033_ID,
    GPIO_0034_ID,
    GPIO_0035_ID,
    GPIO_0036_ID,
    GPIO_0037_ID,     // End Port A
    //
    GPIO_0040_ID,     // 20h: Begin Port B
    GPIO_0041_ID,
    GPIO_0042_ID,
    GPIO_0043_ID,
    GPIO_0044_ID,
    GPIO_0045_ID,
    GPIO_0046_ID,
    GPIO_0047_ID,
    //
    GPIO_0050_ID,    // 28h
    GPIO_0051_ID,
    GPIO_0052_ID,
    GPIO_0053_ID,
    GPIO_0054_ID,
    GPIO_0055_ID,
    GPIO_0056_ID,
    GPIO_0057_ID,
    //
    GPIO_0060_ID,    // 30h
    GPIO_0061_ID,
    GPIO_0062_ID,
    GPIO_0063_ID,
    GPIO_0064_ID,
    GPIO_0065_ID,
    GPIO_0066_ID,
    GPIO_0067_ID,
    //
    GPIO_0070_ID,    // 38h
    GPIO_0071_ID,
    GPIO_0072_ID,
    GPIO_0073_ID,
    GPIO_0074_ID,
    GPIO_0075_ID,
    GPIO_0076_ID,
    GPIO_0077_ID,     // End Port B
    //
    GPIO_0100_ID,     // 40h: Begin Port C
    GPIO_0101_ID,
    GPIO_0102_ID,
    GPIO_0103_ID,
    GPIO_0104_ID,
    GPIO_0105_ID,
    GPIO_0106_ID,
    GPIO_0107_ID,
    //
    GPIO_0110_ID,    // 48h
    GPIO_0111_ID,
    GPIO_0112_ID,
    GPIO_0113_ID,
    GPIO_0114_ID,
    GPIO_0115_ID,
    GPIO_0116_ID,
    GPIO_0117_ID,
    //
    GPIO_0120_ID,    // 50h
    GPIO_0121_ID,
    GPIO_0122_ID,
    GPIO_0123_ID,
    GPIO_0124_ID,
    GPIO_0125_ID,
    GPIO_0126_ID,
    GPIO_0127_ID,
    //
    GPIO_0130_ID,    // 58h
    GPIO_0131_ID,
    GPIO_0132_ID,
    GPIO_0133_ID,
    GPIO_0134_ID,
    GPIO_0135_ID,
    GPIO_0136_ID,
    GPIO_0137_ID,     // End Port C
    //
    GPIO_0140_ID,     // 60h: Begin Port D
    GPIO_0141_ID,
    GPIO_0142_ID,
    GPIO_0143_ID,
    GPIO_0144_ID,
    GPIO_0145_ID,
    GPIO_0146_ID,
    GPIO_0147_ID,
    //
    GPIO_0150_ID,    // 68h
    GPIO_0151_ID,
    GPIO_0152_ID,
    GPIO_0153_ID,
    GPIO_0154_ID,
    GPIO_0155_ID,
    GPIO_0156_ID,
    GPIO_0157_ID,
    //
    GPIO_0160_ID,    // 70h
    GPIO_0161_ID,
    GPIO_0162_ID,
    GPIO_0163_ID,
    GPIO_0164_ID,
    GPIO_0165_ID,
    GPIO_0166_ID,
    GPIO_0167_ID,
    //
    MAX_GPIO_ID

} GPIO_ID;


enum gpio_prop_t
{
   GPIO_PROP_PU_PD,
   GPIO_PROP_PWR_GATE,
   GPIO_PROP_INT_DET,
   GPIO_PROP_OBUFF_TYPE,
   GPIO_PROP_DIR,
   GPIO_PROP_ALT_OUT_EN,
   GPIO_PROP_POLARITY,
   GPIO_PROP_MUX_SEL,
   GPIO_PROP_ALL,
   GPIO_PROP_MAX
};


enum gpio_pupd_t
{
   GPIO_PUPD_NONE,
   GPIO_PULLUP_EN,
   GPIO_PULLDN_EN,
   GPIO_PUPD_NONE2
};


enum gpio_idetect_t
{
   GPIO_DET_LEVEL_LOW,
   GPIO_DET_LEVEL_HIGH,
   GPIO_DET_RSVD2,
   GPIO_DET_RSVD3,
   GPIO_DET_DISABLE,
   GPIO_DET_RSVD5,
   GPIO_DET_RSVD6,
   GPIO_DET_RSVD7,
   GPIO_DET_RSVD8,
   GPIO_DET_RSVD9,
   GPIO_DET_RSVDA,
   GPIO_DET_RSVDB,
   GPIO_DET_RSVDC,
   GPIO_DET_RISING_EDGE,
   GPIO_DET_FALLING_EDGE,
   GPIO_DET_BOTH_EDGES
};


enum gpio_buff_type_t
{
   GPIO_OUT_BUFF_PUSH_PULL,
   GPIO_OUT_BUFF_OPEN_DRAIN
};


enum gpio_dir_t
{
   GPIO_DIR_IN,
   GPIO_DIR_OUT
};


enum gpio_polarity_t
{
   GPIO_NON_INVERT,
   GPIO_INVERT
};


enum gpio_mux_t
{
   GPIO_FUNC_GPIO,
   GPIO_FUNC_1,
   GPIO_FUNC_2,
   GPIO_FUNC_3
};

// Slew Rate & Drive Strength
enum gpio_slew_rate_t
{
    GPIO_SLEW_SLOW,
    GPIO_SLEW_FAST
};

enum gpio_drv_str_t
{
    GPIO_DRV_2MA = 0,
    GPIO_DRV_4MA,
    GPIO_DRV_8MA,
    GPIO_DRV_12MA
};




uint16_t GPIOGetConfig(enum gpio_id_t gpio_id);
void GPIOSetConfig(enum gpio_id_t gpio_id, uint16_t config);
void GPIOConfigAndOr(enum gpio_id_t gpio_id, uint16_t and_mask, uint16_t or_mask);

uint32_t GPIOGetControl(enum gpio_id_t gpio_id);

void GPIOSetControl(enum gpio_id_t gpio_id, uint32_t ctrl_val);

void GPIOControlAndOr(enum gpio_id_t gpio_id, uint32_t and_mask, uint32_t or_mask);

void GPIOPropertySet ( enum gpio_id_t gpio_id,
                       enum gpio_prop_t gpio_prop,
                       uint16_t prop_val
                     );

uint8_t GPIOGetSlewRate( enum gpio_id_t gpio_id );
void GPIOSetSlewRate ( enum gpio_id_t gpio_id,
                       enum gpio_slew_rate_t slew_rate );
uint8_t GPIOGetDriveStr ( enum gpio_id_t gpio_id );
void GPIOSetDriveStr ( enum gpio_id_t gpio_id,
                       enum gpio_drv_str_t drv_str );
uint8_t GPIOGetDriveStrAndSlew ( enum gpio_id_t gpio_id );
void GPIOSetDriveStrAndSlew ( enum gpio_id_t gpio_id,
                              uint8_t drv_and_slew );

void GPIOSetOutput ( enum gpio_id_t gpio_id,
                     uint8_t gpio_state
                     );

void GPIOToggleOutput ( enum gpio_id_t gpio_id );

uint8_t GPIOReadPin( enum gpio_id_t gpio_id );

void GPIOPinLock(enum gpio_id_t gpio_id);

#ifdef __cplusplus
}
#endif

#endif // #ifndef _MEC14XX_GPIO_H
/* end mec14XX_gpio.h */
/**   @}
 */





