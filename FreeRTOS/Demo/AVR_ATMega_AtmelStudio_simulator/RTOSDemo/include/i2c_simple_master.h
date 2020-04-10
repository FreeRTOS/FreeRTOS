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

#ifndef I2C_SIMPLE_MASTER_H
#define I2C_SIMPLE_MASTER_H

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <i2c_types.h>

#ifdef __cplusplus
extern "C" {
#endif

#define I2C_TIMEOUT 10000

uint8_t     I2C_0_read1ByteRegister(i2c_address_t address, uint8_t reg);
uint16_t    I2C_0_read2ByteRegister(i2c_address_t address, uint8_t reg);
i2c_error_t I2C_0_write1ByteRegister(i2c_address_t address, uint8_t reg, uint8_t data);
i2c_error_t I2C_0_write2ByteRegister(i2c_address_t address, uint8_t reg, uint16_t data);

i2c_error_t I2C_0_writeNBytes(i2c_address_t address, void *data, size_t len);
i2c_error_t I2C_0_readDataBlock(i2c_address_t address, uint8_t reg, void *data, size_t len);
i2c_error_t I2C_0_readNBytes(i2c_address_t address, void *data, size_t len);

#ifdef __cplusplus
}
#endif

#endif /* I2C_SIMPLE_MASTER_H_INCLUDED */
