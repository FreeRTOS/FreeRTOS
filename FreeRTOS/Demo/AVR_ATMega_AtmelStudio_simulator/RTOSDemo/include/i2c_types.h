
/**
 * \file
 *
 * \brief I2C master driver.
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

#ifndef I2C_TYPES_H
#define I2C_TYPES_H

#include <stdint.h>

typedef enum {
	I2C_NOERR, // The message was sent.
	I2C_BUSY,  // Message was NOT sent, bus was busy.
	I2C_FAIL   // Message was NOT sent, bus failure
	           // If you are interested in the failure reason,
	           // Sit on the event call-backs.
} i2c_error_t;

typedef enum { i2c_stop = 1, i2c_restart_read, i2c_restart_write, i2c_continue, i2c_reset_link } i2c_operations_t;

typedef i2c_operations_t (*i2c_callback)(void *p);

typedef uint8_t i2c_address_t;

// common callback responses
i2c_operations_t i2c_cb_return_stop(void *p);
i2c_operations_t i2c_cb_return_reset(void *p);
i2c_operations_t i2c_cb_restart_write(void *p);
i2c_operations_t i2c_cb_restart_read(void *p);

#endif /* I2C_TYPES_H */
