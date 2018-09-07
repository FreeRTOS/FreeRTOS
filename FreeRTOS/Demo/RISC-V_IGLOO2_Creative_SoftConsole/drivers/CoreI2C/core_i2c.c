/*******************************************************************************
 * (c) Copyright 2009-2015 Microsemi  SoC Products Group.  All rights reserved.
 * 
 * CoreI2C software driver implementation.
 * 
 * SVN $Revision: 7984 $
 * SVN $Date: 2015-10-12 12:07:40 +0530 (Mon, 12 Oct 2015) $
 */
#include <stdint.h>
#include <stdlib.h>
#include <stddef.h>
#include <unistd.h>
#include <errno.h>
#include <sys/stat.h>
#include <sys/times.h>
#include <stdio.h>
#include <string.h>
#include "cpu_types.h"
#include "core_smbus_regs.h"
#include "core_i2c.h"
#include "hal.h"
#include "hal_assert.h"


#include <string.h>

#ifdef __cplusplus
extern "C" {
#endif

/*------------------------------------------------------------------------------
 * I2C transaction direction.
 */
#define WRITE_DIR    0u
#define READ_DIR     1u

/* -- TRANSACTIONS TYPES -- */
#define NO_TRANSACTION                      0u
#define MASTER_WRITE_TRANSACTION            1u
#define MASTER_READ_TRANSACTION             2u
#define MASTER_RANDOM_READ_TRANSACTION      3u
#define WRITE_SLAVE_TRANSACTION             4u
#define READ_SLAVE_TRANSACTION              5u

/* -- SMBUS H/W STATES -- */
/* -- MASTER STATES -- */
#define ST_BUS_ERROR        0x00u           /* Bus error during MST or selected slave modes */
#define ST_I2C_IDLE         0xF8u           /* No activity and no interrupt either... */
#define ST_START            0x08u           /* start condition sent */
#define ST_RESTART          0x10u           /* repeated start */
#define ST_SLAW_ACK         0x18u           /* SLA+W sent, ack received */
#define ST_SLAW_NACK        0x20u           /* SLA+W sent, nack received */
#define ST_TX_DATA_ACK      0x28u           /* Data sent, ACK'ed */
#define ST_TX_DATA_NACK     0x30u           /* Data sent, NACK'ed */
#define ST_LOST_ARB         0x38u           /* Master lost arbitration */
#define ST_SLAR_ACK         0x40u           /* SLA+R sent, ACK'ed */
#define ST_SLAR_NACK        0x48u           /* SLA+R sent, NACK'ed */
#define ST_RX_DATA_ACK      0x50u           /* Data received, ACK sent */
#define ST_RX_DATA_NACK     0x58u           /* Data received, NACK sent */
#define ST_RESET_ACTIVATED  0xD0u           /* Master reset is activated */
#define ST_STOP_TRANSMIT    0xE0u           /* Stop has been transmitted */

/* -- SLAVE STATES -- */
#define ST_SLAVE_SLAW       0x60u           /* SLA+W received */
#define ST_SLAVE_SLAR_ACK   0xA8u           /* SLA+R received, ACK returned */
#define ST_SLV_LA           0x68u           /* Slave lost arbitration */
#define ST_GCA              0x70u           /* GCA received */
#define ST_GCA_LA           0x78u           /* GCA lost arbitration */
#define ST_RDATA            0x80u           /* Data received */
#define ST_SLA_NACK         0x88u           /* Slave addressed, NACK returned */
#define ST_GCA_ACK          0x90u           /* Previously addresses with GCA, data ACKed */
#define ST_GCA_NACK         0x98u           /* GCA addressed, NACK returned */
#define ST_RSTOP            0xA0u           /* Stop received */
#define ST_SLARW_LA         0xB0u           /* Arbitration lost */
#define ST_RACK             0xB8u           /* Byte sent, ACK received */
#define ST_SLAVE_RNACK      0xC0u           /* Byte sent, NACK received */
#define ST_FINAL            0xC8u           /* Final byte sent, ACK received */
#define ST_SLV_RST          0xD8u           /* Slave reset state */


/* I2C Channel base offset */
#define CHANNEL_BASE_SHIFT    5u
#define CHANNEL_MASK        0x1E0u

/*
 * Maximum address offset length in slave write-read transactions.
 * A maximum of two bytes will be interpreted as address offset within the slave
 * tx buffer.
 */
#define MAX_OFFSET_LENGTH       2u

/*------------------------------------------------------------------------------
 * I2C interrupts control functions implemented "i2c_interrupt.c".
 * the implementation of these functions depend on the underlying hardware
 * design and how the CoreI2C interrupt line is connected to the system's
 * interrupt controller.
 */
void I2C_enable_irq( i2c_instance_t * this_i2c );
void I2C_disable_irq( i2c_instance_t * this_i2c );
static void enable_slave_if_required(i2c_instance_t * this_i2c);

/*------------------------------------------------------------------------------
 * I2C_init()
 * See "core_i2c.h" for details of how to use this function.
 */
void I2C_init
(
    i2c_instance_t * this_i2c,
    addr_t base_address,
    uint8_t ser_address,
    i2c_clock_divider_t ser_clock_speed
)
{
    psr_t saved_psr;
    uint_fast16_t clock_speed = (uint_fast16_t)ser_clock_speed;
    
    /*
     * We need to disable ints while doing this as there is no guarantee we
     * have not been called already and the ISR is active.
     */

   saved_psr=HAL_disable_interrupts();
    
    /*
     * Initialize all items of the this_i2c data structure to zero. This
     * initializes all state variables to their init value. It relies on
     * the fact that NO_TRANSACTION, I2C_SUCCESS and I2C_RELEASE_BUS all
     * have an actual value of zero.
     */
    memset(this_i2c, 0, sizeof(i2c_instance_t));
    
    /*
     * Set base address of I2C hardware used by this instance.
     */
    this_i2c->base_address = base_address;

    /*
     * Update Serial address of the device
     */
    this_i2c->ser_address = ((uint_fast8_t)ser_address << 1u);
    
    /*
     * Configure hardware.
     */
    HAL_set_8bit_reg_field(this_i2c->base_address, ENS1, 0x00); /* Reset I2C hardware. */
    HAL_set_8bit_reg_field(this_i2c->base_address, ENS1, 0x01); /* set enable bit */
    HAL_set_8bit_reg_field(this_i2c->base_address, CR2, ( (clock_speed >> 2) & 0x01) );
    HAL_set_8bit_reg_field(this_i2c->base_address, CR1, ( (clock_speed >> 1) & 0x01) );
    HAL_set_8bit_reg_field(this_i2c->base_address, CR0, ( clock_speed & 0x01) );

    HAL_set_8bit_reg(this_i2c->base_address, ADDRESS, this_i2c->ser_address);
    HAL_set_8bit_reg(this_i2c->base_address, ADDRESS1, this_i2c->ser_address);
    
    /*
     * Finally safe to enable interrupts.
     */

   	HAL_restore_interrupts( saved_psr );
}
/*------------------------------------------------------------------------------
 * I2C_channel_init()
 * See "core_i2c.h" for details of how to use this function.
 */
void I2C_channel_init
(
    i2c_instance_t * this_i2c_channel,
    i2c_instance_t * this_i2c,
    i2c_channel_number_t channel_number,
    i2c_clock_divider_t ser_clock_speed
)
{
    psr_t saved_psr;
    uint_fast16_t clock_speed = (uint_fast16_t)ser_clock_speed;
    
    HAL_ASSERT(channel_number < I2C_MAX_CHANNELS);
    HAL_ASSERT(I2C_CHANNEL_0 != channel_number);

    /* 
     * Cannot allow channel 0 in this function as we will trash the hardware
     * base address and slave address.
     */
    if ((channel_number < I2C_MAX_CHANNELS) &&
        (I2C_CHANNEL_0 != channel_number))
    {
        /*
         * We need to disable ints while doing this as the hardware should already
         * be active at this stage.
         */

   	saved_psr=HAL_disable_interrupts();
        /*
         * Initialize channel data.
         */
        memset(this_i2c_channel, 0, sizeof(i2c_instance_t));
        
        this_i2c_channel->base_address =
               ((this_i2c->base_address) & ~((addr_t)CHANNEL_MASK)) 
            | (((addr_t)channel_number) << CHANNEL_BASE_SHIFT);

        this_i2c_channel->ser_address = this_i2c->ser_address;

        HAL_set_8bit_reg_field(this_i2c_channel->base_address, ENS1, 0x00); /* Reset I2C channel hardware. */
        HAL_set_8bit_reg_field(this_i2c_channel->base_address, ENS1, 0x01); /* set enable bit */
        HAL_set_8bit_reg_field(this_i2c_channel->base_address, CR2, ( (clock_speed >> 2) & 0x01) );
        HAL_set_8bit_reg_field(this_i2c_channel->base_address, CR1, ( (clock_speed >> 1) & 0x01) );
        HAL_set_8bit_reg_field(this_i2c_channel->base_address, CR0, ( clock_speed & 0x01) );
        /*
         * Finally safe to enable interrupts.
         */

   	HAL_restore_interrupts( saved_psr );
    }
}

/*------------------------------------------------------------------------------
 * I2C_write()
 * See "core_i2c.h" for details of how to use this function.
 */
void I2C_write
(
    i2c_instance_t * this_i2c,
    uint8_t serial_addr,
    const uint8_t * write_buffer,
    uint16_t write_size,
    uint8_t options
)
{
    psr_t saved_psr;
    volatile uint8_t stat_ctrl;


   	saved_psr=HAL_disable_interrupts();

    /* Update the transaction only when there is no transaction going on I2C */
    if( this_i2c->transaction == NO_TRANSACTION)
    {
      this_i2c->transaction = MASTER_WRITE_TRANSACTION;
    }

    /* Update the Pending transaction information so that transaction can restarted */
    this_i2c->pending_transaction = MASTER_WRITE_TRANSACTION ;

    /* Update target address */
    this_i2c->target_addr = (uint_fast8_t)serial_addr << 1u;
    this_i2c->dir = WRITE_DIR;
    this_i2c->master_tx_buffer = write_buffer;
    this_i2c->master_tx_size = write_size;
    this_i2c->master_tx_idx = 0u;

    /* Set I2C status in progress */
    this_i2c->master_status = I2C_IN_PROGRESS;
    this_i2c->options = options;

    if(I2C_IN_PROGRESS == this_i2c->slave_status)
    {
        this_i2c->is_transaction_pending = 1u;
    }
    else
    {
        HAL_set_8bit_reg_field(this_i2c->base_address, STA, 0x01u);
    }

    /*
     * Clear interrupts if required (depends on repeated starts).
     * Since the Bus is on hold, only then prior status needs to
     * be cleared.
     */
    if ( I2C_HOLD_BUS == this_i2c->bus_status )
    {
        HAL_set_8bit_reg_field(this_i2c->base_address, SI, 0x00u);
    }

    stat_ctrl = HAL_get_8bit_reg( this_i2c->base_address, STATUS);
    stat_ctrl = stat_ctrl;  /* Avoids lint warning. */

    /* Enable the interrupt. ( Re-enable) */
    I2C_enable_irq( this_i2c );


   	HAL_restore_interrupts(saved_psr);
}

/*------------------------------------------------------------------------------
 * I2C_read()
 * See "core_i2c.h" for details of how to use this function.
 */
void I2C_read
(
    i2c_instance_t * this_i2c,
    uint8_t serial_addr,
    uint8_t * read_buffer,
    uint16_t read_size,
    uint8_t options
)
{
    psr_t saved_psr;
    volatile uint8_t stat_ctrl;


   	saved_psr=HAL_disable_interrupts();
    
    /* Update the transaction only when there is no transaction going on I2C */
    if( this_i2c->transaction == NO_TRANSACTION)
    {
      this_i2c->transaction = MASTER_READ_TRANSACTION;
    }

    /* Update the Pending transaction information so that transaction can restarted */
    this_i2c->pending_transaction = MASTER_READ_TRANSACTION ;

    /* Update target address */
    this_i2c->target_addr = (uint_fast8_t)serial_addr << 1u;

    this_i2c->dir = READ_DIR;

    this_i2c->master_rx_buffer = read_buffer;
    this_i2c->master_rx_size = read_size;
    this_i2c->master_rx_idx = 0u;

    /* Set I2C status in progress */
    this_i2c->master_status = I2C_IN_PROGRESS;

    this_i2c->options = options;
    
    if(I2C_IN_PROGRESS == this_i2c->slave_status)
    {
        this_i2c->is_transaction_pending = 1u;
    }
    else
    {
        HAL_set_8bit_reg_field(this_i2c->base_address, STA, 0x01u);
    }

    /*
     * Clear interrupts if required (depends on repeated starts).
     * Since the Bus is on hold, only then prior status needs to
     * be cleared.
     */
    if ( I2C_HOLD_BUS == this_i2c->bus_status )
    {
        HAL_set_8bit_reg_field(this_i2c->base_address, SI, 0x00u);
    }

    stat_ctrl = HAL_get_8bit_reg( this_i2c->base_address, STATUS);
    stat_ctrl = stat_ctrl;  /* Avoids lint warning. */

    /* Enable the interrupt. ( Re-enable) */
    I2C_enable_irq( this_i2c );

   	HAL_restore_interrupts( saved_psr );

}

/*------------------------------------------------------------------------------
 * I2C_write_read()
 * See "core_i2c.h" for details of how to use this function.
 */
void I2C_write_read
(
    i2c_instance_t * this_i2c,
    uint8_t serial_addr,
    const uint8_t * addr_offset,
    uint16_t offset_size,
    uint8_t * read_buffer,
    uint16_t read_size,
    uint8_t options
)
{
    HAL_ASSERT(offset_size > 0u);
    HAL_ASSERT(addr_offset != (uint8_t *)0);
    HAL_ASSERT(read_size > 0u);
    HAL_ASSERT(read_buffer != (uint8_t *)0);
    
    this_i2c->master_status = I2C_FAILED;
    
    if((read_size > 0u) && (offset_size > 0u))
    {
        psr_t saved_psr;
        volatile uint8_t stat_ctrl;


   	saved_psr=HAL_disable_interrupts();

        /* Update the transaction only when there is no transaction going on I2C */
        if( this_i2c->transaction == NO_TRANSACTION)
        {
            this_i2c->transaction = MASTER_RANDOM_READ_TRANSACTION;
        }

        /* Update the Pending transaction information so that transaction can restarted */
        this_i2c->pending_transaction = MASTER_RANDOM_READ_TRANSACTION ;

        /* Update target address */
        this_i2c->target_addr = (uint_fast8_t)serial_addr << 1u;

        this_i2c->dir = WRITE_DIR;

        this_i2c->master_tx_buffer = addr_offset;
        this_i2c->master_tx_size = offset_size;
        this_i2c->master_tx_idx = 0u;

        this_i2c->master_rx_buffer = read_buffer;
        this_i2c->master_rx_size = read_size;
        this_i2c->master_rx_idx = 0u;
        
        /* Set I2C status in progress */
        this_i2c->master_status = I2C_IN_PROGRESS;
        this_i2c->options = options;
        
        if(I2C_IN_PROGRESS == this_i2c->slave_status)
        {
            this_i2c->is_transaction_pending = 1u;
        }
        else
        {
            HAL_set_8bit_reg_field(this_i2c->base_address, STA, 0x01u);
        }

        /*
         * Clear interrupts if required (depends on repeated starts).
         * Since the Bus is on hold, only then prior status needs to
         * be cleared.
         */
        if ( I2C_HOLD_BUS == this_i2c->bus_status )
        {
            HAL_set_8bit_reg_field(this_i2c->base_address, SI, 0x00u);
        }

        stat_ctrl = HAL_get_8bit_reg( this_i2c->base_address, STATUS);
        stat_ctrl = stat_ctrl;  /* Avoids lint warning. */
            
        /* Enable the interrupt. ( Re-enable) */
        I2C_enable_irq( this_i2c );


   	HAL_restore_interrupts( saved_psr );
    }
}

/*------------------------------------------------------------------------------
 * I2C_get_status()
 * See "core_i2c.h" for details of how to use this function.
 */
i2c_status_t I2C_get_status
(
    i2c_instance_t * this_i2c
)
{
    i2c_status_t i2c_status ;

    i2c_status = this_i2c->master_status ;

    return i2c_status;
}

/*------------------------------------------------------------------------------
 * I2C_wait_complete()
 * See "core_i2c.h" for details of how to use this function.
 */
i2c_status_t I2C_wait_complete
(
    i2c_instance_t * this_i2c,
    uint32_t timeout_ms
)
{
    i2c_status_t i2c_status;
    psr_t saved_psr;
    /*
     * Because we have no idea of what CPU we are supposed to be running on
     * we need to guard this write to the timeout value to avoid ISR/user code
     * interaction issues. Checking the status below should be fine as only a
     * single byte should change in that.
     */

   	saved_psr=HAL_disable_interrupts();
    this_i2c->master_timeout_ms = timeout_ms;

   	HAL_restore_interrupts( saved_psr );

    /* Run the loop until state returns I2C_FAILED  or I2C_SUCESS*/
    do {
        i2c_status = this_i2c->master_status;
    } while(I2C_IN_PROGRESS == i2c_status);
    return i2c_status;
}

/*------------------------------------------------------------------------------
 * I2C_system_tick()
 * See "core_i2c.h" for details of how to use this function.
 */
void I2C_system_tick
(
    i2c_instance_t * this_i2c,
    uint32_t ms_since_last_tick
)
{
    if(this_i2c->master_timeout_ms != I2C_NO_TIMEOUT)
    {
       if(this_i2c->master_timeout_ms > ms_since_last_tick)
        {
            this_i2c->master_timeout_ms -= ms_since_last_tick;
        }
        else
        {
            psr_t saved_psr;
            /*
             * We need to disable interrupts here to ensure we can update the
             * shared data without the I2C ISR interrupting us.
             */

   	saved_psr=HAL_disable_interrupts();

            /*
             * Mark current transaction as having timed out.
             */
            this_i2c->master_status = I2C_TIMED_OUT;
            this_i2c->transaction = NO_TRANSACTION;
            this_i2c->is_transaction_pending = 0;


   	HAL_restore_interrupts( saved_psr );
            
            /*
             * Make sure we do not incorrectly signal a timeout for subsequent
             * transactions.
             */
            this_i2c->master_timeout_ms = I2C_NO_TIMEOUT;
        }
    }
}

/*------------------------------------------------------------------------------
 * I2C_set_slave_tx_buffer()
 * See "core_i2c.h" for details of how to use this function.
 */
void I2C_set_slave_tx_buffer
(
    i2c_instance_t * this_i2c,
    const uint8_t * tx_buffer,
    uint16_t tx_size
)
{
    psr_t saved_psr;

    /*
     * We need to disable interrupts here to ensure we can update the
     * shared data without the I2C ISR interrupting us.
     */

   	saved_psr=HAL_disable_interrupts();
    
    this_i2c->slave_tx_buffer = tx_buffer;
    this_i2c->slave_tx_size = tx_size;
    this_i2c->slave_tx_idx = 0u;
    

   	HAL_restore_interrupts( saved_psr );
}

/*------------------------------------------------------------------------------
 * I2C_set_slave_rx_buffer()
 * See "core_i2c.h" for details of how to use this function.
 */
void I2C_set_slave_rx_buffer
(
    i2c_instance_t * this_i2c,
    uint8_t * rx_buffer,
    uint16_t rx_size
)
{
    psr_t saved_psr;

    /*
     * We need to disable interrupts here to ensure we can update the
     * shared data without the I2C ISR interrupting us.
     */

   	saved_psr=HAL_disable_interrupts();

    this_i2c->slave_rx_buffer = rx_buffer;
    this_i2c->slave_rx_size = rx_size;
    this_i2c->slave_rx_idx = 0u;


   	HAL_restore_interrupts( saved_psr );
}

/*------------------------------------------------------------------------------
 * I2C_set_slave_mem_offset_length()
 * See "core_i2c.h" for details of how to use this function.
 */
void I2C_set_slave_mem_offset_length
(
    i2c_instance_t * this_i2c,
    uint8_t offset_length
)
{
    HAL_ASSERT(offset_length <= MAX_OFFSET_LENGTH);
    
    /*
     * Single byte update, should be interrupt safe
     */
    if(offset_length > MAX_OFFSET_LENGTH)
    {
        this_i2c->slave_mem_offset_length = MAX_OFFSET_LENGTH;
    }
    else
    {
        this_i2c->slave_mem_offset_length = offset_length;
    }
}

/*------------------------------------------------------------------------------
 * I2C_register_write_handler()
 * See "core_i2c.h" for details of how to use this function.
 */
void I2C_register_write_handler
(
    i2c_instance_t * this_i2c,
    i2c_slave_wr_handler_t handler
)
{
    psr_t saved_psr;

    /*
     * We need to disable interrupts here to ensure we can update the
     * shared data without the I2C ISR interrupting us.
     */

   	saved_psr=HAL_disable_interrupts();

    this_i2c->slave_write_handler = handler;


   	HAL_restore_interrupts( saved_psr );
}

/*------------------------------------------------------------------------------
 * I2C_enable_slave()
 * See "core_i2c.h" for details of how to use this function.
 */
void I2C_enable_slave
(
    i2c_instance_t * this_i2c
)
{
    psr_t saved_psr;

    /*
     * We need to disable interrupts here to ensure we can update the
     * hardware register and slave mode flag without the I2C ISR interrupting
     * us.
     */

   	saved_psr=HAL_disable_interrupts();

    /* Set the Assert Acknowledge bit. */
    HAL_set_8bit_reg_field(this_i2c->base_address, AA, 0x01u);

    /* Enable slave mode */
    this_i2c->is_slave_enabled = 1u;


   	HAL_restore_interrupts( saved_psr );

    /* Enable I2C IRQ*/
    I2C_enable_irq( this_i2c );
}

/*------------------------------------------------------------------------------
 * I2C_disable_slave()
 * See "core_i2c.h" for details of how to use this function.
 */
void I2C_disable_slave
(
    i2c_instance_t * this_i2c
)
{
    psr_t saved_psr;

    /*
     * We need to disable interrupts here to ensure we can update the
     * hardware register without the I2C ISR interrupting us.
     */

   	saved_psr=HAL_disable_interrupts();
    
    /* Reset the assert acknowledge bit. */
    HAL_set_8bit_reg_field(this_i2c->base_address, AA, 0x00u);

    /* Disable slave mode with IRQ blocked to make whole change atomic */
    this_i2c->is_slave_enabled = 0u;


   	HAL_restore_interrupts( saved_psr );
}

/*------------------------------------------------------------------------------
 * 
 */
static void enable_slave_if_required
(
    i2c_instance_t * this_i2c
)
{
    /*
     * This function is only called from within the ISR and so does not need
     * guarding on the register access.
     */
    if( 0 != this_i2c->is_slave_enabled )
    {
        HAL_set_8bit_reg_field( this_i2c->base_address, AA, 0x01u );
    }
}
/*------------------------------------------------------------------------------
 * I2C_set_slave_second_addr()
 * See "i2c.h" for details of how to use this function.
 */
void I2C_set_slave_second_addr
(
    i2c_instance_t * this_i2c,
    uint8_t second_slave_addr
)
{
    uint8_t second_slave_address;
    
    /*
      This function does not support CoreI2C hardware configured with a fixed 
      second slave address.  The current implementation of the ADDR1[0] register
      bit makes it difficult for the driver to support both programmable and
      fixed second slave address, so we choose to support programmable only.
      With the programmable configuration, ADDR1[0] and ADDR0[0] both control
      enable/disable of GCA recognition, as an effective OR of the 2 bit fields.
      Therefore we set ADDR1[0] to 0 here, so that only ADDR0[0] controls GCA.
     */
    second_slave_address = (uint8_t)((second_slave_addr << 1u) & (~SLAVE1_EN_MASK));

    /*
     * Single byte register write, should be interrupt safe
     */
    HAL_set_8bit_reg(this_i2c->base_address, ADDRESS1, second_slave_address);
}

/*------------------------------------------------------------------------------
 * I2C_disable_slave_second_addr()
 * See "i2c.h" for details of how to use this function.
 */
void I2C_disable_slave_second_addr
(
    i2c_instance_t * this_i2c
)
{
    /*
      We are disabling the second slave address by setting the value of the 2nd
      slave address to the primary slave address. The reason for using this method
      of disabling 2nd slave address is that ADDRESS1[0] has different meaning 
      depending on hardware configuration. Its use would likely interfere with
      the intended GCA setting.
     */
    /*
     * Single byte register write, should be interrupt safe
     */
    HAL_set_8bit_reg(this_i2c->base_address, ADDRESS1, this_i2c->ser_address);
}

/*------------------------------------------------------------------------------
 * i2C_set_gca()
 * See "i2c.h" for details of how to use this function.
 */

void I2C_set_gca
(
    i2c_instance_t * this_i2c
)
{
    /* 
     * This read modify write access should be interrupt safe as the address
     * register is not written to in the ISR.
     */
    /* accept GC addressing. */
    HAL_set_8bit_reg_field(this_i2c->base_address, GC, 0x01u);
}

/*------------------------------------------------------------------------------
 * I2C_clear_gca()
 * See "i2c.h" for details of how to use this function.
 */
void I2C_clear_gca
(
    i2c_instance_t * this_i2c
)
{
    /* 
     * This read modify write access should be interrupt safe as the address
     * register is not written to in the ISR.
     */
    /* Clear GC addressing. */
    HAL_set_8bit_reg_field(this_i2c->base_address, GC, 0x00u);
}

/*------------------------------------------------------------------------------
 * I2C_isr()
 * See "core_i2c.h" for details of how to use this function.
 */
void I2C_isr
(
    i2c_instance_t * this_i2c
)
{
    volatile uint8_t status;
    uint8_t data;
    uint8_t hold_bus;
    uint8_t clear_irq = 1u;

    status = HAL_get_8bit_reg( this_i2c->base_address, STATUS);
    
    switch( status )
    {
        /************** MASTER TRANSMITTER / RECEIVER *******************/
      
        case ST_START: /* start has been xmt'd */
        case ST_RESTART: /* repeated start has been xmt'd */
  	    //write_hex(STDOUT_FILENO, status);
            HAL_set_8bit_reg_field( this_i2c->base_address, STA, 0x00u);
            HAL_set_8bit_reg( this_i2c->base_address, DATA, this_i2c->target_addr); /* write call address */
            HAL_set_8bit_reg_field( this_i2c->base_address, DIR, this_i2c->dir); /* set direction bit */
            if(this_i2c->dir == WRITE_DIR)
            {
                 this_i2c->master_tx_idx = 0u;
            }
            else
            {
                 this_i2c->master_rx_idx = 0u;
            }

            /*
             * Clear the pending transaction. This condition will be true if the slave 
             * has acquired the bus to carry out pending master transaction which 
             * it had received during its slave transmission or reception mode. 
             */
            if(this_i2c->is_transaction_pending)
            {
                this_i2c->is_transaction_pending = 0u;
            }

            /*
             * Make sure to update proper transaction after master START
             * or RESTART
             */
            if(this_i2c->transaction != this_i2c->pending_transaction)
            {
                this_i2c->transaction = this_i2c->pending_transaction;
            }
            break;
            
        case ST_LOST_ARB:
              /* Set start bit.  Let's keep trying!  Don't give up! */
              HAL_set_8bit_reg_field(this_i2c->base_address, STA, 0x01u);
              break;

        case ST_STOP_TRANSMIT:
             /* Stop has been transmitted. Do nothing */
              break;

        /******************* MASTER TRANSMITTER *************************/
        case ST_SLAW_NACK:
  	    //write_hex(STDOUT_FILENO, status);
            /* SLA+W has been transmitted; not ACK has been received - let's stop. */
            HAL_set_8bit_reg_field(this_i2c->base_address, STO, 0x01u);
            this_i2c->master_status = I2C_FAILED;
            this_i2c->transaction = NO_TRANSACTION;
            enable_slave_if_required(this_i2c);
            break;
            
        case ST_SLAW_ACK:
        case ST_TX_DATA_ACK:
  	    //write_hex(STDOUT_FILENO, status);
            /* data byte has been xmt'd with ACK, time to send stop bit or repeated start. */
            if (this_i2c->master_tx_idx < this_i2c->master_tx_size)
            {    
                HAL_set_8bit_reg(this_i2c->base_address, DATA, (uint_fast8_t)this_i2c->master_tx_buffer[this_i2c->master_tx_idx++]);
            }
            else if ( this_i2c->transaction == MASTER_RANDOM_READ_TRANSACTION )
            {
                /* We are finished sending the address offset part of a random read transaction.
                 * It is is time to send a restart in order to change direction. */
                 this_i2c->dir = READ_DIR;
                 HAL_set_8bit_reg_field(this_i2c->base_address, STA, 0x01u);
            }
            else /* done sending. let's stop */
            {
                /*
                 * Set the transaction back to NO_TRANSACTION to allow user to do further
                 * transaction
                 */
                this_i2c->transaction = NO_TRANSACTION;
                hold_bus = this_i2c->options & I2C_HOLD_BUS;

                /* Store the information of current I2C bus status in the bus_status*/
                this_i2c->bus_status  = hold_bus;
                if ( hold_bus == 0u )
                { 
                    HAL_set_8bit_reg_field(this_i2c->base_address, STO, 0x01u);  /*xmt stop condition */
                    enable_slave_if_required(this_i2c);
                }
                else
                {
                    I2C_disable_irq( this_i2c );
                    clear_irq = 0u;
                }
                this_i2c->master_status = I2C_SUCCESS;
            }
            break;

          case ST_TX_DATA_NACK:
  	    //write_hex(STDOUT_FILENO, status);
            /* data byte SENT, ACK to be received
             * In fact, this means we've received a NACK (This may not be 
             * obvious, but if we've rec'd an ACK then we would be in state 
             * 0x28!) hence, let's send a stop bit
             */
            HAL_set_8bit_reg_field(this_i2c->base_address, STO, 0x01u);/* xmt stop condition */
            this_i2c->master_status = I2C_FAILED;

            /*
             * Set the transaction back to NO_TRANSACTION to allow user to do further
             * transaction
             */
            this_i2c->transaction = NO_TRANSACTION;
            enable_slave_if_required(this_i2c);
            break;
              
      /********************* MASTER (or slave?) RECEIVER *************************/
      
      /* STATUS codes 08H, 10H, 38H are all covered in MTX mode */
        case ST_SLAR_ACK: /* SLA+R tx'ed. */
//  	    //write_hex(STDOUT_FILENO, status);
            /* Let's make sure we ACK the first data byte received (set AA bit in CTRL) unless
             * the next byte is the last byte of the read transaction.
             */
            if(this_i2c->master_rx_size > 1u)
            {
                HAL_set_8bit_reg_field(this_i2c->base_address, AA, 0x01u);
            }
            else if(1u == this_i2c->master_rx_size)
            {
                HAL_set_8bit_reg_field(this_i2c->base_address, AA, 0x00u);
            }
            else /* this_i2c->master_rx_size == 0u */
            {
                HAL_set_8bit_reg_field(this_i2c->base_address, AA, 0x01u);
                HAL_set_8bit_reg_field(this_i2c->base_address, STO, 0x01u);
                this_i2c->master_status = I2C_SUCCESS;
                this_i2c->transaction = NO_TRANSACTION;
            }
            break;
            
        case ST_SLAR_NACK: /* SLA+R tx'ed; let's release the bus (send a stop condition) */
//  	    //write_hex(STDOUT_FILENO, status);
            HAL_set_8bit_reg_field(this_i2c->base_address, STO, 0x01u);
            this_i2c->master_status = I2C_FAILED;

            /*
             * Set the transaction back to NO_TRANSACTION to allow user to do further
             * transaction
             */
            this_i2c->transaction = NO_TRANSACTION;
            enable_slave_if_required(this_i2c);
            break;
          
        case ST_RX_DATA_ACK: /* Data byte received, ACK returned */
//  	    //write_hex(STDOUT_FILENO, status);
            /* First, get the data */
            this_i2c->master_rx_buffer[this_i2c->master_rx_idx++] = HAL_get_8bit_reg(this_i2c->base_address, DATA);
            if( this_i2c->master_rx_idx >= (this_i2c->master_rx_size - 1u))
            {
                /* If we're at the second last byte, let's set AA to 0 so
                 * we return a NACK at the last byte. */
                HAL_set_8bit_reg_field(this_i2c->base_address, AA, 0x00u);
            }
            break;
            
        case ST_RX_DATA_NACK: /* Data byte received, NACK returned */
//  	    //write_hex(STDOUT_FILENO, status);
            /* Get the data, then send a stop condition */
            this_i2c->master_rx_buffer[this_i2c->master_rx_idx] = HAL_get_8bit_reg(this_i2c->base_address, DATA);
          
            hold_bus = this_i2c->options & I2C_HOLD_BUS; 

            /* Store the information of current I2C bus status in the bus_status*/
            this_i2c->bus_status  = hold_bus;
            if ( hold_bus == 0u )
            { 
                HAL_set_8bit_reg_field(this_i2c->base_address, STO, 0x01u);  /*xmt stop condition */

                /* Bus is released, now we can start listening to bus, if it is slave */
                   enable_slave_if_required(this_i2c);
            }
            else
            {
                I2C_disable_irq( this_i2c );
                clear_irq = 0u;
            }
            /*
             * Set the transaction back to NO_TRANSACTION to allow user to do further
             * transaction
             */
            this_i2c->transaction = NO_TRANSACTION;
            this_i2c->master_status = I2C_SUCCESS;
            break;
        
        /******************** SLAVE RECEIVER **************************/
        case ST_GCA_NACK: /* NACK after, GCA addressing */
        case ST_SLA_NACK: /* Re-enable AA (assert ack) bit for future transmissions */
  	    //write_hex(STDOUT_FILENO, status);
            HAL_set_8bit_reg_field(this_i2c->base_address, AA, 0x01u);

            this_i2c->transaction = NO_TRANSACTION;
            this_i2c->slave_status = I2C_SUCCESS;
            
            /* Check if transaction was pending. If yes, set the START bit */
            if(this_i2c->is_transaction_pending)
            {
                HAL_set_8bit_reg_field(this_i2c->base_address, STA, 0x01u);
            }
            break;
            
        case ST_GCA_LA: /* Arbitr. lost (GCA rec'd) */
        case ST_SLV_LA: /* Arbitr. lost (SLA rec'd) */
  	    //write_hex(STDOUT_FILENO, status);
            /*
             *  We lost arbitration and either the GCE or our address was the
             *  one received so pend the master operation we were starting.
             */
            this_i2c->is_transaction_pending = 1u;
            /* Fall through to normal ST processing as we are now in slave mode */

        case ST_GCA: /* General call address received, ACK returned */
        case ST_SLAVE_SLAW: /* SLA+W received, ACK returned */
  	    //write_hex(STDOUT_FILENO, status);
            this_i2c->transaction = WRITE_SLAVE_TRANSACTION;
            this_i2c->slave_rx_idx = 0u;
            this_i2c->random_read_addr = 0u;
            /*
             * If Start Bit is set clear it, but store that information since it is because of
             * pending transaction
             */
            if(HAL_get_8bit_reg_field(this_i2c->base_address, STA))
            {
                HAL_set_8bit_reg_field(this_i2c->base_address, STA, 0x00u);
                this_i2c->is_transaction_pending = 1u;
            }
            this_i2c->slave_status = I2C_IN_PROGRESS;
#ifdef INCLUDE_SLA_IN_RX_PAYLOAD
            /* Fall through to put address as first byte in payload buffer */
#else
            /* Only break from this case if the slave address must NOT be included at the
             * beginning of the received write data. */
            break;
#endif            
        case ST_GCA_ACK: /* DATA received; ACK sent after GCA */
        case ST_RDATA: /* DATA received; must clear DATA register */
  	    //write_hex(STDOUT_FILENO, status);
            if((this_i2c->slave_rx_buffer != (uint8_t *)0)
               && (this_i2c->slave_rx_idx < this_i2c->slave_rx_size))
            {
                data = HAL_get_8bit_reg(this_i2c->base_address, DATA);
                this_i2c->slave_rx_buffer[this_i2c->slave_rx_idx++] = data;
                
#ifdef INCLUDE_SLA_IN_RX_PAYLOAD
                if((ST_RDATA == status) || (ST_GCA_ACK == status))
                {
                    /* Ignore the slave address byte in the random read address
                       computation in the case where INCLUDE_SLA_IN_RX_PAYLOAD
                       is defined. */
#endif
                    this_i2c->random_read_addr = (this_i2c->random_read_addr << 8) + data;
#ifdef INCLUDE_SLA_IN_RX_PAYLOAD
                }
#endif
            }
            
            if(this_i2c->slave_rx_idx >= this_i2c->slave_rx_size)
            {
                /* Rx buffer is full. NACK next received byte. */
                HAL_set_8bit_reg_field(this_i2c->base_address, AA, 0x00u); 
            }
            break;
            
        case ST_RSTOP:
  	    //write_hex(STDOUT_FILENO, status);
            /* STOP or repeated START occurred. */
            /* We cannot be sure if the transaction has actually completed as
             * this hardware state reports that either a STOP or repeated START
             * condition has occurred. We assume that this is a repeated START
             * if the transaction was a write from the master to this point.*/
            if ( this_i2c->transaction == WRITE_SLAVE_TRANSACTION )
            {
                if ( this_i2c->slave_rx_idx == this_i2c->slave_mem_offset_length )
                {
                    this_i2c->slave_tx_idx = this_i2c->random_read_addr;
                }
                /* Call the slave's write transaction handler if it exists. */
                if ( this_i2c->slave_write_handler != 0u )
                {
                    i2c_slave_handler_ret_t h_ret;
                    h_ret = this_i2c->slave_write_handler( this_i2c, this_i2c->slave_rx_buffer, (uint16_t)this_i2c->slave_rx_idx );
                    if ( I2C_REENABLE_SLAVE_RX == h_ret )
                    {
                        /* There is a small risk that the write handler could
                         * call I2C_disable_slave() but return
                         * I2C_REENABLE_SLAVE_RX in error so we only enable
                         * ACKs if still in slave mode. */
                         enable_slave_if_required(this_i2c);
                    }
                    else
                    {
                        HAL_set_8bit_reg_field( this_i2c->base_address, AA, 0x0u );
                        /* Clear slave mode flag as well otherwise in mixed
                         * master/slave applications, the AA bit will get set by
                         * subsequent master operations. */
                        this_i2c->is_slave_enabled = 0u;
                    }
                }
                else
                {
                    /* Re-enable address acknowledge in case we were ready to nack the next received byte. */
                    HAL_set_8bit_reg_field( this_i2c->base_address, AA, 0x01u );
                }
            }
            else /* A stop or repeated start outside a write/read operation */
            {
                /*
                 * Reset slave_tx_idx so that a subsequent read will result in the slave's
                 * transmit buffer being sent from the first byte.
                 */
                this_i2c->slave_tx_idx = 0u;
                /*
                 * See if we need to re-enable acknowledgement as some error conditions, such
                 * as a master prematurely ending a transfer, can see us get here with AA set
                 * to 0 which will disable slave operation if we are not careful.
                 */
                enable_slave_if_required(this_i2c);
            }

            /* Mark any previous master write transaction as complete. */
            this_i2c->slave_status = I2C_SUCCESS;
            
            /* Check if transaction was pending. If yes, set the START bit */
            if(this_i2c->is_transaction_pending)
            {
                HAL_set_8bit_reg_field(this_i2c->base_address, STA, 0x01u);
            }

            /*
             * Set the transaction back to NO_TRANSACTION to allow user to do further
             * transaction
             */
            this_i2c->transaction = NO_TRANSACTION;

            break;
            
        case ST_SLV_RST: /* SMBUS ONLY: timeout state. must clear interrupt */
  	    //write_hex(STDOUT_FILENO, status);
            /*
             * Set the transaction back to NO_TRANSACTION to allow user to do further
             * transaction.
             */
            this_i2c->transaction = NO_TRANSACTION;
            /*
             * Reset slave_tx_idx so that a subsequent read will result in the slave's
             * transmit buffer being sent from the first byte.
             */
            this_i2c->slave_tx_idx = 0u;
            /*
             * Clear status to I2C_FAILED only if there was an operation in progress.
             */
            if(I2C_IN_PROGRESS == this_i2c->slave_status)
            {
                this_i2c->slave_status = I2C_FAILED;
            }

            enable_slave_if_required(this_i2c); /* Make sure AA is set correctly */

            break;
            
        /****************** SLAVE TRANSMITTER **************************/
        case ST_SLAVE_SLAR_ACK: /* SLA+R received, ACK returned */
        case ST_SLARW_LA:       /* Arbitration lost, and: */
        case ST_RACK:           /* Data tx'ed, ACK received */
  	    //write_hex(STDOUT_FILENO, status);
            if ( status == ST_SLAVE_SLAR_ACK )
            {
                this_i2c->transaction = READ_SLAVE_TRANSACTION;
                this_i2c->random_read_addr = 0u;
                this_i2c->slave_status = I2C_IN_PROGRESS;
                /* If Start Bit is set clear it, but store that information since it is because of
                 * pending transaction
                 */
                if(HAL_get_8bit_reg_field(this_i2c->base_address, STA))
                {
                    HAL_set_8bit_reg_field(this_i2c->base_address, STA, 0x00u);
                    this_i2c->is_transaction_pending = 1u;
                 }
            }
            if (this_i2c->slave_tx_idx >= this_i2c->slave_tx_size)
            {
                /* Ensure 0xFF is returned to the master when the slave specifies
                 * an empty transmit buffer. */
                HAL_set_8bit_reg(this_i2c->base_address, DATA, 0xFFu);
            }
            else
            {
                /* Load the data the data byte to be sent to the master. */
                HAL_set_8bit_reg(this_i2c->base_address, DATA, (uint_fast8_t)this_i2c->slave_tx_buffer[this_i2c->slave_tx_idx++]);
            }
            /* Determine if this is the last data byte to send to the master. */
            if (this_i2c->slave_tx_idx >= this_i2c->slave_tx_size) /* last byte? */
            {
                 HAL_set_8bit_reg_field(this_i2c->base_address, AA, 0x00u); 
                /* Next read transaction will result in slave's transmit buffer
                 * being sent from the first byte. */
                this_i2c->slave_tx_idx = 0u;
            }
            break;
        
        case ST_SLAVE_RNACK:    /* Data byte has been transmitted; not-ACK has been received. */
        case ST_FINAL: /* Last Data byte tx'ed, ACK received */
  	    //write_hex(STDOUT_FILENO, status);
            /* We assume that the transaction will be stopped by the master.
             * Reset slave_tx_idx so that a subsequent read will result in the slave's
             * transmit buffer being sent from the first byte. */
            this_i2c->slave_tx_idx = 0u;
            HAL_set_8bit_reg_field(this_i2c->base_address, AA, 0x01u); 

            /*  Mark previous state as complete */
            this_i2c->slave_status = I2C_SUCCESS;
            /* Check if transaction was pending. If yes, set the START bit */
            if(this_i2c->is_transaction_pending)
            {
                HAL_set_8bit_reg_field(this_i2c->base_address, STA, 0x01u);
            }
            /*
             * Set the transaction back to NO_TRANSACTION to allow user to do further
             * transaction
             */
            this_i2c->transaction = NO_TRANSACTION;

            break;

        /* Master Reset has been activated Wait 35 ms for interrupt to be set,
         * clear interrupt and proceed to 0xF8 state. */
        case ST_RESET_ACTIVATED:
        case ST_BUS_ERROR: /* Bus error during MST or selected slave modes */
        default:
  	    //write_hex(STDOUT_FILENO, status);
            /* Some undefined state has encountered. Clear Start bit to make
             * sure, next good transaction happen */
            HAL_set_8bit_reg_field(this_i2c->base_address, STA, 0x00u);
            /*
             * Set the transaction back to NO_TRANSACTION to allow user to do further
             * transaction.
             */
            this_i2c->transaction = NO_TRANSACTION;
            /*
             * Reset slave_tx_idx so that a subsequent read will result in the slave's
             * transmit buffer being sent from the first byte.
             */
            this_i2c->slave_tx_idx = 0u;
            /*
             * Clear statuses to I2C_FAILED only if there was an operation in progress.
             */
            if(I2C_IN_PROGRESS == this_i2c->master_status)
            {
                this_i2c->master_status = I2C_FAILED;
            }

            if(I2C_IN_PROGRESS == this_i2c->slave_status)
            {
                this_i2c->slave_status = I2C_FAILED;
            }

            break;
    }
    
    if ( clear_irq )
    {
        /* clear interrupt. */
        HAL_set_8bit_reg_field(this_i2c->base_address, SI, 0x00u);
    }
    
    /* Read the status register to ensure the last I2C registers write took place
     * in a system built around a bus making use of posted writes. */
//    status = HAL_get_8bit_reg( this_i2c->base_address, STATUS);
}

/*------------------------------------------------------------------------------
 * I2C_smbus_init()
 * See "i2c.h" for details of how to use this function.
 */
 
/*
 * SMBSUS_NO    = 1
 * SMBALERT_NO  = 1
 * SMBus enable = 1
 */
#define INIT_AND_ENABLE_SMBUS   0x54u
void I2C_smbus_init
(
    i2c_instance_t * this_i2c
)
{
    /*
     * Single byte register write, should be interrupt safe
     */
    /* Enable SMBUS */
    HAL_set_8bit_reg(this_i2c->base_address, SMBUS, INIT_AND_ENABLE_SMBUS);
}

/*------------------------------------------------------------------------------
 * I2C_enable_smbus_irq()
 * See "i2c.h" for details of how to use this function.
 */
void I2C_enable_smbus_irq
(
    i2c_instance_t * this_i2c,
    uint8_t  irq_type
)
{
    psr_t saved_psr;

    /*
     * We need to disable interrupts here to ensure we can update the
     * hardware register without the SMBUS IRQs interrupting us.
     */

   	saved_psr=HAL_disable_interrupts();

    if ( irq_type & I2C_SMBALERT_IRQ)
    {
        HAL_set_8bit_reg_field(this_i2c->base_address, SMBALERT_IE, 0x01u);
    }
    if ( irq_type & I2C_SMBSUS_IRQ)
    {
        HAL_set_8bit_reg_field(this_i2c->base_address, SMBSUS_IE, 0x01u);
    }
    

   	HAL_restore_interrupts( saved_psr );
}

/*------------------------------------------------------------------------------
 * I2C_disable_smbus_irq()
 * See "i2c.h" for details of how to use this function.
 */
void I2C_disable_smbus_irq
(
    i2c_instance_t * this_i2c,
    uint8_t  irq_type
)
{
    psr_t saved_psr;

    /*
     * We need to disable interrupts here to ensure we can update the
     * hardware register without the SMBUS IRQs interrupting us.
     */

   	saved_psr=HAL_disable_interrupts();

    if ( irq_type & I2C_SMBALERT_IRQ)
    {
        HAL_set_8bit_reg_field(this_i2c->base_address, SMBALERT_IE, 0x00u);
    }
    if (irq_type & I2C_SMBSUS_IRQ )
    {
        HAL_set_8bit_reg_field(this_i2c->base_address, SMBSUS_IE, 0x00u);
    }
    

   	HAL_restore_interrupts( saved_psr );
}

/*------------------------------------------------------------------------------
 * I2C_suspend_smbus_slave()
 * See "i2c.h" for details of how to use this function.
 */
void I2C_suspend_smbus_slave
(
    i2c_instance_t * this_i2c
)
{
    psr_t saved_psr;

    /*
     * We need to disable interrupts here to ensure we can update the
     * hardware register without the SMBUS IRQs interrupting us.
     */

   	saved_psr=HAL_disable_interrupts();

    HAL_set_8bit_reg_field(this_i2c->base_address, SMBSUS_NO_CONTROL, 0x00u);


   	HAL_restore_interrupts( saved_psr );
}

/*------------------------------------------------------------------------------
 * I2C_resume_smbus_slave()
 * See "i2c.h" for details of how to use this function.
 */
void I2C_resume_smbus_slave
(
    i2c_instance_t * this_i2c
)
{
    psr_t saved_psr;

    /*
     * We need to disable interrupts here to ensure we can update the
     * hardware register without the SMBUS IRQs interrupting us.
     */

   	saved_psr=HAL_disable_interrupts();

    HAL_set_8bit_reg_field(this_i2c->base_address, SMBSUS_NO_CONTROL, 0x01u);


   	HAL_restore_interrupts( saved_psr );
}

/*------------------------------------------------------------------------------
 * I2C_reset_smbus()
 * See "i2c.h" for details of how to use this function.
 */
void I2C_reset_smbus
(
    i2c_instance_t * this_i2c
)
{
    psr_t saved_psr;

    /*
     * We need to disable interrupts here to ensure we can update the
     * hardware register without the SMBUS IRQs interrupting us.
     */

   	saved_psr=HAL_disable_interrupts();
    HAL_set_8bit_reg_field(this_i2c->base_address, SMBUS_MST_RESET, 0x01u);
    

   	HAL_restore_interrupts( saved_psr );
}

/*------------------------------------------------------------------------------
 * I2C_set_smbus_alert()
 * See "i2c.h" for details of how to use this function.
 */
void I2C_set_smbus_alert
(
    i2c_instance_t * this_i2c
)
{
    psr_t saved_psr;

    /*
     * We need to disable interrupts here to ensure we can update the
     * hardware register without the SMBUS IRQs interrupting us.
     */

   	saved_psr=HAL_disable_interrupts();
    HAL_set_8bit_reg_field(this_i2c->base_address, SMBALERT_NO_CONTROL, 0x00u);


   	HAL_restore_interrupts( saved_psr );
}

/*------------------------------------------------------------------------------
 * I2C_clear_smbus_alert()
 * See "i2c.h" for details of how to use this function.
 */
void I2C_clear_smbus_alert
(
    i2c_instance_t * this_i2c
)
{
    psr_t saved_psr;

    /*
     * We need to disable interrupts here to ensure we can update the
     * hardware register without the SMBUS IRQs interrupting us.
     */

   	saved_psr=HAL_disable_interrupts();

    HAL_set_8bit_reg_field(this_i2c->base_address, SMBALERT_NO_CONTROL, 0x01u);


   	HAL_restore_interrupts( saved_psr );
}

/*------------------------------------------------------------------------------
 * I2C_get_irq_status()
 * See "i2c.h" for details of how to use this function.
 */
uint8_t I2C_get_irq_status
(
    i2c_instance_t * this_i2c
)
{
    uint8_t status ;
    uint8_t irq_type = I2C_NO_IRQ ;

    status = HAL_get_8bit_reg(this_i2c->base_address, SMBUS);

    if( status & (uint8_t)SMBALERT_NI_STATUS_MASK )
    {
        irq_type |= I2C_SMBALERT_IRQ ;
    }

    if( status & (uint8_t)SMBSUS_NI_STATUS_MASK )
    {
        irq_type |= I2C_SMBSUS_IRQ ;
    }

    status = HAL_get_8bit_reg(this_i2c->base_address, CONTROL);

    if( status & (uint8_t)SI_MASK )
    {
        irq_type |= I2C_INTR_IRQ ;
    }
    return(irq_type);
}

/*------------------------------------------------------------------------------
 * I2C_set_slave_addr2()
 * See "i2c.h" for details of how to use this function.
 */
void I2C_set_user_data
(
    i2c_instance_t * this_i2c,
    void * p_user_data
)
{
    this_i2c->p_user_data = p_user_data ;
}

/*------------------------------------------------------------------------------
 * I2C_get_user_data()
 * See "i2c.h" for details of how to use this function.
 */
void * I2C_get_user_data
(
    i2c_instance_t * this_i2c
)
{
    return( this_i2c->p_user_data);
}

#ifdef __cplusplus
}
#endif

