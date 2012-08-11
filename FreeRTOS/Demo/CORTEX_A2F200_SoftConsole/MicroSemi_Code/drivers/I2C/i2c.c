/*******************************************************************************
 * (c) Copyright 2007-2008 Actel Corporation.  All rights reserved.
 *
 * SmartFusion microcontroller subsystem I2C bare metal software driver
 * implementation.
 *
 * SVN $Revision: 2152 $
 * SVN $Date: 2010-02-11 14:44:11 +0000 (Thu, 11 Feb 2010) $
 */


#include "i2c.h"
#include "../../CMSIS/mss_assert.h"

#ifdef __cplusplus
extern "C" {
#endif

/*------------------------------------------------------------------------------
 * I2C transaction direction.
 */
#define WRITE_DIR	0
#define READ_DIR	1

/* -- TRANSACTIONS TYPES -- */
#define NO_TRANSACTION						0
#define MASTER_WRITE_TRANSACTION			1
#define MASTER_READ_TRANSACTION				2
#define MASTER_RANDOM_READ_TRANSACTION		3
#define WRITE_SLAVE_TRANSACTION				4
#define READ_SLAVE_TRANSACTION				5
#define RANDOM_READ_SLAVE_TRANSACTION		6


/* -- SMBUS H/W STATES -- */
/* -- MASTER STATES -- */
#define ST_START 		0x08		/* start condition sent */
#define ST_RESTART 		0x10		/* repeated start */
#define ST_SLAW_ACK 	0x18		/* SLA+W sent, ack received */
#define ST_SLAW_NACK 	0x20		/* SLA+W sent, nack received */
#define ST_TX_DATA_ACK 	0x28		/* Data sent, ACK'ed */
#define ST_TX_DATA_NACK	0x30		/* Data sent, NACK'ed */
#define ST_LOST_ARB 	0x38		/* Master lost arbitration */
#define ST_SLAR_ACK 	0x40		/* SLA+R sent, ACK'ed */
#define ST_SLAR_NACK 	0x48		/* SLA+R sent, NACK'ed */
#define ST_RX_DATA_ACK 	0x50		/* Data received, ACK sent */
#define ST_RX_DATA_NACK 0x58		/* Data received, NACK sent */

/* -- SLAVE STATES -- */
#define ST_SLAVE_SLAW       0x60			/* SLA+W received */
#define ST_SLAVE_SLAR_ACK   0xA8			/* SLA+R received, ACK returned */
#define ST_SLV_LA           0x68			/* Slave lost arbitration */
#define ST_GCA              0x70			/* GCA received */
#define	ST_GCA_LA           0x78			/* GCA lost arbitration */
#define ST_RDATA            0x80			/* Data received */
#define ST_SLA_NACK         0x88			/* Slave addressed, NACK returned */
#define	ST_GCA_ACK          0x90			/* Previously addresses with GCA, data ACKed */
#define ST_GCA_NACK         0x98			/* GCA addressed, NACK returned */
#define ST_RSTOP            0xA0			/* Stop received */
#define ST_REPEAT           0xA0			/* Repeated start received */
#define ST_SLAR_ACKS        0xA8			/* Slave read received, ACKed */
#define ST_SLARW_LA         0xB0			/* Arbitration lost */
#define ST_RACK             0xB8			/* Byte sent, ACK received */
#define ST_SLAVE_RNACK      0xC0			/* Byte sent, NACK received */
#define ST_FINAL            0xC8			/* Final byte sent, ACK received */
#define ST_BERR             0x00			/* Error on the bus */
#define ST_SLV_RST          0xD8			/* Slave reset state */

/*------------------------------------------------------------------------------
 *
 */
static uint32_t disable_interrupts( void );
static void restore_interrupts( uint32_t primask );
static void mss_i2c_isr( mss_i2c_instance_t * this_i2c );

/*------------------------------------------------------------------------------
 *
 *------------------------------------------------------------------------------
 *
 */
mss_i2c_instance_t g_mss_i2c0;
mss_i2c_instance_t g_mss_i2c1;

/*------------------------------------------------------------------------------
 * MSS_I2C_init()
 * See "mss_i2c.h" for details of how to use this function.
 */
void MSS_I2C_init
(
	mss_i2c_instance_t * this_i2c,
	uint8_t ser_address,
	mss_i2c_clock_divider_t ser_clock_speed
)
{
    uint_fast16_t clock_speed = ser_clock_speed;

    ASSERT( (this_i2c == &g_mss_i2c0) || (this_i2c == &g_mss_i2c1) );

    if ( this_i2c == &g_mss_i2c0 )
    {
        this_i2c->irqn = I2C0_IRQn;
        this_i2c->hw_reg = I2C0;
        this_i2c->hw_reg_bit = I2C0_BITBAND;

        /* reset I2C0 */
        SYSREG->SOFT_RST_CR |= SYSREG_I2C0_SOFTRESET_MASK;
        /* Clear any previously pended I2C0 interrupt */
        NVIC_ClearPendingIRQ( I2C0_IRQn );
        /* Take I2C0 out of reset. */
        SYSREG->SOFT_RST_CR &= ~SYSREG_I2C0_SOFTRESET_MASK;
    }
    else
    {
        this_i2c->irqn = I2C1_IRQn;
        this_i2c->hw_reg = I2C1;
        this_i2c->hw_reg_bit = I2C1_BITBAND;

        /* reset I2C1 */
        SYSREG->SOFT_RST_CR |= SYSREG_I2C1_SOFTRESET_MASK;
        /* Clear any previously pended I2C1 interrupt */
        NVIC_ClearPendingIRQ( I2C1_IRQn );
        /* Take I2C1 out of reset. */
        SYSREG->SOFT_RST_CR &= ~SYSREG_I2C1_SOFTRESET_MASK;
    }

	this_i2c->transaction = NO_TRANSACTION;

	this_i2c->ser_address = ser_address;

	this_i2c->tx_buffer = 0;
	this_i2c->tx_size = 0;
	this_i2c->tx_idx = 0;

	this_i2c->rx_buffer = 0;
	this_i2c->rx_size = 0;
	this_i2c->rx_idx = 0;

    this_i2c->status = MSS_I2C_SUCCESS;

	this_i2c->random_read_addr = 0;

	this_i2c->slave_write_handler = 0;
	this_i2c->slave_mem_offset_length = 0;

    this_i2c->hw_reg_bit->CTRL_ENS1 = 0x01; /* set enable bit */
    this_i2c->hw_reg_bit->CTRL_CR2 = (clock_speed >> 2) & 0x01;
    this_i2c->hw_reg_bit->CTRL_CR1 = (clock_speed >> 1) & 0x01;
    this_i2c->hw_reg_bit->CTRL_CR0 = clock_speed & 0x01;
    this_i2c->hw_reg->ADDR = this_i2c->ser_address;
	
	/* The interrupt can cause a context switch, so ensure its priority is
	between configKERNEL_INTERRUPT_PRIORITY and configMAX_SYSCALL_INTERRUPT_PRIORITY. */
	NVIC_SetPriority( this_i2c->irqn, configLIBRARY_MAX_SYSCALL_INTERRUPT_PRIORITY );
	
	vSemaphoreCreateBinary( ( this_i2c->xI2CCompleteSemaphore ) );
	xSemaphoreTake( ( this_i2c->xI2CCompleteSemaphore ), 0 );
	configASSERT( ( this_i2c->xI2CCompleteSemaphore ) );
}

/*------------------------------------------------------------------------------
 * MSS_I2C_set_slave_mem_offset_length()
 * See "mss_i2c.h" for details of how to use this function.
 */
void MSS_I2C_set_slave_mem_offset_length
(
	mss_i2c_instance_t * this_i2c,
	uint8_t offset_length
)
{
    ASSERT( (this_i2c == &g_mss_i2c0) || (this_i2c == &g_mss_i2c1) );

	this_i2c->slave_mem_offset_length = offset_length;
}

/*------------------------------------------------------------------------------
 * MSS_I2C_register_write_handler()
 * See "mss_i2c.h" for details of how to use this function.
 */
void MSS_I2C_register_write_handler
(
	mss_i2c_instance_t * this_i2c,
	mss_i2c_slave_wr_handler_t handler
)
{
    ASSERT( (this_i2c == &g_mss_i2c0) || (this_i2c == &g_mss_i2c1) );

	this_i2c->slave_write_handler = handler;
}

/*------------------------------------------------------------------------------
 * MSS_I2C_write()
 * See "mss_i2c.h" for details of how to use this function.
 */
void MSS_I2C_write
(
	mss_i2c_instance_t * this_i2c,
	uint8_t serial_addr,
	const uint8_t * write_buffer,
	uint16_t write_size,
    uint8_t options
)
{
    volatile uint8_t stat_ctrl;
    uint8_t serial_interrupt;

	uint32_t primask;

    ASSERT( (this_i2c == &g_mss_i2c0) || (this_i2c == &g_mss_i2c1) );
	configASSERT( ( this_i2c->xI2CCompleteSemaphore ) );

	primask = disable_interrupts();

	this_i2c->transaction = MASTER_WRITE_TRANSACTION;

	this_i2c->target_addr = serial_addr;
	this_i2c->dir = WRITE_DIR;
	this_i2c->tx_buffer = write_buffer;
	this_i2c->tx_size = write_size;
	this_i2c->tx_idx = 0;

    this_i2c->status = MSS_I2C_IN_PROGRESS;
    this_i2c->options = options;

    /* Clear interrupts if required (depends on repeated starts).*/
    serial_interrupt = this_i2c->hw_reg_bit->CTRL_SI;
    this_i2c->hw_reg_bit->CTRL_STA = 0x01;

    if ( serial_interrupt != 0 )
    {
        this_i2c->hw_reg_bit->CTRL_SI = 0x00;
        NVIC_ClearPendingIRQ( this_i2c->irqn );
    }

    stat_ctrl = this_i2c->hw_reg->STATUS;

    NVIC_EnableIRQ( this_i2c->irqn );

    restore_interrupts( primask );
}

/*------------------------------------------------------------------------------
 * MSS_I2C_read()
 * See "mss_i2c.h" for details of how to use this function.
 */
void MSS_I2C_read
(
	mss_i2c_instance_t * this_i2c,
	uint8_t serial_addr,
	uint8_t * read_buffer,
	uint16_t read_size,
    uint8_t options
)
{
	uint32_t primask;

    ASSERT( (this_i2c == &g_mss_i2c0) || (this_i2c == &g_mss_i2c1) );

	if ( read_size > 0 )
	{
        volatile uint8_t stat_ctrl;
        uint8_t serial_interrupt;

		primask = disable_interrupts();

		this_i2c->transaction = MASTER_READ_TRANSACTION;

		this_i2c->target_addr = serial_addr;
		this_i2c->dir = READ_DIR;
		this_i2c->rx_buffer = read_buffer;
		this_i2c->rx_size = read_size;
		this_i2c->rx_idx = 0;

        this_i2c->status = MSS_I2C_IN_PROGRESS;

        this_i2c->options = options;

        /* Clear interrupts if required (depends on repeated starts).*/
        serial_interrupt = this_i2c->hw_reg_bit->CTRL_SI;
        this_i2c->hw_reg_bit->CTRL_STA = 0x01;

        if ( serial_interrupt != 0 )
        {
            this_i2c->hw_reg_bit->CTRL_SI = 0x00;
            NVIC_ClearPendingIRQ( this_i2c->irqn );
        }

        stat_ctrl = this_i2c->hw_reg->STATUS;

        NVIC_EnableIRQ( this_i2c->irqn );

        restore_interrupts( primask );
	}
}

/*------------------------------------------------------------------------------
 * MSS_I2C_write_read()
 * See "mss_i2c.h" for details of how to use this function.
 */
void MSS_I2C_write_read
(
	mss_i2c_instance_t * this_i2c,
	uint8_t serial_addr,
	const uint8_t * addr_offset,
	uint16_t offset_size,
	uint8_t * read_buffer,
	uint16_t read_size,
    uint8_t options
)
{
    volatile uint8_t stat_ctrl;
    uint8_t serial_interrupt;
	uint32_t primask;

    ASSERT( (this_i2c == &g_mss_i2c0) || (this_i2c == &g_mss_i2c1) );

	primask = disable_interrupts();

	this_i2c->transaction = MASTER_RANDOM_READ_TRANSACTION;
	this_i2c->target_addr = serial_addr;
	this_i2c->dir = WRITE_DIR;
	this_i2c->tx_buffer = addr_offset;
	this_i2c->tx_size = offset_size;
	this_i2c->tx_idx = 0;

	this_i2c->rx_buffer = read_buffer;
	this_i2c->rx_size = read_size;
	this_i2c->rx_idx = 0;

    this_i2c->status = MSS_I2C_IN_PROGRESS;
    this_i2c->options = options;

    /* Clear interrupts if required (depends on repeated starts).*/
    serial_interrupt = this_i2c->hw_reg_bit->CTRL_SI;
    this_i2c->hw_reg_bit->CTRL_STA = 0x01;

    if ( serial_interrupt != 0 )
    {
        this_i2c->hw_reg_bit->CTRL_SI = 0x00;
        NVIC_ClearPendingIRQ( this_i2c->irqn );
    }

    stat_ctrl = this_i2c->hw_reg->STATUS;

    NVIC_EnableIRQ( this_i2c->irqn );

    restore_interrupts( primask );
}

/*------------------------------------------------------------------------------
 * MSS_I2C_set_slave_rx_buffer()
 * See "mss_i2c.h" for details of how to use this function.
 */
void MSS_I2C_set_slave_rx_buffer
(
	mss_i2c_instance_t * this_i2c,
	uint8_t * rx_buffer,
	uint16_t rx_size
)
{
	uint32_t primask;

    ASSERT( (this_i2c == &g_mss_i2c0) || (this_i2c == &g_mss_i2c1) );

	primask = disable_interrupts();

	this_i2c->rx_buffer = rx_buffer;
	this_i2c->rx_size = rx_size;
	this_i2c->rx_idx = 0;

	restore_interrupts( primask );
}


/*------------------------------------------------------------------------------
 * MSS_I2C_get_status()
 * See "mss_i2c.h" for details of how to use this function.
 */
mss_i2c_status_t MSS_I2C_get_status
(
    mss_i2c_instance_t * this_i2c
)
{
    ASSERT( (this_i2c == &g_mss_i2c0) || (this_i2c == &g_mss_i2c1) );

    return this_i2c->status;
}

/*------------------------------------------------------------------------------
 * MSS_I2C_set_slave_tx_buffer()
 * See "mss_i2c.h" for details of how to use this function.
 */
void MSS_I2C_set_slave_tx_buffer
(
	mss_i2c_instance_t * this_i2c,
	uint8_t * tx_buffer,
	uint16_t tx_size
)
{
	uint32_t primask;

    ASSERT( (this_i2c == &g_mss_i2c0) || (this_i2c == &g_mss_i2c1) );

	primask = disable_interrupts();

	this_i2c->tx_buffer = tx_buffer;
	this_i2c->tx_size = tx_size;
	this_i2c->tx_idx = 0;

	restore_interrupts( primask );

	/* Set the assert acknowledge bit. */
    this_i2c->hw_reg_bit->CTRL_AA = 0x01;
}

/*------------------------------------------------------------------------------
 * MSS_I2C_enable_slave_rx()
 * See "mss_i2c.h" for details of how to use this function.
 */
void MSS_I2C_enable_slave_rx
(
	mss_i2c_instance_t * this_i2c
)
{
    ASSERT( (this_i2c == &g_mss_i2c0) || (this_i2c == &g_mss_i2c1) );

	/* Set the assert acknowledge bit. */
    this_i2c->hw_reg_bit->CTRL_AA = 0x01;
	/* accept GC addressing. */
    this_i2c->hw_reg_bit->ADDR_GC = 0x01;

    NVIC_EnableIRQ( this_i2c->irqn );
}

/*------------------------------------------------------------------------------
 * MSS_I2C_wait_complete()
 * See "mss_i2c.h" for details of how to use this function.
 */
mss_i2c_status_t MSS_I2C_wait_complete
(
    mss_i2c_instance_t * this_i2c
)
{
    ASSERT( (this_i2c == &g_mss_i2c0) || (this_i2c == &g_mss_i2c1) );

#ifdef USE_OLD_I2C_POLLING_CODE
    while ( this_i2c->status == MSS_I2C_IN_PROGRESS )
    {
        /* Wait for transaction to compltete.*/
        ;
    }
#else
	configASSERT( ( this_i2c->xI2CCompleteSemaphore ) );
	if( xTaskGetSchedulerState() == taskSCHEDULER_NOT_STARTED )
	{
		while ( this_i2c->status == MSS_I2C_IN_PROGRESS )
		{
			/* Wait for transaction to compltete.*/
			;
		}
	}
	else
	{
		xSemaphoreTake( this_i2c->xI2CCompleteSemaphore, portMAX_DELAY );
	}
#endif

    return this_i2c->status;
}

/*------------------------------------------------------------------------------
 * MSS I2C interrupt service routine.
 *------------------------------------------------------------------------------
 * Parameters:
 *
 * 	mss_i2c_instance_t * this_i2c:
 * 		Pointer to the mss_i2c_instance_t data structure holding all data related to
 * 		the	MSS I2C instance that generated the interrupt.
 */
static void mss_i2c_isr
(
	mss_i2c_instance_t * this_i2c
		)
{
	volatile uint8_t status;
	uint8_t data;
    uint8_t hold_bus;
    uint8_t clear_irq = 1;
	long lHigherPriorityTaskWoken = pdFALSE;
	configASSERT( ( this_i2c->xI2CCompleteSemaphore ) );

    ASSERT( (this_i2c == &g_mss_i2c0) || (this_i2c == &g_mss_i2c1) );

    status = this_i2c->hw_reg->STATUS;

	switch( status )
	{
	    /************** MASTER TRANSMITTER / RECEIVER *******************/

	    case ST_START: /* start has been xmt'd */
	    case ST_RESTART: /* repeated start has been xmt'd */
            this_i2c->hw_reg_bit->CTRL_STA = 0x0;
            this_i2c->hw_reg->DATA = this_i2c->target_addr;
            this_i2c->hw_reg_bit->DATA_DIR = this_i2c->dir;

	    	this_i2c->tx_idx = 0;
	    	this_i2c->rx_idx = 0;
	    	break;

	    case ST_LOST_ARB:
			/* Set start bit.  Let's keep trying!  Don't give up! */
            this_i2c->hw_reg_bit->CTRL_STA = 0x01;
			break;

	    /******************* MASTER TRANSMITTER *************************/
	    case ST_SLAW_ACK:
	    	/* call address has been xmt'd with ACK, time to send data byte and increment index. */
            if ( this_i2c->tx_idx < this_i2c->tx_size )
            {
                /* load data byte */
                this_i2c->hw_reg->DATA = this_i2c->tx_buffer[this_i2c->tx_idx++];
            }
            else
            {
                NVIC_DisableIRQ( this_i2c->irqn );
            }
	    	break;

	    case ST_SLAW_NACK:
#if 0
	    	/* SLA+W has been transmitted; not ACK has been received - let's stop. */
            this_i2c->hw_reg_bit->CTRL_STO = 0x01;
            this_i2c->status = MSS_I2C_FAILED;
#endif
	    	/* call address has been xmt'd with ACK, time to send data byte and increment index. */
            if ( this_i2c->tx_idx < this_i2c->tx_size )
            {
                /* load data byte */
                this_i2c->hw_reg->DATA = this_i2c->tx_buffer[this_i2c->tx_idx++];
            }
            else
            {
                NVIC_DisableIRQ( this_i2c->irqn );
            }
			break;

	    case ST_TX_DATA_ACK:
			/* data byte has been xmt'd with ACK, time to send stop bit or repeated start. */
			if (this_i2c->tx_idx < this_i2c->tx_size)
			{
                this_i2c->hw_reg->DATA = this_i2c->tx_buffer[this_i2c->tx_idx++];
			}
			else if ( this_i2c->transaction == MASTER_RANDOM_READ_TRANSACTION )
			{
				/* We are finished sending the address offset part of a random read transaction.
				 * It is is time to send a restart in order to change direction. */
				 this_i2c->dir = READ_DIR;
                 this_i2c->hw_reg_bit->CTRL_STA = 0x01;
			}
			else /* done sending. let's stop */
			{
                hold_bus = this_i2c->options & MSS_I2C_HOLD_BUS;
                if ( hold_bus == 0 )
                {
                    this_i2c->hw_reg_bit->CTRL_STO = 0x01; /*xmt stop condition */
                }
                else
                {
                    NVIC_DisableIRQ( this_i2c->irqn );
                    clear_irq = 0;
                }
                this_i2c->status = MSS_I2C_SUCCESS;
				xSemaphoreGiveFromISR( this_i2c->xI2CCompleteSemaphore, &lHigherPriorityTaskWoken );
			}
			break;

		  case ST_TX_DATA_NACK:
#if 0
			 /* data byte SENT, ACK to be received
		     * In fact, this means we've received a NACK (This may not be
             * obvious, but if we've rec'd an ACK then we would be in state
             * 0x28!) hence, let's send a stop bit
             */
            this_i2c->hw_reg_bit->CTRL_STO = 0x01;
            this_i2c->status = MSS_I2C_FAILED;
#endif
			/* data byte has been xmt'd with ACK, time to send stop bit or repeated start. */
			if (this_i2c->tx_idx < this_i2c->tx_size)
			{
                this_i2c->hw_reg->DATA = this_i2c->tx_buffer[this_i2c->tx_idx++];
			}
			else if ( this_i2c->transaction == MASTER_RANDOM_READ_TRANSACTION )
			{
				/* We are finished sending the address offset part of a random read transaction.
				 * It is is time to send a restart in order to change direction. */
				 this_i2c->dir = READ_DIR;
                 this_i2c->hw_reg_bit->CTRL_STA = 0x01;
			}
			else /* done sending. let's stop */
			{
                hold_bus = this_i2c->options & MSS_I2C_HOLD_BUS;
                if ( hold_bus == 0 )
                {
                    this_i2c->hw_reg_bit->CTRL_STO = 0x01; /*xmt stop condition */
                }
                else
                {
                    NVIC_DisableIRQ( this_i2c->irqn );
                    clear_irq = 0;
                }
                this_i2c->status = MSS_I2C_SUCCESS;
				xSemaphoreGiveFromISR( this_i2c->xI2CCompleteSemaphore, &lHigherPriorityTaskWoken );
			}
            break;

	  /********************* MASTER (or slave?) RECEIVER *************************/

	  /* STATUS codes 08H, 10H, 38H are all covered in MTX mode */
		case ST_SLAR_ACK: /* SLA+R tx'ed. */
			/* Let's make sure we ACK the first data byte received (set AA bit in CTRL) unless
			 * the next byte is the last byte of the read transaction.
             */
			if( this_i2c->rx_size > 1 )
			{
                this_i2c->hw_reg_bit->CTRL_AA = 0x01;
			}
			else
			{
                this_i2c->hw_reg_bit->CTRL_AA = 0x00;
			}
			break;

		case ST_SLAR_NACK: /* SLA+R tx'ed; let's release the bus (send a stop condition) */
            this_i2c->hw_reg_bit->CTRL_STO = 0x01;
            this_i2c->status = MSS_I2C_FAILED;
			xSemaphoreGiveFromISR( this_i2c->xI2CCompleteSemaphore, &lHigherPriorityTaskWoken );
			break;

		case ST_RX_DATA_ACK: /* Data byte received, ACK returned */
			/* First, get the data */
            this_i2c->rx_buffer[this_i2c->rx_idx++] = this_i2c->hw_reg->DATA;

			if( this_i2c->rx_idx >= this_i2c->rx_size - 1)
			{
				/* If we're at the second last byte, let's set AA to 0 so
				 * we return a NACK at the last byte. */
                this_i2c->hw_reg_bit->CTRL_AA = 0x00;
			}
			break;

	    case ST_RX_DATA_NACK: /* Data byte received, NACK returned */
            /* Get the data, then send a stop condition */
            this_i2c->rx_buffer[this_i2c->rx_idx++] = this_i2c->hw_reg->DATA;

            hold_bus = this_i2c->options &  MSS_I2C_HOLD_BUS;
            if ( hold_bus == 0 )
            {
                this_i2c->hw_reg_bit->CTRL_STO = 0x01;  /*xmt stop condition */
            }
            else
            {
                NVIC_DisableIRQ( this_i2c->irqn );
                clear_irq = 0;
            }

            this_i2c->status = MSS_I2C_SUCCESS;
//			xSemaphoreGiveFromISR( this_i2c->xI2CCompleteSemaphore, &lHigherPriorityTaskWoken );
            break;

		/******************** SLAVE RECEIVER **************************/
		case ST_GCA_NACK: /* NACK after, GCA addressing */
		case ST_SLA_NACK: /* Get Data, but also re-enable AA (assert ack) bit for future transmissions */
			if ( this_i2c->rx_buffer != 0 )
			{
                this_i2c->rx_buffer[this_i2c->rx_idx] = this_i2c->hw_reg->DATA;
			}
            this_i2c->hw_reg_bit->CTRL_AA = 0x01;
			break;

		case ST_SLAVE_SLAW: /* SLA+W received, ACK returned */
			this_i2c->transaction = WRITE_SLAVE_TRANSACTION;
			this_i2c->rx_idx = 0;
			this_i2c->random_read_addr = 0;
#ifndef INCLUDE_SLA_IN_RX_PAYLOAD
			/* Only break from this case if the slave address must NOT be included at the
			 * beginning of the received write data. */
			break;
#endif
		case ST_GCA_ACK: /* DATA received; ACK sent after GCA */
		case ST_RDATA: /* DATA received; must clear DATA register */
			if (this_i2c->rx_idx >= this_i2c->rx_size - 2)
			{
                this_i2c->hw_reg_bit->CTRL_AA = 0x00;   /* send a NACK when done (next reception) */
			}
            data = this_i2c->hw_reg->DATA;
			this_i2c->rx_buffer[this_i2c->rx_idx++] = data;
			this_i2c->random_read_addr = (this_i2c->random_read_addr << 8) + data;

			break;

		case ST_RSTOP:
			/* STOP or repeated START occured. */
			/* We cannot be sure if the transaction has actually completed as
			 * this hardware state reports that either a STOP or repeated START
			 * condition has occured. We assume that this is a repeated START
			 * if the transaction was a write from the master to this point.*/
			if ( this_i2c->transaction == WRITE_SLAVE_TRANSACTION )
			{
				if ( this_i2c->rx_idx == this_i2c->slave_mem_offset_length )
				{
					this_i2c->transaction = RANDOM_READ_SLAVE_TRANSACTION;
					this_i2c->tx_idx = this_i2c->random_read_addr;
				}
				else
				{
					/* Call the slave's write transaction handler if it exists. */
					if ( this_i2c->slave_write_handler != 0 )
					{
						mss_i2c_slave_handler_ret_t h_ret;
						h_ret = this_i2c->slave_write_handler( this_i2c->rx_buffer, (uint16_t)this_i2c->rx_idx );
						if ( MSS_I2C_REENABLE_SLAVE_RX == h_ret )
						{
                            this_i2c->hw_reg_bit->CTRL_AA = 0x01;
						}
						else
						{
                            this_i2c->hw_reg_bit->CTRL_AA = 0x00;
						}
					}
				}
			}
			/* Mark any previous master write transaction as complete. */
            this_i2c->status = MSS_I2C_SUCCESS;
//			xSemaphoreGiveFromISR( this_i2c->xI2CCompleteSemaphore, &lHigherPriorityTaskWoken );
			break;

		case ST_SLV_RST: /* SMBUS ONLY: timeout state. must clear interrupt */
		case ST_SLV_LA: /* Arbitr. lost (SLA rec'd) */
		case ST_GCA: /* General call address received, ACK returned */
		case ST_GCA_LA: /* Arbitr. lost (GCA rec'd) */
			/* do nothing */
			break;

		/****************** SLAVE TRANSMITTER **************************/
		case ST_SLAVE_SLAR_ACK: /* SLA+R received, ACK returned */
		case ST_SLARW_LA: /* Arbitration lost, and: */
		case ST_RACK: /* Data tx'ed, ACK received */
            if ( status == ST_SLAVE_SLAR_ACK )
            {
                this_i2c->transaction = READ_SLAVE_TRANSACTION;
                this_i2c->random_read_addr = 0;
            }
			/* Load the data, and determine if it is the last one */
            this_i2c->hw_reg->DATA = this_i2c->tx_buffer[this_i2c->tx_idx++];
			if (this_i2c->tx_idx >= this_i2c->tx_size - 1) /* last byte? */
			{
                this_i2c->hw_reg_bit->CTRL_AA = 0x00;
				/* Next read transaction will result in slave's transmit buffer
				 * being sent from the first byte. */
				this_i2c->tx_idx = 0;
			}
			break;

		case ST_SLAVE_RNACK:	/* Data byte has been transmitted; not-ACK has been received. */
			/* We assume that the transaction will be stopped by the master.
			 * Reset tx_idx so that a subsequent read will result in the slave's
			 * transmit buffer being sent from the first byte. */
			this_i2c->tx_idx = 0;
			break;

		case ST_FINAL: /* Last Data byte tx'ed, ACK recieved */
		default:
			/* do nothing */
			break;
	}

    if ( clear_irq )
    {
    	/* clear interrupt. */
        this_i2c->hw_reg_bit->CTRL_SI = 0x00;
    }

    /* Read the status register to ensure the last I2C registers write took place
     * in a system built around a bus making use of posted writes. */
    status = this_i2c->hw_reg->STATUS;
	
	portEND_SWITCHING_ISR( lHigherPriorityTaskWoken );
}

/*------------------------------------------------------------------------------
 *
 */
uint32_t disable_interrupts( void )
{
    uint32_t primask;
    primask = __get_PRIMASK();
    return primask;
}

/*------------------------------------------------------------------------------
 *
 */
void restore_interrupts( uint32_t primask )
{
    __set_PRIMASK( primask );
}

/*------------------------------------------------------------------------------
 *
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void I2C0_IRQHandler( void )
#else
void I2C0_IRQHandler( void )
#endif
{
	mss_i2c_isr( &g_mss_i2c0 );
    NVIC_ClearPendingIRQ( I2C0_IRQn );
}

/*------------------------------------------------------------------------------
 *
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void I2C1_IRQHandler( void )
#else
void I2C1_IRQHandler( void )
#endif
{
	mss_i2c_isr( &g_mss_i2c1 );
    NVIC_ClearPendingIRQ( I2C1_IRQn );
}

#ifdef __cplusplus
}
#endif
