/**************************************************************************
 * Project           		: shakti devt board
 * Name of the file	     	: i2c_driver.c
 * Brief Description of file    : Demonstartes the working of i2c protocol.
 * Name of Author               : Kotteeswaran
 * Email id                     : kottee.1@gmail.com

 Copyright (C) 2019  IIT Madras. All rights reserved.

 This program is free software: you can redistribute it and/or modify
 it under the terms of the GNU General Public License as published by
 the Free Software Foundation, either version 3 of the License, or
 (at your option) any later version.

 This program is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with this program.  If not, see <https://www.gnu.org/licenses/>.
 ***************************************************************************/
/**
  @file i2c_driver.c
  @brief Contains the driver routines for i2c driver using dedicated I2C pins.
  @detail This file has the driver support for i2c using dedicated i2c pins.
  This file contains init, configure, read and write routines*/

/* Enable these bits only when corresponding interrupt is needed.*/

#include "i2c.h"//Includes the definitions of i2c communication protocol//
#include "log.h"
#include "utils.h"

/* Enable these bits only when corresponding interrupt is needed.*/

//#define USE_SA_WRITE_I2C_INTERRUPT 1
//#define USE_WRITE_I2C_INTERRUPT 1
//#define USE_READ_I2C_INTERRUPT 1

i2c_struct *i2c_instance[MAX_I2C_COUNT];

/**
 * @fn void i2c_init()
 * @brief Initialises the i2c modules.
 * @details Initialises the i2c array modules to the max. no of i2c modules present
 */
void i2c_init()
{
	for(int i=0; i< MAX_I2C_COUNT; i++)
	{
		i2c_instance[i] = (i2c_struct*) (I2C0_BASE + (i * I2C_OFFSET));
	}
}

/** @fn int config_i2c(i2c_struct * instance, unsigned char prescale_div, unsigned char scl_div)
 * @brief This routine configures the serial clock frequency count and
 *  prescaler count.
 * @details There are 4 registers which are configurable. This function
 *   writes into the registr based on the passed address. he serial clock count
 *   and prescalar count decides the frequency (sck) that needs to be used for
 *   the I2C serial communication. Then resets status register.
 * @param i2c_struct*
 * @param unsigned char prescale_div
 * @param unsigned char scl_div
 * @return REturns 0 if success; else returns -ENXIO.
 */
int config_i2c(i2c_struct * instance, unsigned char prescale_div, unsigned char scl_div)
{
	unsigned char temp = 0;
	log_debug("\tI2C: Initializing the Controller\n");

	if(prescale_div  != instance->prescale )
	{
		instance->prescale = prescale_div;
#ifdef DEBUG 
		temp = instance->prescale;

		if((temp | 0x00) != prescale_div)
		{
			log_error("\t Failed to write Prescale division Written Value: 0x%x; read Value: 0x%x\n", prescale_div, instance->prescale);
			return -ENXIO;
		}
		else
		{
			log_debug("\tPrescaler successfully initalized\n");
		}
#endif
	}

	if(scl_div != instance->scl )
	{
		instance->scl = scl_div;  //Setting the I2C clock value to be 1, which will set the clock for module and prescaler clock


#ifdef DEBUG 
		temp = instance->scl;

		/* Just reading the written value to see if all is well -- Compiler should not optimize this load!!! Compiler can just optimize the store to pointer address followed by load pointer to a register to just an immediate load to the register since clock register is not used anywhere -- but the purpose is lost. Don't give compiler optimizations */
		if((temp | 0x00) != scl_div)
		{
			log_error("\tClock initialization failed Write Value: 0x%x; read Value: 0x%x\n", scl_div, temp);
			return -ENXIO;
		}
		else
		{
			log_debug("\tClock successfully initalized\n");
		}
#endif
	}

	/* S1=0x80 S0 selected, serial interface off */
	log_debug("\tClearing the status register. \n");
	instance->control = I2C_PIN;

	// Reading set control Register Value to ensure sanctity
	log_debug("\tReading Status Register \n");
	temp = instance->control;

	//Check whether the status register is cleared or not.
	if((temp & 0x7f) != 0){
		log_error("\tDevice Not Recognized\n");
		return -ENXIO;
	}

	log_debug("\tWaiting for a specified time\n ");
	waitfor(900); //1 Second software wait -- Should be 900000 but setting to 900 now since simulation is already slow
	log_debug("\tDone Waiting \n ");
	log_info("\nControl: %x; Status: %x", instance->control, instance->status);
	/* Enable Serial Interface */
	instance->control = I2C_IDLE;
	waitfor(900); //1 Second software wait -- Should be 900000 but setting to 900 now since simulation is already slow

	temp = instance->status;

	/* Check to see if I2C is really in Idle and see if we can access the status register -- If not something wrong in initialization. This also verifies if Control is properly written since zero bit will be initialized to zero*/
	if(temp != (I2C_PIN | I2C_BB)){
		log_error("\n\tInitialization failed; Status Reg: %x\n", temp);
		return -ENXIO;
	}

	log_info("\tI2C Initialization success\n");
	return 0;
}

/**
 * @fn int wait_till_I2c_bus_free(i2c_struct * instance)
 * @brief wait for the i2c bus to be freee.
 * @details once a I2C Transaction is started, the bus needs to be freed for other devices
 *    to use the bus. This function checks the busy bit in status register to become free 
 *    for a particular time. If it becomes free, returns 0, else negative value.
 * @param i2c_struct*
 * @return Returns 0 if the bus becomes free; else returns ETIMEDOUT.
 */
int wait_till_I2c_bus_free(i2c_struct * instance)
{
	log_debug("\tCheck for I2C Bus Busy to be free.\n");
	int timeout = DEF_TIMEOUT;
	int status;

	status = instance->status;

	while (!(status & I2C_BB) && --timeout) {
		waitfor(20000); /* wait for 100 us */
		status = instance->status;
	}

	if (timeout == 0) {
		log_error("\t Bus busy wait - timed out. Resetting\n");
		return ETIMEDOUT;
	}

	return 0;
}

/**
 * @fn int wait_till_txrx_operation_Completes(i2c_struct * instance, int *status)
 * @brief  Waits in the loop till the i2c tx/rx operation completes
 * @details The PIN bit in the status register becomes high when tx/rx operation 
 *     starts and becomes low once done. This function checks whether tx/rx operaiton is complete or not. 
 * @param i2c_struct* 
 * @param int *status  --> contents of the status register
 * @return zero if success; else -ETIMEOUT
 */
int wait_till_txrx_operation_Completes(i2c_struct * instance, int *status)
{

	int timeout = DEF_TIMEOUT;

	*status = instance->status;

	while ((*status & I2C_PIN) && --timeout) {
		waitfor(10000); /* wait for 100 us */
		*status = instance->status;
	}

	if (timeout == 0){
		log_info("\tWait for pin timed out\n");
		return ETIMEDOUT;
	}

	waitfor(10000); /* wait for 100 us */
	log_debug("\n I2C tx_rx operation is completed");
	return 0;
}

/**
 * @fn int sendbytes(i2c_struct * instance, const char *buf, int count, int last, int eni)
 * @brief  writes "n" number of bits over i2c bus.
 * @details Called when the user wants to write n number of bits over i2c bus.
 * @param i2c_struct*  --- i2c structure pointer
 * @param const char *buf --- Pointer to buffer which contains the data to be written.
 * @param int count --- No of bytes to be written.
 * @param int last --- If 1, I2C stop command can be sent
 * @param int eni  --- External Interrupt Control
 * @return Returns number of bytes written else EREMOTEIO.
 */
int sendbytes(i2c_struct * instance, const char *buf, int count, int last, int eni)
{
	int wrcount, status, timeout;
	printf("\tStarting Write Transaction -- Did you create tri1 nets for SDA and SCL in verilog?\n");
	for (wrcount=0; wrcount<count; ++wrcount) {
		instance->data = buf[wrcount];
		timeout = wait_till_txrx_operation_Completes(instance, &status);
		if (timeout) {
			printf("\tTimeout happened - Write did not go through the BFM -- Diagnose\n");
			instance->control = I2C_STOP;
			return EREMOTEIO;
		}
		if (status & I2C_LRB) { // What error is this?
			instance->control = I2C_STOP;//~
			printf("\tSome status check failing\n");
			return EREMOTEIO;
		}
	}
	if (last){
		printf("\tLast byte sent : Issue a stop\n");
		instance->control = I2C_STOP;
	}
	else{
		printf("\tSending Rep Start and doing some other R/W transaction\n");

		if(!eni)
			instance->control = I2C_REPSTART;
		else
			instance->control = I2C_REPSTART_ENI;
	}

	return wrcount;
}

/**
 * @fn int readbytes(i2c_struct * instance, char *buf, int count, int last)
 * @brief Reads "n" number of bytes from I2C Bus
 * @details Reads n number of bytes over I2C Bus and store teh same in 
 *          "buf" pointer.
 * @param i2c_struct*  --- i2c structure pointer
 * @param const char *buf --- Pointer to buffer which contains the read data.
 * @param int count --- No of bytes to be read.
 * @param int last --- If 1, I2C stop command can be sent
 * @return Returns number of bytest read over i2c bus. else -1.
 */
int readbytes(i2c_struct * instance, char *buf, int count, int last)
{
	int i, status;
	int wfp;

	/* increment number of bytes to read by one -- read dummy byte */
	for (i = 0; i <= count; i++) {
		wfp = wait_till_txrx_operation_Completes(instance, &status);
		if (wfp) {
			instance->control = I2C_STOP;
			return -1;
		}

		if ((status & I2C_LRB) && (i != count)) {
			instance->control = I2C_STOP;
			printf("\tNo ack\n");
			return -1;
		}

		if (i)
		{
			buf[i - 1] = instance->data;
			printf("\n Read Value: %x", buf[i - 1]);
		}
		else
			instance->data = !instance->data; /* dummy read */

		if (i == count - 1) {
			instance->control = I2C_ESO;
		} else if (i == count) {
			if (last)
				instance->control = I2C_STOP;
			else
				instance->control = I2C_REPSTART_ENI;
		}

	}

	return i-1; //excluding the dummy read
}

/**
 * @fn int i2c_send_slave_address(i2c_struct * instance, unsigned char slaveAddress, unsigned char rdWrCntrl, unsigned long delay)
 * @brief  Performs the intilization of i2c slave.
 * @details Writes slave addresss into the i2b to start write or read operation.
 * @param i2c_struct*
 * @param unsigned char slaveAddress
 * @param unsigned char rdWrCntrl
 * @param unsigned long delay
 * @return Zero if success; else non zero
 */
int i2c_send_slave_address(i2c_struct * instance, unsigned char slaveAddress, unsigned char rdWrCntrl, unsigned long delay)
{
	int timeout;
	unsigned char temp = 0;
	int status = 0;

	delay = delay;

	if(rdWrCntrl == 0)
		slaveAddress |= I2C_WRITE;
	else
		slaveAddress |= I2C_READ;

	//Writing the slave address that needs to be written into data register.
	instance->data = slaveAddress;
	log_debug("\tSlave Address 0x%x written into data register\n", slaveAddress);

	//Reads back the data register to confirm
	temp = instance->data; //Reads the slave address from I2C controller

	if(slaveAddress != (int)temp)
	{
		log_error("\tSlave address is not matching; Written Add. Value: 0x%x; Read Add. Value: 0x%x\n", slaveAddress, temp);
		log_error("\n There is some issue in AXI interface. Please check.");
		return EAXI_ERROR;
	}

	//Waits till the bus becomes free.
	while(wait_till_I2c_bus_free(instance))
	{
		log_error("\tError in Waiting for BB\n");
		return EI2C_BUS_ERROR;
	}


	//Send the start condition and slave address to slave
#ifndef USE_SA_WRITE_I2C_INTERRUPT
	instance->control = I2C_START; //Sending the slave address to the I2C slave
	waitfor(90000);
	//Wait for PIN to become low.
	timeout = wait_till_txrx_operation_Completes(instance, &status);
	if (timeout) {//Asking the controller to send a start signal to initiate the transaction
		printf("\tTimeout happened - Write did not go through the BFM -- Diagnose\n");
		instance->control = I2C_STOP; //~
		return EI2C_PIN_ERROR;
	}

	if (status & I2C_LRB) {
		instance->control = I2C_STOP; //~
		printf("\tSome status check failing\n");
		return EI2C_LRB_ERROR;
	}

#else
	i2c_complete_flag = 0;

	instance->control = I2C_START_ENI; //Sending the slave address to the I2C slave
	while(!i2c_complete_flag);
	log_info("\n Slave Address Write Operation is complete.");
	i2c_complete_flag = 0;
#endif

	return I2C_SUCCESS;
}

/**
 * @fn int i2c_write_data(i2c_struct * instance, unsigned char writeData, unsigned char delay)
 * @brief I does the reading or writing from the address specified .
 * @details Writes one byte to the slave I2C DEVICE.
 * @param i2c_struct*, 
 * @param unsigned char writedata
 * @param unsigned char delay
 * @return Returns Zeron on success; else -EREMOTEIO
 */
int i2c_write_data(i2c_struct * instance, unsigned char writeData, unsigned char delay)
{
	int timeout;
	int status = 0;
	delay = delay;

	instance->data= writeData;

#ifndef USE_WRITE_I2C_INTERRUPT
	timeout = wait_till_txrx_operation_Completes(instance, &status);
	if (timeout) {
		printf("\tTimeout happened - Write did not go through the BFM -- Diagnose\n");
		instance->control = I2C_STOP; //~
		return EREMOTEIO;
	}

	if (status & I2C_LRB)
	{ // What error is this?
		instance->control = I2C_STOP; //~
		printf("\tSome status check failing\n");
		return EI2C_LRB_ERROR;
	}
#else
	i2c_complete_flag = 0;
	instance->control = I2C_STOP_ENI; //Sending the sslave address to the I2C slave

	while(!i2c_complete_flag);
	log_info("\n Write Operation is complete.");
	i2c_complete_flag = 0;
#endif

	return I2C_SUCCESS;
}

/**
 * @fn int i2c_read_data(i2c_struct * instance, unsigned char *read_data, unsigned char delay)
 * @brief It does the reading or writing from the address specified .
 * @details Reads a byte of data over I2C bus from the passed I2C location.
 * @param i2c_struct*
 * @param unsigned char  *read_data
 * @param unsigned char delay
 * @return Zero on success; else -ETIMEOUT
 */
//#define READ_INTERRUPT 1
int i2c_read_data(i2c_struct * instance, unsigned char *read_data, unsigned char delay)
{
	int status = 0;

	/* Make a dummy read as per spec of the I2C controller */

	*read_data = instance->data; //~

#ifdef USE_WRITE_I2C_INTERRUPT	
	i2c_complete_flag = 0;
	instance->control = I2C_REPSTART_ENI; //~

	while(!i2c_complete_flag);
	*read_data = instance->data;

	printf("\n I2C Read Data = %x", i2c_read_data);
#else
	while(wait_till_txrx_operation_Completes(instance, &status))
	{
		printf("\twaiting for pin\n");
		waitfor(delay);
	}
#endif
	return I2C_SUCCESS;
}

/**
 * @fn int i2c_send_interrupt_slave_address(i2c_struct * instance, unsigned char slaveAddress, unsigned char rdWrCntrl, unsigned long delay)
 * @brief Sends the slave address over I2C Bus.
 * @details Interrupt based routine to send slave address to the I2C slave device
 * @param i2c_struct*
 * @param unsigned char slaveAddress
 * @param unsigned char rdWrCntrl
 * @param unsigned long delay
 * @return Zero on success. Else corresponding error value.
 */
int i2c_send_interrupt_slave_address(i2c_struct * instance, unsigned char slaveAddress, unsigned char rdWrCntrl, unsigned long delay)
{
	int timeout;
	unsigned char temp = 0;
	int status = 0;
	delay = delay;

	if(rdWrCntrl == 0)
		slaveAddress |= I2C_WRITE;
	else
		slaveAddress |= I2C_READ;

	log_debug("\n\tSetting Slave Address : 0x%x\n", slaveAddress);/* Writes the slave address to I2C controller */
	//Writing the slave address that needs to be written into data register.
	instance->data = slaveAddress;
	log_debug("\tSlave Address is written into data register\n");

	//Reads back the data register to confirm
	temp = instance->data; //Reads the slave address from I2C controller
	log_debug("\tSet slave address read again, which is 0x%x\n",temp);

	if(slaveAddress != (int)temp)
	{
		log_error("\tSlave address is not matching; Written Add. Value: 0x%x; Read Add. Value: 0x%x\n", slaveAddress, temp);
		log_error("\n There is some issue in AXI interface. Please check.");
		return EAXI_ERROR;
	}

	//Waits till the bus becomes free.
	while(wait_till_I2c_bus_free(instance))
	{
		log_error("\tError in Waiting for BB\n");
		return EI2C_BUS_ERROR;
	}

	//Send the start condition and slave address to slave
#ifndef USE_SA_WRITE_I2C_INTERRUPT
	instance->control = I2C_START;; //Sending the slave address to the I2C slave
	//Wait for PIN to become low.
	timeout = wait_till_txrx_operation_Completes(instance, &status);
	if (timeout) {//Asking the controller to send a start signal to initiate the transaction
		printf("\tTimeout happened - Write did not go through the BFM -- Diagnose\n");
		instance->control = I2C_STOP; //~
		return EI2C_PIN_ERROR;
	}

	if (status & I2C_LRB) {
		instance->control = I2C_STOP; //~
		printf("\tSome status check failing\n");
		return EI2C_LRB_ERROR;
	}
#else
	i2c_complete_flag = 0;
	instance->control = I2C_REPSTART_ENI; //Sending the slave address to the I2C slave
	while(!i2c_complete_flag);
	log_info("\n Slave Address Write Operation is complete.");
	i2c_complete_flag = 0;
#endif
	log_info("\n Slave address is written successfully");
	return I2C_SUCCESS;
}

/**
 * @fn int i2c_read_interrupt_data(i2c_struct * instance, unsigned char *read_data, unsigned char delay, unsigned char last)
 * @brief  Interrupt based I2C read 
 * @details Interrupt based i2c read function to read from the I2C slave.
 * @param i2c_struct
 * @param unsigned char *read_data
 * @param unsigned char delay 
 * @param unsigned char last
 * @return Zero on success.
 */
int i2c_read_interrupt_data(i2c_struct * instance, unsigned char *read_data, unsigned char delay, unsigned char last)
{
	int status = 0;

	/* Make a dummy read as per spec of the I2C controller */
	*read_data = instance->data;

#ifdef USE_READ_I2C_INTERRUPT	
	i2c_complete_flag = 0;

	if(last)
	{
		instance->control = I2C_STOP_ENI; //~
		while(!i2c_complete_flag);
	}
	else
	{
		/* Needs to be tested */
		//			instance->control = I2C_REPSTART_ENI;
		//			printf("\n Call I2C rep. start eni");
		//			while(!i2c_complete_flag);
	}
	printf("\n I2C Read Data = %x", *read_data);
#else
	while(wait_till_txrx_operation_Completes(instance, &status))
	{
		printf("\twaiting for pin\n");
		waitfor(delay);
	}
	if(!last)
	{
		printf("\n Rep Start");				
		//				instance->control = I2C_REPSTART;
	}
	else
	{
		printf("\nCall I2C Stop");
		instance->control = I2C_STOP;
	}
#endif
	return I2C_SUCCESS;
}

/**
 * @fn int i2c_write_interrupt_data(i2c_struct * instance, unsigned char writeData, unsigned char delay, unsigned char last)
 * @brief Interrupt based I2C write function.
 * @details Writes a byte of data into slave I2C bus using interrupt.
 * @param i2c_struct*
 * @param unsigned char writeData
 * @param unsigned char delay
 * @param unsigned char last
 * @return Zero on success. Else based on the error.
 */
int i2c_write_interrupt_data(i2c_struct * instance, unsigned char writeData, unsigned char delay, unsigned char last)
{
	int timeout;
	int status = 0;
	delay = delay;

	instance->data = writeData;

#ifndef USE_WRITE_I2C_INTERRUPT
	timeout = wait_till_txrx_operation_Completes(instance, &status);
	if (timeout) {
		printf("\tTimeout happened - Write did not go through the BFM -- Diagnose\n");
		instance->control = I2C_STOP; //~
		return EREMOTEIO;
	}

	if (status & I2C_LRB)
	{ // What error is this?
		instance->control = I2C_STOP;//~
		printf("\tSome status check failing\n");
		return EI2C_LRB_ERROR;
	}

	if(1 == last)
	{
		instance->control = I2C_STOP;;
		printf("\tI2C Write Success and completes\n");
	}
#else
	i2c_complete_flag = 0;

	if(last)
	{
		instance->control = I2C_STOP_ENI; //Sending the sslave address to the I2C slave
		printf("\n Calling stop eni write");
		while(!i2c_complete_flag);
	}
	else
	{
		//			instance->control = I2C_REPSTART_ENI;
		//			printf("\n Calling repstart eni write");
		//		while(!i2c_complete_flag);
	}
	log_info("\n Write Operation is complete.");
	i2c_complete_flag = 0;
#endif
	return I2C_SUCCESS;
}
