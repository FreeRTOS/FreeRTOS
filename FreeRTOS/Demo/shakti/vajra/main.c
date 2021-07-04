#include "FreeRTOS.h"
#include "task.h"
#include "log.h"
#include "uart.h"
#include "utils.h"
#include "gpio.h"
#include "queue.h"
#include "timers.h"
#include "spi.h"
#include <stdint.h> 
#include "i2c.h"

#define I2C i2c_instance[1]

#define BMP280_SLAVE_ADDRESS 0xEC	//Defines the Starting address of slave//
#define DELAY_VALUE 900
#define PRESCALER_COUNT 0x1F
#define SCLK_COUNT 0x91
#define BMP280_CTRL_MEANS 0xF4
#define BMP280_NORMAL_MODE 0x26
#define BMP280_STATUS_REGISTER 0xF3
#define BMP280_CONFIG_REGISTER 0xF5
#define BMP280_RESET_REGISTER 0xE0

#define BMP280_REG_DIG_T1 0x88
#define BMP280_REG_DIG_T2 0x8A
#define BMP280_REG_DIG_T3 0x8C

#define BMP280_REG_DIG_P1 0x8E
#define BMP280_REG_DIG_P2 0x90
#define BMP280_REG_DIG_P3 0x92
#define BMP280_REG_DIG_P4 0x94
#define BMP280_REG_DIG_P5 0x96
#define BMP280_REG_DIG_P6 0x98
#define BMP280_REG_DIG_P7 0x9A
#define BMP280_REG_DIG_P8 0x9C
#define BMP280_REG_DIG_P9 0x9E

uint32_t gpress = 0;
uint32_t gtemp = 0;
uint16_t bmp280_calib_dig_T1;
int16_t  bmp280_calib_dig_T2;
int16_t  bmp280_calib_dig_T3;

uint16_t bmp280_calib_dig_P1;
int16_t  bmp280_calib_dig_P2;
int16_t  bmp280_calib_dig_P3;
int16_t  bmp280_calib_dig_P4;
int16_t  bmp280_calib_dig_P5;
int16_t  bmp280_calib_dig_P6;
int16_t  bmp280_calib_dig_P7;
int16_t  bmp280_calib_dig_P8;
int16_t  bmp280_calib_dig_P9;


uint16_t bmp280_calib_dig_T1;
int16_t  bmp280_calib_dig_T2;
int16_t  bmp280_calib_dig_T3;

uint16_t bmp280_calib_dig_P1;
int16_t  bmp280_calib_dig_P2;
int16_t  bmp280_calib_dig_P3;
int16_t  bmp280_calib_dig_P4;
int16_t  bmp280_calib_dig_P5;
int16_t  bmp280_calib_dig_P6;
int16_t  bmp280_calib_dig_P7;
int16_t  bmp280_calib_dig_P8;
int16_t  bmp280_calib_dig_P9;

int write_bmp280_register(i2c_struct*, uint32_t, unsigned char, uint32_t);
int read_bmp280_values(i2c_struct*, uint32_t, uint32_t*, uint32_t*, uint32_t);
short read_bmp280_values16(i2c_struct*, uint32_t, uint32_t);
int read_bmp280_register(i2c_struct*, uint32_t, uint32_t*, uint32_t);

 /** @fn int read_bmp280_register(i2c_struct *instance, uint32_t reg_offset, uint32_t *readTemp, uint32_t delay) 
 * @brief It helps to read the register value of the bmp280.
 * @details It reads the 1byte register value of the chip.
 * @warning The slave should have support for this option.
 * @param i2c_struct *instance  It uses instance[0].
 * @param uint32_t reg_offset  Used to store the register offset value.
 * @param uint32_t *readTemp  Reading the temperature value.
 * @param uint32_t delay  Used delay for I2C functionality.
 * @return It returns the value to the main.
 */
int read_bmp280_register(i2c_struct *instance, uint32_t reg_offset, uint32_t *readTemp, uint32_t delay)
{
	unsigned char read_buf[4] = {'\0'};
	unsigned char temp = 0;

	//Writes the slave address for write
	i2c_send_slave_address(instance, BMP280_SLAVE_ADDRESS, I2C_WRITE, 800);

	//Writes the pointer to address that needs to be read
	i2c_write_data(instance, reg_offset , delay);

	//Stops the I2C transaction to start reading the temperature value.
	instance->control = I2C_STOP;

	//Writes the slave address for read
	i2c_send_slave_address(instance, BMP280_SLAVE_ADDRESS, I2C_READ, 800);

	/* Make a dummy read as per spec of the I2C controller */
	i2c_read_data(instance, &temp, delay);
	instance->control = I2C_NACK;

	//Reads the MSB Byte of temperature [D9 - D1]
	i2c_read_data(instance, &read_buf[0], delay);

	instance->control = I2C_STOP;
	*readTemp = read_buf[0] ;
	return 0;
}

/** @fn int read_bmp280_values(i2c_struct * instance, uint32_t reg_offset, uint32_t *pressure, uint32_t *temperature, uint32_t delay) 
 * @brief Functions used to reads the temperature and pressure values.
 * @details It reads 8bits data of temperature and pressure.
 * @warning The slave should have support for this option.
 * @param i2c_struct * instance  It uses i2c_instance[0].
 * @param uint32_t reg_offset  Used to store the register offset value.
 * @param uint32_t *pressure  Reading the pressure value.
 * @param uint32_t *temperature  Reading the temperature value.
 * @param uint32_t delay  Used delay for I2C functionality.
 */
int read_bmp280_values(i2c_struct * instance, uint32_t reg_offset,
		       uint32_t *pressure, uint32_t *temperature, uint32_t delay)
{
	unsigned char read_buf[6] = {'\0'};
	int32_t adc_P, adc_T, var1, var2, t_fine; 
	int32_t temp;
	int32_t p;

	//Writes the slave address for write
	i2c_send_slave_address(instance, BMP280_SLAVE_ADDRESS, I2C_WRITE, 800);

	//Writes the pointer to address that needs to be read
	i2c_write_data(instance, reg_offset , delay);

	//Stops the I2C transaction to start reading the temperature value.
	instance->control = I2C_STOP;

	//Writes the slave address for read
	i2c_send_slave_address(instance, BMP280_SLAVE_ADDRESS, I2C_READ, 800);

	/* Make a dummy read as per spec of the I2C controller */
	i2c_read_data(instance, read_buf, delay);

	//Read Pressure
	i2c_read_data(instance, &read_buf[0], delay);
	i2c_read_data(instance, &read_buf[1], delay);
	i2c_read_data(instance, &read_buf[2], delay);

	//Read Temperature	
	i2c_read_data(instance, &read_buf[3], delay);
	i2c_read_data(instance, &read_buf[4], delay);
	instance->control = I2C_NACK;
	i2c_read_data(instance, &read_buf[5], delay);

	instance->control = I2C_STOP;
	adc_P = ((read_buf[0] << 12) | (read_buf[1] << 4) | (read_buf[2] >> 4));
	adc_T = ((read_buf[3] << 12) | (read_buf[4] << 4) | (read_buf[5] >> 4));

	// Calculate TEMPERATURE
	var1 = ((((adc_T / 8) - ((int32_t)bmp280_calib_dig_T1 * 2))) * ((int32_t)bmp280_calib_dig_T2)) / 2048;
	var2 = (((((adc_T / 16) - ((int32_t)bmp280_calib_dig_T1)) * ((adc_T / 16) - ((int32_t)bmp280_calib_dig_T1))) / 4096) * ((int32_t)bmp280_calib_dig_T3)) / 16384;
	t_fine = var1 + var2;

	temp = (t_fine * 5 + 128) / 256;
	*temperature = temp;

	printf("\nTemperature Value:%u.%u °C", (temp/100),(temp%100));

	//Calculate Pressure
	var1 = 0; 
	var2 = 0;

	var1 = (((int32_t)t_fine) / 2) - (int32_t)64000;
	var2 = (((var1/4) * (var1/4)) / 2048 ) * ((int32_t)bmp280_calib_dig_P6);
	var2 = var2 + ((var1 * ((int32_t)bmp280_calib_dig_P5)) * 2);
	var2 = (var2/4) + (((int32_t)bmp280_calib_dig_P4) * 65536);
	var1 = ((((int32_t)bmp280_calib_dig_P3 * (((var1/4) * (var1/4)) / 8192 )) / 8) + ((((int32_t)bmp280_calib_dig_P2) * var1)/2)) / 262144;
	var1 =((((32768 + var1)) * ((int32_t)bmp280_calib_dig_P1)) / 32768);

	if (var1 == 0)
		return 0; // avoid exception caused by division by zero

	p = (((uint32_t)(((int32_t)1048576) - adc_P) - (var2 / 4096))) * 3125;

	if (p < (int32_t) 0x80000000)
		p = (p * 2) / ((uint32_t)var1);

	else
		p = (p / (uint32_t)var1) * 2;

	var1 = (((int32_t)bmp280_calib_dig_P9) * ((int32_t)(((p/8) * (p/8)) / 8192))) / 4096;
	var2 = (((int32_t)(p/4)) * ((int32_t)bmp280_calib_dig_P8)) / 8192;

	p = (uint32_t)((int32_t)p + ((var1 + var2 + (int32_t)bmp280_calib_dig_P7)/16));
	*pressure = p;

	printf("\nThe Pressure Value:%u.%u Kpa",(p/1000),(p%1000));
	return 0;
}

/** @fn short read_bmp280_values16(i2c_struct * instance, uint32_t reg_offset, uint32_t delay)
 * @brief Functions is used to read 16bits values.
 * @details It used to read 16bits from the chips.
 * @warning The slave should have support for this option.
 * @param i2c_struct * instance  It uses i2c_instance[0].
 * @param uint32_t reg_offset  Used to store the register offset value.
 * @param uint32_t delay  Used delay for I2C functionality.
 * @return It returns 16bits value to the main.
 */
short read_bmp280_values16(i2c_struct * instance, uint32_t reg_offset, uint32_t delay)
{
	unsigned char read_buf[2] = {'\0'};
	unsigned char temp = 0;

	//Writes the slave address for write
	i2c_send_slave_address(instance, BMP280_SLAVE_ADDRESS, I2C_WRITE, 800);

	//Writes the pointer to address that needs to be read
	i2c_write_data(instance, reg_offset , delay);

	//Stops the I2C transaction to start reading the temperature value.
	instance->control = I2C_STOP;

	//Writes the slave address for read
	i2c_send_slave_address(instance, BMP280_SLAVE_ADDRESS, I2C_READ, 800);

	/* Make a dummy read as per spec of the I2C controller */
	i2c_read_data(instance, &temp, delay);

	i2c_read_data(instance, &read_buf[0], delay);
	instance->control = I2C_NACK;
	i2c_read_data(instance, &read_buf[1], delay);
	instance->control = I2C_STOP;

	return ( ( read_buf[1] << 8 ) | read_buf[0] );	
}

/** @fn int write_bmp280_register(i2c_struct * instance, uint32_t reg_offset, unsigned char write_value, uint32_t delay) 
 * @brief It used to write the desired value to the register.
 * @details To get the result chip have to given the instruction by writing a value to yhe register.
 * @warning The slave should have support for this option.
 * @param i2c_struct * instance  It uses i2c_instance[0].
 * @param uint32_t reg_offset  Used to store the register offset value.
 * @param unsigned char write_value  Passing the value want write to register.
 * @param uint32_t delay  Used delay for I2C functionality.
 * @return Returns 0 to the main after stopping I2C.
 */
int write_bmp280_register(i2c_struct * instance, uint32_t reg_offset, unsigned char write_value, uint32_t delay)
{
	i2c_send_slave_address(instance, BMP280_SLAVE_ADDRESS, I2C_WRITE, delay);

	i2c_write_data(instance, reg_offset , delay);
	i2c_write_data(instance, write_value , delay);

	//Stops the I2C transaction to start reading the temperature value.
	instance->control = I2C_STOP;
	return 0;
}

/*-----------------------------------------------------------*/

/*
 * FreeRTOS hook for when malloc fails, enable in FreeRTOSConfig.
 */
void vApplicationMallocFailedHook( void );

/*
 * FreeRTOS hook for when freertos is idling, enable in FreeRTOSConfig.
 */
void vApplicationIdleHook( void );

/*
 * FreeRTOS hook for when a stackoverflow occurs, enable in FreeRTOSConfig.
 */
void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName );

void vTaskgpio(__attribute__((unused)) void *pvParameters);
void vTaskspiwrite(__attribute__((unused)) void *pvParameters);
void vTaskbmp280(__attribute__((unused)) void *pvParameters);
/*-----------------------------------------------------------*/

int main(void)
{
	/*
	   The demo here is to show the capability of vajra SoC of shakti family.
	   Here we read temperature & pressure from bmp280, and update it regularly to spi flash.
	   Based on temperature, we control the gpio pin.
	 */

	printf("FREERTOS starting\n");

	xTaskCreate(vTaskbmp280,"Task 3",500,NULL,1,NULL);
	xTaskCreate(vTaskgpio,"Task 1",500,NULL,1,NULL);
	xTaskCreate(vTaskspiwrite,"Task 2",500,NULL,1,NULL);

	printf("Task scheduler started\n");	/* Task scheduledd with help of
						   clint */
	vTaskStartScheduler();

	/* Exit FreeRTOS */
	return 0;
}
/*-----------------------------------------------------------*/
void vTaskbmp280(__attribute__((unused)) void *pvParameters )
{
	const TickType_t xDelay1000ms = pdMS_TO_TICKS( 10 );

	uint32_t tempReadValue = 0;
	uint32_t delay = 100;

	i2c_init();

	//Initialises I2C Controller
	if(config_i2c(I2C, PRESCALER_COUNT,SCLK_COUNT))
	{
		log_error("\tSomething Wrong In Initialization\n");
		return;
	}
	else
		log_info("\tIntilization BMP280_STATUS_REGISTER Happened Fine\n");

	write_bmp280_register(I2C, BMP280_CONFIG_REGISTER, 0xC0, delay);
	write_bmp280_register(I2C, BMP280_CTRL_MEANS, 0x27, delay);

	if(0 == read_bmp280_register(I2C, 0xD0, &tempReadValue, delay))
	{
		if (0x58 != tempReadValue)
		{
			printf("\n Device Not detected");
			return;
		}
	}

	write_bmp280_register(I2C, BMP280_RESET_REGISTER, 0xB6, delay);
	read_bmp280_register(I2C, BMP280_RESET_REGISTER, &tempReadValue, delay);

	bmp280_calib_dig_T1 = read_bmp280_values16(I2C, BMP280_REG_DIG_T1, delay);
	bmp280_calib_dig_T2 = read_bmp280_values16(I2C, BMP280_REG_DIG_T2, delay);
	bmp280_calib_dig_T3 = read_bmp280_values16(I2C, BMP280_REG_DIG_T3, delay);

	bmp280_calib_dig_P1 = read_bmp280_values16(I2C, BMP280_REG_DIG_P1, delay);
	bmp280_calib_dig_P2 = read_bmp280_values16(I2C, BMP280_REG_DIG_P2, delay);
	bmp280_calib_dig_P3 = read_bmp280_values16(I2C, BMP280_REG_DIG_P3, delay);
	bmp280_calib_dig_P4 = read_bmp280_values16(I2C, BMP280_REG_DIG_P4, delay);
	bmp280_calib_dig_P5 = read_bmp280_values16(I2C, BMP280_REG_DIG_P5, delay);
	bmp280_calib_dig_P6 = read_bmp280_values16(I2C, BMP280_REG_DIG_P6, delay);
	bmp280_calib_dig_P7 = read_bmp280_values16(I2C, BMP280_REG_DIG_P7, delay);
	bmp280_calib_dig_P8 = read_bmp280_values16(I2C, BMP280_REG_DIG_P8, delay);
	bmp280_calib_dig_P9 = read_bmp280_values16(I2C, BMP280_REG_DIG_P9, delay);

	/* As per most tasks, this task is implemented in an infinite loop. */
	for( ;; )
	{
		write_bmp280_register(I2C, BMP280_CTRL_MEANS, BMP280_NORMAL_MODE,
				      delay);

		if(0 == read_bmp280_register(I2C, BMP280_STATUS_REGISTER,
					     &tempReadValue, delay))
		{
			if(!(tempReadValue & 0x9))
			{
				//Read pressure and temperature values.
				read_bmp280_values(I2C, 0xF7, &gpress,
						   &gtemp, delay);
			}
		}
		else
		{
			log_error("\nTemperature read failed.");
		}

		vTaskDelay( xDelay1000ms );
		/* Delay for a period. */
	}
}

static void spi_write(void)
{
	uint32_t write_address = 0x0b00000;

	flash_device_id();
	waitfor(200);

	flash_write_enable();
	flash_erase(0x00b00000); //erases an entire sector
	flash_status_register_read();

	//flash write
	flash_write_enable();
	flash_write(write_address, gtemp);
	flash_status_register_read();

	flash_write(write_address + 0x4, gpress);
	flash_status_register_read();
}

void vTaskspiwrite(__attribute__((unused)) void *pvParameters )
{
	const TickType_t xDelay1000ms = pdMS_TO_TICKS(10);

	configure_spi(SPI1_OFFSET);
	spi_init();

	/* As per most tasks, this task is implemented in an infinite loop. */
	for( ;; )
	{
		spi_write();

		vTaskDelay( xDelay1000ms );
		/* Delay for a period. */
	}
}

void vTaskgpio(__attribute__((unused)) void *pvParameters)
{
	const TickType_t xDelay1000ms = pdMS_TO_TICKS(10);

	write_word(GPIO_DIRECTION_CNTRL_REG, 0x190);

	/*
	   We are giving 1 gpio pin for each device. GPIO4. GPIO7.
	   GPIO8. It is upto the end user to use them appropriately.
	 */
	for( ;; )
	{
		if(gtemp > 3000)
		{
			// switch on air cooler
			write_word(GPIO_DATA_REG, 0x10);
		}
		else if(gtemp > 2600)
		{
			//Full speed fan rotation
			write_word(GPIO_DATA_REG, 0xf0);
		}
		else if(gtemp < 26)
		{
			//mild speed fan rotation
			write_word(GPIO_DATA_REG, 0x100);
		}

		vTaskDelay( xDelay1000ms );
		/* Delay for a period. */
	}
}

/*-----------------------------------------------------------*/

void vApplicationMallocFailedHook( void )
{
	/* vApplicationMallocFailedHook() will only be called if
	   configUSE_MALLOC_FAILED_HOOK is set to 1 in FreeRTOSConfig.h.  It is a hook
	   function that will get called if a call to pvPortMalloc() fails.
	   pvPortMalloc() is called internally by the kernel whenever a task, queue,
	   timer or semaphore is created.  It is also called by various parts of the
	   demo application.  If heap_1.c or heap_2.c are used, then the size of the
	   heap available to pvPortMalloc() is defined by configTOTAL_HEAP_SIZE in
	   FreeRTOSConfig.h, and the xPortGetFreeHeapSize() API function can be used
	   to query the size of free heap space that remains (although it does not
	   provide information on how the remaining heap might be fragmented). */
	taskDISABLE_INTERRUPTS();
	for( ;; );
}
/*-----------------------------------------------------------*/

void vApplicationIdleHook( void )
{
	/* vApplicationIdleHook() will only be called if configUSE_IDLE_HOOK is set
	   to 1 in FreeRTOSConfig.h.  It will be called on each iteration of the idle
	   task.  It is essential that code added to this hook function never attempts
	   to block in any way (for example, call xQueueReceive() with a block time
	   specified, or call vTaskDelay()).  If the application makes use of the
	   vTaskDelete() API function (as this demo application does) then it is also
	   important that vApplicationIdleHook() is permitted to return to its calling
	   function, because it is the responsibility of the idle task to clean up
	   memory allocated by the kernel to any task that has since been deleted. */
}
/*-----------------------------------------------------------*/

void vApplicationStackOverflowHook( TaskHandle_t pxTask, char *pcTaskName )
{
	( void ) pcTaskName;
	( void ) pxTask;

	/* Run time stack overflow checking is performed if
	   configCHECK_FOR_STACK_OVERFLOW is defined to 1 or 2.  This hook
	   function is called if a stack overflow is detected. */
	taskDISABLE_INTERRUPTS();
	for( ;; );
}
/*-----------------------------------------------------------*/
