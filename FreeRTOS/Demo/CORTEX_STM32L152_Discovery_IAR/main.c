/*
    FreeRTOS V7.6.0 - Copyright (C) 2013 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that has become a de facto standard.             *
     *                                                                       *
     *    Help yourself get started quickly and support the FreeRTOS         *
     *    project by purchasing a FreeRTOS tutorial book, reference          *
     *    manual, or both from: http://www.FreeRTOS.org/Documentation        *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    >>! NOTE: The modification to the GPL is included to allow you to distribute
    >>! a combined work that includes FreeRTOS without being obliged to provide
    >>! the source code for proprietary components outside of the FreeRTOS
    >>! kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available from the following
    link: http://www.freertos.org/a00114.html

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

/*
    FreeRTOS V7.6.0 - Copyright (C) 2013 Real Time Engineers Ltd.
    All rights reserved

    VISIT http://www.FreeRTOS.org TO ENSURE YOU ARE USING THE LATEST VERSION.

    ***************************************************************************
     *                                                                       *
     *    FreeRTOS provides completely free yet professionally developed,    *
     *    robust, strictly quality controlled, supported, and cross          *
     *    platform software that has become a de facto standard.             *
     *                                                                       *
     *    Help yourself get started quickly and support the FreeRTOS         *
     *    project by purchasing a FreeRTOS tutorial book, reference          *
     *    manual, or both from: http://www.FreeRTOS.org/Documentation        *
     *                                                                       *
     *    Thank you!                                                         *
     *                                                                       *
    ***************************************************************************

    This file is part of the FreeRTOS distribution.

    FreeRTOS is free software; you can redistribute it and/or modify it under
    the terms of the GNU General Public License (version 2) as published by the
    Free Software Foundation >>!AND MODIFIED BY!<< the FreeRTOS exception.

    >>! NOTE: The modification to the GPL is included to allow you to distribute
    >>! a combined work that includes FreeRTOS without being obliged to provide
    >>! the source code for proprietary components outside of the FreeRTOS
    >>! kernel.

    FreeRTOS is distributed in the hope that it will be useful, but WITHOUT ANY
    WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
    FOR A PARTICULAR PURPOSE.  Full license text is available from the following
    link: http://www.freertos.org/a00114.html

    1 tab == 4 spaces!

    ***************************************************************************
     *                                                                       *
     *    Having a problem?  Start by reading the FAQ "My application does   *
     *    not run, what could be wrong?"                                     *
     *                                                                       *
     *    http://www.FreeRTOS.org/FAQHelp.html                               *
     *                                                                       *
    ***************************************************************************

    http://www.FreeRTOS.org - Documentation, books, training, latest versions,
    license and Real Time Engineers Ltd. contact details.

    http://www.FreeRTOS.org/plus - A selection of FreeRTOS ecosystem products,
    including FreeRTOS+Trace - an indispensable productivity tool, a DOS
    compatible FAT file system, and our tiny thread aware UDP/IP stack.

    http://www.OpenRTOS.com - Real Time Engineers ltd license FreeRTOS to High
    Integrity Systems to sell under the OpenRTOS brand.  Low cost OpenRTOS
    licenses offer ticketed support, indemnification and middleware.

    http://www.SafeRTOS.com - High Integrity Systems also provide a safety
    engineered and independently SIL3 certified version for use in safety and
    mission critical applications that require provable dependability.

    1 tab == 4 spaces!
*/

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "queue.h"

/* ST library functions. */
#include "stm32l1xx.h"
#include "discover_board.h"
#include "discover_functions.h"

/* Priorities at which the Rx and Tx tasks are created. */
#define configQUEUE_RECEIVE_TASK_PRIORITY	( tskIDLE_PRIORITY + 1 )
#define	configQUEUE_SEND_TASK_PRIORITY		( tskIDLE_PRIORITY + 2 )

/* The number of items the queue can hold.  This is 1 as the Rx task will
remove items as they are added so the Tx task should always find the queue
empty. */
#define mainQUEUE_LENGTH					( 1 )

/* The LED used to indicate that a value has been received on the queue. */
#define mainQUEUE_LED						( 0 )

/* The rate at which the Tx task sends to the queue. */
#define mainTX_DELAY						( 500UL / portTICK_RATE_MS )

/* A block time of zero simply means "don't block". */
#define mainDONT_BLOCK						( 0 )

/* The value that is sent from the Tx task to the Rx task on the queue. */
#define mainQUEUED_VALUE					( 100UL )

/* The length of time the LED will remain on for.  It is on just long enough
to be able to see with the human eye so as not to distort the power readings too
much. */
#define mainLED_TOGGLE_DELAY				( 20 / portTICK_RATE_MS )

/*-----------------------------------------------------------*/

/*
 * The Rx and Tx tasks as described at the top of this file.
 */
static void prvQueueReceiveTask( void *pvParameters );
static void prvQueueSendTask( void *pvParameters );

/*-----------------------------------------------------------*/

/* The queue to pass data from the Tx task to the Rx task. */
static xQueueHandle xQueue = NULL;

/*
 * Set up the hardware ready to run this demo.
 */
static void prvSetupHardware( void );

/*-----------------------------------------------------------*/

int main( void )
{
	prvSetupHardware();

	/* Create the queue. */
	xQueue = xQueueCreate( mainQUEUE_LENGTH, sizeof( unsigned long ) );
	configASSERT( xQueue );

	/* Start the two tasks as described at the top of this file. */
	xTaskCreate( prvQueueReceiveTask, ( const signed char * const ) "Rx", configMINIMAL_STACK_SIZE, NULL, configQUEUE_RECEIVE_TASK_PRIORITY, NULL );
	xTaskCreate( prvQueueSendTask, ( const signed char * const ) "TX", configMINIMAL_STACK_SIZE, NULL, configQUEUE_SEND_TASK_PRIORITY, NULL );

	/* Start the scheduler running running. */
	vTaskStartScheduler();

	/* If all is well the next line of code will not be reached as the
	scheduler will be running.  If the next line is reached then it is likely
	there was insufficient FreeRTOS heap available for the idle task and/or
	timer task to be created.  See http://www.freertos.org/a00111.html. */
	for( ;; );
}
/*-----------------------------------------------------------*/

static void prvQueueSendTask( void *pvParameters )
{
const unsigned long ulValueToSend = mainQUEUED_VALUE;

	/* Remove compiler warning about unused parameter. */
	( void ) pvParameters;

	for( ;; )
	{
		/* Place this task into the blocked state until it is time to run again.
		The kernel will place the MCU into the Retention low power sleep state
		when the idle task next runs. */
		vTaskDelay( mainTX_DELAY );

		/* Send to the queue - causing the queue receive task to flash its LED.
		It should not be necessary to block on the queue send because the Rx
		task will already have removed the last queued item. */
		xQueueSend( xQueue, &ulValueToSend, mainDONT_BLOCK );
	}
}
/*-----------------------------------------------------------*/

static void prvQueueReceiveTask( void *pvParameters )
{
unsigned long ulReceivedValue;

	/* Remove compiler warning about unused parameter. */
	( void ) pvParameters;

	for( ;; )
	{
		/* Wait until something arrives in the queue. */
		xQueueReceive( xQueue, &ulReceivedValue, portMAX_DELAY );

		/*  To get here something must have arrived, but is it the expected
		value?  If it is, turn the LED on for a short while. */
		if( ulReceivedValue == mainQUEUED_VALUE )
		{
			GPIO_HIGH( LD_GPIO_PORT, LD_GREEN_GPIO_PIN );
			vTaskDelay( mainLED_TOGGLE_DELAY );
			GPIO_LOW( LD_GPIO_PORT, LD_GREEN_GPIO_PIN );
		}
	}
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
/* GPIO, EXTI and NVIC Init structure declaration */
GPIO_InitTypeDef GPIO_InitStructure;
EXTI_InitTypeDef EXTI_InitStructure;
NVIC_InitTypeDef NVIC_InitStructure;
void SystemCoreClockUpdate( void );

	SystemCoreClockUpdate();

	/* Essential on STM32 Cortex-M devices. */
	NVIC_PriorityGroupConfig( NVIC_PriorityGroup_4 );

	/* Enable HSI Clock */
	RCC_HSICmd(ENABLE);

	/*!< Wait till HSI is ready */
	while( RCC_GetFlagStatus( RCC_FLAG_HSIRDY ) == RESET );

	/* Set HSI as sys clock*/
	RCC_SYSCLKConfig( RCC_SYSCLKSource_HSI );

	/* Set MSI clock range to ~4.194MHz*/
	RCC_MSIRangeConfig( RCC_MSIRange_6 );

	/* Enable the GPIOs clocks */
	RCC_AHBPeriphClockCmd( RCC_AHBPeriph_GPIOA | RCC_AHBPeriph_GPIOB | RCC_AHBPeriph_GPIOC| RCC_AHBPeriph_GPIOD| RCC_AHBPeriph_GPIOE| RCC_AHBPeriph_GPIOH, ENABLE );

	/* Enable comparator, PWR mngt clocks */
	RCC_APB1PeriphClockCmd( RCC_APB1Periph_COMP | RCC_APB1Periph_PWR,ENABLE );

	/* Enable ADC & SYSCFG clocks */
	RCC_APB2PeriphClockCmd( RCC_APB2Periph_SYSCFG , ENABLE );

	/* Allow access to the RTC */
	PWR_RTCAccessCmd( ENABLE );

	/* Reset RTC Backup Domain */
	RCC_RTCResetCmd( ENABLE );
	RCC_RTCResetCmd( DISABLE );

	/* LSE Enable */
	RCC_LSEConfig( RCC_LSE_ON );

	/* Wait until LSE is ready */
	while( RCC_GetFlagStatus( RCC_FLAG_LSERDY ) == RESET );

	/* RTC Clock Source Selection */
	RCC_RTCCLKConfig( RCC_RTCCLKSource_LSE );

	/* Enable the RTC */
	RCC_RTCCLKCmd( ENABLE );

	/* Disable HSE */
	RCC_HSEConfig( RCC_HSE_OFF );

	if( RCC_GetFlagStatus( RCC_FLAG_HSERDY ) != RESET )
	{
		/* Stay in infinite loop if HSE is not disabled*/
		while( 1 );
	}

	/* Set internal voltage regulator to 1.8V */
	PWR_VoltageScalingConfig( PWR_VoltageScaling_Range1 );

	/* Wait Until the Voltage Regulator is ready */
	while( PWR_GetFlagStatus( PWR_FLAG_VOS ) != RESET );

	/* Configure User Button pin as input */
	GPIO_InitStructure.GPIO_Pin = USERBUTTON_GPIO_PIN;
	GPIO_InitStructure.GPIO_Mode = GPIO_Mode_IN;
	GPIO_InitStructure.GPIO_PuPd = GPIO_PuPd_NOPULL;
	GPIO_InitStructure.GPIO_Speed = GPIO_Speed_40MHz;
	GPIO_Init( USERBUTTON_GPIO_PORT, &GPIO_InitStructure );

	/* Select User Button pin as input source for EXTI Line */
	SYSCFG_EXTILineConfig( EXTI_PortSourceGPIOA,EXTI_PinSource0 );

	/* Configure EXT1 Line 0 in interrupt mode trigged on Rising edge */
	EXTI_InitStructure.EXTI_Line = EXTI_Line0 ;  /* PA0 for User button AND IDD_WakeUP */
	EXTI_InitStructure.EXTI_Mode = EXTI_Mode_Interrupt;
	EXTI_InitStructure.EXTI_Trigger = EXTI_Trigger_Rising;
	EXTI_InitStructure.EXTI_LineCmd = ENABLE;
	EXTI_Init( &EXTI_InitStructure );

	/* Enable and set EXTI0 Interrupt to the lowest priority */
	NVIC_InitStructure.NVIC_IRQChannel = EXTI0_IRQn;
	NVIC_InitStructure.NVIC_IRQChannelPreemptionPriority = configLIBRARY_LOWEST_INTERRUPT_PRIORITY;
	NVIC_InitStructure.NVIC_IRQChannelSubPriority = 0;
	NVIC_InitStructure.NVIC_IRQChannelCmd = ENABLE;
	NVIC_Init( &NVIC_InitStructure );

	/* Configure the LED_pin as output push-pull for LD3 & LD4 usage */
	GPIO_InitStructure.GPIO_Pin = LD_GREEN_GPIO_PIN | LD_BLUE_GPIO_PIN;
	GPIO_InitStructure.GPIO_Mode = GPIO_Mode_OUT;
	GPIO_InitStructure.GPIO_OType = GPIO_OType_PP;
	GPIO_InitStructure.GPIO_PuPd = GPIO_PuPd_NOPULL;
	GPIO_InitStructure.GPIO_Speed = GPIO_Speed_2MHz;
	GPIO_Init( LD_GPIO_PORT, &GPIO_InitStructure );

	/* Force a low level on LEDs */
	GPIO_LOW( LD_GPIO_PORT, LD_GREEN_GPIO_PIN );
	GPIO_LOW( LD_GPIO_PORT, LD_BLUE_GPIO_PIN );
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

void vApplicationStackOverflowHook( xTaskHandle pxTask, signed char *pcTaskName )
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

void vApplicationTickHook( void )
{
	/* This function will be called by each tick interrupt if
	configUSE_TICK_HOOK is set to 1 in FreeRTOSConfig.h.  User code can be
	added here, but the tick hook is called from an interrupt context, so
	code must not attempt to block, and only the interrupt safe FreeRTOS API
	functions can be used (those that end in FromISR()). */
}
/*-----------------------------------------------------------*/

void vAssertCalled( void )
{
volatile unsigned long ul = 0;

	taskENTER_CRITICAL();
	{
		/* Set ul to a non-zero value using the debugger to step out of this
		function. */
		while( ul == 0 )
		{
			__asm volatile( "NOP" );
		}
	}
	taskEXIT_CRITICAL();
}


#if 0
/**
  ******************************************************************************
  * @file    main.c
  * @author  Microcontroller Division
  * @version V1.0.3
  * @date    May-2013
  * @brief   Main program body
  ******************************************************************************
  * @copy
  *
  * THE PRESENT FIRMWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS
  * WITH CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE
  * TIME. AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY
  * DIRECT, INDIRECT OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING
  * FROM THE CONTENT OF SUCH FIRMWARE AND/OR THE USE MADE BY CUSTOMERS OF THE
  * CODING INFORMATION CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
  *
  * <h2><center>&copy; COPYRIGHT 2011 STMicroelectronics</center></h2>
  */

/* Includes ------------------------------------------------------------------*/

#include "main.h"

#define BOR_MODIFY
#define BOR_LEVEL OB_BOR_OFF  /*!< BOR is disabled at power down, the reset is asserted when the VDD power supply reachs the PDR(Power Down Reset) threshold (1.5V) */


/* Private variables ---------------------------------------------------------*/

static TSL_tTick_ms_T last_tick_tsl;  /* Hold the last tsl time value */
extern unsigned char Bias_Current;    /* Bias Current stored in E²Prom used for ICC mesurement precision */
extern uint8_t t_bar[2];              /* LCD bar graph: used for displaying active function */
extern bool self_test;                /* Auto_test activation flag: set by interrupt handler if user button is pressed for a few seconds */
extern bool Idd_WakeUP;               /* */
extern volatile bool KeyPressed;      /* */
extern bool UserButton;               /* Set by interrupt handler to indicate that user button is pressed */
uint8_t state_machine;                /* Machine status used by main() wich indicats the active function, set by user button in interrupt handler */
uint16_t Int_CurrentSTBY;             /* */

#ifdef STM32L1XX_MDP
  uint8_t message[29] = "     ** 32L152CDISCOVERY  **";
	#else
	uint8_t message[29] = "     ** STM32L1-DISCOVERY **";
#endif
/*******************************************************************************/
/**
  * @brief main entry point.
  * @par Parameters None
  * @retval void None
  * @par Required preconditions: None
  */
int main(void)
{
  bool StanbyWakeUp ;
  float Current_STBY;
  __IO uint32_t BOROptionBytes = 0;

 /*!< At this stage the microcontroller clock setting is already configured,
       this is done through SystemInit() function which is called from startup
       file (startup_stm32l1xx_md.s) before to branch to application main.
       To reconfigure the default setting of SystemInit() function, refer to
       system_stm32l1xx.c file
     */

  /* store Standby Current*/
  Int_CurrentSTBY = Current_Measurement();

  /* Check if the StandBy flag is set */
  if (PWR_GetFlagStatus(PWR_FLAG_SB) != RESET)
  {
    /* System resumed from STANDBY mode */
    /* Clear StandBy flag */
    RCC_APB1PeriphClockCmd(RCC_APB1Periph_PWR,ENABLE);
    PWR_ClearFlag(PWR_FLAG_SB);
    /* set StandbyWakeup indicator*/
    StanbyWakeUp = TRUE;
  } else
  {
    /* Reset StandbyWakeup indicator*/
    StanbyWakeUp = FALSE;
  }

	#ifdef BOR_MODIFY
  /* Get BOR Option Bytes */
  BOROptionBytes = FLASH_OB_GetBOR();

  if((BOROptionBytes & 0x0F) != BOR_LEVEL)
  {
    /* Unlocks the option bytes block access */
    FLASH_OB_Unlock();

    /* Clears the FLASH pending flags */
    FLASH_ClearFlag(FLASH_FLAG_EOP|FLASH_FLAG_WRPERR | FLASH_FLAG_PGAERR
                  | FLASH_FLAG_SIZERR | FLASH_FLAG_OPTVERR);

    /* Select the desired V(BOR) Level ---------------------------------------*/
    FLASH_OB_BORConfig(BOR_LEVEL);

    /* Launch the option byte loading */
    FLASH_OB_Launch();
  }
#endif

  /* Configure Clocks for Application need */
  RCC_Configuration();

  /* Set internal voltage regulator to 1.8V */
  PWR_VoltageScalingConfig(PWR_VoltageScaling_Range1);

  /* Wait Until the Voltage Regulator is ready */
  while (PWR_GetFlagStatus(PWR_FLAG_VOS) != RESET) ;

  /* Init I/O ports */
  Init_GPIOs();

  /* Initializes ADC */
  ADC_Icc_Init();

  /* Enable General interrupts */
  enableGlobalInterrupts();

  /* Init Touch Sensing configuration */
  TSL_user_Init();

  /* Initializes the LCD glass */
  LCD_GLASS_Init();

  /* Reset Keypressed flag used in interrupt and Scrollsentence */
  KeyPressed = FALSE;

  /* user button actif */
  UserButton = TRUE;

  /* Check if User button press at Power ON  */
  if ((USERBUTTON_GPIO_PORT->IDR & USERBUTTON_GPIO_PIN) != 0x0)
  {
    /* Measure operational amplifier bias current and store value in E²Prom for application need*/
    Bias_measurement();
  }

  /* Standard application startup */
  if ( !StanbyWakeUp )
  {
    /* Reset autotest flag stored in memory */
    AUTOTEST(FALSE) ;

		/* Display Welcome message */
    LCD_GLASS_ScrollSentence(message,1,SCROLL_SPEED);
    if (!KeyPressed)
    {
       /* if welcome message not skipped Display blinking message JP1 ON*/
      LCD_BlinkConfig(LCD_BlinkMode_AllSEG_AllCOM,LCD_BlinkFrequency_Div512);
      LCD_GLASS_DisplayString("JP1 ON");
      TEMPO;
      TEMPO;
      TEMPO;
      TEMPO;
      LCD_BlinkConfig(LCD_BlinkMode_Off,LCD_BlinkFrequency_Div32);
    }
  /* Wake up from Standby or autotest */
  }  else  {
    /*Check Autotest value stored in flash to get wakeup context*/
    if (self_test)
    {
      /* Wake UP: Return of RESET by Auto test */
      auto_test_part2();
    } else {
      /* Wake UP: Return of RESET by Current STAND BY measurement */
      LCD_GLASS_ScrollSentence("     STANDBY WAKEUP",1,SCROLL_SPEED);
      /* Substract bias current from operational amplifier*/
      if ( Int_CurrentSTBY > Bias_Current )
        Int_CurrentSTBY -= Bias_Current;
      Current_STBY = Int_CurrentSTBY * Vdd_appli()/ADC_CONV;
      Current_STBY *= 20L;
      display_MuAmp((uint32_t)Current_STBY);
      /* Wait for user button press to continue */
      while(!KeyPressed);
    }
  }
  /* Reset KeyPress Flag */
  KeyPressed = FALSE;
  /* Clear LCD bars */
  BAR0_OFF;
  BAR1_OFF;
  BAR2_OFF;
  BAR3_OFF;
  /* Switch off the leds*/
  GPIO_HIGH(LD_GPIO_PORT,LD_GREEN_GPIO_PIN);
  GPIO_LOW(LD_GPIO_PORT,LD_BLUE_GPIO_PIN);
  /* Set application state machine to VREF state  */
  state_machine = STATE_VREF ;
  /*Until application reset*/
  while (1)
  {
  /* run autotest if requested by the user */
    if (self_test)
      auto_test();
    /* Perform Actions depending on current application State  */
    switch (state_machine)
    {
        /* VREF State : Display VRef value */
        case STATE_VREF:
          GPIO_TOGGLE(LD_GPIO_PORT,LD_BLUE_GPIO_PIN);
          GPIO_TOGGLE(LD_GPIO_PORT,LD_GREEN_GPIO_PIN);
          Vref_measure();
          TEMPO ;
        break;

        /* Slider Value State : Display the TS slider value */
        case STATE_SLIDER_VALUE:

        // Execute STMTouch Driver state machine
        if (TSL_user_Action() == TSL_STATUS_OK)
          {
            ProcessSensors(); // Execute sensors related tasks
          }
        break;

        /* Slider button State : Display the curent TS button pressed  */
        case STATE_SLIDER_BUTTON:
        // Execute STMTouch Driver state machine
        if (TSL_user_Action() == TSL_STATUS_OK)
          {
            ProcessSensorsButtons(); // Execute sensors related tasks
          }
          break;

        /* ICC RUN State : ICC mesurements in Run and Sleep modes   */
        case STATE_ICC_RUN:
          LCD_GLASS_DisplayString(" RUN  ");
          TEMPO;
          Icc_RUN();
          TEMPO;
          TEMPO;
          TEMPO;
          TEMPO;
          LCD_GLASS_DisplayString(" SLEEP ");
          TEMPO;
          Icc_SLEEP();
          TEMPO;
          TEMPO;
          TEMPO;
          TEMPO;
        break;

        /* ICC LOW POWER RUN State : ICC mesurements in LowPower run and LowPower Sleep modes */
        case STATE_ICC_LP_RUN:
          LCD_GLASS_DisplayString("LP RUN");
          TEMPO;
          Icc_LPRUN();
          TEMPO;
          TEMPO;
          TEMPO;
          TEMPO;
          LCD_GLASS_DisplayString("LP SLP");
          TEMPO;
          Icc_LPSLEEP();
          TEMPO;
          TEMPO;
          TEMPO;
          TEMPO;
        break;

        /* ICC STOP  State : ICC mesurements in Stop and STOP NoRTC modes */
        case STATE_ICC_STOP:
          LCD_GLASS_DisplayString(" STOP ");
          TEMPO;
          Icc_STOP();
          TEMPO;
          TEMPO;
          TEMPO;
          TEMPO;
          LCD_GLASS_DisplayString("SP-NRTC");
          TEMPO;
          Icc_Stop_NoRTC();
          TEMPO;
          TEMPO;
          TEMPO;
          TEMPO;
          break;

        /* ICC Standby  State : ICC mesurements in Standby mode */
        case STATE_ICC_STBY:
          LCD_GLASS_DisplayString("STBY  ");
          TEMPO;
          TEMPO;
        ADC_Icc_Test(MCU_STBY);
        /* Following break never performed dues to software reset in previous function */
        break;

        /* for safe: normaly never reaches */
        default:
          LCD_GLASS_Clear();
          LCD_GLASS_DisplayString("ERROR");
        break;
      }
      /* Reset KeyPress flag*/
      KeyPressed = FALSE;
    }
}

/**
  * @brief  Configures the different system clocks.
  * @param  None
  * @retval None
  */
void RCC_Configuration(void)
{
  /* Enable HSI Clock */
  RCC_HSICmd(ENABLE);

  /*!< Wait till HSI is ready */
  while (RCC_GetFlagStatus(RCC_FLAG_HSIRDY) == RESET);

  /* Set HSI as sys clock*/
  RCC_SYSCLKConfig(RCC_SYSCLKSource_HSI);

  /* Set MSI clock range to ~4.194MHz*/
  RCC_MSIRangeConfig(RCC_MSIRange_6);

  /* Enable the GPIOs clocks */
  RCC_AHBPeriphClockCmd(RCC_AHBPeriph_GPIOA | RCC_AHBPeriph_GPIOB | RCC_AHBPeriph_GPIOC| RCC_AHBPeriph_GPIOD| RCC_AHBPeriph_GPIOE| RCC_AHBPeriph_GPIOH, ENABLE);

  /* Enable comparator, LCD and PWR mngt clocks */
  RCC_APB1PeriphClockCmd(RCC_APB1Periph_COMP | RCC_APB1Periph_LCD | RCC_APB1Periph_PWR,ENABLE);

  /* Enable ADC & SYSCFG clocks */
  RCC_APB2PeriphClockCmd(RCC_APB2Periph_ADC1 | RCC_APB2Periph_SYSCFG , ENABLE);

  /* Allow access to the RTC */
  PWR_RTCAccessCmd(ENABLE);

  /* Reset RTC Backup Domain */
  RCC_RTCResetCmd(ENABLE);
  RCC_RTCResetCmd(DISABLE);

  /* LSE Enable */
  RCC_LSEConfig(RCC_LSE_ON);

  /* Wait until LSE is ready */
  while (RCC_GetFlagStatus(RCC_FLAG_LSERDY) == RESET);

   /* RTC Clock Source Selection */
  RCC_RTCCLKConfig(RCC_RTCCLKSource_LSE);

  /* Enable the RTC */
  RCC_RTCCLKCmd(ENABLE);

  /*Disable HSE*/
  RCC_HSEConfig(RCC_HSE_OFF);
  if(RCC_GetFlagStatus(RCC_FLAG_HSERDY) != RESET )
  {
    /* Stay in infinite loop if HSE is not disabled*/
    while(1);
  }
}

/**
  * @brief  To initialize the I/O ports
  * @caller main
  * @param None
  * @retval None
  */
void  Init_GPIOs (void)
{
  /* GPIO, EXTI and NVIC Init structure declaration */
  GPIO_InitTypeDef GPIO_InitStructure;
  EXTI_InitTypeDef EXTI_InitStructure;
  NVIC_InitTypeDef NVIC_InitStructure;

  /* Configure User Button pin as input */
  GPIO_InitStructure.GPIO_Pin = USERBUTTON_GPIO_PIN;
  GPIO_InitStructure.GPIO_Mode = GPIO_Mode_IN;
  GPIO_InitStructure.GPIO_PuPd = GPIO_PuPd_NOPULL;
  GPIO_InitStructure.GPIO_Speed = GPIO_Speed_40MHz;
  GPIO_Init(USERBUTTON_GPIO_PORT, &GPIO_InitStructure);

  /* Select User Button pin as input source for EXTI Line */
  SYSCFG_EXTILineConfig(EXTI_PortSourceGPIOA,EXTI_PinSource0);

  /* Configure EXT1 Line 0 in interrupt mode trigged on Rising edge */
  EXTI_InitStructure.EXTI_Line = EXTI_Line0 ;  // PA0 for User button AND IDD_WakeUP
  EXTI_InitStructure.EXTI_Mode = EXTI_Mode_Interrupt;
  EXTI_InitStructure.EXTI_Trigger = EXTI_Trigger_Rising;
  EXTI_InitStructure.EXTI_LineCmd = ENABLE;
  EXTI_Init(&EXTI_InitStructure);

  /* Enable and set EXTI0 Interrupt to the lowest priority */
  NVIC_InitStructure.NVIC_IRQChannel = EXTI0_IRQn ;
  NVIC_InitStructure.NVIC_IRQChannelPreemptionPriority = 0x0F;
  NVIC_InitStructure.NVIC_IRQChannelSubPriority = 0x0F;
  NVIC_InitStructure.NVIC_IRQChannelCmd = ENABLE;
  NVIC_Init(&NVIC_InitStructure);

  /* Configure the LED_pin as output push-pull for LD3 & LD4 usage*/
  GPIO_InitStructure.GPIO_Pin = LD_GREEN_GPIO_PIN | LD_BLUE_GPIO_PIN;
  GPIO_InitStructure.GPIO_Mode = GPIO_Mode_OUT;
  GPIO_InitStructure.GPIO_OType = GPIO_OType_PP;
  GPIO_InitStructure.GPIO_PuPd = GPIO_PuPd_NOPULL;
  GPIO_InitStructure.GPIO_Speed = GPIO_Speed_2MHz;
  GPIO_Init(LD_GPIO_PORT, &GPIO_InitStructure);

  /* Force a low level on LEDs*/
  GPIO_LOW(LD_GPIO_PORT,LD_GREEN_GPIO_PIN);
  GPIO_LOW(LD_GPIO_PORT,LD_BLUE_GPIO_PIN);

/* Counter enable: GPIO set in output for enable the counter */
  GPIO_InitStructure.GPIO_Pin = CTN_CNTEN_GPIO_PIN;
  GPIO_Init( CTN_GPIO_PORT, &GPIO_InitStructure);

/* To prepare to start counter */
  GPIO_HIGH(CTN_GPIO_PORT,CTN_CNTEN_GPIO_PIN);

/* Configure Port A LCD Output pins as alternate function */
  GPIO_InitStructure.GPIO_Pin = GPIO_Pin_1 | GPIO_Pin_2 | GPIO_Pin_3 | GPIO_Pin_8 | GPIO_Pin_9 |GPIO_Pin_10 |GPIO_Pin_15;
  GPIO_InitStructure.GPIO_Mode = GPIO_Mode_AF;
  GPIO_Init( GPIOA, &GPIO_InitStructure);

/* Select LCD alternate function for Port A LCD Output pins */
  GPIO_PinAFConfig(GPIOA, GPIO_PinSource1,GPIO_AF_LCD) ;
  GPIO_PinAFConfig(GPIOA, GPIO_PinSource2,GPIO_AF_LCD) ;
  GPIO_PinAFConfig(GPIOA, GPIO_PinSource3,GPIO_AF_LCD) ;
  GPIO_PinAFConfig(GPIOA, GPIO_PinSource8,GPIO_AF_LCD) ;
  GPIO_PinAFConfig(GPIOA, GPIO_PinSource9,GPIO_AF_LCD) ;
  GPIO_PinAFConfig(GPIOA, GPIO_PinSource10,GPIO_AF_LCD) ;
  GPIO_PinAFConfig(GPIOA, GPIO_PinSource15,GPIO_AF_LCD) ;

  /* Configure Port B LCD Output pins as alternate function */
  GPIO_InitStructure.GPIO_Pin = GPIO_Pin_3 | GPIO_Pin_4 | GPIO_Pin_5 | GPIO_Pin_8 | GPIO_Pin_9 \
                                 | GPIO_Pin_10 | GPIO_Pin_11 | GPIO_Pin_12 | GPIO_Pin_13 | GPIO_Pin_14 | GPIO_Pin_15;
  GPIO_InitStructure.GPIO_Mode = GPIO_Mode_AF;
  GPIO_Init( GPIOB, &GPIO_InitStructure);

  /* Select LCD alternate function for Port B LCD Output pins */
  GPIO_PinAFConfig(GPIOB, GPIO_PinSource3,GPIO_AF_LCD) ;
  GPIO_PinAFConfig(GPIOB, GPIO_PinSource4,GPIO_AF_LCD) ;
  GPIO_PinAFConfig(GPIOB, GPIO_PinSource5,GPIO_AF_LCD) ;
  GPIO_PinAFConfig(GPIOB, GPIO_PinSource8,GPIO_AF_LCD) ;
  GPIO_PinAFConfig(GPIOB, GPIO_PinSource9,GPIO_AF_LCD) ;
  GPIO_PinAFConfig(GPIOB, GPIO_PinSource10,GPIO_AF_LCD) ;
  GPIO_PinAFConfig(GPIOB, GPIO_PinSource11,GPIO_AF_LCD) ;
  GPIO_PinAFConfig(GPIOB, GPIO_PinSource12,GPIO_AF_LCD) ;
  GPIO_PinAFConfig(GPIOB, GPIO_PinSource13,GPIO_AF_LCD) ;
  GPIO_PinAFConfig(GPIOB, GPIO_PinSource14,GPIO_AF_LCD) ;
  GPIO_PinAFConfig(GPIOB, GPIO_PinSource15,GPIO_AF_LCD) ;

  /* Configure Port C LCD Output pins as alternate function */
  GPIO_InitStructure.GPIO_Pin = GPIO_Pin_0 | GPIO_Pin_1 | GPIO_Pin_2 | GPIO_Pin_3 | GPIO_Pin_6 \
                                 | GPIO_Pin_7 | GPIO_Pin_8 | GPIO_Pin_9 | GPIO_Pin_10 |GPIO_Pin_11 ;
  GPIO_InitStructure.GPIO_Mode = GPIO_Mode_AF;
  GPIO_Init( GPIOC, &GPIO_InitStructure);

  /* Select LCD alternate function for Port B LCD Output pins */
  GPIO_PinAFConfig(GPIOC, GPIO_PinSource0,GPIO_AF_LCD) ;
  GPIO_PinAFConfig(GPIOC, GPIO_PinSource1,GPIO_AF_LCD) ;
  GPIO_PinAFConfig(GPIOC, GPIO_PinSource2,GPIO_AF_LCD) ;
  GPIO_PinAFConfig(GPIOC, GPIO_PinSource3,GPIO_AF_LCD) ;
  GPIO_PinAFConfig(GPIOC, GPIO_PinSource6,GPIO_AF_LCD) ;
  GPIO_PinAFConfig(GPIOC, GPIO_PinSource7,GPIO_AF_LCD) ;
  GPIO_PinAFConfig(GPIOC, GPIO_PinSource8,GPIO_AF_LCD) ;
  GPIO_PinAFConfig(GPIOC, GPIO_PinSource9,GPIO_AF_LCD) ;
  GPIO_PinAFConfig(GPIOC, GPIO_PinSource10,GPIO_AF_LCD) ;
  GPIO_PinAFConfig(GPIOC, GPIO_PinSource11,GPIO_AF_LCD) ;

  /* Configure ADC (IDD_MEASURE) pin as Analogue */
  GPIO_InitStructure.GPIO_Pin = IDD_MEASURE  ;
  GPIO_InitStructure.GPIO_Mode = GPIO_Mode_AN;
  GPIO_Init( IDD_MEASURE_PORT, &GPIO_InitStructure);
}


/**
  * @brief  Executed when a sensor is in Error state
  * @param  None
  * @retval None
  */
void MyLinRots_ErrorStateProcess(void)
{
  // Add here your own processing when a sensor is in Error state
  TSL_linrot_SetStateOff();
}


/**
  * @brief  Executed when a sensor is in Off state
  * @param  None
  * @retval None
  */
void MyLinRots_OffStateProcess(void)
{
  // Add here your own processing when a sensor is in Off state
}



/**
  * @brief  Inserts a delay time.
  * @param  nTime: specifies the delay time length, in 1 ms.
  * @retval None
  */
void Delay(uint32_t nTime)
{
  while (TSL_tim_CheckDelay_ms((TSL_tTick_ms_T) nTime, &last_tick_tsl) != TSL_STATUS_OK);
}


#ifdef  USE_FULL_ASSERT

/**
  * @brief  Reports the name of the source file and the source line number
  *         where the assert_param error has occurred.
  * @param  file: pointer to the source file name
  * @param  line: assert_param error line source number
  * @retval None
  */
void assert_failed(uint8_t* file, uint32_t line)
{
  /* User can add his own implementation to report the file name and line number,
     ex: printf("Wrong parameters value: file %s on line %d\r\n", file, line) */
  /* Infinite loop */
  while (1);
}

#endif

void vApplicationStackOverflowHook( void )
{
}

/******************* (C) COPYRIGHT 2011 STMicroelectronics *****END OF FILE****/

#endif

