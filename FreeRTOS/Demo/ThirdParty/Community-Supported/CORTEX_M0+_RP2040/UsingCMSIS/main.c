/* Kernel includes. */
#include "FreeRTOS.h" /* Must come first. */
#include "task.h"     /* RTOS task related API prototypes. */
#include "timers.h"   /* Software timer related API prototypes. */
#include <stdio.h>
#include "pico/stdlib.h"
#include "RP2040.h"   /* CMSIS Header for RP2040 */

#define mainTASK_PRIORITY     ( tskIDLE_PRIORITY + 1 )

/*-----------------------------------------------------------*/

/*
 * Implement this function for any hardware specific clock configuration
 * that was not already performed before main() was called.
 */
static void prvSetupHardware( void );

/*
 * The main task
 */
static void prvMainTask( void *pvParameters );

/*
 * The blink task
 */
static void prvBlinkTask( void *pvParameters );

int main(void) {
    TimerHandle_t xExampleSoftwareTimer = NULL;

    /* Configure the system ready to run the demo.  The clock configuration
    can be done here if it was not done before main() was called. */
    prvSetupHardware();

    /* Create the main task */
    xTaskCreate(     /* The function that implements the task. */
            prvMainTask,
            /* Text name for the task, just to help debugging. */
            "main",
            /* The size (in words) of the stack that should be created
            for the task. */
            configMINIMAL_STACK_SIZE,
            /* A parameter that can be passed into the task.  Not used
            in this simple demo. */
            NULL,
            /* The priority to assign to the task.  tskIDLE_PRIORITY
            (which is 0) is the lowest priority.  configMAX_PRIORITIES - 1
            is the highest priority. */
            mainTASK_PRIORITY,
            /* Used to obtain a handle to the created task.  Not used in
            this simple demo, so set to NULL. */
            NULL);

    /* Create the blink task */
    xTaskCreate(     /* The function that implements the task. */
            prvBlinkTask,
            /* Text name for the task, just to help debugging. */
            "blink",
            /* The size (in words) of the stack that should be created
            for the task. */
            configMINIMAL_STACK_SIZE,
            /* A parameter that can be passed into the task.  Not used
            in this simple demo. */
            NULL,
            /* The priority to assign to the task.  tskIDLE_PRIORITY
            (which is 0) is the lowest priority.  configMAX_PRIORITIES - 1
            is the highest priority. */
            mainTASK_PRIORITY,
            /* Used to obtain a handle to the created task.  Not used in
            this simple demo, so set to NULL. */
            NULL);


    vTaskStartScheduler();

    /* should never reach here */
    panic_unsupported();
}
/*-----------------------------------------------------------*/

static void prvBlinkTask( void *pvParameters )
{
    for( ;; )
    {
        vTaskDelay(pdMS_TO_TICKS( 500 ));
        gpio_put(PICO_DEFAULT_LED_PIN, !gpio_get(PICO_DEFAULT_LED_PIN));
    }
}

#include "hardware/irq.h"
static void prvMainTask( void *pvParameters )
{
    for( ;; )
    {
        vTaskDelay(pdMS_TO_TICKS( 3000 ));
        puts("Disabling SysTick interrupt via CMSIS");
        SysTick->CTRL &= ~SysTick_CTRL_TICKINT_Msk;
        busy_wait_ms(3000); // pause
        SysTick->CTRL |= SysTick_CTRL_TICKINT_Msk;
        puts("Enabled SysTick interrupt via CMSIS");
    }
}
/*-----------------------------------------------------------*/

static void prvSetupHardware( void )
{
    /* Want to be able to printf */
    stdio_init_all();
    /* And flash LED */
    gpio_init(PICO_DEFAULT_LED_PIN);
    gpio_set_dir(PICO_DEFAULT_LED_PIN, GPIO_OUT);
}