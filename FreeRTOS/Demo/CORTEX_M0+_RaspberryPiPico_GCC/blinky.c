#include <FreeRTOS.h>
#include <task.h>

#include "gpio.h"

static void prvBlinkyTask( void *pvParameters );

#define LED_PIN 25
#define blinkyTASK_PRIORITY         ( tskIDLE_PRIORITY + 1 )
#define TASK_DELAY  1000

int main()
{
    gpio_init( LED_PIN );
    gpio_set_dir( LED_PIN, GPIO_OUT );
    xTaskCreate( prvBlinkyTask,
                 "PicoBlinky",
                 configMINIMAL_STACK_SIZE,
                 NULL,
                 blinkyTASK_PRIORITY,
                 NULL );
    vTaskStartScheduler();

    for( ;; );
}

static void prvBlinkyTask( void *pvParameters )
{
    while(1) {
        gpio_put( LED_PIN, 1 );
        vTaskDelay( TASK_DELAY );
        gpio_put( LED_PIN, 0 );
        vTaskDelay( TASK_DELAY );
    }
}
