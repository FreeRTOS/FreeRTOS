#include <stddef.h>                     // For NULL
#include "FreeRTOSConfig_Template.h"
#include "task.h"

/* Blink Task */
void BlinkTask(void *pvParameters)
{
    (void) pvParameters;  // Avoid unused parameter warning

    while(1)
    {
        // toggle LED here (pseudo-code)
        // HAL_GPIO_TogglePin(GPIOx, GPIO_PIN_y);
        vTaskDelay(pdMS_TO_TICKS(500));
    }
}

int main(void)
{
    // Initialize hardware
    SystemInit();

    // Create Blink task
    xTaskCreate(BlinkTask, "Blink", configMINIMAL_STACK_SIZE, NULL, 1, NULL);

    // Start FreeRTOS scheduler
    vTaskStartScheduler();

    while(1); // Should never reach here
}
