#include <stdint.h>
#include <soc.h>
#include <csi_core.h>

extern void CORET_IRQHandler(void);
extern void Default_handler(void);
extern void console_init();
void (*g_irqvector[32])(void);

void irq_vectors_init(void)
{
    int i;

    for (i = 0; i < 32; i++) {
        g_irqvector[i] = Default_handler;
    }

    g_irqvector[CORET_IRQn] = CORET_IRQHandler;
}
 
 
#define CONFIG_SYSTICK_HZ 100
#define CONFIG_SYSTEM_FREQ 24000000
 
void  SystemInit(void) 
{
	irq_vectors_init();
	drv_coret_config(CONFIG_SYSTEM_FREQ / CONFIG_SYSTICK_HZ, CORET_IRQn);    //10ms
    drv_nvic_enable_irq(CORET_IRQn);
	
	console_init();
    return;
}
