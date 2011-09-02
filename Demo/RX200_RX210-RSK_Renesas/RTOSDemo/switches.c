/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

#include "iodefine.h"

extern xQueueHandle SwitchQueue;

// IRQ1
#pragma interrupt (Excep_IRQ1(vect=65))
void Excep_IRQ1(void);

// IRQ3
#pragma interrupt (Excep_IRQ3(vect=67))
void Excep_IRQ3(void);

// IRQ4
#pragma interrupt (Excep_IRQ4(vect=68))
void Excep_IRQ4(void);



void SwitchSetup(void)
{
	/* Configure SW 1-3 pin settings */
    PORT3.PDR.BIT.B1 = 0;		/* Switch 1 - Port 3.1 - IRQ1 */
    PORT3.PDR.BIT.B3 = 0;		/* Switch 2 - Port 3.3 - IRQ3 */
    PORT3.PDR.BIT.B4 = 0;		/* Switch 3 - Port 3.4 - IRQ4 */

	PORT3.PMR.BIT.B1 = 1;
	PORT3.PMR.BIT.B3 = 1;
	PORT3.PMR.BIT.B4 = 1;
	
	MPC.PWPR.BIT.B0WI = 0;		// Writing to the PFSWE bit is enabled
	MPC.PWPR.BIT.PFSWE = 1;		// Writing to the PFS register is enabled
	MPC.P31PFS.BIT.ISEL = 1;
	MPC.P33PFS.BIT.ISEL = 1;
	MPC.P34PFS.BIT.ISEL = 1;

	/* IRQ1	*/
	ICU.IER[0x08].BIT.IEN1 = 1;	
	ICU.IPR[65].BIT.IPR = configMAX_SYSCALL_INTERRUPT_PRIORITY - 1;
	ICU.IR[65].BIT.IR = 0;
	ICU.IRQCR[1].BIT.IRQMD = 1;	// falling edge
	
	/* IRQ3	*/
	ICU.IER[0x08].BIT.IEN3 = 1;	
	ICU.IPR[67].BIT.IPR = configMAX_SYSCALL_INTERRUPT_PRIORITY - 1;
	ICU.IR[67].BIT.IR = 0;
	ICU.IRQCR[3].BIT.IRQMD = 1;	// falling edge

	/* IRQ4	*/
	ICU.IER[0x08].BIT.IEN4 = 1;	
	ICU.IPR[68].BIT.IPR = configMAX_SYSCALL_INTERRUPT_PRIORITY - 1;
	ICU.IR[68].BIT.IR = 0;
	ICU.IRQCR[4].BIT.IRQMD = 1;	// falling edge
	
}

void Excep_IRQ1(void)
{
	portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;
	static portTickType PreviousCount = 0;
	portTickType CurrentCount;
	static unsigned char ID_Switch1 = 1;
	
	CurrentCount = xTaskGetTickCount();
	
	if( (CurrentCount - PreviousCount) > (125 / portTICK_RATE_MS) )
	{
		xQueueSendToBackFromISR( SwitchQueue, &ID_Switch1, &xHigherPriorityTaskWoken);
	}
	PreviousCount = CurrentCount;
    portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
}

void Excep_IRQ3(void)
{
	static portTickType PreviousCount = 0;
	portTickType CurrentCount;

	portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;
	static unsigned char ID_Switch2 = 2;

	CurrentCount = xTaskGetTickCount();
	
	if( (CurrentCount - PreviousCount) > (250 / portTICK_RATE_MS) )
	{
		xQueueSendToBackFromISR( SwitchQueue, &ID_Switch2, &xHigherPriorityTaskWoken);
	}
	PreviousCount = CurrentCount;
    portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
}

void Excep_IRQ4(void)
{
	static portTickType PreviousCount = 0;
	portTickType CurrentCount;

	portBASE_TYPE xHigherPriorityTaskWoken = pdFALSE;
	static unsigned char ID_Switch3 = 3;
	
	CurrentCount = xTaskGetTickCount();
	
	if( (CurrentCount - PreviousCount) > (125 / portTICK_RATE_MS) )
	{
		xQueueSendToBackFromISR( SwitchQueue, &ID_Switch3, &xHigherPriorityTaskWoken);
	}
	PreviousCount = CurrentCount;
    portYIELD_FROM_ISR( xHigherPriorityTaskWoken );
}