
void main(void)
{
unsigned long i = 0;

	for( ;; )
	{
		i++;
	}
}

void vApplicationSetupTimerInterrupt( void )
{
}

void vApplicationMallocFailedHook( void )
{
	for( ;; );
}

void vApplicationStackOverflowHook( void )
{
}

void vApplicationIdleHook( void )
{
}




