// Copyright (c) 2019, XMOS Ltd, All rights reserved

#include <platform.h>

#include "rtos_printf.h"
#include "testing_main.h"

extern "C" {
int c_main( int tile, chanend xTile0Chan, chanend xTile1Chan, chanend xTile2Chan, chanend xTile3Chan );
}

void xctask1(void)
{
	rtos_printf("xc task 1 on core %u\n", get_logical_core_id());
	for (;;);
}

void xctask2(void)
{
	rtos_printf("xc task 2 on core %u\n", get_logical_core_id());
	for (;;);
}

int main(void)
{
	chan c_t0_t1;

	par {
		on tile[0]:
		{
			par {
#if ( testingmainENABLE_XC_TASKS == 1 )
				xctask1();
#endif
				c_main( 0, null, c_t0_t1, null, null );
			}
		}
#if ( testingmainNUM_TILES > 1 )
		on tile[1]:
		{
			par {
#if ( testingmainENABLE_XC_TASKS == 1 )
				xctask2();
#endif
				c_main( 1, c_t0_t1, null, null, null );
			}
		}
#endif
	}
	return 0;
}
