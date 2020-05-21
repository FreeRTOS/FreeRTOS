#include "FreeRTOS.h"

#include "unity_fixture.h"
#include "unity_internals.h"

int main( void )
{
	UNITY_BEGIN();

	RUN_TEST_GROUP( Full_FREERTOS_TCP );

	UNITY_END();
}
