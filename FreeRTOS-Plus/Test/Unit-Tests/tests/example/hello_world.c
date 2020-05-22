#include "hello_world.h"
#include "some_value.h"

int8_t average(int8_t value1, int8_t value2, int8_t value3)
{
	return (int8_t)( ( (int16_t)value1 + (int16_t)value2 + (int16_t)value3) / 3 );
}

int Print_Hello_world( void )
{
	int32_t value;
        value = some_number();
	return printf("Hello World! %d\n",  value);
}
