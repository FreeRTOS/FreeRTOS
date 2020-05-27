/* Include Unity header */
#include <unity.h>

/* Include standard libraries */
#include <stdlib.h>
#include <string.h>

#include "mock_some_value.h"

/* Include header file(s) which have declaration 
 * of functions under test */
#include "hello_world.h"

void test_average_normal( void )
{
    int8_t result;

    /* Check normal operation */
    result = average(4, 5, 6);
    TEST_ASSERT_EQUAL_INT(5, result);

    /* Check whether the buffer used to store
     * intermediate result overflows or not */
    result = average(255, 255, 255);
    TEST_ASSERT_EQUAL_INT(-1, result);

}

void test_average_round_off( void )
{
    int8_t result;

    /* Check the round off value */
    result = average(1, 2, 2);
    TEST_ASSERT_EQUAL_INT(1, result);
}

void test_Print_Hello_world( void )
{
    int32_t result;

    /* check how the Printf returns the value */
    some_number_ExpectAndReturn( 5 );
    result = Print_Hello_world();
    TEST_ASSERT_EQUAL_INT(15, result);
}
