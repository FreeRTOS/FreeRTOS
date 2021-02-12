
#include "FreeRTOS.h"
#include "timers.h"

#include "unity.h"
#include "unity_fixture.h"

TEST_GROUP( Timers );

TEST_SETUP( Timers )
{}

TEST_TEAR_DOWN( Timers )
{}

TEST_GROUP_RUNNER( Timers )
{
    RUN_TEST_CASE( Timers, TimerHappyPath );
}

TEST( Timers, TimerHappyPath )
{
    TEST_ASSERT( 1 );
}