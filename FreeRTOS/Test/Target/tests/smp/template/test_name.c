/*
 * FreeRTOS V202212.00
 * Copyright (C) 2022 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

/**
 * @file test.c
 * @brief Describe the test here briefly.
 *
 * Describe the test here in detail.
 */

/* Kernel includes. */
#include "FreeRTOS.h"
#include "task.h"

/*-----------------------------------------------------------*/

#ifndef TEST_CONFIG_H
    #error test_config.h must be included at the end of FreeRTOSConfig.h.
#endif

/* Include test_setting_config.h here if the target needs to override any of
 * the test framework macros defined in test_default_setting_config.h, e.g.
 * to use a test framework other than Unity. Set configTARGET_TEST_USE_CUSTOM_SETTING
 * to 1 in the target's FreeRTOSConfig.h to enable this. */
#if ( configTARGET_TEST_USE_CUSTOM_SETTING == 1 )
    #include "test_setting_config.h"
#endif

/* Fills in the default test framework macros, e.g. testBEGIN_FUNCTION, for
 * any that were not overridden above. */
#include "test_default_setting_config.h"

/*-----------------------------------------------------------*/

#if ( configNUMBER_OF_CORES < 2 )
    #error This test is for FreeRTOS SMP and therefore, requires at least 2 cores.
#endif

/*-----------------------------------------------------------*/

/* Declare #defines used in this file here. */

/*-----------------------------------------------------------*/

/* Declare local functions used in this file here. */

/*-----------------------------------------------------------*/

/* Declare local variables used in this file here. */

/*-----------------------------------------------------------*/

/* Runs before every test, put init calls here. */
testSETUP_FUNCTION_PROTOTYPE( setUp )
{
    /* Create FreeRTOS resources required for the test. */
}
/*-----------------------------------------------------------*/

/* Runs after every test, put clean-up calls here. */
testTEARDOWN_FUNCTION_PROTOTYPE( tearDown )
{
    /* Delete all the FreeRTOS resources created in setUp. */
}
/*-----------------------------------------------------------*/

void Test_TestCaseName( void )
{
    /* Perform any API call needed for the test. */

    /* Verify the result. */
}
/*-----------------------------------------------------------*/

/* Function that runs the test case. This function must be called
 * from a FreeRTOS task. */
testENTRY_FUNCTION_PROTOTYPE( vRunTestCaseName )
{
    testBEGIN_FUNCTION();

    testRUN_TEST_CASE_FUNCTION( Test_TestCaseName );

    testEND_FUNCTION();
}
/*-----------------------------------------------------------*/
