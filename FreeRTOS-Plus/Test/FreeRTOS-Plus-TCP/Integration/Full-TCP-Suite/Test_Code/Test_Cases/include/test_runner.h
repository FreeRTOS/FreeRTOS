/*
 * FreeRTOS V202212.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
 * @file aws_test_runner.h
 * @brief The function to be called to run all the tests.
 */

#ifndef _AWS_TEST_RUNNER_H_
#define _AWS_TEST_RUNNER_H_

/*
 * @brief If set to 1, will run DQP_FR tests only.
 */
#define testrunnerTEST_FILTER    0


/**
 * @brief Size of shared array.
 *
 */
#define testrunnerBUFFER_SIZE    ( 4000 )

/**
 * @brief Buffer used for all tests.
 *
 * Since tests are run in series, they can use the same memory array.
 * This makes significant heap savings.
 */
extern char cBuffer[ testrunnerBUFFER_SIZE ];

/**
 * @brief FreeRTOS heap measurement taken before tests are run.
 */
extern unsigned int xHeapBefore;

/**
 * @brief FreeRTOS heap measurement taken after all tests are run.
 */
extern unsigned int xHeapAfter;


/**
 * @brief Runs all the tests.
 */
void TEST_RUNNER_RunTests_task( void * pvParameters );



#endif /* _AWS_TEST_RUNNER_H_ */
