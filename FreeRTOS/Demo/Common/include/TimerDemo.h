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

#ifndef TIMER_DEMO_H
#define TIMER_DEMO_H

void vStartTimerDemoTask( TickType_t xBaseFrequencyIn );
BaseType_t xAreTimerDemoTasksStillRunning( TickType_t xCycleFrequency );
void vTimerPeriodicISRTests( void );

/*
 * Test the behavior of backlogged timers.  The backlog tests should not be
 * included while other demos are running concurrently with the timer demo.  The
 * backlog tests utilize xTaskCatchUpTicks(), which is logically equivalent to
 * starving all tasks for some number of ticks.  Under these conditions, other
 * demos may errantly detect test failures.
 */
void vTimerDemoIncludeBacklogTests( BaseType_t includeBacklogTests );

#endif /* TIMER_DEMO_H */
