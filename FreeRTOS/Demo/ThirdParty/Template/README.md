# Create a Test Project

## Initial Setup

1. Create a new directory in the [FreeRTOS Partner Supported Demos Repository](https://github.com/FreeRTOS/FreeRTOS-Partner-Supported-Demos/tree/main)
   or [FreeRTOS Community Supported Demos Repository](https://github.com/FreeRTOS/FreeRTOS-Community-Supported-Demos/tree/main).
   The suggested name for the directory is `<hardware_name>_<compiler_name>`.
2. Create a project for your hardware and tool-chain in this directory.
3. Copy all the files in the [FreeRTOS/Demo/ThirdParty/Template](https://github.com/FreeRTOS/FreeRTOS/tree/main/FreeRTOS/Demo/ThirdParty/Template)
   directory to your project directory:
   * `IntQueueTimer.h`
   * `IntQueueTimer.c`
   * `TestRunner.h`
   * `TestRunner.c`
   * `RegTests.h`
   * `RegTests.c`

## Project Configuration

1. Compile the following additional files in your project:
   * All files in the [FreeRTOS/Demo/Common/Minimal](https://github.com/FreeRTOS/FreeRTOS/tree/main/FreeRTOS/Demo/Common/Minimal) directory except
     `comtest_strings.c` , `comtest.c` ,`flash.c`, `flash_timer.c` and `sp_flop.c`.
2. Add the following paths to your include search path:
   * `FreeRTOS/Demo/Common/include`.
3. Call the `void vStartTests( void )` function from your `main` function after
   doing all the hardware initialization. Note that this function starts the
   scheduler and therefore, never returns.
```c
#include "TestRunner.h"

void main( void )
{
    /* Startup and Hardware initialization. */

    /* Start tests. */
    vStartTests();

    /* Should never reach here. */
    for( ; ; );
}
```

## Set up FreeRTOSConfig.h

1. Enable tick hook by adding the following line in your `FreeRTOSConfig.h`:
```c
#define configUSE_TICK_HOOK 1
```
2. Set the task notification array size to 3 by adding the following line in
   your `FreeRTOSConfig.h`:
```c
#define configTASK_NOTIFICATION_ARRAY_ENTRIES 3
```
3. Enable printing by mapping `configPRINTF` to your print function. Note that
   `configPRINTF` calls are wrapped in double parentheses to support C89. If you
    have a thread-safe `printf` function, the following is what should be added
    in your `FreeRTOSConfig.h`:
```c
#define configPRINTF( X ) printf X
```
4. Add the following defines in your `FreeRTOSConfig.h`:
```c
#define configSTART_TASK_NOTIFY_TESTS             0
#define configSTART_TASK_NOTIFY_ARRAY_TESTS       0
#define configSTART_BLOCKING_QUEUE_TESTS          0
#define configSTART_SEMAPHORE_TESTS               0
#define configSTART_POLLED_QUEUE_TESTS            0
#define configSTART_INTEGER_MATH_TESTS            0
#define configSTART_GENERIC_QUEUE_TESTS           0
#define configSTART_PEEK_QUEUE_TESTS              0
#define configSTART_MATH_TESTS                    0
#define configSTART_RECURSIVE_MUTEX_TESTS         0
#define configSTART_COUNTING_SEMAPHORE_TESTS      0
#define configSTART_QUEUE_SET_TESTS               0
#define configSTART_QUEUE_OVERWRITE_TESTS         0
#define configSTART_EVENT_GROUP_TESTS             0
#define configSTART_INTERRUPT_SEMAPHORE_TESTS     0
#define configSTART_QUEUE_SET_POLLING_TESTS       0
#define configSTART_BLOCK_TIME_TESTS              0
#define configSTART_ABORT_DELAY_TESTS             0
#define configSTART_MESSAGE_BUFFER_TESTS          0
#define configSTART_STREAM_BUFFER_TESTS           0
#define configSTART_STREAM_BUFFER_INTERRUPT_TESTS 0
#define configSTART_TIMER_TESTS                   0
#define configSTART_INTERRUPT_QUEUE_TESTS         0
#define configSTART_REGISTER_TESTS                0
#define configSTART_DELETE_SELF_TESTS             0
```

## Create and Run Register Tests

1. Fill the definitions of the following functions in the `RegTests.c` file
   copied in the [Initial Setup](#Initial-Setup) step:
   * `prvRegisterTest1Task`
   * `prvRegisterTest2Task`
   * `prvRegisterTest3Task`
   * `prvRegisterTest4Task`
2. Define `configSTART_REGISTER_TESTS` to `1` in your `FreeRTOSConfig.h`:
```c
#define configSTART_REGISTER_TESTS                1
```
3. Build and run the register tests. The output should look like the following:
```
No errors
No errors
No errors
No errors
```

## Setup and Run Interrupt Nesting Tests

1. If your hardware **does not** support interrupt nesting, skip this section.
2. Fill the `void vInitialiseTimerForIntQueueTest( void )` function in the
   `IntQueueTimer.c` file copied in the [Initial Setup](#Initial-Setup) step to
   initialize and start a hardware timer. Make sure that the timer interrupt
   runs at a logical priority less than or equal to `configMAX_SYSCALL_INTERRUPT_PRIORITY`.
   The following is an example for ARM MPS2 which starts TIM0 timer:
```c
void vInitialiseTimerForIntQueueTest( void )
{
    /* Clear interrupt. */
    CMSDK_TIMER0->INTCLEAR = ( 1ul <<  0 );

    /* Reload value is slightly offset from the other timer. */
    CMSDK_TIMER0->RELOAD = ( configCPU_CLOCK_HZ / tmrTIMER_0_FREQUENCY ) + 1UL;
    CMSDK_TIMER0->CTRL   = ( ( 1ul <<  3 ) | ( 1ul <<  0 ) );

    NVIC_SetPriority( TIMER0_IRQn, configMAX_SYSCALL_INTERRUPT_PRIORITY );
    NVIC_EnableIRQ( TIMER0_IRQn );
}
```
3. Either install `void IntQueueTestTimerHandler( void )` function as the timer
   interrupt handler or call it from the timer interrupt handler of the above
   timer. The following is an example for ARM MPS2 which calls
   `IntQueueTestTimerHandler` from the TIM0 handler:
```c
void TIMER0_Handler( void )
{
    /* Clear interrupt. */
    CMSDK_TIMER0->INTCLEAR = ( 1ul <<  0 );

    IntQueueTestTimerHandler();
}
```
4. Define `configSTART_INTERRUPT_QUEUE_TESTS` to `1` in your `FreeRTOSConfig.h`:
```c
#define configSTART_INTERRUPT_QUEUE_TESTS         1
```
5. Build and run the tests. The output should look like the following:
```
No errors
No errors
No errors
No errors
```

## Running All Tests

1. Define all the `configSTART_<Test_Name>_TESTS` macros to `1` in your
`FreeRTOSConfig.h`.
2. Build and run the tests. The output should look like the following:
```
No errors
No errors
No errors
No errors
```
3. If you cannot fit all the tests in one binary because of Flash or RAM space,
you can run tests one by one or in groups by defining
`configSTART_<Test_Name>_TESTS` macros to `0` or `1` as needed.

## Add README
Add a `README.md` file in the project directory with the following information:
* Link to the hardware page.
* How to setup tool-chain.
* How to build and run the project.
* Any other relevant information.
