# FreeRTOS Kernel SMP Unit Test

FreeRTOS Kernel SMP unit test verifies the SMP scheduler logic in tasks.c which
is enclosed by `configNUMBER_OF_CORES > 1`. The common scheduler logic for single
core and SMP is still verified in FreeRTOS/FreeRTOS/Test/CMock/tasks.

## Folder structure and test group naming
FreeRTOS SMP unit test has the following folder structure:
```
./FreeRTOS/FreeRTOS/Test/CMock/smp
├── Makefile
├── config_assert
│   └── config_assert_utest.c
├── multiple_priorities_no_timeslice_mock
│   └── covg_multiple_priorities_no_timeslice_mock_utest.c
├── multiple_priorities_no_timeslice
│   ├── covg_multiple_priorities_no_timeslice_utest.c
│   └── multiple_priorities_no_timeslice_utest.c
├── multiple_priorities_timeslice
│   ├── covg_multiple_priorities_timeslice_utest.c
│   └── multiple_priorities_timeslice_utest.c
├── single_priority_no_timeslice
│   ├── covg_single_priority_no_timeslice_utest.c
│   └── single_priority_no_timeslice_utest.c
├── single_priority_timeslice
│   ├── covg_single_priority_timeslice_utest.c
│   └── single_priority_timeslice_utest.c
├── global_vars.h
├── smp_utest_common.c
└── smp_utest_common.h
```

FreeRTOS SMP unit test cases are divided into groups and each folder represents
a test group. Test cases with same configurations in FreeRTOSConfig.h are grouped
together in a test group.

The following test groups are created for the combinations of `configRUN_MULTIPLE_PRIORITIES`
and `configUSE_TIME_SLICING`:
* single_priority_timeslice
* single_priority_no_timeslice
* multiple_priorities_timeslice
* multiple_priorities_no_timeslice

In order to increase the test coverage rate, test group **multiple_priorities_no_timeslice_mock**
is created to mock the APIs in list.h. The configuration is similar to **multiple_priorities_no_timeslice**.
 * multiple_priorities_no_timeslice_mock

config_assert test group is created to cover `configASSERT` in FreeRTOS SMP scheduler logic.
* config_assert

## Functional tests and coverage tests
Each test group has two types of test cases, the functional test cases and coverage
test cases. To distinguish these test cases, the source code file has the following
naming convention:
* Coverage test : covg_\<test_group_name\>_utest.c
* Functional test : \<test_group_name\>_utest.c

### Functional tests
Functional test cases verify that the SMP scheduler logic performs as described
by functional requirements. The test case specifies the functional requirement to
be verified, the test steps and expected result in the comment.

The following is an example of the functional test:
```c
/**
 * @brief AWS_IoT-FreeRTOS_SMP_TC-1
 * The purpose of this test is to verify when multiple CPU cores are available and
 * the FreeRTOS kernel is configured as (configRUN_MULTIPLE_PRIORITIES = 0) that tasks
 * of equal priority will execute simultaneously. The kernel will be configured as follows:
 *
 * #define configRUN_MULTIPLE_PRIORITIES                    0
 * #define configUSE_TIME_SLICING                           0
 * #define configNUMBER_OF_CORES                            (N > 1)
 *
 * This test can be run with FreeRTOS configured for any number of cores greater than 1 .
 *
 * Tasks are created prior to starting the scheduler.
 *
 * Task (T1)	    Task (TN)
 * Priority – 1     Priority –1
 * State - Ready	State - Ready
 *
 * After calling vTaskStartScheduler()
 *
 * Task (T1)	               Task (TN)
 * Priority – 1                Priority – 1
 * State - Running (Core 0)	   State - Running (Core N)
 */
void test_priority_verification_tasks_equal_priority( void )
{
    TaskHandle_t xTaskHandles[ configNUMBER_OF_CORES ] = { NULL };
    uint32_t i;

    /* Create configNUMBER_OF_CORES tasks of equal priority */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskCreate( vSmpTestTask, "SMP Task", configMINIMAL_STACK_SIZE, NULL, 1, &xTaskHandles[ i ] );
    }

    vTaskStartScheduler();

    /* Verify all configNUMBER_OF_CORES tasks are in the running state */
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        verifySmpTask( &xTaskHandles[ i ], eRunning, i );
    }
}
```

### Coverage tests
Coverage test cases verify a specific path of SMP scheduler logic.
The test case specifies the lines of code to be covered in the test case.
To minimize dependencies, mock functions are used wherever possible.


The following is an example of the coverage test:
```c
/**
 * @brief xTaskResumeFromISR - resume higher priority suspended task
 *
 * A higher priority task from ISR is resumed in the test case when scheduler
 * suspended. The return value of xTaskResumeFromISR indicates yield required
 * for the core calling this API.
 *
 * <b>Coverage</b>
 * @code{c}
 * prvYieldForTask( pxTCB );
 *
 * if( xYieldPendings[ portGET_CORE_ID() ] != pdFALSE )
 * {
 *     xYieldRequired = pdTRUE;
 * }
 * @endcode
 * ( xYieldPendings[ portGET_CORE_ID() ] != pdFALSE ) is true.
 */
void test_coverage_xTaskResumeFromISR_resume_higher_priority_suspended_task( void )
{
    TCB_t xTaskTCBs[ configNUMBER_OF_CORES + 1U ] = { NULL };
    uint32_t i;
    BaseType_t xReturn;

    /* Setup the variables and structure. */
    vListInitialise( &xSuspendedTaskList );
    vListInitialise( &xPendingReadyList );
    for( i = 0; i < configNUMBER_OF_CORES; i++ )
    {
        xTaskTCBs[ i ].uxPriority = 1;
        xTaskTCBs[ i ].xTaskRunState = i;
        xYieldPendings[ i ] = pdFALSE;
        pxCurrentTCBs[ i ] = &xTaskTCBs[ i ];
    }
    /* A suspended task is created to be resumed from ISR. The task has higher priority
     * than uxTopReadyPriority and the scheduler is suspended. The task will be added
     * to xPendingReadyList after resumed from ISR. */
    xTaskTCBs[ configNUMBER_OF_CORES ].uxPriority = 2;
    listINSERT_END( &xSuspendedTaskList, &xTaskTCBs[ i ].xStateListItem );
    uxTopReadyPriority = 1;
    uxSchedulerSuspended = pdTRUE;

    /* Expections. */
    vFakePortAssertIfInterruptPriorityInvalid_Ignore();

    /* API calls. */
    xReturn = xTaskResumeFromISR( &xTaskTCBs[ i ] );

    /* Validateions. In single priority test, the calling core is requested to yield
     * since a higher priority task is resumed. */
    TEST_ASSERT( xReturn == pdTRUE );
}
```
