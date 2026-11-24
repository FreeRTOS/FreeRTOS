# How does the test framework work?

Every test file is written against a small set of `test*` macros instead of
calling Unity APIs directly. This lets each target choose its own test
framework without changing any test source file:

| Macro | Default (Unity) | Purpose |
| --- | --- | --- |
| `testSETUP_FUNCTION_PROTOTYPE( fxn )` | `void fxn( void )` | Declares the `setUp` function run before each test case. |
| `testTEARDOWN_FUNCTION_PROTOTYPE( fxn )` | `void fxn( void )` | Declares the `tearDown` function run after each test case. |
| `testENTRY_FUNCTION_PROTOTYPE( fxn )` | `void fxn( void )` | Declares the function a test runner task calls to run the test. |
| `testBEGIN_FUNCTION()` | `UNITY_BEGIN()` | Called at the start of the entry function. |
| `testRUN_TEST_CASE_FUNCTION( fxn )` | `RUN_TEST( fxn )` | Runs a single test case. |
| `testEND_FUNCTION()` | `UNITY_END()` | Called at the end of the entry function. |

These macros are defined in `tests/include/test_macro_definitions.h`, which
every test file includes directly after `FreeRTOS.h` (see
`tests/smp/template/test_name.c`). Each macro is only defined if it isn't
already defined, so if a target has defined a macro earlier in the include
chain - typically from its `FreeRTOSConfig.h` - that definition wins and the
Unity-based default is skipped.

If a target needs a test framework other than Unity, or otherwise needs to
override any of the macros above:

1. In the target's `FreeRTOSConfig.h` (or a header it includes), `#define`
   the macros that need to be overridden.
1. Also define `configTARGET_TEST_USE_CUSTOM_MACRO_DEFINITIONS` there so that
   `test_macro_definitions.h` does not unconditionally include `unity.h`.

Because `FreeRTOS.h` includes `FreeRTOSConfig.h`, and every test file includes
`FreeRTOS.h` before `test_macro_definitions.h`, these overrides are visible by
the time `test_macro_definitions.h` is reached.

# How to add a new test?

1. Create a directory in the `tests` directory which will contain the test.
   For example: `tests/smp/multiple_tasks_running`.
1. Copy the `test_name.c` and `test_config.h` files from `tests/smp/template`
   to the newly created directory above.
1. Rename the `test_name.c` according to the test name.
1. Implement the test in the above test file, using the `test*` macros
   described above (`testSETUP_FUNCTION_PROTOTYPE`, `testTEARDOWN_FUNCTION_PROTOTYPE`,
   `testENTRY_FUNCTION_PROTOTYPE`, `testBEGIN_FUNCTION`,
   `testRUN_TEST_CASE_FUNCTION`, `testEND_FUNCTION`) instead of calling Unity
   APIs directly, so the test can run under any target's test framework. See
   [How does the test framework work?](#how-does-the-test-framework-work)
   above.
1. Add any FreeRTOS specific configuration required for the test to `test_config.h`.

# How to add a new target?

1. Create a target specific directory in the `boards` directory.
1. Create required build files.
    - Include `test_config.h` in `FreeRTOSConfig.h` at the end.
    - Ensure that the following configurations are not defined in `FreeRTOSConfig.h` as those are defined in `test_config.h`:
        - `configRUN_MULTIPLE_PRIORITIES`
        - `configUSE_CORE_AFFINITY`
        - `configUSE_MINIMAL_IDLE_HOOK`
        - `configUSE_TASK_PREEMPTION_DISABLE`
        - `configUSE_TIME_SLICING`
        - `configUSE_PREEMPTION`
    - If the target uses the default Unity-based test framework, no further
      action is required. If it needs to customize the test framework, define
      `configTARGET_TEST_USE_CUSTOM_MACRO_DEFINITIONS` and the overridden
      `test*` macros in `FreeRTOSConfig.h` (or a header it includes), as
      described in
      [How does the test framework work?](#how-does-the-test-framework-work)
      above.

# How to add a test to a target

1. Create a directory in the target's directory which will contain
   the test. For example: `boards/pico/tests/smp/multiple_tasks_running`.
1. Create a C file and invoke the test case from a task. The invocation
   usually looks like the following:
    ```c
    void prvTestRunnerTask( void * pvParameters )
    {
        /* Invoke the test case. */
        vRunTestCaseName();
    }
    ```
1. Add the file created above and the test case file to the build system used
   for the target.
