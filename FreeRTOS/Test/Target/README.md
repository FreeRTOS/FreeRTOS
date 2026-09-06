# Test framework

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

These macros are defined in `tests/include/test_default_setting_config.h`,
which every test file includes (see `tests/smp/template/test_name.c` for the
required include order). If a macro is already defined - for example by a
target-specific `test_setting_config.h` - the default in
`test_default_setting_config.h` is skipped, so targets only need to override
the macros that differ from the Unity-based default.

If a target needs a test framework other than Unity, or otherwise needs to
override any of the macros above:

1. Create a `test_setting_config.h` header for the target with `#define`s for
   the macros that need to be overridden. Define `testNOT_USING_UNITY` in it
   if the target does not use Unity at all, since `test_default_setting_config.h`
   otherwise includes `unity.h` unconditionally.
1. Set `configTARGET_TEST_USE_CUSTOM_SETTING` to `1` in the target's
   `FreeRTOSConfig.h` so that the test files pick up `test_setting_config.h`.

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
   APIs directly, so the test can run under any target's test framework.
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
      action is required. If it needs to customize the test framework, add a
      `test_setting_config.h` and set `configTARGET_TEST_USE_CUSTOM_SETTING`
      to `1`, as described in [Test framework](#test-framework) above.

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
