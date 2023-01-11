# How to add a new test?
1. Create a directory in the `FreeRTOS/Test/Target/tests` directory which will
   contain the test. For example: `FreeRTOS/Test/Target/tests/smp/multiple_tasks_running`.
1. Copy the `test_name.c` and `test_config.h` files from this template directory to
   the newly created directory above.
1. Rename the `test_name.c` according to the test name.
1. Add any FreeRTOS specific configuration required to `test_config.h`.
1. Implement the test in `test.c`.
1. Create a directory in the `FreeRTOS/Test/Target/boards/pico/tests` directory which will
   contain the test. For example: `FreeRTOS/Test/Target/boards/pico/tests/smp/multiple_tasks_running`.
1. Create `CMakeLists.txt` and `main.c` files to the newly created directory above.
1. Implement the test in `CMakeLists.txt` and `main.c`.
   - `CMakeLists.txt` is a set of rules for CMAKE to generagte the binary for this test case.
   - `main.c` is the entry function for the program to start with.

# How to add a new target?
1. Create a target specific directory in the `FreeRTOS/Test/Target/boards` directory.
1. Create required build files.
1. Invoke test case(s) from a task. It ensures that the test case
   can behave like a check task and ensure that every other task did what it was
   expected to do. The invocation will look like -
    ```c
    void prvTestRunnerTask( void * pvParameters )
    {
        ( void ) pvParameters;
        
        /* Execute test case provided in test.c */
        Run_Test_Name();
    }
    ```
