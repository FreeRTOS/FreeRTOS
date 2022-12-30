# FreeRTOS Kernel Tests For The RP2040

## Template: Temaplate showcasing a wide spectrum of FreeRTOS capabilities.

The intent is that it is useful to boostrap test creation. Simply duplicate it, pair it down and then specialize as needed.

* tasks: SMP scheduled and AMP like bare-metal tasks
* queues
* sempahors
* timers
* target specific operations via preprocessor directives

NOTES:

* (Gaurov) use a fork instead of a branch
* (Gaurov) address some real test cases
  * table of tests, start with the simple tests first.
    * e.g. the test where two tests are running at one time and make sure that it works on two platforms
* (joshua) change from serial logging to in memory accounting
* (joshua) include a validator thread
* (joshua) support other targets
  * actually try another target
  * possibly have target_pico.cmake files, et and include per target or something
  * directory structure as is today or target.cmake, etc. test.c might be a more
  * general dir.

* (joshua) use the unity code generation mechanism. second iteration

