This proof demonstrates the memory safety of the TaskCreate function,
and is identical to the TaskCreate folder proof, but with 1 modification:
the portSTACK_GROWTH macro is set to 1 instead of -1.

This macro setting is achieved by including a .h file 
(from this directory) in 
tasks.c that unsets and resets the macro.