Standard I/O
============

Freedom Metal integrates with libc ``STDOUT`` to provide virtual terminal support.
The default ``STDOUT`` device is the first UART serial peripheral on the target.
If no UART serial peripheral is present, such as in the case of SiFive CoreIP
test harnesses, then the bytes sent to ``STDOUT`` are dropped.

Hello World
-----------

Using the virtual terminal with Freedom Metal is exactly what you might expect:

.. code-block:: C
   :linenos:

   #include <stdio.h>

   int main(void) {
      printf("Hello, world!");

      return 0;
   }

