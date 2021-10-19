===============================================================================
# hal folder
===============================================================================

The HAL folder provides support code for use by the bare metal drivers for the
fabric IP cores.
The HAL folder contains files using a combination of C and assembly source code.

The hal folder should be included in a PolarFire SoC Embedded project under the 
platform directory. See location in the drawing below.

The hal folder contains:

* register access functions
* assert macros

### Project directory strucutre, showing where hal folder sits.

   +---------+      +-----------+
   | src     +----->|application|
   +---------+  |   +-----------+
                |
                |   +-----------+
                +-->|modules    |
                |   +-----------+
                |
                |   +-----------+     +---------+
                +-->|platform   +---->|config   |
                    +-----------+  |  +---------+
                                   |
                                   |  +---------+
                                   +->|drivers  |
                                   |  +---------+
                                   |
                                   |  +---------+
                                   +->|hal      |
                                   |  +---------+
                                   |
                                   |  +---------+
                                   +->|mpfs_hal |
                                      +---------+