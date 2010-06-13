
The PM module is very specific to the device it is integrated in. Thus instead
of providing one low-level software driver for all PM modules which could be
cumbersome to use and maintain, this folder contains instead several versions of
PM software drivers, depending on the device it was intended for.

Furthermore, the software drivers do not have the same API (mostly due to major
differences between PM module versions).

Note however that the power_clocks_lib.c/.h collection is destined to provide
a high-level API abstracting the existence of modules dealing with Power
Management and Clock configuration and System Control.

Here is a brief presentation of the files present in this folder:
- pm_at32ap7000.h, pm_at32ap7000.c: low-level software driver for a PM module
  with version 100

- pm.c, pm.h: low-level software driver for a PM module with version 2xx
- pm_conf_clocks.c: Clocks configuration library relying on pm.c/.h for a PM
  module with version 2xx. Its interface is available in pm.h.

- pm_uc3l.h, pm_uc3l.c: low-level software driver for the UC3L devices PM module

- pm_uc3c.h, pm_uc3c.c: low-level software driver for the UC3C devices PM module

- power_clocks_lib.h, power_clocks_lib.c: high-level library to abstract features
  such as oscillators/pll/dfll configuration, clock configuration, System-sensible
  parameters configuration, buses clocks configuration, sleep mode, reset. This
  list of features being quite broad, an implementation of this library must
  use several modules of a device.
