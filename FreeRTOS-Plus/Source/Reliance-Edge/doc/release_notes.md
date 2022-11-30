# Reliance Edge Release Notes

This file contains a list of updates made to Reliance Edge over the course of
recent releases and a list of known issues.

## Release History and Changes

### Reliance Edge v2.0, January 2017

- Added support for Linux as a host environment
  - All "host" projects may now be built in either Windows or Linux using the
    `make` command.  The formatter and image builder are built, and the checker
    and image copier are also built in the commercial kit.
  - An additional host tool has been added for Linux only: `redfuse`.  It is a
    File System in User Space (FUSE) implementation, allowing a Reliance Edge
    volume to be mounted directly on Linux for easy access.  It is built from
    the host project folder using the command `make redfuse`.
  - The OS-specific API test (commercial kit only) is now ported to run on Linux
    for the purpose of verifying the FUSE implementation.
- Fixed a bug that could leave a directory in an invalid state after removing
  files.  For example, an affected directory might report a non-zero length even
  after all files had been deleted.
- Fixed a bug that would leave the driver in a bad state if a mount operation
  failed due to missing or corrupt metaroot blocks.

### Reliance Edge v1.1 (Beta), November 2016

- Added support for a discard (trim) interface in the commercial kit.  While
  discards are not integral to the behavior of the filesystem, they allow
  certain types of Flash drivers and media to perform at optimal speed and
  efficiency.  The commercial version of Reliance Edge now allows the user to
  implement this interface for compatible storage media.
  - This change added new fields to the configuration files redconf.h and
    redconf.c. The configuration utility has been updated to version 1.1 and
    existing configuration files must be updated using the updated utility.
- The configuration utility now has keyboard shortcuts for opening and saving
  the configuration.
- The configuration utility now adds version macros to easily identify when an
  outdated configuration file is used with Reliance Edge or vice versa.

### Reliance Edge v1.0.4, July 2016

- Added ARM mbed and ARM mbed OS support in the commercial kit, with an example
  projects for ARM mbed OS on the NXP FRDM-K64F board.
- Some minor deficiencies in the POSIX-like API test suite have been addressed.

### Reliance Edge v1.0.3, June 2016

- Added support for static memory allocation configuration in FreeRTOS
  version 9.  No common code changes.

### Reliance Edge v1.0.2, February 2016

#### Common Code Changes
- A new per-volume configuration option has been added: users can specify a
  number of times to retry a block device read, write or flush operation before
  returning a failure.  The configuration tool has been updated to version 1.0.2
  with this change.
  - This added a new field to the volume configuration in redconf.c: existing
    redconf.c files from v1.0.1 and earlier must be updated to work with v1.0.2.
    Open redconf.h and redconf.c with the configuration tool, enable
    "Retry block device I/O on failure" for any volumes if desired, and save the
    redconf files.

#### FreeRTOS Port Changes
- Added support for the STM32 HAL SD card driver in the FreeRTOS block device
  interface.  Two boards are supported out-of-the-box: the STM324xG-EVAL and the
  STM32F746NG-Discovery.  A sample project is included for the STM324xG-EVAL.

#### MQX Port Changes
- Fixed a bug which prevented Reliance Edge from compiling if the File System
  Essentials API was selected in the configuration.
- Fixed a bug which would have returned an uninitialized value from
  `RedOsBDevFlush()` for block devices that support flushing.

### Reliance Edge v1.0.1, October 2015

- Added MQX RTOS support in the commercial kit, with example projects for
  the Kinetis Design Studio.
- Bug fix in the F_DRIVER implementation of the FreeRTOS block device service.

### Reliance Edge v1.0, July 2015

#### Common Code Changes

- First release of commercial kit and MISRA C:2012 Design Assurance Package.
  The commercial kit includes many new tools and tests which were not previously
  available.
- Overhauled parsing of command-line parameters to be consistent for all tools
  and tests.  Command-line tools now use Unix-style short and long options (such
  as `-H` and `--help`) instead of DOS-style switches (such as `/?`).
- Renamed all os/\*/include/ostypes.h headers to os/\*/include/redostypes.h, so
  that all headers use the product prefix.  If you created a port using v0.9,
  this header needs to be renamed and its header guard (#ifndef OSTYPES_H etc.)
  should also be updated.
- Add a new header for OS-specific MISRA C:2012 deviation macros, located at
  os/\*/include/redosdeviations.h.  If you created a port using v0.9, copy the
  template from os/stub/include/redosdeviations.h into the include directory.
- Eliminated support for sector sizes less than 256.  If using a smaller sector
  size (say for a RAM disk), this must now be emulated in the implementation of
  the block device OS service.
- Added RedFseFormat() as an optional FSE API, allowing FSE applications to
  format the volume at run-time.
  - This added a new macro to redconf.h: existing redconf.h files from v0.9 must
    be updated to work with v1.0.  Open redconf.h with the configuration tool,
    ignore the warning about the missing macro, and save it.
- Internal restructuring has renamed the macros for the string and memory
  functions used in redconf.h.  An existing redconf.h file from v0.9 will need
  to be updated; for a file containing the old names, the new config tool will
  default to using the (slow) Reliance Edge string/memory functions; to use the
  C library or custom versions, this will need to be selected in the
  configuration utility.
- Fix a bug which would result in an error when attempting to create a name with
  one or more trailing path separators (such as `red_mkdir("/foo/bar/")`).
- Fix a bug where an open handle for an inode on one volume would prevent the
  same inode number from being deleted on a different volume.

#### FreeRTOS Port Changes

- The implementation of the timestamp OS service no longer requires that
  `configUSE_TIMERS` be set to `1`.

### Reliance Edge v0.9 (Beta), April 2015

First public release.

## Known Issues

### Visual Studio 2005

The Reliance Edge Win32 port (used for the host tools and the Win32 test
project) cannot be compiled by Visual Studio 2005.  This is not going to be
fixed since VS2005 is an old toolset.  Newer versions of Visual Studio, starting
with Visual Studio 2008, work just fine.
