# Reliance Edge Release Notes

This file contains a list of updates made to Reliance Edge over the course of
recent releases and a list of known issues.

## Release History and Changes

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

