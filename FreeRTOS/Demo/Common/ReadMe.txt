Contains the files that are not specific to any one demo, but are instead used
by all the demo applications.

Most of the directories are now obsolete, and only maintained for backward
compatibility.  The directories in active use are:

+ Minimal - this contains the implementation of what are referred to as the
"Standard Demo Tasks".  These are used by all the demo applications.  Their only
purpose is to demonstrate the FreeRTOS API and test the FreeRTOS features.  The
directory is called 'Minimal' as it contains a minimal implementation of files
contained in the 'Full' directory - but the 'Full' directory is no longer used.

+ include - contains header files for the C source files located in the Minimal
directory.