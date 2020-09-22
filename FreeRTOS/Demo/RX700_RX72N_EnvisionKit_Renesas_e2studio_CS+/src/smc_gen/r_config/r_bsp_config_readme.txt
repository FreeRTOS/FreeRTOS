FIT r_config folder
-------------------
The purpose of the r_config folder is to provide one place where the user can store all of their FIT configuration 
files. Putting the files in one place makes them easy to find, backup, and put in a version control system.

FIT Modules are distributed with a reference configuration file. These files end with '_reference.h'. For example,
the reference configuration file for the r_bsp is named r_bsp_config_reference.h. Reference configuration files are 
provided so that the user always has a known-good configuration to revert to. When adding a FIT Module to a project the
user should copy this reference configuration file to this folder and remove '_reference' from the filename 
(r_bsp_config_reference.h is renamed to r_bsp_config.h).  For the r_bsp the reference configuration file can be found in
the 'board' folder for the currently chosen development board. For other FIT Modules the reference configuration file
can be found in the 'ref' folder of the FIT Module.
