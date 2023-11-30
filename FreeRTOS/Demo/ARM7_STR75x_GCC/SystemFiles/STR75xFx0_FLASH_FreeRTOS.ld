/*
Default linker script for STR75xFx0
Copyright RAISONANCE S.A.S. 2006
*/

/* include the common STRxxx sub-script */
INCLUDE "systemfiles/STR75x_COMMON_FreeRTOS.ld"

/* include the memory spaces definitions sub-script */
INCLUDE "systemfiles/STR75xFx0_DEF_FreeRTOS.ld"

/* include the sections management sub-script for FLASH mode */
INCLUDE "systemfiles/sections_FLASH_FreeRTOS.ld"


