/******************************************************************************
  FILE    : startcf.h
  PURPOSE : startup code for ColdFire
  LANGUAGE: C


  Notes:
        1) Default entry point is _startup. 
           . disable interrupts
           . the SP is set to __SP_AFTER_RESET
           . SP must be initialized to valid memory 
             in case the memory it points to is not valid using MEMORY_INIT macro
        2) __initialize_hardware is called. Here you can initialize memory and some peripherics
           at this point global variables are not initialized yet
        3) After __initialize_hardware memory is setup; initialize SP to _SP_INIT and perform 
           needed initialisations for the language (clear memory, data rom copy).
        4) void __initialize_system(void); is called
           to allow additional hardware initialization (UART, GPIOs, etc...)
        5) Jump to main 

*/
/********************************************************************************/

#ifndef STARTCF_H
#define STARTCF_H


#ifdef __cplusplus
extern "C" {
#endif

#include "support_common.h"

extern unsigned long far __SP_INIT[];
extern unsigned long far __SP_AFTER_RESET[];


#ifndef MEMORY_INIT
/* If MEMORY_INIT is set then it performs
   minimal memory initialization (to preset SP to __SP_AFTER_RESET, etc...)
*/
#define MEMORY_INIT
#endif
							 

void _startup(void);

#ifndef SUPPORT_ROM_TO_RAM
  /*
   * If SUPPORT_ROM_TO_RAM is set, _S_romp is used to define the copy to be performed.
   * If it is not set, there's a single block to copy, performed directly without 
   * using the __S_romp structure, based on __DATA_RAM, __DATA_ROM and
   * __DATA_END symbols.
   *
   * Set to 0 for more aggressive dead stripping ...
   */
#define SUPPORT_ROM_TO_RAM 1
#endif

/* format of the ROM table info entry ... */
typedef struct RomInfo {
	void            *Source;
	void            *Target;
	unsigned long    Size;
} RomInfo;

/* imported data */
extern far RomInfo _S_romp[];		/* linker defined symbol */

#ifdef __cplusplus
}
#endif

#endif
