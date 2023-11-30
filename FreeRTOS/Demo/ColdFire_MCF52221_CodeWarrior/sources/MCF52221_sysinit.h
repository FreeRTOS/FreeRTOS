/*
 * File:		mcf52221demo_sysinit.h
 * Purpose:		Power-on Reset configuration of the MCF52221.
 *
 * Notes:
 *
 */

#ifndef __MCF52221DEMO_SYSINIT_H__
#define __MCF52221DEMO_SYSINIT_H__

#ifdef __cplusplus
extern "C" {
#endif



#if ENABLE_UART_SUPPORT==1 

#define TERMINAL_PORT       0
#define TERMINAL_BAUD       kBaud19200

#endif  /* ENABLE_UART_SUPPORT==1 */

#define SYSTEM_CLOCK_KHZ  80000     /* system bus frequency in kHz */


/********************************************************************/
/* __initialize_hardware Startup code routine
 * 
 * __initialize_hardware is called by the startup code right after reset, 
 * with interrupt disabled and SP pre-set to a valid memory area.
 * Here you should initialize memory and some peripherics;
 * at this point global variables are not initialized yet.
 * The startup code will initialize SP on return of this function.
 */
void __initialize_hardware(void);

/********************************************************************/
/* __initialize_system Startup code routine
 * 
 * __initialize_system is called by the startup code when all languages 
 * specific initialization are done to allow additional hardware setup.
 */ 
void __initialize_system(void);



#ifdef __cplusplus
}
#endif

#endif /* __MCF52221DEMO_SYSINIT_H__ */


