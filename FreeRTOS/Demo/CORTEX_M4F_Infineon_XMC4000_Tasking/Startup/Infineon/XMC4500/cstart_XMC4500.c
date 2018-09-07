/*
**      @(#)cstart.c    1.9     $E%
**
**  Copyright 1997-2013 Altium BV                                         *
**
**      DESCRIPTION:
**
**      The system startup code initializes the processor's registers
**      and the application C variables.
**
*/

#pragma nomisrac
#pragma profiling       off                     /* prevent profiling information on cstart      */
#pragma optimize        abcefgIJKlopRsUy        /* preset optimization level                    */
#pragma tradeoff        4                       /* preset tradeoff level                        */
#pragma runtime         BCMSZ                   /* disable runtime error checking for cstart    */
#pragma warning         750                     /* do not warn about unsaved registers          */
#pragma section         .text=cstart            /* use: .text.cstart as the section name        */

#include <stdlib.h>
#include <dbg.h>

#define VTOR            (*(volatile unsigned int *)0xE000ED08)
/* In the absence of DAVE code engine, CMSIS SystemInit() must perform clock 
   tree setup. 
   
   This decision routine defined here will always return TRUE.
   
   When overridden by a definition defined in DAVE code engine, this routine
   returns FALSE indicating that the code engine has performed the clock setup
*/   
#pragma weak AllowPLLInitByStartup
uint32_t AllowPLLInitByStartup( void )
{
        return 1;
}



extern  unsigned char   _lc_ub_stack[];
extern  unsigned char   _lc_vtor_value[];

#pragma weak    exit
#pragma extern  _Exit
#pragma extern  main
extern  int     main( int argc, char *argv[] );
extern  void    SystemInit( void );
extern  void    __init( void );
#if     __PROF_ENABLE__
extern  void    __prof_init( void );
#endif

#ifdef __POSIX__
extern  void *  _posix_boot_stack_top;
extern  int     posix_main( void );
#endif

#ifdef  __USE_ARGC_ARGV
#ifndef __ARGCV_BUFSIZE
#define __ARGCV_BUFSIZE         256
#endif
static  char    argcv[__ARGCV_BUFSIZE];
#endif

void    __interrupt() __frame() Reset_Handler( void )
{

        /*
         *      Anticipate possible ROM/RAM remapping
         *      by loading the 'real' program address.
         */
        __remap_pc();
        /*
         *      Initialize stack pointer.
         */
        __setsp( _lc_ub_stack );
        /*
         *      Call a user function which initializes hardware,
         *      such as ROM/RAM re-mapping or MMU configuration.
         */
        SystemInit();
        /*
         *      Copy initialized sections from ROM to RAM
         *      and clear uninitialized data sections in RAM.
         */
        __init();
        __asm( "_cptable_handled:" );                                   /* symbol may be used by debugger       */

        /*
         * Load VTOR register with the actual vector table
         * start address
         */
        VTOR = (unsigned int)_lc_vtor_value;
        
#ifdef __POSIX__
        __setsp( _posix_boot_stack_top );
#endif
#if  __PROF_ENABLE__
        __prof_init();
#endif
#ifdef __POSIX__
        exit( posix_main() );
#elif defined __USE_ARGC_ARGV
        exit( main( _argcv( argcv, __ARGCV_BUFSIZE ), (char **)argcv ) );
#else
        exit( main( 0, NULL ) );
#endif
        return;
}
