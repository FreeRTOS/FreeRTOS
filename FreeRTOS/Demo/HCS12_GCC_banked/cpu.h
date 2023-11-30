/** 
 * sci.c controls SCI for GCC/HCS12 version of FreeRTOS Demo
 * To replace CodeWarrior Cpu.h
 *
 * Author Jefferson L Smith, Robotronics Inc.
 */

#ifndef __Cpu
#define __Cpu

/*Types definition*/
typedef unsigned char bool;
typedef unsigned char byte;
typedef unsigned int word;
typedef unsigned long dword;

#define ATTR_INT	__attribute__((interrupt))
#define ATTR_FAR	__attribute__((far))
#define ATTR_NEAR	__attribute__((near))
#define ATTR_BANK0	__attribute__((far,section (".bank0")))
#define ATTR_BANK1	__attribute__((far,section (".bank1")))
#define ATTR_BANK2	__attribute__((far,section (".bank2")))
#define ATTR_BANK3	__attribute__((far,section (".bank3")))
#define ATTR_BANK4	__attribute__((far,section (".bank4")))
#define ATTR_BANK5	__attribute__((far,section (".bank5")))
#define ATTR_BANK6	__attribute__((far,section (".bank6")))
#define ATTR_BANK7	__attribute__((far,section (".bank7")))
#define ATTR_BANK8	__attribute__((far,section (".bank8")))
#define ATTR_BANK9	__attribute__((far,section (".bank9")))
#define ATTR_BANK10	__attribute__((far,section (".bank10")))
#define ATTR_BANK11	__attribute__((far,section (".bank11")))
#define ATTR_BANK12	__attribute__((far,section (".bank12")))
#define ATTR_BANK13	__attribute__((far,section (".bank13")))

#include "PE_Error.h"
#include <sys/param.h>
#include <sys/ports.h>

#endif /* ifndef __Cpu */
