/******************************************************************************/
/* lnk_msp430f5438a.cmd - LINKER COMMAND FILE FOR LINKING MSP430F5438A PROGRAMS     */
/*                                                                            */
/*   Usage:  lnk430 <obj files...>    -o <out file> -m <map file> lnk.cmd     */
/*           cl430  <src files...> -z -o <out file> -m <map file> lnk.cmd     */
/*                                                                            */
/*----------------------------------------------------------------------------*/
/* These linker options are for command line linking only.  For IDE linking,  */
/* you should set your linker options in Project Properties                   */
/* -c                                               LINK USING C CONVENTIONS  */
/* -stack  0x0100                                   SOFTWARE STACK SIZE       */
/* -heap   0x0100                                   HEAP AREA SIZE            */
/*                                                                            */
/*----------------------------------------------------------------------------*/


/****************************************************************************/
/* SPECIFY THE SYSTEM MEMORY MAP                                            */
/****************************************************************************/

MEMORY
{
    SFR                     : origin = 0x0000, length = 0x0010
    PERIPHERALS_8BIT        : origin = 0x0010, length = 0x00F0
    PERIPHERALS_16BIT       : origin = 0x0100, length = 0x0100
    RAM                     : origin = 0x1C00, length = 0x4000
    INFOA                   : origin = 0x1980, length = 0x0080
    INFOB                   : origin = 0x1900, length = 0x0080
    INFOC                   : origin = 0x1880, length = 0x0080
    INFOD                   : origin = 0x1800, length = 0x0080
    FLASH                   : origin = 0x5C00, length = 0xA380
    FLASH2                  : origin = 0x10000,length = 0x35C00
    INT00                   : origin = 0xFF80, length = 0x0002
    INT01                   : origin = 0xFF82, length = 0x0002
    INT02                   : origin = 0xFF84, length = 0x0002
    INT03                   : origin = 0xFF86, length = 0x0002
    INT04                   : origin = 0xFF88, length = 0x0002
    INT05                   : origin = 0xFF8A, length = 0x0002
    INT06                   : origin = 0xFF8C, length = 0x0002
    INT07                   : origin = 0xFF8E, length = 0x0002
    INT08                   : origin = 0xFF90, length = 0x0002
    INT09                   : origin = 0xFF92, length = 0x0002
    INT10                   : origin = 0xFF94, length = 0x0002
    INT11                   : origin = 0xFF96, length = 0x0002
    INT12                   : origin = 0xFF98, length = 0x0002
    INT13                   : origin = 0xFF9A, length = 0x0002
    INT14                   : origin = 0xFF9C, length = 0x0002
    INT15                   : origin = 0xFF9E, length = 0x0002
    INT16                   : origin = 0xFFA0, length = 0x0002
    INT17                   : origin = 0xFFA2, length = 0x0002
    INT18                   : origin = 0xFFA4, length = 0x0002
    INT19                   : origin = 0xFFA6, length = 0x0002
    INT20                   : origin = 0xFFA8, length = 0x0002
    INT21                   : origin = 0xFFAA, length = 0x0002
    INT22                   : origin = 0xFFAC, length = 0x0002
    INT23                   : origin = 0xFFAE, length = 0x0002
    INT24                   : origin = 0xFFB0, length = 0x0002
    INT25                   : origin = 0xFFB2, length = 0x0002
    INT26                   : origin = 0xFFB4, length = 0x0002
    INT27                   : origin = 0xFFB6, length = 0x0002
    INT28                   : origin = 0xFFB8, length = 0x0002
    INT29                   : origin = 0xFFBA, length = 0x0002
    INT30                   : origin = 0xFFBC, length = 0x0002
    INT31                   : origin = 0xFFBE, length = 0x0002
    INT32                   : origin = 0xFFC0, length = 0x0002
    INT33                   : origin = 0xFFC2, length = 0x0002
    INT34                   : origin = 0xFFC4, length = 0x0002
    INT35                   : origin = 0xFFC6, length = 0x0002
    INT36                   : origin = 0xFFC8, length = 0x0002
    INT37                   : origin = 0xFFCA, length = 0x0002
    INT38                   : origin = 0xFFCC, length = 0x0002
    INT39                   : origin = 0xFFCE, length = 0x0002
    INT40                   : origin = 0xFFD0, length = 0x0002
    INT41                   : origin = 0xFFD2, length = 0x0002
    INT42                   : origin = 0xFFD4, length = 0x0002
    INT43                   : origin = 0xFFD6, length = 0x0002
    INT44                   : origin = 0xFFD8, length = 0x0002
    INT45                   : origin = 0xFFDA, length = 0x0002
    INT46                   : origin = 0xFFDC, length = 0x0002
    INT47                   : origin = 0xFFDE, length = 0x0002
    INT48                   : origin = 0xFFE0, length = 0x0002
    INT49                   : origin = 0xFFE2, length = 0x0002
    INT50                   : origin = 0xFFE4, length = 0x0002
    INT51                   : origin = 0xFFE6, length = 0x0002
    INT52                   : origin = 0xFFE8, length = 0x0002
    INT53                   : origin = 0xFFEA, length = 0x0002
    INT54                   : origin = 0xFFEC, length = 0x0002
    INT55                   : origin = 0xFFEE, length = 0x0002
    INT56                   : origin = 0xFFF0, length = 0x0002
    INT57                   : origin = 0xFFF2, length = 0x0002
    INT58                   : origin = 0xFFF4, length = 0x0002
    INT59                   : origin = 0xFFF6, length = 0x0002
    INT60                   : origin = 0xFFF8, length = 0x0002
    INT61                   : origin = 0xFFFA, length = 0x0002
    INT62                   : origin = 0xFFFC, length = 0x0002
    RESET                   : origin = 0xFFFE, length = 0x0002
}

/****************************************************************************/
/* SPECIFY THE SECTIONS ALLOCATION INTO MEMORY                              */
/****************************************************************************/

SECTIONS
{
    .bss       : {} > RAM                /* GLOBAL & STATIC VARS              */
    .sysmem    : {} > RAM                /* DYNAMIC MEMORY ALLOCATION AREA    */
    .stack     : {} > RAM (HIGH)         /* SOFTWARE SYSTEM STACK             */

/* Can be modified to test the use of high memory. */
/* Original line. */
    .text      : {}>> FLASH | FLASH2  /* CODE                              */
/* Modified line. */
/*    .text      : {} >> FLASH2  */             /* CODE                              */
	.main      : {} > FLASH
    .text:_isr : {} > FLASH              /* ISR CODE SPACE                    */
    .cinit     : {} > FLASH              /* INITIALIZATION TABLES             */
//#ifdef (__LARGE_DATA_MODEL__)
    .const     : {} > FLASH | FLASH2     /* CONSTANT DATA                     */
//#else
//    .const     : {} > FLASH              /* CONSTANT DATA                     */
//#endif
    .cio       : {} > RAM                /* C I/O BUFFER                      */

    .pinit     : {} > FLASH              /* C++ CONSTRUCTOR TABLES            */

    .infoA     : {} > INFOA              /* MSP430 INFO FLASH MEMORY SEGMENTS */
    .infoB     : {} > INFOB
    .infoC     : {} > INFOC
    .infoD     : {} > INFOD

    .int00   : {} > INT00                /* MSP430 INTERRUPT VECTORS          */
    .int01   : {} > INT01
    .int02   : {} > INT02
    .int03   : {} > INT03
    .int04   : {} > INT04
    .int05   : {} > INT05
    .int06   : {} > INT06
    .int07   : {} > INT07
    .int08   : {} > INT08
    .int09   : {} > INT09
    .int10   : {} > INT10
    .int11   : {} > INT11
    .int12   : {} > INT12
    .int13   : {} > INT13
    .int14   : {} > INT14
    .int15   : {} > INT15
    .int16   : {} > INT16
    .int17   : {} > INT17
    .int18   : {} > INT18
    .int19   : {} > INT19
    .int20   : {} > INT20
    .int21   : {} > INT21
    .int22   : {} > INT22
    .int23   : {} > INT23
    .int24   : {} > INT24
    .int25   : {} > INT25
    .int26   : {} > INT26
    .int27   : {} > INT27
    .int28   : {} > INT28
    .int29   : {} > INT29
    .int30   : {} > INT30
    .int31   : {} > INT31
    .int32   : {} > INT32
    .int33   : {} > INT33
    .int34   : {} > INT34
    .int35   : {} > INT35
    .int36   : {} > INT36
    .int37   : {} > INT37
    .int38   : {} > INT38
    .int39   : {} > INT39
    .int40   : {} > INT40
    .int41   : {} > INT41
    .int42   : {} > INT42
    .int43   : {} > INT43
    .int44   : {} > INT44
    .int45   : {} > INT45
    .int46   : {} > INT46
    .int47   : {} > INT47
    .int48   : {} > INT48
    .int49   : {} > INT49
    .int50   : {} > INT50
    .int51   : {} > INT51
    .int52   : {} > INT52
    .int53   : {} > INT53
    .int54   : {} > INT54
    .int55   : {} > INT55
    .int56   : {} > INT56
    .int57   : {} > INT57
    .int58   : {} > INT58
    .int59   : {} > INT59
    .int60   : {} > INT60
    .int61   : {} > INT61
    .int62   : {} > INT62
    .reset   : {} > RESET              /* MSP430 RESET VECTOR               */ 
}

/****************************************************************************/
/* INCLUDE PERIPHERALS MEMORY MAP                                           */
/****************************************************************************/

-l msp430f5438a.cmd

