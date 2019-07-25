/* ============================================================================ */
/* Copyright (c) 2014, Texas Instruments Incorporated                           */
/*  All rights reserved.                                                        */
/*                                                                              */
/*  Redistribution and use in source and binary forms, with or without          */
/*  modification, are permitted provided that the following conditions          */
/*  are met:                                                                    */
/*                                                                              */
/*  *  Redistributions of source code must retain the above copyright           */
/*     notice, this list of conditions and the following disclaimer.            */
/*                                                                              */
/*  *  Redistributions in binary form must reproduce the above copyright        */
/*     notice, this list of conditions and the following disclaimer in the      */
/*     documentation and/or other materials provided with the distribution.     */
/*                                                                              */
/*  *  Neither the name of Texas Instruments Incorporated nor the names of      */
/*     its contributors may be used to endorse or promote products derived      */
/*     from this software without specific prior written permission.            */
/*                                                                              */
/*  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" */
/*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,       */
/*  THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR      */
/*  PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR            */
/*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,       */
/*  EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,         */
/*  PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; */
/*  OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,    */
/*  WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR     */
/*  OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,              */
/*  EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                          */
/* ============================================================================ */

/******************************************************************************/
/* lnk_msp430fr5969.cmd - LINKER COMMAND FILE FOR LINKING MSP430FR5969 PROGRAMS     */
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
/* Version: 1.159                                                             */
/*----------------------------------------------------------------------------*/

/****************************************************************************/
/* Specify the system memory map                                            */
/****************************************************************************/

MEMORY
{
    SFR                     : origin = 0x0000, length = 0x0010
    PERIPHERALS_8BIT        : origin = 0x0010, length = 0x00F0
    PERIPHERALS_16BIT       : origin = 0x0100, length = 0x0100
    RAM                     : origin = 0x1C00, length = 0x0800
    INFOA                   : origin = 0x1980, length = 0x0080
    INFOB                   : origin = 0x1900, length = 0x0080
    INFOC                   : origin = 0x1880, length = 0x0080
    INFOD                   : origin = 0x1800, length = 0x0080
    FRAM                    : origin = 0x4400, length = 0xBB80
    FRAM2                   : origin = 0x10000,length = 0x4000
    JTAGSIGNATURE           : origin = 0xFF80, length = 0x0004, fill = 0xFFFF
    BSLSIGNATURE            : origin = 0xFF84, length = 0x0004, fill = 0xFFFF
    IPESIGNATURE            : origin = 0xFF88, length = 0x0008, fill = 0xFFFF
    INT00                   : origin = 0xFF90, length = 0x0002
    INT01                   : origin = 0xFF92, length = 0x0002
    INT02                   : origin = 0xFF94, length = 0x0002
    INT03                   : origin = 0xFF96, length = 0x0002
    INT04                   : origin = 0xFF98, length = 0x0002
    INT05                   : origin = 0xFF9A, length = 0x0002
    INT06                   : origin = 0xFF9C, length = 0x0002
    INT07                   : origin = 0xFF9E, length = 0x0002
    INT08                   : origin = 0xFFA0, length = 0x0002
    INT09                   : origin = 0xFFA2, length = 0x0002
    INT10                   : origin = 0xFFA4, length = 0x0002
    INT11                   : origin = 0xFFA6, length = 0x0002
    INT12                   : origin = 0xFFA8, length = 0x0002
    INT13                   : origin = 0xFFAA, length = 0x0002
    INT14                   : origin = 0xFFAC, length = 0x0002
    INT15                   : origin = 0xFFAE, length = 0x0002
    INT16                   : origin = 0xFFB0, length = 0x0002
    INT17                   : origin = 0xFFB2, length = 0x0002
    INT18                   : origin = 0xFFB4, length = 0x0002
    INT19                   : origin = 0xFFB6, length = 0x0002
    INT20                   : origin = 0xFFB8, length = 0x0002
    INT21                   : origin = 0xFFBA, length = 0x0002
    INT22                   : origin = 0xFFBC, length = 0x0002
    INT23                   : origin = 0xFFBE, length = 0x0002
    INT24                   : origin = 0xFFC0, length = 0x0002
    INT25                   : origin = 0xFFC2, length = 0x0002
    INT26                   : origin = 0xFFC4, length = 0x0002
    INT27                   : origin = 0xFFC6, length = 0x0002
    INT28                   : origin = 0xFFC8, length = 0x0002
    INT29                   : origin = 0xFFCA, length = 0x0002
    INT30                   : origin = 0xFFCC, length = 0x0002
    INT31                   : origin = 0xFFCE, length = 0x0002
    INT32                   : origin = 0xFFD0, length = 0x0002
    INT33                   : origin = 0xFFD2, length = 0x0002
    INT34                   : origin = 0xFFD4, length = 0x0002
    INT35                   : origin = 0xFFD6, length = 0x0002
    INT36                   : origin = 0xFFD8, length = 0x0002
    INT37                   : origin = 0xFFDA, length = 0x0002
    INT38                   : origin = 0xFFDC, length = 0x0002
    INT39                   : origin = 0xFFDE, length = 0x0002
    INT40                   : origin = 0xFFE0, length = 0x0002
    INT41                   : origin = 0xFFE2, length = 0x0002
    INT42                   : origin = 0xFFE4, length = 0x0002
    INT43                   : origin = 0xFFE6, length = 0x0002
    INT44                   : origin = 0xFFE8, length = 0x0002
    INT45                   : origin = 0xFFEA, length = 0x0002
    INT46                   : origin = 0xFFEC, length = 0x0002
    INT47                   : origin = 0xFFEE, length = 0x0002
    INT48                   : origin = 0xFFF0, length = 0x0002
    INT49                   : origin = 0xFFF2, length = 0x0002
    INT50                   : origin = 0xFFF4, length = 0x0002
    INT51                   : origin = 0xFFF6, length = 0x0002
    INT52                   : origin = 0xFFF8, length = 0x0002
    INT53                   : origin = 0xFFFA, length = 0x0002
    INT54                   : origin = 0xFFFC, length = 0x0002
    RESET                   : origin = 0xFFFE, length = 0x0002
}

/****************************************************************************/
/* Specify the sections allocation into memory                              */
/****************************************************************************/

SECTIONS
{
    GROUP(READ_WRITE_MEMORY)
    {
       .TI.persistent : {}                  /* For #pragma persistent            */
       .cio           : {}                  /* C I/O Buffer                      */
       .sysmem        : {}                  /* Dynamic memory allocation area    */
    } PALIGN(0x0400), RUN_END(fram_rx_start) > 0x4400

    .cinit            : {}  > FRAM          /* Initialization tables             */
    .pinit            : {}  > FRAM          /* C++ Constructor tables            */
    .init_array       : {}  > FRAM          /* C++ Constructor tables            */
    .mspabi.exidx     : {}  > FRAM          /* C++ Constructor tables            */
    .mspabi.extab     : {}  > FRAM          /* C++ Constructor tables            */
#ifndef __LARGE_DATA_MODEL__
    .const            : {} >> FRAM          /* Constant data                     */
#else
    .const            : {} >> FRAM | FRAM2  /* Constant data                     */
#endif

    .text:_isr        : {}  > FRAM          /* Code ISRs                         */
#ifndef __LARGE_DATA_MODEL__
    .text             : {} >> FRAM          /* Code                              */
#else
    .text             : {} >> FRAM2 | FRAM  /* Code                              */
#endif

    GROUP(IPENCAPSULATED_MEMORY)
    {
       .ipestruct     : {}                  /* IPE Data structure             */
       .ipe           : {}                  /* IPE                            */
       .ipe:_isr      : {}                  /* IPE ISRs                       */
    } PALIGN(0x0400), RUN_START(fram_ipe_start) RUN_END(fram_ipe_end) > FRAM

    .jtagsignature : {} > JTAGSIGNATURE     /* JTAG Signature                    */
    .bslsignature  : {} > BSLSIGNATURE      /* BSL Signature                     */

    GROUP(SIGNATURE_SHAREDMEMORY)
    {
       .ipesignature   : {}                 /* IPE Signature                     */
       .jtagpassword   : {}                 /* JTAG Password                     */
    } > IPESIGNATURE

    .bss        : {} > RAM                  /* Global & static vars              */
    .data       : {} > RAM                  /* Global & static vars              */
    .TI.noinit  : {} > RAM                  /* For #pragma noinit                */
    .stack      : {} > RAM (HIGH)           /* Software system stack             */

    .infoA     : {} > INFOA              /* MSP430 INFO FRAM  Memory segments */
    .infoB     : {} > INFOB
    .infoC     : {} > INFOC
    .infoD     : {} > INFOD

    /* MSP430 Interrupt vectors          */
    .int00       : {}               > INT00
    .int01       : {}               > INT01
    .int02       : {}               > INT02
    .int03       : {}               > INT03
    .int04       : {}               > INT04
    .int05       : {}               > INT05
    .int06       : {}               > INT06
    .int07       : {}               > INT07
    .int08       : {}               > INT08
    .int09       : {}               > INT09
    .int10       : {}               > INT10
    .int11       : {}               > INT11
    .int12       : {}               > INT12
    .int13       : {}               > INT13
    .int14       : {}               > INT14
    .int15       : {}               > INT15
    .int16       : {}               > INT16
    .int17       : {}               > INT17
    .int18       : {}               > INT18
    .int19       : {}               > INT19
    .int20       : {}               > INT20
    .int21       : {}               > INT21
    .int22       : {}               > INT22
    .int23       : {}               > INT23
    .int24       : {}               > INT24
    .int25       : {}               > INT25
    .int26       : {}               > INT26
    .int27       : {}               > INT27
    .int28       : {}               > INT28
    .int29       : {}               > INT29
    AES256       : { * ( .int30 ) } > INT30 type = VECT_INIT
    RTC          : { * ( .int31 ) } > INT31 type = VECT_INIT
    PORT4        : { * ( .int32 ) } > INT32 type = VECT_INIT
    PORT3        : { * ( .int33 ) } > INT33 type = VECT_INIT
    TIMER3_A1    : { * ( .int34 ) } > INT34 type = VECT_INIT
    TIMER3_A0    : { * ( .int35 ) } > INT35 type = VECT_INIT
    PORT2        : { * ( .int36 ) } > INT36 type = VECT_INIT
    TIMER2_A1    : { * ( .int37 ) } > INT37 type = VECT_INIT
    TIMER2_A0    : { * ( .int38 ) } > INT38 type = VECT_INIT
    PORT1        : { * ( .int39 ) } > INT39 type = VECT_INIT
    TIMER1_A1    : { * ( .int40 ) } > INT40 type = VECT_INIT
    TIMER1_A0    : { * ( .int41 ) } > INT41 type = VECT_INIT
    DMA          : { * ( .int42 ) } > INT42 type = VECT_INIT
    USCI_A1      : { * ( .int43 ) } > INT43 type = VECT_INIT
    TIMER0_A1    : { * ( .int44 ) } > INT44 type = VECT_INIT
    TIMER0_A0    : { * ( .int45 ) } > INT45 type = VECT_INIT
    ADC12        : { * ( .int46 ) } > INT46 type = VECT_INIT
    USCI_B0      : { * ( .int47 ) } > INT47 type = VECT_INIT
    USCI_A0      : { * ( .int48 ) } > INT48 type = VECT_INIT
    WDT          : { * ( .int49 ) } > INT49 type = VECT_INIT
    TIMER0_B1    : { * ( .int50 ) } > INT50 type = VECT_INIT
    TIMER0_B0    : { * ( .int51 ) } > INT51 type = VECT_INIT
    COMP_E       : { * ( .int52 ) } > INT52 type = VECT_INIT
    UNMI         : { * ( .int53 ) } > INT53 type = VECT_INIT
    SYSNMI       : { * ( .int54 ) } > INT54 type = VECT_INIT
    .reset       : {}               > RESET  /* MSP430 Reset vector         */ 
}

/****************************************************************************/
/* MPU/IPE Specific memory segment definitons                               */
/****************************************************************************/

#ifdef _IPE_ENABLE
   #define IPE_MPUIPLOCK 0x0080
   #define IPE_MPUIPENA 0x0040
   #define IPE_MPUIPPUC 0x0020

   // Evaluate settings for the control setting of IP Encapsulation
   #if defined(_IPE_ASSERTPUC1)
        #if defined(_IPE_LOCK ) && (_IPE_ASSERTPUC1 == 0x08))
         fram_ipe_enable_value = (IPE_MPUIPENA | IPE_MPUIPPUC |IPE_MPUIPLOCK);
        #elif defined(_IPE_LOCK )
         fram_ipe_enable_value = (IPE_MPUIPENA | IPE_MPUIPLOCK);
      #elif (_IPE_ASSERTPUC1 == 0x08)
         fram_ipe_enable_value = (IPE_MPUIPENA | IPE_MPUIPPUC);
      #else
         fram_ipe_enable_value = (IPE_MPUIPENA);
      #endif
   #else
      #if defined(_IPE_LOCK )
         fram_ipe_enable_value = (IPE_MPUIPENA | IPE_MPUIPLOCK);
      #else
         fram_ipe_enable_value = (IPE_MPUIPENA);
      #endif
   #endif

   // Segment definitions
   #ifdef _IPE_MANUAL                  // For custom sizes selected in the GUI
      fram_ipe_border1 = (_IPE_SEGB1>>4);
      fram_ipe_border2 = (_IPE_SEGB2>>4);
   #else                           // Automated sizes generated by the Linker
      fram_ipe_border2 = (fram_ipe_end + 0x400)>> 4;
      fram_ipe_border1 = fram_ipe_start >> 4;
   #endif

   fram_ipe_settings_struct_address = Ipe_settingsStruct >> 4;
   fram_ipe_checksum = ~((fram_ipe_enable_value & fram_ipe_border2 & fram_ipe_border1) | (fram_ipe_enable_value & ~fram_ipe_border2 & ~fram_ipe_border1) | (~fram_ipe_enable_value & fram_ipe_border2 & ~fram_ipe_border1) | (~fram_ipe_enable_value & ~fram_ipe_border2 & fram_ipe_border1));
#endif

#ifdef _MPU_ENABLE
   #define MPUPW (0xA500)    /* MPU Access Password */
   #define MPUENA (0x0001)   /* MPU Enable */
   #define MPULOCK (0x0002)  /* MPU Lock */
   #define MPUSEGIE (0x0010) /* MPU Enable NMI on Segment violation */

   __mpu_enable = 1;
   // Segment definitions
   #ifdef _MPU_MANUAL // For custom sizes selected in the GUI
      mpu_segment_border1 = _MPU_SEGB1 >> 4;
      mpu_segment_border2 = _MPU_SEGB2 >> 4;
      mpu_sam_value = (_MPU_SAM0 << 12) | (_MPU_SAM3 << 8) | (_MPU_SAM2 << 4) | _MPU_SAM1;
   #else // Automated sizes generated by Linker
      mpu_segment_border1 = fram_rx_start >> 4;
      mpu_segment_border2 = fram_rx_start >> 4;
      mpu_sam_value = 0x1513; // Info R, Seg3 RX, Seg2 R, Seg1 RW
   #endif
   #ifdef _MPU_LOCK
      #ifdef _MPU_ENABLE_NMI
         mpu_ctl0_value = MPUPW | MPUENA | MPULOCK | MPUSEGIE;
      #else
         mpu_ctl0_value = MPUPW | MPUENA | MPULOCK;
      #endif
   #else
      #ifdef _MPU_ENABLE_NMI
         mpu_ctl0_value = MPUPW | MPUENA | MPUSEGIE;
      #else
         mpu_ctl0_value = MPUPW | MPUENA;
      #endif
   #endif
#endif

/****************************************************************************/
/* Include peripherals memory map                                           */
/****************************************************************************/

-l msp430fr5969.cmd

