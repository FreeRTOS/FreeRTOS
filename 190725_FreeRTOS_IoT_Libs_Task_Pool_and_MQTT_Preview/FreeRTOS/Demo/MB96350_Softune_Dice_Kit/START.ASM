;====================================================================
; $Id: START.ASM,v 1.31 2008/02/27 10:23:34 mcuae Exp $
;====================================================================
; THIS SAMPLE CODE IS PROVIDED AS IS AND IS SUBJECT TO ALTERATIONS.  
;  FUJITSU MICROELECTRONICS ACCEPTS NO RESPONSIBILITY OR LIABILITY   
;         FOR ANY ERRORS OR ELIGIBILITY FOR ANY PURPOSES.            
;                                                                    
;    Startup file for memory and basic controller initialisation     
;                                                                    
;    MB96300 Family C Compiler
;                                                                    
;    (C) FUJITSU MICROELECTRONICS EUROPE 1998-2008                   
;====================================================================

          .PROGRAM  STARTUP  
          .TITLE    "STARTUP FILE FOR MEMORY INITIALISATION"

;====================================================================
; 1  Contents
;====================================================================
; 1   Contents
; 2   Disclaimer
; 3   History
;
; 4   SETTINGS              (USER INTERFACE)
; 4.1   Controller Series, Device
; 4.2   C-language Memory model
; 4.3   Function-Call Interface
; 4.4   Constant Data Handling
; 4.5   Stack Type and Stack Size
; 4.6   General Register Bank
; 4.7   Low-Level Library Interface

; 4.8   Clock Selection
; 4.9   Clock Stabilization Time
; 4.10  External Bus Interface
; 4.11  ROM Mirror configuration
; 4.12  Flash Security
; 4.13  Flash Write Protection
; 4.14  Boot Vector
; 4.15  UART scanning
; 4.16  Enable RAMCODE Copying
; 4.17  Enable information stamp in ROM
; 4.18  Enable Background Debugging Mode
;
; 5   Section and Data Declaration
; 5.1   Several fixed addresses (fixed for MB963xx controllers)
; 5.2   Declaration of __near addressed data sections
; 5.3   Declaration of RAMCODE section and labels
; 5.4   Declaration of sections containing other sections description
; 5.5   Stack area and stack top definition/declaration
; 5.6   Direct page register dummy label definition
; 5.7   Set Flash Security
; 5.8   Set Flash write protection
; 5.9   Debug address specification
;
; 6   Start-Up Code
; 6.1   Import external symbols
; 6.2   Program start (the boot vector should point here)
; 6.3   "NOT RESET YET" WARNING
; 6.4   Initialisation of processor status
; 6.5   Set clock ratio (ignore subclock)
; 6.6   Set external bus configuration
; 6.7   Prepare stacks and set the active stack type
; 6.8   Copy initial values to data areas
; 6.9   Clear uninitialized data areas to zero
; 6.10  Set Data Bank Register (DTB) and Direct Page Register (DPR)
; 6.11  ICU register initialization workaround
; 6.12  Wait for PLL to stabilize
; 6.13  Initialise Low-Level Library Interface
; 6.14  Call C-language main function
; 6.15  Shut down library
; 6.16  Program end loop
;
;====================================================================
; 2  Disclaimer
;====================================================================
;                  FUJITSU MICROELECTRONICS EUROPE GMBH
;                  Pittlerstrasse 47, 63225 Langen, Germany 
;                  Tel.:++49 6103 690-0, Fax -122
;                                                               
;    The following software is for demonstration purposes only. 
;    It is not fully tested, nor validated in order to fulfil 
;    its task under all circumstances. Therefore, this software 
;    or any part of it must only be used in an evaluation       
;    laboratory environment.                                    
;    This software is subject to the rules of our standard      
;    DISCLAIMER, that is delivered with our SW-tools on the 
;    Fujitsu Microcontrollers DVD (V5.0 or higher "\START.HTM") or
;    on our Internet Pages:                                      
;    http://www.fme.gsdc.de/gsdc.htm
;    http://emea.fujitsu.com/microelectronics 
;
;====================================================================
; 3  History
;====================================================================
; $Id: START.ASM,v 1.31 2008/02/27 10:23:34 mcuae Exp $

#define VERSION  "1.31"
/*
$Log: START.ASM,v $
Revision 1.31  2008/02/27 10:23:34  mcuae
- CPU_48MHZ_CLKP1_32MHZ_CLKP2_16MHZ clock setting added

Revision 1.30  2008/02/26 15:28:21  mcuae
- clock settings corrected
- Main/Satellite Flash term outdated, now: Flash A, Flash B

Revision 1.29  2008/02/11 15:26:33  mwilla
- device configuration for ext. bus i/f settings updated

Revision 1.28  2008/01/25 08:03:48  mwilla
- clock settings corrected and optimized

Revision 1.27  2008/01/04 12:26:08  mwilla
- device list expanded
- clock settings optimized

Revision 1.26  2007/10/17 11:53:34  mwilla
- device list expanded
- ICU initialization workaround added
- sections settings grouped

Revision 1.25  2007/09/28 07:33:18  mwilla
- Bug in BDM baudrate calculation corrected

Revision 1.24  2007/09/26 14:03:08  mwilla
- Device list for MB96340 series updated and expanded

Revision 1.23  2007/08/06 14:48:16  mwilla
- BDM section always reserved, filled with 0xFF, if not configured

Revision 1.22  2007/08/02 08:34:03  mwilla
- communication mode bits of BDM configuration grouped

Revision 1.21  2007/07/13 08:23:05  mwilla
- device selection for BDM baud rate improved

Revision 1.20  2007/06/12 10:43:57  mwilla
- BDM-Baud-Rate calculation includes crystal frequency

Revision 1.19  2007/06/06 07:46:55  mwilla
- add Background Debugging Configuration
- Stack initialization moved before variable initialization
- values of cystal frequency and device macros changed

Revision 1.18  2007/04/16 07:56:02  phuene
- update clock settings when crystal is 8 MHz so that the CLKVCO is low

Revision 1.17  2007/04/10 11:30:43  phuene
- add MB96320 Series
- Clock settings optimized for CPU_8MHZ_CLKP2_8MHZ, CPU_12MHZ_CLKP2_12MHZ, CPU_16MHZ_CLKP2_16MHZ, CPU_24MHZ_CLKP2_24MHZ, CPU_32MHZ_CLKP2_32MHZ
- make the selection for the individual devices also consider the selected Series
- support 8 MHz crystal
- add clock setting CPU_32MHZ_CLKP1_16MHZ_CLKP2_16MHZ
- prohibit CPU_32MHZ_CLKP2_16MHZ, CPU_CLKP1_16MHZ_CLKP2_16MHZ for MB96F348H and MB96F348T according to functional limitation 16FXFL0014

Revision 1.16  2007/02/07 12:38:10  phuene
- support disabling the UART scanning in Internal Vector Mode
- distinguish between Reset Vector and Boot Vector: the Boot Vector points to the start of the user application

Revision 1.15  2007/02/07 09:00:19  phuene
- add .SKIP instructions to occupy the whole ROM configuration block area

Revision 1.14  2007/01/29 13:15:06  phuene
- fix CPU_4MHZ_MAIN_CLKP2_4MHZ clock setting

Revision 1.13  2007/01/03 10:40:14  phuene
- change clock setting CPU_24MHZ_CLKP2_16MHZ to CPU_24MHZ_CLKP2_12MHZ; this allows for better performance of MB96F348H/T
- use additional preprocessor statements to avoid checking for PLL ready twice in some cases

Revision 1.12  2007/01/02 10:16:20  phuene
- correct CLKP2 (CAN) clock for CPU_32MHZ and MB96F348H/T
- correct CLKP2 (CAN) clock for CPU_24MHZ for all other devices than MB96F348H/T

Revision 1.11  2006/12/28 10:49:52  phuene
- corrected PLL setting for CPU_16MHZ for MB96348H, MB96348T

Revision 1.10  2006/12/28 08:41:57  phuene
- correct revision number at new location

Revision 1.1  2006/12/28 07:20:01  phuene
- new location in CVS

Revision 1.9  2006/12/27 13:00:45  phuene
- add support for ROM Mirror when using the Simulator
- add support for 16FXFL0022, 16FXFL0023

Revision 1.8  2006/12/11 16:43:37  phuene
- fix typo

Revision 1.7  2006/12/11 16:35:08  phuene
- add setting for Clock Stabilization Times
- modify clock settings:
  - CLKP2 < 28 MHz
  - remove clock settings using more wait cycles than absolutely required

Revision 1.6  2006/11/03 13:38:45  phuene
- modify clock settings to also set the Flash Memory Timing
- add support for both parameter passing models

Revision 1.5  2006/08/07 14:01:44  phuene
- change default clock setting to PLLx4 for CLKS1, CLKS2
- correct clock setting
- disable Flash Security by default for Main Flash, Satellite Flash
- disable availability of Satellite Flash by default

Revision 0.1  2006/01/25 15:37:46  phu
- initial version based on start.asm for MB90340 Series, version 3.8
Revision 0.2  2006/07/14 15:37:46  phu
- include PIER settings for External Bus operation
Revision 0.3  2006/07/14 15:37:46  phu
- add MB96350 Series
- correct PIER settings for HRQ and RDY signals
Revision 0.4  2006/08/07 15:35:35  phu
- change default clock setting to PLLx4 for CLKS1, CLKS2
- correct clock setting
- disable Flash Security by default for Main Flash, Satellite Flash
- disable availability of Satellite Flash by default
*/
;====================================================================

;====================================================================
; 4  Settings
;====================================================================
;
; CHECK ALL OPTIONS WHETHER THEY FIT TO THE APPLICATION
;
; Configure this startup file in the "Settings" section. Search for
; comments with leading "; <<<". This points to the items to be set.
;====================================================================
#set      OFF       0
#set      ON        1

;====================================================================
; 4.1  Controller Series, Device
;====================================================================

#set      MB96320   0
#set      MB96330   1
#set      MB96340   2
#set      MB96350   3
#set      MB96360   4
#set      MB96370   5
#set      MB96380   6
#set      MB96390   7

#set      SERIES    MB96350        ; <<< select Series


; Please specify the device according to the following selection;
; x = {W, S}.
; Note: Do not change order because of device number dependency in
; 6.5 Clock settings, 5.9 Debug address specification,
; and 6.11 ICU register initialization workaround!

; MB96320 series
#set      MB96326RxA   1
#set      MB96326YxA   2

; MB96330 series
#set      MB96338RxA   1
#set      MB96338UxA   2

; MB96340 series
#set      MB96348HxA   1
#set      MB96348TxA   2
#set      MB96346RxA   3 
#set      MB96346YxA   4 
#set      MB96346AxA   5
#set      MB96347RxA   6 
#set      MB96347YxA   7 
#set      MB96347AxA   8
#set      MB96348RxA   9 
#set      MB96348YxA  10 
#set      MB96348AxA  11
#set      MB96346RxB  12 
#set      MB96346AxB  13
#set      MB96346YxB  14 
#set      MB96347RxB  15 
#set      MB96347AxB  16
#set      MB96347YxB  17 
#set      MB96348CxA  18
#set      MB96348HxB  19 
#set      MB96348TxB  20 
#set      MB96348RxB  21 
#set      MB96348AxB  22
#set      MB96348YxB  23 
#set      MB96348CxC  24
#set      MB96348HxC  25 
#set      MB96348TxC  26 

; MB96350 series
#set      MB96356RxA   1
#set      MB96356YxA   2

; MB96360 series
#set      MB96365RxA   1
#set      MB96365YxA   2

; MB96370 series
#set      MB96379RxA   1
#set      MB96379YxA   2

; MB96380 series
#set      MB96384RxA   1
#set      MB96384YxA   2
#set      MB96385RxA   3
#set      MB96385YxA   4
#set      MB96386RxA   5
#set      MB96386YxA   6
#set      MB96387RxA   7
#set      MB96387YxA   8
#set      MB96386RxB   9
#set      MB96386YxB  10
#set      MB96387RxB  11
#set      MB96387YxB  12

; MB96390 series
#set      MB96395RxA   1
    

#set      DEVICE    MB96356RxA      ; <<< select device

;====================================================================
; 4.2  C-language Memory model
;====================================================================

                                   ;      data      code   
#set      SMALL     0              ;     16 Bit    16 Bit
#set      MEDIUM    1              ;     16 Bit    24 Bit
#set      COMPACT   2              ;     24 Bit    16 Bit
#set      LARGE     3              ;     24 Bit    24 Bit
#set      AUTOMODEL 4              ; works always, might occupy two
                                   ; additional bytes


#set      MEMMODEL  AUTOMODEL      ; <<< C-memory model

; The selected memory model should be set in order to fit to the
; model selected for the compiler. 
; Note, in this startup version AUTOMODEL will work for all
; C-models. However, if the compiler is configured for SMALL or
; COMPACT, two additional bytes on stack are occupied. If this is not
; acceptable, the above setting should be set to the correct model.

;====================================================================
; 4.3  Function-Call Interface
;====================================================================
 
          #if __REG_PASS__
            .REG_PASS
          #endif

; Above statement informs Assembler on compatibility of start-up code
; to  Function Call Interface  as selected for the application. There
; is nothing to configure.
; The Function-Call Interface specifies the method of passing parame-
; ter from function caller to callee.  The standard method of FCC907S
; compiler  uses  "stack argument passing".  Alternatively,  language
; tools can be configured for "register argument passing".
; For details see the compiler manual.
; This start-up file is compatible to both interfaces.

;====================================================================
; 4.4  Constant Data Handling
;====================================================================

#set      ROMCONST    0            ; works only with compiler ROMCONST
#set      RAMCONST    1            ; works with BOTH compiler settings
#set      AUTOCONST   RAMCONST     ; works with BOTH compiler settings
                              
#set      CONSTDATA   AUTOCONST    ; <<< set RAM/ROM/AUTOCONST

; - AUTOCONST (default) is the same as RAMCONST
; - RAMCONST/AUTOCONST should always work, even if compiler is set to
;   ROMCONST. If compiler is set to ROMCONST and this startup file is
;   set to RAMCONST or AUTOCONST, this startup file will generate an
;   empty section CINIT in RAM. However, the code, which copies from 
;   CONST to CINIT will not have any effect, because size of section is 0.
; - It is highly recommended to set the compiler to ROMCONST for 
;   single-chip mode or internal ROM+ext bus. The start-up file 
;   should be set to AUTOCONST.
; - ROMCONST setting on systems with full external bus requires exter-
;   nal address mapping.
;   Single-chip can be emulated by the emulator debugger.
;   ROM mirror can also be used with simulator.
;
; see also ROM MIRROR options 

;====================================================================
; 4.5  Stack Type and Stack Size
;====================================================================

#set      USRSTACK       0      ; user stack: for main program
#set      SYSSTACK       1      ; system stack: for main program and interrupts

#set      STACKUSE  SYSSTACK    ; <<< set active stack

#set      STACK_RESERVE  ON     ; <<< reserve stack area in this module
#set      STACK_SYS_SIZE 200   ; <<< byte size of System stack
#set      STACK_USR_SIZE 2      ; <<< byte size of User stack 

#set      STACK_FILL     ON     ; <<< fills the stack area with pattern
#set      STACK_PATTERN  0x55AA ; <<< the pattern to write to stack

; - If the active stack is set to SYSSTACK, it is used for main program
;   and interrupts. In this case, the user stack can be set to a dummy
;   size.
;   If the active stack is set to user stack, it is used for the main
;   program but the system stack is automatically activated, if an inter-
;   rupt is serviced. Both stack areas must have a reasonable size.
; - If STACK_RESERVE is ON, the sections USTACK and SSTACK are reserved 
;   in this module. Otherwise, they have to be reserved in other modules.
;   If STACK_RESERVE is OFF, the size definitions STACK_SYS_SIZE and 
;   STACK_USR_SIZE have no meaning.
; - Even if they are reserved in other modules, they are still initialised
;   in this start-up file.
; - Filling the stack with a pattern allows to dynamically check the stack 
;   area, which had already been used.
;
; - If only system stack is used and SSB is linked to a different bank
;   than USB, make sure that all C-modules (which generate far pointers 
;   to stack data) have "#pragma SSB". Applies only to exclusive confi-
;   gurations.
; - Note, several library functions require quite a big stack (due to 
;   ANSI). Check the stack information files (*.stk) in the LIB\907
;   directory.

;====================================================================
; 4.6  General Register Bank
;====================================================================

#set      REGBANK   0           ; <<< set default register bank

; set the General Register Bank that is to be used after startup.
; Usually, this is bank 0, which applies to address H'180..H'18F. Set
; in the range from 0 to 31.
; Note: All used register banks have to be reserved (linker options).

#if REGBANK > 31 || REGBANK < 0
#  error REGBANK setting out of range
#endif

;====================================================================
; 4.7  Low-Level Library Interface
;====================================================================

#set      CLIBINIT       OFF    ; <<< select extended library usage

; This option has only to be set, if stream-IO/standard-IO function of
; the C-library have to be used (printf(), fopen()...). This also 
; requires low-level functions to be defined by the application 
; software.
; For other library functions (like e.g. sprintf()) all this is not
; necessary. However, several functions consume a large amount of stack.

;====================================================================
; 4.8  Clock Selection
;====================================================================

; The clock selection requires that a 4 MHz external clock is provided
; as the Main Clock. If a different frequency is used, the Flash Memory
; Timing settings must be checked!

#set      CLOCKWAIT      ON     ; <<< wait for stabilized clock, if
                                ;     Main Clock or PLL is used

; The clock is set quite early. However, if CLOCKWAIT is ON, polling 
; for machine clock to be switched to Main Clock or PLL is done at 
; the end of this file. Therefore, the stabilization time is not 
; wasted. Main() will finally start at correct speed. Resources can 
; be used immediately.
; Note: Some frequency settings (below) necessarily need a stabilized
; PLL for final settings. In these cases, the CLOCKWAIT setting above 
; does not have any effect.
;
; This startup file version does not support subclock.

#set      FREQ_4MHZ       D'4000000L
#set      FREQ_8MHZ       D'8000000L

#set      CRYSTAL         FREQ_4MHZ  ; <<< select external crystal frequency

#set      CPU_4MHZ_MAIN_CLKP2_4MHZ            0x0004
#set      CPU_4MHZ_PLL_CLKP2_4MHZ             0x0104
#set      CPU_8MHZ_CLKP2_8MHZ                 0x0108
#set      CPU_12MHZ_CLKP2_12MHZ               0x010C
#set      CPU_16MHZ_CLKP2_16MHZ               0x0110
#set      CPU_24MHZ_CLKP2_12MHZ               0x0118
#set      CPU_32MHZ_CLKP2_16MHZ               0x0120
#set      CPU_32MHZ_CLKP1_16MHZ_CLKP2_16MHZ   0x0220
#set      CPU_48MHZ_CLKP2_16MHZ               0x0130
#set      CPU_48MHZ_CLKP1_32MHZ_CLKP2_16MHZ   0x0230
#set      CPU_56MHZ_CLKP2_14MHZ               0x0138

#set      CLOCK_SPEED     CPU_56MHZ_CLKP2_14MHZ               ; <<< set clock speeds

; The peripheral clock CLKP1 is set to the same frequency than the CPU.
; The peripheral clock CLKP2 has its setting. This is because it
; feeds only the CAN controllers and Sound Generators. These do not
; need high frequency clocks.

;====================================================================
; 4.9  Clock Stabilization Time
;====================================================================

#set      MC_2_10_CYCLES   0
#set      MC_2_12_CYCLES   1
#set      MC_2_13_CYCLES   2
#set      MC_2_14_CYCLES   3
#set      MC_2_15_CYCLES   4
#set      MC_2_16_CYCLES   5
#set      MC_2_17_CYCLES   6
#set      MC_2_18_CYCLES   7

#set      MC_STAB_TIME     MC_2_15_CYCLES ; <<< select Main Clock Stabilization Time

;====================================================================
; 4.10 External Bus Interface
;====================================================================

#set      SINGLE_CHIP     0        ; all internal
#set      INTROM_EXTBUS   1        ; mask ROM or FLASH memory used
#set      EXTROM_EXTBUS   2        ; full external bus (INROM not used) 

#set      BUSMODE SINGLE_CHIP      ; <<< set bus mode (see mode pins)

#set      MULTIPLEXED     0        ; 
#set      NON_MULTIPLEXED 1        ; only if supported by the device

#set      ADDRESSMODE MULTIPLEXED  ; <<< set address-mode

; Some devices support multiplexed and/or non-multiplexed Bus mode
; please refer to the related datasheet/hardwaremanual


; If BUSMODE is "SINGLE_CHIP", ignore remaining bus settings.

; Select the used Chip Select areas
#set      CHIP_SELECT0       OFF   ; <<< enable chip select area
#set      CHIP_SELECT1       OFF   ; <<< enable chip select area
#set      CHIP_SELECT2       OFF   ; <<< enable chip select area
#set      CHIP_SELECT3       OFF   ; <<< enable chip select area
#set      CHIP_SELECT4       OFF   ; <<< enable chip select area
#set      CHIP_SELECT5       OFF   ; <<< enable chip select area

#set      HOLD_REQ           OFF   ; <<< select Hold function
#set      EXT_READY          OFF   ; <<< select external Ready function
#set      EXT_CLOCK_ENABLE   OFF   ; <<< select external bus clock output
#set      EXT_CLOCK_INVERT   OFF   ; <<< select clock inversion
#set      EXT_CLOCK_SUSPEND  OFF   ; <<< select if external clock is suspended when no transfer in progress

; The external bus clock is derived from core clock CLKB. Select the divider for the external bus clock.

#set      EXT_CLOCK_DIV1     0
#set      EXT_CLOCK_DIV2     1
#set      EXT_CLOCK_DIV4     2
#set      EXT_CLOCK_DIV8     3
#set      EXT_CLOCK_DIV16    4
#set      EXT_CLOCK_DIV32    5
#set      EXT_CLOCK_DIV64    6
#set      EXT_CLOCK_DIV128   7

#set      EXT_CLOCK_DIVISION  EXT_CLOCK_DIV1 ; <<< select clock divider

#set      ADDR_PINS_23_16    B'00000000     ; <<< select used address lines 
                                            ;     A23..A16 to be output.
#set      ADDR_PINS_15_8     B'00000000     ; <<< select used address lines 
                                            ;     A15..A8 to be output.
#set      ADDR_PINS_7_0      B'00000000     ; <<< select used address lines 
                                            ;     A7..A0 to be output.

#set      LOW_BYTE_SIGNAL    OFF   ; <<< select low byte signal LBX
#set      HIGH_BYTE_SIGNAL   OFF   ; <<< select high byte signal UBX
#set      LOW_WRITE_STROBE   OFF   ; <<< select write strobe signal WRLX/WRX
#set      HIGH_WRITE_STROBE  OFF   ; <<< select write strobe signal WRHX
#set      READ_STROBE        OFF   ; <<< select read strobe signal RDX
#set      ADDRESS_STROBE     OFF   ; <<< select address strobe signal ALE/ASX
#set      ADDRESS_STROBE_LVL OFF   ; <<< select address strobe function: OFF - active low; ON - active high


#set      CS0_CONFIG  B'0000000000000000    ; <<< select Chip Select Area 0 configuration
;                       |||||||||||||+++-- Automatic wait cycles (0: 0, 1: 1, 2: 2, 3: 3, 4: 4, 5: 8, 6: 16, 7: 32)
;                       ||||||||||||+----- Address Cycle Extension (0: not extended, 1: extension by 1 cycle)
;                       |||||||||||+------ Strobe timing (0: scheme 0, 1: scheme 1)
;                       ||||||||||+------- Write strobe function (0: WRLX strobe, 1: WRX strobe)
;                       |||||||||+-------- Endianess (0: little endian, 1: big endian)
;                       ||||||||+--------- Bus width (0: 16bit, 1: 8bit)
;                       |||||+++---------- ignored
;                       ||||+------------- Chip Select output enable (0: CS disabled, 1: CS enabled)
;                       |||+-------------- Chip Select level (0: low active, 1: high active)
;                       ||+--------------- Access type limitation (0: code and data, 1: data only)
;                       ++---------------- ignored

#set      CS1_CONFIG  B'0000000000000000    ; <<< select Chip Select Area 1 configuration
;                       |||||||||||||+++-- Automatic wait cycles (0: 0, 1: 1, 2: 2, 3: 3, 4: 4, 5: 8, 6: 16, 7: 32)
;                       ||||||||||||+----- Address Cycle Extension (0: not extended, 1: extension by 1 cycle)
;                       |||||||||||+------ Strobe timing (0: scheme 0, 1: scheme 1)
;                       ||||||||||+------- Write strobe function (0: WRLX strobe, 1: WRX strobe)
;                       |||||||||+-------- Endianess (0: little endian, 1: big endian)
;                       ||||||||+--------- Bus width (0: 16bit, 1: 8bit)
;                       |||||+++---------- ignored
;                       ||||+------------- Chip Select output enable (0: CS disabled, 1: CS enabled)
;                       |||+-------------- Chip Select level (0: low active, 1: high active)
;                       ||+--------------- Access type limitation (0: code and data, 1: data only)
;                       ++---------------- ignored

#set      CS2_CONFIG  B'0000011000000000    ; <<< select Chip Select Area 2 configuration
;                       |||||||||||||+++-- Automatic wait cycles (0: 0, 1: 1, 2: 2, 3: 3, 4: 4, 5: 8, 6: 16, 7: 32)
;                       ||||||||||||+----- Address Cycle Extension (0: not extended, 1: extension by 1 cycle)
;                       |||||||||||+------ Strobe timing (0: scheme 0, 1: scheme 1)
;                       ||||||||||+------- Write strobe function (0: WRLX strobe, 1: WRX strobe)
;                       |||||||||+-------- Endianess (0: little endian, 1: big endian)
;                       ||||||||+--------- Bus width (0: 16bit, 1: 8bit)
;                       |||||+++---------- External area size (0: 64kB, 1: 128kB, 2: 256kB, 3: 512kB, 4: 1MB, 5: 2MB, 6: 4MB, 7: 8MB)
;                       ||||+------------- Chip Select output enable (0: CS disabled, 1: CS enabled)
;                       |||+-------------- Chip Select level (0: low active, 1: high active)
;                       ||+--------------- Access type limitation (0: code and data, 1: data only)
;                       ++---------------- ignored

#set      CS3_CONFIG  B'0000011000000000    ; <<< select Chip Select Area 3 configuration
;                       |||||||||||||+++-- Automatic wait cycles (0: 0, 1: 1, 2: 2, 3: 3, 4: 4, 5: 8, 6: 16, 7: 32)
;                       ||||||||||||+----- Address Cycle Extension (0: not extended, 1: extension by 1 cycle)
;                       |||||||||||+------ Strobe timing (0: scheme 0, 1: scheme 1)
;                       ||||||||||+------- Write strobe function (0: WRLX strobe, 1: WRX strobe)
;                       |||||||||+-------- Endianess (0: little endian, 1: big endian)
;                       ||||||||+--------- Bus width (0: 16bit, 1: 8bit)
;                       |||||+++---------- External area size (0: 64kB, 1: 128kB, 2: 256kB, 3: 512kB, 4: 1MB, 5: 2MB, 6: 4MB, 7: 8MB)
;                       ||||+------------- Chip Select output enable (0: CS disabled, 1: CS enabled)
;                       |||+-------------- Chip Select level (0: low active, 1: high active)
;                       ||+--------------- Access type limitation (0: code and data, 1: data only)
;                       ++---------------- ignored

#set      CS4_CONFIG  B'0000011000000000    ; <<< select Chip Select Area 4 configuration
;                       |||||||||||||+++-- Automatic wait cycles (0: 0, 1: 1, 2: 2, 3: 3, 4: 4, 5: 8, 6: 16, 7: 32)
;                       ||||||||||||+----- Address Cycle Extension (0: not extended, 1: extension by 1 cycle)
;                       |||||||||||+------ Strobe timing (0: scheme 0, 1: scheme 1)
;                       ||||||||||+------- Write strobe function (0: WRLX strobe, 1: WRX strobe)
;                       |||||||||+-------- Endianess (0: little endian, 1: big endian)
;                       ||||||||+--------- Bus width (0: 16bit, 1: 8bit)
;                       |||||+++---------- External area size (0: 64kB, 1: 128kB, 2: 256kB, 3: 512kB, 4: 1MB, 5: 2MB, 6: 4MB, 7: 8MB)
;                       ||||+------------- Chip Select output enable (0: CS disabled, 1: CS enabled)
;                       |||+-------------- Chip Select level (0: low active, 1: high active)
;                       ||+--------------- Access type limitation (0: code and data, 1: data only)
;                       ++---------------- ignored

#set      CS5_CONFIG  B'0000011000000000    ; <<< select Chip Select Area 5 configuration
;                       |||||||||||||+++-- Automatic wait cycles (0: 0, 1: 1, 2: 2, 3: 3, 4: 4, 5: 8, 6: 16, 7: 32)
;                       ||||||||||||+----- Address Cycle Extension (0: not extended, 1: extension by 1 cycle)
;                       |||||||||||+------ Strobe timing (0: scheme 0, 1: scheme 1)
;                       ||||||||||+------- Write strobe function (0: WRLX strobe, 1: WRX strobe)
;                       |||||||||+-------- Endianess (0: little endian, 1: big endian)
;                       ||||||||+--------- Bus width (0: 16bit, 1: 8bit)
;                       |||||+++---------- External area size (0: 64kB, 1: 128kB, 2: 256kB, 3: 512kB, 4: 1MB, 5: 2MB, 6: 4MB, 7: 8MB)
;                       ||||+------------- Chip Select output enable (0: CS disabled, 1: CS enabled)
;                       |||+-------------- Chip Select level (0: low active, 1: high active)
;                       ||+--------------- Access type limitation (0: code and data, 1: data only)
;                       ++---------------- ignored


#set      CS2_START  0x00       ; <<< select start bank of chip select area; valid values: 0x00..0xFF
#set      CS3_START  0x40       ; <<< select start bank of chip select area; valid values: 0x00..0xFF
#set      CS4_START  0x80       ; <<< select start bank of chip select area; valid values: 0x00..0xFF
#set      CS5_START  0xC0       ; <<< select start bank of chip select area; valid values: 0x00..0xFF


;====================================================================
; 4.11 ROM Mirror configuration
;====================================================================

#set      MIRROR_8KB    0
#set      MIRROR_16KB   1
#set      MIRROR_24KB   2
#set      MIRROR_32KB   3

#set      ROMMIRROR     ON          ; <<< ROM mirror function ON/OFF
#set      MIRROR_BANK   0xF         ; <<< ROM Mirror bank, allowed entries: 0x0..0xF for the banks 0xF0..0xFF
#set      MIRROR_SIZE   MIRROR_32KB ; <<< ROM Mirror size

; One can select which ROM area to mirror into the upper half of bank 00.
; If ROMMIRROR = OFF is selected, the address range 0x008000..0x00FFFF
; shows the contents of the respective area of bank 1: 0x018000..0x01FFFF.
; If ROMMIRROR = ON is selected, the memory bank to mirror can be selected.
; Available banks are 0xF0 to 0xFF. Furthermore, the ROM Mirror area size can
; be selected. 4 sizes are available: 8 kB, 16 kB, 24 kB, or 32 kB. The ROM Mirror
; from the highest address of the selected bank downwards, e.g. if bank 0xFF and
; mirror size 24 kB is selected, the memory range 0xFFA000..0xFFFFFF is mirrored
; to address range 0x00A000..0x00FFFF. The memory area not selected for
; ROM Mirror is still mirrored from bank 0x01.
; This is necessary to get the compiler ROMCONST option working. This is intended
; to increase performance, if a lot of dynamic data have to be accessed.
; In SMALL and MEDIUM model these data can be accessed within bank 0,
; which allows to use near addressing. Please make sure to have the linker 
; setting adjusted accordingly!


;====================================================================
; 4.12 Flash Security
;====================================================================

#set      FLASH_A_SECURITY_ENABLE    OFF ; <<< enable Flash Security for Flash A (old "Main Flash")
#set      FLASH_B_AVAILABLE          OFF ; <<< select if Flash B is available
#set      FLASH_B_SECURITY_ENABLE    OFF ; <<< enable Flash Security for Flash B (old "Satellite Flash")

; set the Flash Security unlock key (16 bytes)
; all 0: unlock not possible
#set      FLASH_A_UNLOCK_0           0x00
#set      FLASH_A_UNLOCK_1           0x00
#set      FLASH_A_UNLOCK_2           0x00
#set      FLASH_A_UNLOCK_3           0x00
#set      FLASH_A_UNLOCK_4           0x00
#set      FLASH_A_UNLOCK_5           0x00
#set      FLASH_A_UNLOCK_6           0x00
#set      FLASH_A_UNLOCK_7           0x00
#set      FLASH_A_UNLOCK_8           0x00
#set      FLASH_A_UNLOCK_9           0x00
#set      FLASH_A_UNLOCK_10          0x00
#set      FLASH_A_UNLOCK_11          0x00
#set      FLASH_A_UNLOCK_12          0x00
#set      FLASH_A_UNLOCK_13          0x00
#set      FLASH_A_UNLOCK_14          0x00
#set      FLASH_A_UNLOCK_15          0x00

#set      FLASH_B_UNLOCK_0           0x00
#set      FLASH_B_UNLOCK_1           0x00
#set      FLASH_B_UNLOCK_2           0x00
#set      FLASH_B_UNLOCK_3           0x00
#set      FLASH_B_UNLOCK_4           0x00
#set      FLASH_B_UNLOCK_5           0x00
#set      FLASH_B_UNLOCK_6           0x00
#set      FLASH_B_UNLOCK_7           0x00
#set      FLASH_B_UNLOCK_8           0x00
#set      FLASH_B_UNLOCK_9           0x00
#set      FLASH_B_UNLOCK_10          0x00
#set      FLASH_B_UNLOCK_11          0x00
#set      FLASH_B_UNLOCK_12          0x00
#set      FLASH_B_UNLOCK_13          0x00
#set      FLASH_B_UNLOCK_14          0x00
#set      FLASH_B_UNLOCK_15          0x00


;====================================================================
; 4.13  Flash Write Protection
;====================================================================

#set      FLASH_A_WRITE_PROTECT           OFF       ; <<< select Flash A write protection
#set      PROTECT_SECTOR_SA0              OFF       ; <<< select individual sector to protect
#set      PROTECT_SECTOR_SA1              OFF       ; <<< select individual sector to protect
#set      PROTECT_SECTOR_SA2              OFF       ; <<< select individual sector to protect
#set      PROTECT_SECTOR_SA3              OFF       ; <<< select individual sector to protect
#set      PROTECT_SECTOR_SA32             OFF       ; <<< select individual sector to protect
#set      PROTECT_SECTOR_SA33             OFF       ; <<< select individual sector to protect
#set      PROTECT_SECTOR_SA34             OFF       ; <<< select individual sector to protect
#set      PROTECT_SECTOR_SA35             OFF       ; <<< select individual sector to protect
#set      PROTECT_SECTOR_SA36             OFF       ; <<< select individual sector to protect
#set      PROTECT_SECTOR_SA37             OFF       ; <<< select individual sector to protect
#set      PROTECT_SECTOR_SA38             OFF       ; <<< select individual sector to protect
#set      PROTECT_SECTOR_SA39             OFF       ; <<< select individual sector to protect

#set      FLASH_B_WRITE_PROTECT           OFF       ; <<< select Flash write protection
#set      PROTECT_SECTOR_SB0              OFF       ; <<< select individual sector to protect
#set      PROTECT_SECTOR_SB1              OFF       ; <<< select individual sector to protect
#set      PROTECT_SECTOR_SB2              OFF       ; <<< select individual sector to protect
#set      PROTECT_SECTOR_SB3              OFF       ; <<< select individual sector to protect


;====================================================================
; 4.14  Boot Vector
;====================================================================

#set      BOOT_VECTOR_TABLE  1              ; enable boot vector
#set      BOOT_VECTOR_FIXED  2              ; enable boot vector

#set      BOOT_VECTOR   BOOT_VECTOR_TABLE   ; <<< select type of boot vector

; If boot vector generation is enabled (BOOT_VECTOR_TABLE, BOOT_VECTOR_FIXED),
; appropriate code is generated. If it is disabled (OFF), start-up file does
; not care about.
;
;   BOOT_VECTOR_TABLE: - Create table entry at address oxFFFFDC.
;                      - Any start address can be set and start-up file will
;                        set address of this start code.
;   BOOT_VECTOR_FIXED: - Instead of table entry, a special marker is set in
;                        ROM Configuration Block, which enables the fixed
;                        start address 0xDF0080. This is prefered setting 
;                        for user boot loaders.
;                 OFF: - Do not set table entry and marker. This might be used
;                        for application to be loaded by boot loader.
;
; Note
; BOOT_VECTOR_TABLE setting can also be used, if all other interrupt vectors
; are specified via "pragma intvect". Only if interrupts 0..7 are specified
; via "pragma intvect", these will conflict with the vector in this module.
; The reason is the INTVECT section, which includes the whole area from the
; lowest to the highest specified vector.

#if BOOT_VECTOR == BOOT_VECTOR_TABLE
          .SECTION        RESVECT, CONST, LOCATE=H'FFFFDC
          .DATA.E _start
          .SECTION        BOOT_SELECT, CONST, LOCATE=H'DF0030
          .DATA.L 0xFFFFFFFF
          
#else
#  if BOOT_VECTOR == BOOT_VECTOR_FIXED
          .SECTION        BOOT_SELECT, CONST, LOCATE=H'DF0030
          .DATA.L 0x292D3A7B        ; "Magic Word"
#  else
          .SECTION        BOOT_SELECT, CONST, LOCATE=H'DF0030
          .SKIP   4
#  endif
#endif

;====================================================================
; 4.15  UART scanning
;====================================================================

#set      UART_SCANNING   OFF        ; <<< enable UART scanning in
                                     ;     Internal Vector Mode
;
; By default, the MCU scans in Internal Vector Mode for a UART 
; communication after reset. This enables to establish a serial 
; communication without switching to Serial Communication Mode.
; For the final application, set this switch to OFF to achieve the 
; fastest start-up time.

#if UART_SCANNING == ON
#  if ((SERIES == MB96340) && (DEVICE < 3))
#    error Device does not support UART scanning on/off
#  else
          .SECTION        UART_SCAN_SELECT, CONST, LOCATE=H'DF0034
          .DATA.L 0xFFFFFFFF
#  endif ; (SERIES == MB96340 && DEVICE < 3)
#else          
          .SECTION        UART_SCAN_SELECT, CONST, LOCATE=H'DF0034
          .DATA.L 0x292D3A7B        ; Decativation "Magic Word"
#endif
          .SKIP   0x08


;====================================================================
; 4.16  Enable RAMCODE Copying
;====================================================================

#set      COPY_RAMCODE      OFF     ; <<< enable RAMCODE section to
                                    ; be copied from ROM to RAM

; To get this option properly working the code to be executed has to
; be linked to section RAMCODE (e.g. by #pragma section). The section
; RAMCODE has be located in RAM and the section @RAMCODE has to be
; located at a fixed address in ROM by linker settings.

;====================================================================
; 4.17  Enable information stamp in ROM
;====================================================================

#set      VERSION_STAMP     OFF     ; <<< enable version number in
                                    ; separated section


#if VERSION_STAMP == ON
          .SECTION  VERSIONS, CONST ; change name, if necessary
          .SDATA    "Start ", VERSION, "\n\0" 
#endif

;====================================================================
; 4.18  Enable Background Debugging Mode
;====================================================================

#set      BACKGROUND_DEBUGGING  ON  ; <<< enable Background Debugging
                                    ; mode

#set      BDM_CONFIGURATION  B'0000000000010011  ; <<< set BDM configuration
;                                    ||||||||++--- BdmUART
;                                    ||||||||      (0: A, 1: B, 2: C, 3: D)
;                                    ||||||++----- BdmSynchMode
;                                    ||||||        (0: Async., 1: Sync.
;                                    ||||||        2: BdmKLine, 3: res.)
;                                    |||||+------- BdmAutoStart
;                                    ||||+-------- BdmExtBreakpointCfg
;                                    |||+--------- BdmKeepRClock
;                                    ||+---------- BdmCaliRClock
;                                    |+----------- BdmKeepBCD
;                                    +------------ BdmUserKernel

#set      BDM_BAUDRATE    115200   ; <<< set Baudrate in Bits/s for BDM

#set      BDM_EXT_CONFIG  0xFFFFFF ; <<< set external Config/Kernel

#set      BDM_WD_PATTERN  0x00     ; <<< set watchdog pattern

#set      BDM_PFCS0       0x0000   ; <<< set default breakpoint
#set      BDM_PFCS1       0x0000   ;     configurations 
#set      BDM_PFCS2       0x0000
#set      BDM_PFCS3       0x0000

#set      BDM_PFA0        0xFFFFFF ; <<< set address
#set      BDM_PFA1        0xFFFFFF ;     configurations
#set      BDM_PFA2        0xFFFFFF
#set      BDM_PFA3        0xFFFFFF
#set      BDM_PFA4        0xFFFFFF
#set      BDM_PFA5        0xFFFFFF
#set      BDM_PFA6        0xFFFFFF
#set      BDM_PFA7        0xFFFFFF

#set      BDM_PFD0        0xFFFF   ; <<< set patch data 
#set      BDM_PFD1        0xFFFF   ;     configurations
#set      BDM_PFD2        0xFFFF
#set      BDM_PFD3        0xFFFF
#set      BDM_PFD4        0xFFFF
#set      BDM_PFD5        0xFFFF
#set      BDM_PFD6        0xFFFF
#set      BDM_PFD7        0xFFFF


; <<< END OF SETTINGS >>>

;====================================================================
; 5  Section and Data Declaration
;====================================================================

;====================================================================
; 5.1  Several fixed addresses (fixed for MB963xx controllers)
;====================================================================

MCSRA      .EQU      0x03F1          ; Flash A Memory configuration register
MTCRA      .EQU      0x03F2          ; Flash A Memory timing register
MCSRB      .EQU      0x03F5          ; Flash B Memory configuration register
MTCRB      .EQU      0x03F6          ; Flash B Memory timing register
ROMM       .EQU      0x03AE          ; ROM mirror control register
CKSR       .EQU      0x0401          ; Clock select control register
CKSSR      .EQU      0x0402          ; Clock stabilization select register
CKMR       .EQU      0x0403          ; Clock monitor register
CKFCR      .EQU      0x0404          ; Clock frequency control register
PLLCR      .EQU      0x0406          ; PLL control register
VRCR       .EQU      0x042C          ; Voltage Regulator Control register
ICE01      .EQU      0x0041          ; Input capture 0/1 source
ICE67      .EQU      0x0053          ; Input capture 6/7 source
ICE89      .EQU      0x0515          ; Input capture 8/9 source
ICE1011    .EQU      0x051B          ; Input capture 10/11 source
ICS89      .EQU      0x0514          ; Input capture 8/9 edge select
ICS1011    .EQU      0x051A          ; Input capture 10/11 edge select
TCCSL2     .EQU      0x0502          ; Free running timer 2 control/status register
TCCSL3     .EQU      0x0506          ; Free running timer 3 control/status register
#if BUSMODE != SINGLE_CHIP           ; only for devices with external bus
PIER00     .EQU      0x0444
PIER01     .EQU      0x0445
PIER02     .EQU      0x0446
PIER03     .EQU      0x0447
PIER12     .EQU      0x0450
EACL0      .EQU      0x06E0
EACH0      .EQU      0x06E1
EACL1      .EQU      0x06E2
EACH1      .EQU      0x06E3
EACL2      .EQU      0x06E4
EACH2      .EQU      0x06E5
EACL3      .EQU      0x06E6
EACH3      .EQU      0x06E7
EACL4      .EQU      0x06E8
EACH4      .EQU      0x06E9
EACL5      .EQU      0x06EA
EACH5      .EQU      0x06EB
EAS2       .EQU      0x06EC
EAS3       .EQU      0x06ED
EAS4       .EQU      0x06EE
EAS5       .EQU      0x06EF
EBM        .EQU      0x06F0
EBCF       .EQU      0x06F1
EBAE0      .EQU      0x06F2
EBAE1      .EQU      0x06F3
EBAE2      .EQU      0x06F4
EBCS       .EQU      0x06F5
#endif ; BUSMODE != SINGLE_CHIP

;====================================================================
; 5.2  Declaration of __near addressed data sections
;====================================================================

; sections to be cleared
          .SECTION  DATA,      DATA,   ALIGN=2  ; zero clear area
          .SECTION  DATA2,     DATA,   ALIGN=2  ; zero clear area
          .SECTION  DIRDATA,   DIR,    ALIGN=2  ; zero clear direct
          .SECTION  LIBDATA,   DATA,   ALIGN=2  ; zero clear lib area

; sections to be initialised with start-up values
          .SECTION  INIT,      DATA,   ALIGN=2  ; initialised area
          .SECTION  INIT2,     DATA,   ALIGN=2  ; initialised area
          .SECTION  DIRINIT,   DIR,    ALIGN=2  ; initialised dir
          .SECTION  LIBINIT,   DATA,   ALIGN=2  ; initialised lib area
#if CONSTDATA == RAMCONST
          .SECTION  CINIT,     DATA,   ALIGN=2  ; initialised const
          .SECTION  CINIT2,    DATA,   ALIGN=2  ; initialised const
#endif

; sections containing start-up values for initialised sections above
          .SECTION  DCONST,    CONST,  ALIGN=2  ; DINIT initialisers
          .SECTION  DIRCONST, DIRCONST,ALIGN=2  ; DIRINIT initialisers
          .SECTION  LIBDCONST, CONST,  ALIGN=2  ; LIBDCONST init val

          ; following section is either copied to CINIT (RAMCONST) or
          ; mapped by ROM-mirror function (ROMCONST)
          .SECTION  CONST,     CONST,  ALIGN=2  ; CINIT initialisers
          .SECTION  CONST2,    CONST,  ALIGN=2  ; CINIT initialisers

;====================================================================
; 5.3  Declaration of RAMCODE section and labels
;====================================================================

#if COPY_RAMCODE == ON
          .SECTION  RAMCODE,   CODE,  ALIGN=1  
          .IMPORT _RAM_RAMCODE                  ; provided by linker
          .IMPORT _ROM_RAMCODE                  ; provided by linker
#endif


;====================================================================
; 5.4  Declaration of sections containing other sections description
;====================================================================

; DCLEAR contains start address and size of all sections to be cleared
; DTRANS contains source and destination address and size of all 
; sections to be initialised with start-up values
; The compiler automatically adds a descriptor for each __far addressed
; data section to DCLEAR or DTRANS. These __far sections are separated 
; for each C-module.

; In addition the start-up file adds the descriptors of the previously
; declared __near section here. This way the same code in the start-up
; file can be used for initialising all sections.

   .SECTION  DCLEAR,    CONST,  ALIGN=2  ; zero clear table
   ;    Address         Bank            Size
   .DATA.H DATA,    BNKSEC DATA,    SIZEOF(DATA   )
   .DATA.H DIRDATA, BNKSEC DIRDATA, SIZEOF(DIRDATA)
   .DATA.H LIBDATA, BNKSEC LIBDATA, SIZEOF(LIBDATA)

   .SECTION  DTRANS,    CONST,  ALIGN=2  ; copy table
   ;    Address         Bank               Address     Bank          Size
   .DATA.H DCONST,   BNKSEC DCONST,   INIT,   BNKSEC INIT,   SIZEOF INIT   
   .DATA.H DIRCONST, BNKSEC DIRCONST, DIRINIT,BNKSEC DIRINIT,SIZEOF DIRINIT
   .DATA.H LIBDCONST,BNKSEC LIBDCONST,LIBINIT,BNKSEC LIBINIT,SIZEOF LIBINIT

#if CONSTDATA == RAMCONST
   .DATA.H CONST,    BNKSEC CONST,    CINIT,  BNKSEC CINIT,  SIZEOF CINIT  
   .DATA.H CONST2,   BNKSEC CONST,    CINIT2, BNKSEC CINIT2, SIZEOF CINIT2
#endif

#if COPY_RAMCODE == ON
   .DATA.L _ROM_RAMCODE, _RAM_RAMCODE
   .DATA.H SIZEOF RAMCODE
#endif

;====================================================================
; 5.5  Stack area and stack top definition/declaration
;====================================================================
#if STACK_RESERVE == ON
            .SECTION  SSTACK, STACK, ALIGN=2

            .EXPORT __systemstack, __systemstack_top
__systemstack:
            .RES.B    (STACK_SYS_SIZE + 1) & 0xFFFE
__systemstack_top:
SSTACK_TOP:

            .SECTION  USTACK, STACK, ALIGN=2

            .EXPORT __userstack, __userstack_top
__userstack:
            .RES.B    (STACK_USR_SIZE + 1) & 0xFFFE
__userstack_top:
USTACK_TOP:

#else
            .SECTION  SSTACK, STACK, ALIGN=2
            .SECTION  USTACK, STACK, ALIGN=2

            .IMPORT __systemstack, __systemstack_top
            .IMPORT __userstack, __userstack_top
#endif

;====================================================================
; 5.6  Direct page register dummy label definition
;====================================================================

          .SECTION  DIRDATA  ; zero clear direct
DIRDATA_S:                                      ; label for DPR init       

; This label is used to get the page of the __direct data.
; Depending on the linkage order of this startup file the label is
; placed anywhere within the __direct data page. However, the
; statement "PAGE (DIRDATA_S)" is processed. Therefore, the lower 
; 8 Bit of the address of DIRDATA_S are not relevant and this feature 
; becomes linkage order independent. 
; Note, the linker settings have to make sure that all __direct
; data are located within the same physical page (256 Byte block).

;====================================================================
; 5.7  Set Flash Security
;====================================================================

          .SECTION FLASH_A_SECURITY, CONST, LOCATE=H'DF0000
#if FLASH_A_SECURITY_ENABLE == 0
	      .DATA.W 0xFFFF ; Security DISABLED
	      .SKIP   16
#else FLASH_A_SECURITY_ENABLE == 1
	      .DATA.W 0x0099 ; Security ENABLED
	      .DATA.W ((FLASH_A_UNLOCK_1  << 8) | FLASH_A_UNLOCK_0)
	      .DATA.W ((FLASH_A_UNLOCK_3  << 8) | FLASH_A_UNLOCK_2)
	      .DATA.W ((FLASH_A_UNLOCK_5  << 8) | FLASH_A_UNLOCK_4)
	      .DATA.W ((FLASH_A_UNLOCK_7  << 8) | FLASH_A_UNLOCK_6)
	      .DATA.W ((FLASH_A_UNLOCK_9  << 8) | FLASH_A_UNLOCK_8)
	      .DATA.W ((FLASH_A_UNLOCK_11 << 8) | FLASH_A_UNLOCK_10)
	      .DATA.W ((FLASH_A_UNLOCK_13 << 8) | FLASH_A_UNLOCK_12)
	      .DATA.W ((FLASH_A_UNLOCK_15 << 8) | FLASH_A_UNLOCK_14)
#endif      
	      .SKIP   4
	      .SKIP   6

#if FLASH_B_AVAILABLE == ON
          .SECTION FLASH_B_SECURITY, CONST, LOCATE=H'DE0000
#  if FLASH_B_SECURITY_ENABLE == 0
	      .DATA.W 0xFFFF ; Security DISABLED
	      .SKIP   16
#  else FLASH_B_SECURITY_ENABLE == 1
	      .DATA.W 0x0099 ; Security ENABLED
	      .DATA.W ((FLASH_B_UNLOCK_1  << 8) | FLASH_B_UNLOCK_0)
	      .DATA.W ((FLASH_B_UNLOCK_3  << 8) | FLASH_B_UNLOCK_2)
	      .DATA.W ((FLASH_B_UNLOCK_5  << 8) | FLASH_B_UNLOCK_4)
	      .DATA.W ((FLASH_B_UNLOCK_7  << 8) | FLASH_B_UNLOCK_6)
	      .DATA.W ((FLASH_B_UNLOCK_9  << 8) | FLASH_B_UNLOCK_8)
	      .DATA.W ((FLASH_B_UNLOCK_11 << 8) | FLASH_B_UNLOCK_10)
	      .DATA.W ((FLASH_B_UNLOCK_13 << 8) | FLASH_B_UNLOCK_12)
	      .DATA.W ((FLASH_B_UNLOCK_15 << 8) | FLASH_B_UNLOCK_14)
#  endif      
	      .SKIP   4
	      .SKIP   6
#endif ; FLASH_B_AVAILABLE == ON


;====================================================================
; 5.8  Set Flash write protection
;====================================================================

          .SECTION FLASH_A_PROTECT, CONST, LOCATE=H'DF001C
#if FLASH_A_WRITE_PROTECT == ON
          .DATA.L 0x292D3A7B
          .DATA.B ~((PROTECT_SECTOR_SA3 << 3) | (PROTECT_SECTOR_SA2 << 2) | (PROTECT_SECTOR_SA1 << 1) | PROTECT_SECTOR_SA0)
          .DATA.E 0xFFFFFF
          .DATA.B ~((PROTECT_SECTOR_SA39 << 7) | (PROTECT_SECTOR_SA38 << 6) | (PROTECT_SECTOR_SA37 << 5) | (PROTECT_SECTOR_SA36 << 4) | (PROTECT_SECTOR_SA35 << 3) | (PROTECT_SECTOR_SA34 << 2) | (PROTECT_SECTOR_SA33 << 1) | PROTECT_SECTOR_SA32)
          .SKIP   3
#else
          .DATA.L 0xFFFFFFFF
          .SKIP   8
#endif ; FLASH_A_WRITE_PROTECT
          .SKIP   8

#if FLASH_B_AVAILABLE == ON
          .SECTION FLASH_B_PROTECT, CONST, LOCATE=H'DE001C
#  if FLASH_B_WRITE_PROTECT == ON
          .DATA.L 0x292D3A7B
          .DATA.B ~((PROTECT_SECTOR_SB3 << 3) | (PROTECT_SECTOR_SB2 << 2) | (PROTECT_SECTOR_SB1 << 1) | PROTECT_SECTOR_SB0)
          .SKIP   7
#  else
          .DATA.L 0xFFFFFFFF
          .SKIP   8
#  endif ; FLASH_B_WRITE_PROTECT
          .SKIP   8
#endif ; FLASH_B_AVAILABLE == ON


;====================================================================
; 5.9  Debug address specification
;====================================================================
;
; BDM configuration section should always be defined for later
; configuration by e.g. debugger tool or (special) programmer tool.

          .SECTION BDM_CONFIG, CONST, LOCATE=H'DF0040
         
#if BACKGROUND_DEBUGGING == ON
          
          .DATA.L 0x292D3A7B
          
          .ORG    H'DF0044
          .DATA.W BDM_CONFIGURATION
          
          .ORG    H'DF0046
#  if ((SERIES == MB96340) && (DEVICE < 3))
#    error Device does not support background debugging
#  endif ; ((SERIES == MB96340) && (DEVICE < 3))
          
#  if ((SERIES == MB96340) && (DEVICE < 12))
          .DATA.W (D'16 * CRYSTAL + BDM_BAUDRATE) / BDM_BAUDRATE
#  else
          .DATA.W (D'32 * CRYSTAL + BDM_BAUDRATE) / BDM_BAUDRATE
#  endif ; ((SERIES == MB96340) && (DEVICE < 12))
                                                 
          .ORG    H'DF0048
          .DATA.E BDM_EXT_CONFIG                              

          .ORG    H'DF004B
          .DATA.B BDM_WD_PATTERN
          
          .ORG    H'DF0050
          .DATA.W BDM_PFCS0
          .DATA.W BDM_PFCS1
          .DATA.W BDM_PFCS2                       
          .DATA.W BDM_PFCS3                      
          
          .DATA.E BDM_PFA0, BDM_PFA1
          .DATA.E BDM_PFA2, BDM_PFA3
          .DATA.E BDM_PFA4, BDM_PFA5           
          .DATA.E BDM_PFA6, BDM_PFA7           
          
          .DATA.W BDM_PFD0, BDM_PFD1
          .DATA.W BDM_PFD2, BDM_PFD3
          .DATA.W BDM_PFD4, BDM_PFD5           
          .DATA.W BDM_PFD6, BDM_PFD7                  
#else
          .DATAB.B 64, 0xFF        ; fill section with 0xFF
          
#endif ; BACKGROUND_DEBUGGING == ON

          .ORG    0xDF0080
          
;====================================================================
; 6  Start-Up Code
;====================================================================

;====================================================================
; 6.1  Import external symbols
;====================================================================

          .IMPORT   _main                    ; user code entrance
#if CLIBINIT == ON
          .IMPORT   __stream_init
          .IMPORT   _exit
          .EXPORT   __exit
#endif          
          .EXPORT   _start

;====================================================================
;   ___  _____   __    ___  _____
;  /       |    /  \  |   \   |                  
;  \___    |   |    | |___/   |   
;      \   |   |----| |  \    |   
;   ___/   |   |    | |   \   |      Begin of actual code section
;
;====================================================================
          .SECTION  CODE_START, CODE, ALIGN=1

;====================================================================
; 6.2  Program start (the reset vector should point here)
;====================================================================
_start:
          NOP  ; This NOP is only for debugging. On debugger the IP
               ; (instruction pointer) should point here after reset

;====================================================================
; 6.3  "NOT RESET YET" WARNING
;====================================================================
notresetyet:
          NOP  ; read hint below!!!!!!!
; If the debugger stays at this NOP after download, the controller has
; not been reset yet. In order to reset all hardware registers it is
; highly recommended to reset the controller.
; However, if no reset vector has been defined on purpose, this start
; address can also be used.
; This mechanism is using the .END instruction at the end of this mo-
; dule. It is not necessary for controller operation but improves 
; security during debugging (mainly emulator debugger).
; If the debugger stays here after a single step from label "_start"
; to label "notresetyet", this note can be ignored.

;====================================================================
; 6.4  Initialisation of processor status
;====================================================================
          AND  CCR, #0x80          ; disable interrupts
          MOV  ILM,#7              ; set interrupt level mask to ALL
          MOV  RP,#REGBANK         ; set register bank pointer 

;====================================================================
; 6.5  Set clock ratio (ignore subclock)
;====================================================================
          MOVN A, #0               ; set bank 0 in DTB for the case that
          MOV  DTB, A              ; start-up code was not jumped by reset
		  
          MOV  CKSSR, #(0xF8 | MC_STAB_TIME)  ; set clock stabilization time

#if (CRYSTAL == FREQ_4MHZ) && (CLOCK_SPEED == CPU_4MHZ_MAIN_CLKP2_4MHZ)
          MOV  CKSR,  #0xB5
#endif ; (CRYSTAL == FREQ_4MHZ) && (CLOCK_SPEED == CPU_4MHZ_MAIN_CLKP2_4MHZ)

#if (CRYSTAL == FREQ_8MHZ) && (CLOCK_SPEED == CPU_4MHZ_MAIN_CLKP2_4MHZ)
          CLRB MCSRA:4
          CLRB MCSRA:5
          CLRB MCSRB:4
          CLRB MCSRB:5
          MOVW CKFCR, #0x1111
          MOVW MTCRA, #0x2128
#    if FLASH_B_AVAILABLE == ON
          MOVW MTCRB, #0x2128
#    endif ; FLASH_B_AVAILABLE == ON
          MOV  CKSR,  #0xB5
#endif ; (CRYSTAL == FREQ_8MHZ) && (CLOCK_SPEED == CPU_4MHZ_MAIN_CLKP2_4MHZ)

#if (CRYSTAL == FREQ_4MHZ) && (CLOCK_SPEED == CPU_4MHZ_PLL_CLKP2_4MHZ)
#  if ((SERIES == MB96340) && (DEVICE < 3))
          MOVW PLLCR, #0x00E0
          MOV  CKSR,  #0xFA
#  else
          MOVW PLLCR, #0x00A1
          MOVW CKFCR, #0x1111
          MOVW MTCRA, #0x2128
#    if FLASH_B_AVAILABLE == ON
          MOVW MTCRB, #0x2128
#    endif ; FLASH_B_AVAILABLE == ON
          MOV  CKSR,  #0xFA
#  endif ; ((SERIES == MB96340) && (DEVICE < 3))
#endif ; (CRYSTAL == FREQ_4MHZ) && (CLOCK_SPEED == CPU_4MHZ_PLL_CLKP2_4MHZ)

#if (CRYSTAL == FREQ_8MHZ) && (CLOCK_SPEED == CPU_4MHZ_PLL_CLKP2_4MHZ)
#  if ((SERIES == MB96340) && (DEVICE < 3))
          MOVW PLLCR, #0x0060
          CLRB MCSRA:4
          CLRB MCSRA:5
          CLRB MCSRB:4
          CLRB MCSRB:5
          MOVW CKFCR, #0x1111
          MOV  CKSR,  #0xFA
#  else
          MOVW PLLCR, #0x0060
          MOVW CKFCR, #0x1111
          MOVW MTCRA, #0x2128
#    if FLASH_B_AVAILABLE == ON
          MOVW MTCRB, #0x2128
#    endif ; FLASH_B_AVAILABLE == ON
          MOV  CKSR,  #0xFA
#  endif ; ((SERIES == MB96340) && (DEVICE < 3))
#endif ; (CRYSTAL == FREQ_8MHZ) && (CLOCK_SPEED == CPU_4MHZ_PLL_CLKP2_4MHZ)

#if (CRYSTAL == FREQ_4MHZ) && (CLOCK_SPEED == CPU_8MHZ_CLKP2_8MHZ)
#  if ((SERIES == MB96340) && (DEVICE < 3))
          MOVW PLLCR, #0x00A1
          MOV  CKSR,  #0xFA
#  else
          MOVW PLLCR, #0x0043
          MOVW CKFCR, #0x1111
          MOVW MTCRA, #0x2128
#    if FLASH_B_AVAILABLE == ON
          MOVW MTCRB, #0x2128
#    endif ; FLASH_B_AVAILABLE == ON
          MOV  CKSR,  #0xFA
#  endif ; ((SERIES == MB96340) && (DEVICE < 3))
#endif ; (CRYSTAL == FREQ_4MHZ) && (CLOCK_SPEED == CPU_8MHZ_CLKP2_8MHZ)

#if (CRYSTAL == FREQ_8MHZ) && (CLOCK_SPEED == CPU_8MHZ_CLKP2_8MHZ)
#  if ((SERIES == MB96340) && (DEVICE < 3))
          MOVW PLLCR, #0x0060
          MOV  CKSR,  #0xFA
#  else
          MOVW PLLCR, #0x0081
          MOVW CKFCR, #0x1111
          MOVW MTCRA, #0x2128
#    if FLASH_B_AVAILABLE == ON
          MOVW MTCRB, #0x2128
#    endif ; FLASH_B_AVAILABLE == ON
          MOV  CKSR,  #0xFA
#  endif ; ((SERIES == MB96340) && (DEVICE < 3))
#endif ; (CRYSTAL == FREQ_8MHZ) && (CLOCK_SPEED == CPU_8MHZ_CLKP2_8MHZ)

#if (CRYSTAL == FREQ_4MHZ) && (CLOCK_SPEED == CPU_12MHZ_CLKP2_12MHZ)
#  if ((SERIES == MB96340) && (DEVICE < 3))
          MOVW PLLCR, #0x0062
          MOV  CKSR,  #0xFA
#  else
          MOVW PLLCR, #0x0025
          MOVW CKFCR, #0x1111
          MOVW MTCRA, #0x2128
#    if FLASH_B_AVAILABLE == ON
          MOVW MTCRB, #0x2128
#    endif ; FLASH_B_AVAILABLE == ON
          MOV  CKSR,  #0xFA
#  endif ; ((SERIES == MB96340) && (DEVICE < 3))
#endif ; (CRYSTAL == FREQ_4MHZ) && (CLOCK_SPEED == CPU_12MHZ_CLKP2_12MHZ)

#if (CRYSTAL == FREQ_8MHZ) && (CLOCK_SPEED == CPU_12MHZ_CLKP2_12MHZ)
#  if ((SERIES == MB96340) && (DEVICE < 3))
          MOVW PLLCR, #0x0061
          CLRB MCSRA:4
          CLRB MCSRA:5
          CLRB MCSRB:4
          CLRB MCSRB:5
          MOVW CKFCR, #0x1111
          MOV  CKSR,  #0xFA
#  else
          MOVW PLLCR, #0x0061
          MOVW CKFCR, #0x1111
          MOVW MTCRA, #0x2128
#    if FLASH_B_AVAILABLE == ON
          MOVW MTCRB, #0x2128
#    endif ; FLASH_B_AVAILABLE == ON
          MOV  CKSR,  #0xFA
#  endif ; ((SERIES == MB96340) && (DEVICE < 3))
#endif ; (CRYSTAL == FREQ_8MHZ) && (CLOCK_SPEED == CPU_12MHZ_CLKP2_12MHZ)

#if (CRYSTAL == FREQ_4MHZ) && (CLOCK_SPEED == CPU_16MHZ_CLKP2_16MHZ)
#  if ((SERIES == MB96340) && (DEVICE < 3))
          MOVW PLLCR, #0x0043
          MOV  CKSR,  #0xFA
#  else
          MOVW PLLCR, #0x0027
          MOVW CKFCR, #0x1111
          MOVW MTCRA, #0x2128
          MOV  MCSRA, #0x70
#    if FLASH_B_AVAILABLE == ON
          MOVW MTCRB, #0x2128
          MOV  MCSRB, #0x70
#    endif ; FLASH_B_AVAILABLE == ON
          MOV  VRCR,  #0xF6
          MOV  CKSR,  #0xFA
#  endif ; ((SERIES == MB96340) && (DEVICE < 3))
#endif ; (CRYSTAL == FREQ_4MHZ) && (CLOCK_SPEED == CPU_16MHZ_CLKP2_16MHZ)

#if (CRYSTAL == FREQ_8MHZ) && (CLOCK_SPEED == CPU_16MHZ_CLKP2_16MHZ)
#  if ((SERIES == MB96340) && (DEVICE < 3))
          MOVW PLLCR, #0x0081
          MOV  CKSR,  #0xFA
#  else
          MOVW PLLCR, #0x0003
          MOVW CKFCR, #0x1111
          MOVW MTCRA, #0x2128
          MOV  MCSRA, #0x70
#    if FLASH_B_AVAILABLE == ON
          MOVW MTCRB, #0x2128
          MOV  MCSRB, #0x70
#    endif ; FLASH_B_AVAILABLE == ON
          MOV  VRCR,  #0xF6
          MOV  CKSR,  #0xFA
#  endif ; ((SERIES == MB96340) && (DEVICE < 3))
#endif ; (CRYSTAL == FREQ_8MHZ) && (CLOCK_SPEED == CPU_16MHZ_CLKP2_16MHZ)

#if (CRYSTAL == FREQ_4MHZ) && (CLOCK_SPEED == CPU_24MHZ_CLKP2_12MHZ)
#  if ((SERIES == MB96340) && (DEVICE < 3))
          MOVW PLLCR, #0x0025
          MOVW CKFCR, #0x1001
          MOV  CKSR,  #0xFA
#  else
          MOVW PLLCR, #0x000B
          MOVW CKFCR, #0x3111
          MOVW MTCRA, #0x4C09
#    if FLASH_B_AVAILABLE == ON
          MOVW MTCRB, #0x4C09
#    endif ; FLASH_B_AVAILABLE == ON
          MOV  CKSR,  #0xFA
#  endif ; ((SERIES == MB96340) && (DEVICE < 3))
#endif ; (CRYSTAL == FREQ_4MHZ) && (CLOCK_SPEED == CPU_24MHZ_CLKP2_12MHZ)
					
#if (CRYSTAL == FREQ_8MHZ) && (CLOCK_SPEED == CPU_24MHZ_CLKP2_12MHZ)
#  if ((SERIES == MB96340) && (DEVICE < 3))
          MOVW PLLCR, #0x0082
          MOVW CKFCR, #0x1001
          MOV  CKSR,  #0xFA
#  else
          MOVW PLLCR, #0x0005
          MOVW CKFCR, #0x3111
          MOVW MTCRA, #0x4C09
#    if FLASH_B_AVAILABLE == ON
          MOVW MTCRB, #0x4C09
#    endif ; FLASH_B_AVAILABLE == ON
          MOV  CKSR,  #0xFA
#  endif ; ((SERIES == MB96340) && (DEVICE < 3))
#endif ; (CRYSTAL == FREQ_8MHZ) && (CLOCK_SPEED == CPU_24MHZ_CLKP2_12MHZ)
					
#if (CRYSTAL == FREQ_4MHZ) && (CLOCK_SPEED == CPU_32MHZ_CLKP2_16MHZ)
#  if ((SERIES == MB96340) && (DEVICE < 3))
#    error Setting prohibited due to 16FXFL0014
#  else
          MOVW PLLCR, #0x0027
          MOVW CKFCR, #0x1001
          MOVW MTCRA, #0x2129
          MOV  MCSRA, #0x70
#    if FLASH_B_AVAILABLE == ON
          MOVW MTCRB, #0x2129
          MOV  MCSRB, #0x70
#    endif ; FLASH_B_AVAILABLE == ON
          MOV  VRCR,  #0xF6
          MOV  CKSR,  #0xFA
#  endif ; ((SERIES == MB96340) && (DEVICE < 3))
#endif ; (CRYSTAL == FREQ_4MHZ) && (CLOCK_SPEED == CPU_32MHZ_CLKP2_16MHZ)
					
#if (CRYSTAL == FREQ_8MHZ) && (CLOCK_SPEED == CPU_32MHZ_CLKP2_16MHZ)
#  if ((SERIES == MB96340) && (DEVICE < 3))
#    error Setting prohibited due to 16FXFL0014
#  else
          MOVW PLLCR, #0x0003
          MOVW CKFCR, #0x1001
          MOVW MTCRA, #0x2129
          MOV  MCSRA, #0x70
#    if FLASH_B_AVAILABLE == ON
          MOVW MTCRB, #0x2129
          MOV  MCSRB, #0x70
#    endif ; FLASH_B_AVAILABLE == ON
          MOV  VRCR,  #0xF6
          MOV  CKSR,  #0xFA
#  endif ; ((SERIES == MB96340) && (DEVICE < 3))
#endif ; (CRYSTAL == FREQ_8MHZ) && (CLOCK_SPEED == CPU_32MHZ_CLKP2_16MHZ)

#if (CRYSTAL == FREQ_4MHZ) && (CLOCK_SPEED == CPU_32MHZ_CLKP1_16MHZ_CLKP2_16MHZ)
#  if ((SERIES == MB96340) && (DEVICE < 3))
#    error Setting prohibited due to 16FXFL0014
#  else
          MOVW PLLCR, #0x0027
          MOVW CKFCR, #0x1101
          MOVW MTCRA, #0x2129
          MOV  MCSRA, #0x70
#    if FLASH_B_AVAILABLE == ON
          MOVW MTCRB, #0x2129
          MOV  MCSRB, #0x70
#    endif ; FLASH_B_AVAILABLE == ON
          MOV  VRCR,  #0xF6
          MOV  CKSR,  #0xFA
#  endif ; ((SERIES == MB96340) && (DEVICE < 3))
#endif ; (CRYSTAL == FREQ_4MHZ) && (CLOCK_SPEED == CPU_32MHZ_CLKP1_16MHZ_CLKP2_16MHZ)

#if (CRYSTAL == FREQ_8MHZ) && (CLOCK_SPEED == CPU_32MHZ_CLKP1_16MHZ_CLKP2_16MHZ)
#  if ((SERIES == MB96340) && (DEVICE < 3))
#    error Setting prohibited due to 16FXFL0014
#  else
          MOVW PLLCR, #0x0003
          MOVW CKFCR, #0x1101
          MOVW MTCRA, #0x2129
          MOV  MCSRA, #0x70
#    if FLASH_B_AVAILABLE == ON
          MOVW MTCRB, #0x2129
          MOV  MCSRB, #0x70
#    endif ; FLASH_B_AVAILABLE == ON
          MOV  VRCR,  #0xF6
          MOV  CKSR,  #0xFA
#  endif ; ((SERIES == MB96340) && (DEVICE < 3))
#endif ; (CRYSTAL == FREQ_8MHZ) && (CLOCK_SPEED == CPU_32MHZ_CLKP1_16MHZ_CLKP2_16MHZ)

#if (CRYSTAL == FREQ_4MHZ) && (CLOCK_SPEED == CPU_48MHZ_CLKP2_16MHZ)
          MOVW PLLCR, #0x0017
          MOVW CKFCR, #0x5111
          MOVW MTCRA, #0x6E3D
          MOV  MCSRA, #0x70
#  if FLASH_B_AVAILABLE == ON
          MOVW MTCRB, #0x6E3D
          MOV  MCSRB, #0x70
#  endif ; FLASH_B_AVAILABLE == ON
          MOV  VRCR,  #0xF6
          MOV  CKSR,  #0xFA
#endif ; (CRYSTAL == FREQ_4MHZ) && (CLOCK_SPEED == CPU_48MHZ_CLKP2_16MHZ)

#if (CRYSTAL == FREQ_8MHZ) && (CLOCK_SPEED == CPU_48MHZ_CLKP2_16MHZ)
          MOVW PLLCR, #0x000B
          MOVW CKFCR, #0x5111
          MOVW MTCRA, #0x6E3D
          MOV  MCSRA, #0x70
#  if FLASH_B_AVAILABLE == ON
          MOVW MTCRB, #0x6E3D
          MOV  MCSRB, #0x70
#  endif ; FLASH_B_AVAILABLE == ON
          MOV  VRCR,  #0xF6
          MOV  CKSR,  #0xFA
#endif ; (CRYSTAL == FREQ_8MHZ) && (CLOCK_SPEED == CPU_48MHZ_CLKP2_16MHZ)

#if (CRYSTAL == FREQ_4MHZ) && (CLOCK_SPEED == CPU_48MHZ_CLKP1_32MHZ_CLKP2_16MHZ)
          MOVW PLLCR, #0x0017
          MOVW CKFCR, #0x5211
          MOVW MTCRA, #0x6E3D
          MOV  MCSRA, #0x70
#  if FLASH_B_AVAILABLE == ON
          MOVW MTCRB, #0x6E3D
          MOV  MCSRB, #0x70
#  endif ; FLASH_B_AVAILABLE == ON
          MOV  VRCR,  #0xF6
          MOV  CKSR,  #0xFA
#endif ; (CRYSTAL == FREQ_4MHZ) && (CLOCK_SPEED == CPU_48MHZ_CLKP1_32MHZ_CLKP2_16MHZ)

#if (CRYSTAL == FREQ_8MHZ) && (CLOCK_SPEED == CPU_48MHZ_CLKP1_32MHZ_CLKP2_16MHZ)
          MOVW PLLCR, #0x000B
          MOVW CKFCR, #0x5211
          MOVW MTCRA, #0x6E3D
          MOV  MCSRA, #0x70
#  if FLASH_B_AVAILABLE == ON
          MOVW MTCRB, #0x6E3D
          MOV  MCSRB, #0x70
#  endif ; FLASH_B_AVAILABLE == ON
          MOV  VRCR,  #0xF6
          MOV  CKSR,  #0xFA
#endif ; (CRYSTAL == FREQ_8MHZ) && (CLOCK_SPEED == CPU_48MHZ_CLKP1_32MHZ_CLKP2_16MHZ)

#if (CRYSTAL == FREQ_4MHZ) && (CLOCK_SPEED == CPU_56MHZ_CLKP2_14MHZ)
          MOVW PLLCR, #0x000D
          MOVW CKFCR, #0x3001
          MOVW MTCRA, #0x233A
          MOV  MCSRA, #0x70
#  if FLASH_B_AVAILABLE == ON
          MOVW MTCRB, #0x233A
          MOV  MCSRB, #0x70
#  endif ; FLASH_B_AVAILABLE == ON
          MOV  VRCR,  #0xF6
          MOV  CKSR,  #0xFA
#endif ; (CRYSTAL == FREQ_4MHZ) && (CLOCK_SPEED == CPU_56MHZ_CLKP2_14MHZ)
	
#if (CRYSTAL == FREQ_8MHZ) && (CLOCK_SPEED == CPU_56MHZ_CLKP2_14MHZ)
          MOVW PLLCR, #0x0006
          MOVW CKFCR, #0x3001
          MOVW MTCRA, #0x233A
          MOV  MCSRA, #0x70
#  if FLASH_B_AVAILABLE == ON
          MOVW MTCRB, #0x233A
          MOV  MCSRB, #0x70
#  endif ; FLASH_B_AVAILABLE == ON
          MOV  VRCR,  #0xF6
          MOV  CKSR,  #0xFA
#endif ; (CRYSTAL == FREQ_8MHZ) && (CLOCK_SPEED == CPU_56MHZ_CLKP2_14MHZ)


;====================================================================
; 6.6  Set external bus configuaration
;====================================================================

#if BUSMODE != SINGLE_CHIP         ; ext bus used
           MOV  EBCF, #((HOLD_REQ << 7) | (EXT_READY << 6) | (EXT_CLOCK_ENABLE << 5) | (EXT_CLOCK_INVERT << 4) | (EXT_CLOCK_SUSPEND << 3) | EXT_CLOCK_DIVISION)
           MOV  EBAE0,#ADDR_PINS_7_0
           MOV  EBAE1,#ADDR_PINS_15_8
           MOV  EBAE2,#ADDR_PINS_23_16
           MOV  EBCS, #((ADDRESS_STROBE_LVL << 6) | (ADDRESS_STROBE << 5) | (READ_STROBE << 4) | (HIGH_WRITE_STROBE << 3) | (LOW_WRITE_STROBE << 2) | (HIGH_BYTE_SIGNAL << 1) | LOW_BYTE_SIGNAL)
           MOVW EACL0,#CS0_CONFIG
           MOVW EACL1,#CS1_CONFIG
           MOVW EACL2,#CS2_CONFIG
           MOVW EACL3,#CS3_CONFIG
           MOVW EACL4,#CS4_CONFIG
           MOVW EACL5,#CS5_CONFIG
           MOV  EAS2, #CS2_START
           MOV  EAS3, #CS3_START
           MOV  EAS4, #CS4_START
           MOV  EAS5, #CS5_START
           MOV  EBM,  #((ADDRESSMODE << 7) | ((BUSMODE-1) << 6) | (CHIP_SELECT5 << 5) | (CHIP_SELECT4 << 4) | (CHIP_SELECT3 << 3) | (CHIP_SELECT2 << 2) | (CHIP_SELECT1 << 1) | CHIP_SELECT0) ; set address mode, ROM access

#  if SERIES == MB96320 || SERIES == MB96330 || SERIES == MB96340 || SERIES == MB96350
           MOV  PIER00,#0xFF
#    if (CS0_CONFIG & 0x0080) == 0 || (CS1_CONFIG & 0x0080) == 0 || (CS2_CONFIG & 0x0080) == 0 || (CS3_CONFIG & 0x0080) == 0 || (CS4_CONFIG & 0x0080) == 0 || (CS5_CONFIG & 0x0080) == 0
           MOV  PIER01,#0xFF
#    endif
#    if HOLD_REQ == ON
           SETB PIER03:4
#    endif
#    if EXT_READY == ON
           SETB PIER03:6
#    endif

#  else if SERIES == MB96370 || SERIES == MB96380
           MOV  PIER01,#0xFF
#    if (CS0_CONFIG & 0x0080) == 0 || (CS1_CONFIG & 0x0080) == 0 || (CS2_CONFIG & 0x0080) == 0 || (CS3_CONFIG & 0x0080) == 0 || (CS4_CONFIG & 0x0080) == 0 || (CS5_CONFIG & 0x0080) == 0
           MOV  PIER02,#0xFF
#    endif
#    if HOLD_REQ == ON
           SETB PIER12:7
#    endif
#    if EXT_READY == ON
           SETB PIER00:2
#    endif
#  endif

#endif 

#if BUSMODE == INTROM_EXTBUS     ; EXTBUS and INTROM/EXTROM
#  if ROMMIRROR == OFF && CONSTDATA == ROMCONST
#    error Mirror function must be ON to mirror internal ROM
#  endif
#endif

ROMM_CONFIG    .EQU     ((MIRROR_BANK << 4) | (MIRROR_SIZE << 1) | (ROMMIRROR))
           MOV  ROMM, #ROMM_CONFIG


;====================================================================
; 6.7  Prepare stacks and set the default stack type
;====================================================================

          AND  CCR,#H'DF            ; clear system stack flag
          MOVL A, #(__userstack_top) & ~1   
          MOVW SP,A                 ; load offset of stack top to pointer
          SWAPW                     ; swap higher word to AL
          MOV  USB, A               ; set bank

#if STACK_FILL == ON                ; preset the stack
          MOV  ADB, A
          MOVW A, #USTACK           ; load start stack address to AL
          MOVW A, #STACK_PATTERN    ; AL -> AH, pattern in AL
          MOVW RW0, #SIZEOF(USTACK) / 2 ; get byte count
          FILSWI    ADB             ; write pattern to stack
#endif

          OR   CCR,#H'20            ; set System stack flag
          MOVL A, #(__systemstack_top) & ~1   
          MOVW SP,A                 ; load offset of stack top to pointer
          SWAPW                     ; swap higher word to AL
          MOV  SSB, A               ; set bank

#if STACK_FILL == ON                ; preset the stack
          MOV  ADB, A
          MOVW A, #SSTACK           ; load start stack address to AL
          MOVW A, #STACK_PATTERN    ; AL -> AH, pattern in AL
          MOVW RW0, #SIZEOF(SSTACK) / 2; get byte count
          FILSWI    ADB             ; write pattern to stack
#endif

#if STACKUSE == USRSTACK
          AND  CCR,#H'DF            ; clear system stack flag
#endif


;   The following macro is needed because of the AUTOMODEL option. If the
;   model is not known while assembling the module, one has to expect 
;   completion of streaminit() by RET or RETP. Because RET removes 2 bytes
;   from stack and RETP removes 4 bytes from stack, SP is reloaded.

#  macro RELOAD_SP

#if STACKUSE == USRSTACK
          MOVW A, #(__userstack_top) & ~1
#else 
          MOVW A, #(__systemstack_top) & ~1
#endif
          MOVW SP,A                         
#  endm


;====================================================================
; 6.8  Copy initial values to data areas.
;====================================================================
;
; Each C-module has its own __far INIT section. The names are generic.
; DCONST_module contains the initializers for the far data of the one
; module. INIT_module reserves the RAM area, which has to be loaded
; with the data from DCONST_module. ("module" is the name of the *.c
; file) 
; All separated DCONST_module/INIT_module areas are described in 
; DTRANS section by start addresses and length of each far section.
;   0000 1. source address (ROM)
;   0004 1. destination address (RAM)
;   0008 length of sections 1
;   000A 2. source address  (ROM)
;   000E 2. destination address (RAM)
;   0012 length of sections 2
;   0014 3. source address ...
; In addition the start-up file adds the descriptors of the __near 
; sections to this table. The order of the descriptors in this table 
; depends on the linkage order.
;====================================================================
          MOV  A, #BNKSEC DTRANS   ; get bank of table
          MOV  DTB, A              ; store bank in DTB
          MOVW RW1, #DTRANS        ; get start offset of table
          OR   CCR, #H'20          ; System stack flag set (SSB used)
          BRA  LABEL2              ; branch to loop condition
LABEL1:
          MOVW A, @RW1+6           ; get bank of destination
          MOV  SSB, A              ; save dest bank in SSB
          MOVW A, @RW1+2           ; get source bank
          MOV  ADB, A              ; save source bank in ADB
          MOVW A, @RW1+4           ; move destination addr in AL
          MOVW A, @RW1             ; AL -> AH, src addr -> AL 
          MOVW RW0, @RW1+8         ; number of bytes to copy -> RW0
          MOVSI     SPB, ADB       ; copy data
          MOVN A, #10              ; length of one table entry is 10
          ADDW RW1, A              ; set pointer to next table entry
LABEL2:                             
          MOVW A, RW1              ; get address of next block
          SUBW A, #DTRANS          ; sub address of first block
          CMPW A, #SIZEOF (DTRANS) ; all blocks processed ?
          BNE  LABEL1              ; if not, branch


;====================================================================
; 6.9   Clear uninitialized data areas to zero
;====================================================================
;
; Each C-module has its own __far DATA section. The names are generic.
; DATA_module contains the reserved area (RAM) to be cleared.
; ("module" is the name of the *.c file) 
; All separated DATA_module areas are described in DCLEAR section by
; start addresses and length of all far section.
;   0000 1. section address (RAM)
;   0004 length of section 1
;   0006 2. section address (RAM)
;   000A length of section 2
;   000C 3. section address (RAM)
;   0010 length of section 3 ...
; In addition the start-up file adds the descriptors of the __near 
; sections to this table. The order of the descriptors in this table 
; depends on the linkage order.
;====================================================================
          MOV  A, #BNKSEC DCLEAR   ; get bank of table
          MOV  DTB, A              ; store bank in DTB
          MOVW RW1, #DCLEAR        ; get start offset of table
          BRA  LABEL4              ; branch to loop condition
LABEL3:                            
          MOV  A, @RW1+2           ; get section bank
          MOV  ADB, A              ; save section bank in ADB
          MOVW RW0, @RW1+4         ; number of bytes to copy -> RW0
          MOVW A, @RW1             ; move section addr in AL
          MOVN A, #0               ; AL -> AH, init value -> AL 
          FILSI     ADB            ; write 0 to section
          MOVN A, #6               ; length of one table entry is 6
          ADDW RW1, A              ; set pointer to next table entry
LABEL4:
          MOVW A, RW1              ; get address of next block
          SUBW A, #DCLEAR          ; sub address of first block
          CMPW A, #SIZEOF (DCLEAR) ; all blocks processed ?
          BNE  LABEL3              ; if not, branch



;====================================================================
; 6.10  Set Data Bank Register (DTB) and Direct Page Register (DPR)
;====================================================================
          MOV  A,#BNKSEC DATA          ; User data bank offset
          MOV  DTB,A

          MOV  A,#PAGE DIRDATA_S       ; User direct page
          MOV  DPR,A

;====================================================================
; 6.11  ICU register initialization workaround
;====================================================================

#if (UART_SCANNING == ON)
#  if (((SERIES == MB96320) && (DEVICE < 3)) || \
       ((SERIES == MB96350) && (DEVICE < 3)))
          MOVN A, #0
          MOV  TCCSL2, A
          MOV  TCCSL3, A
          MOV  ICE67, A
          MOV  ICE89, A
          MOV  ICE1011, A
          MOV  ICS89, A
          MOV  ICS1011, A
#  endif ; ((SERIES == 96350) && ...
#  if (((SERIES == MB96330) && (DEVICE < 2))  || \
       ((SERIES == MB96340) && (DEVICE < 27)) || \
       ((SERIES == MB96370) && (DEVICE < 3))  || \
       ((SERIES == MB96380) && (DEVICE < 13)))
          MOVN A, #0
          MOV  ICE01, A
          MOV  ICE67, A
#  endif ; (((SERIES == MB96330) && (DEVICE < 2)) || ...
#endif ; (UART_SCANNING == ON)

;====================================================================
; 6.12  Wait for clocks to stabilize
;====================================================================

#if (CLOCK_SPEED == CPU_4MHZ_MAIN_CLKP2_4MHZ) && (CLOCKWAIT == ON)
no_MC_yet:
          BBC  CKMR:5,no_MC_yet        ; check MCM and wait for
                                       ; Main Clock to stabilize
#endif ; wait for Main Clock

#if (((CRYSTAL == FREQ_4MHZ) ||(CRYSTAL == FREQ_8MHZ)) && \
     ((CLOCK_SPEED == CPU_12MHZ_CLKP2_12MHZ) || \
     (CLOCK_SPEED == CPU_16MHZ_CLKP2_16MHZ) || \
     (CLOCK_SPEED == CPU_24MHZ_CLKP2_12MHZ)))
no_PLL_0WS:
          BBC  CKMR:6, no_PLL_0WS

#  if ! ((SERIES == MB96340) && (DEVICE < 3))
          MOVW MTCRA, #0x2208
#    if FLASH_B_AVAILABLE == ON
          MOVW MTCRB, #0x2208
#    endif ; FLASH_B_AVAILABLE == ON
#  endif ; ! ((SERIES == MB96340) && (DEVICE < 3))
#endif

#if ((CRYSTAL == FREQ_4MHZ) || (CRYSTAL == FREQ_8MHZ)) && \
     ((CLOCK_SPEED == CPU_48MHZ_CLKP2_16MHZ) || \
      (CLOCK_SPEED == CPU_48MHZ_CLKP1_32MHZ_CLKP2_16MHZ)) && \
     ! ((SERIES == MB96340) && (DEVICE < 3))
no_PLL_1WS:
          BBC  CKMR:6, no_PLL_1WS

          MOVW MTCRA, #0x6B09
#  if FLASH_B_AVAILABLE == ON
          MOVW MTCRB, #0x6B09
#  endif ; FLASH_B_AVAILABLE == ON
#endif

#if (CLOCKWAIT == ON) && \
    ((CLOCK_SPEED == CPU_4MHZ_PLL_CLKP2_4MHZ) || \
     (CLOCK_SPEED == CPU_8MHZ_CLKP2_8MHZ) || \
     (CLOCK_SPEED == CPU_56MHZ_CLKP2_14MHZ))
no_PLL_yet:
          BBC  CKMR:6,no_PLL_yet       ; check PCM and wait for
                                       ; PLL to stabilize
#endif ; wait for PLL

;====================================================================
; 6.13  Initialise Low-Level Library Interface
;====================================================================
;
; Call lib init function and reload stack afterwards, if AUTOMODEL
;====================================================================
#if CLIBINIT == ON
#  if MEMMODEL == SMALL || MEMMODEL == COMPACT
          CALL __stream_init       ; initialise library IO
#  else                            ; MEDIUM, LARGE, AUTOMODEL
          CALLP __stream_init      ; initialise library IO
#    if MEMMODEL == AUTOMODEL          
          RELOAD_SP                ; reload stack since stream_init was
                                   ; possibly left by RET (not RETP)
#    endif  ; AUTOMODEL
#  endif  ; MEDIUM, LARGE, AUTOMODEL
#endif  ; LIBINI

;====================================================================
; 6.14  Call C-language main function
;====================================================================
#if MEMMODEL == SMALL || MEMMODEL == COMPACT
          CALL _main               ; Start main function
#else                              ; MEDIUM, LARGE, AUTOMODEL
          CALLP _main              ; Start main function
                                   ; ignore remaining word on stack, 
                                   ; if main was completed by RET
#endif
;====================================================================
; 6.15  Shut down library
;====================================================================
#if CLIBINIT == ON
#  if MEMMODEL == SMALL || MEMMODEL == COMPACT
          CALL _exit               
#  else                            ; MEDIUM, LARGE, AUTOMODEL
          CALLP _exit              ; ignore remaining word on stack, 
                                   ; if main was completed by RET
#  endif
__exit:
#endif          

;====================================================================
; 6.16  Program end loop
;====================================================================

end:      BRA  end                 ; Loop

          .END notresetyet         ; define debugger start address


;====================================================================
; ----------------------- End of Start-up file ---------------------
;====================================================================
