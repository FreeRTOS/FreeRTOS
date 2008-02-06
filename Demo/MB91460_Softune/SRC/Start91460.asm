/*      THIS SAMPLE CODE IS PROVIDED AS IS AND IS SUBJECT TO ALTERATIONS. FUJITSU       */
/*      MICROELECTRONICS ACCEPTS NO RESPONSIBILITY OR LIABILITY FOR ANY ERRORS OR       */
/*      ELIGIBILITY FOR ANY PURPOSES.                                                   */
/*      (C) 2007,2008 Fujitsu Microelectronics Europe GmbH                              */
;=========================================================================================
; 1  Contents
;=========================================================================================
; 1       Contents
; 2       Disclaimer
;
; 3       History
;
; 4       Settings
; 4.1     Controller device
; 4.2     Boot / flash security 
; 4.3     Stack type and stack size
; 4.4     Copy code from flash to I-RAM
; 4.5     C++ start-up 
; 4.6     Low-level library interface
; 4.7     Clock Configuration
; 4.7.1   Clock selection
; 4.7.2   Select Clock Modulator
; 4.8     External bus interface
; 4.8.1   Select chipselect 
; 4.8.2   Set memory addressing for chipselects
; 4.8.3   Configure chipselect area
; 4.8.4   Set wait cycles for chipselects
; 4.8.5   Configure chipselects SDRAM memory only 
; 4.8.6   Referesh control register RCR 
; 4.8.7   Terminal and timing control register
; 4.8.8   Enable / disable I-cache
; 4.8.9   Enable CACHE for chipselect
; 4.8.10  Select external bus mode (data lines)
; 4.8.11  Select external bus mode (address lines)
; 4.8.12  Select external bus mode (control signals)
;
; 5       Definitions of Configurations
;
; 6       Section and data declaration
; 6.1     Define stack size
; 6.2     Define sections
;
; 7.      S T A R T 
; 7.1     Initialise stack pointer and table base register
; 7.2     Check for CSV reset and set CSV
; 7.3     Check clock condition
; 7.4     Restore default settings after reset
; 7.4.1   Disable clock modulator
; 7.4.2   Check if running on sub clock, change to main clock
; 7.4.3   Disable sub clock
; 7.4.4   Check if running on PLL, gear down PLL
; 7.4.5   Disable PLL
; 7.4.6   Set to main clock
; 7.5     Set memory controller
; 7.6     Clock startup
; 7.6.1   Set Voltage Regulator Settings
; 7.6.2   Power on clock modulator - clock modulator part I
; 7.6.3   Set CLKR register w/o clock mode
; 7.6.4   Start PLLs 
; 7.6.5   Wait for PLL oscillation stabilisation
; 7.6.6   Set clocks 
; 7.6.6.1 Set CPU and peripheral clock
; 7.6.6.2 Set external bus interface clock
; 7.6.6.3 Set CAN clock prescaler
; 7.6.6.4 Switch main clock mode
; 7.6.6.5 Switch sub clock mode
; 7.6.6.6 Switch to PLL mode
; 7.6.7   Enable frequncy modulation - clock modulator part II
; 7.7     Set BusInterface
; 7.7.1   Disable all CS
; 7.7.2   Clear TCR register
; 7.7.3   Set CS0 
; 7.7.4   Set CS1 
; 7.7.5   Set CS2  
; 7.7.6   Set CS3
; 7.7.7   Set CS4
; 7.7.8   Set CS5 
; 7.7.9   Set CS6
; 7.7.10  Set CS7  
; 7.7.11  Set special SDRAM config register  
; 7.7.12  set Port function register
; 7.7.13  Set TCR register
; 7.7.14  Enable cache for selected CS
; 7.7.15  Set SDRAM referesh control register
; 7.7.16  Enable used CS
; 7.7.17  I-cache on/off
; 7.7.18  Set port function register to general as I/O-port
; 7.8     Copy code from flash to I-RAM
; 7.9     Fill stacks
; 7.10    Clear data 
; 7.11    Copy Init section from ROM to RAM
; 7.12    C library initialization
; 7.13    Call C++ constructors
; 7.14    Call main routine
; 7.15    Return from main function
;
;=========================================================================================
; 2  Disclaimer
;=========================================================================================
;                    Fujitsu Microelectronics Europe GmbH                       
;                http://emea.fujitsu.com/microelectronics 
;                                                              
;    The  following  software  is for  demonstration  purposes only. It  is not fully  
;    tested, nor  validated  in order to fullfill its task under  all  circumstances.  
;    Therefore,  this software or  any part of it must only  be used in an evaluation 
;    laboratory environment.                        
;    This  software  is  subject to  the  rules of  our  standard DISCLAIMER, that is
;    delivered with our  SW-tools on  the  Fujitsu  Microcontrollers  CD/DVD (V3.4 or 
;    higher "\START.HTM") or on our Internet Pages:                                   
;    http://www.fme.gsdc.de/gsdc.htm
;    http://emea.fujitsu.com/microelectronics 
;
;=========================================================================================
; 3  History
;=========================================================================================
;
;=========================================================================================
;       MB914xx (FR60 CORE ONLY) Series C Compiler's 
;
;       Startup file for memory and basic controller initialisation
;=========================================================================================
;History:
;
; 2005-04-18 V1.0 UMa  Release first version
; 2005-06-17 V1.1 UMa  Added bus interface, modified c++ startup
; 2005-06-28 V1.2 UMa  minor changes
; 2005-07-27 V1.3 UMa  default values changed
; 2005-10-04 V1.4 UMa  changed code 'Call main Routine'
;                      Added secutiy section for MB91F467D  
;                      Added Flash Access Read Timing setting section;
; 2005-10-04 V1.5 UMa  Added Flash Controller Section
; 2005-10-28 V1.6 UMa  Check for CSV reset
; 2005-11.16 V1.7 UMa  Monitor Debugger support added: Copy of intvect Table
;                      Ext. Int 0 as abort function
;                      Changed PLL-Startup, Reset HWWD added
; 2005-11-16 V1.7 UMa  Examples for MUL_G changed
; 2006-02-14 V1.8 UMa  mb91464a added
;                      Settings for Clock Spervisor added
;                      Name of Section SECURITY changed to SECURITY_VECTORS
;                      Example values for gear-up changed
; 2006-03-17 V1.9 UMa  Changed Startup for Monitor Debugger
; 2006-04-24 v2.0 UMa  Added MB91465K and MB91469G
; 2006-05-03 v2.1 UMa  Added MB91461R; removed MB91V460A
;                      Added settings for the external bus-interface
; 2006-07-28 v2.2 UMa  Added I-RAM copy function (ROM -> IRAM)
;                      Added default settings for FLASH Access Read Timing 
;                      Settings 
;                      Changed default settings for FLASH cache configuration 
;                      Register
;                      Changed check for clock startup
; 2006-08-16 v2.3 MVo  Corrected Boot Security Sector Addresses for MB91469G
; 2006-10-06 v2.4 UMa  Added new devices
;                      Corrected typo in I_RAM to flash copy function
;                      Changed default settings for flash cache configuration
;                      Changed comments for SDRAM bus interface configuration
;                      Changed comments and default setting of CAN Prescaler
;                      Added Stack filler
;                      Added Settings for REGSEL Register
; 2007-02-13 v2.5 UMa  Introduction of default configurations
;                      Changed I_RAM to flash copy function                    
;
;
;=========================================================================================
; 4  Settings
;=========================================================================================
;
; CHECK ALL OPTIONS WHETHER THEY FIT TO THE APPLICATION;
;
; Configure this startup file in the "Settings" section. Search for
; comments with leading "; <<<". This points to the items to be set.
;=========================================================================================
;
#set    OFF             0
#set    ON              1
#set    DEFAULT         2
#set    LOW_PRIOR       31
;
;=========================================================================================
; 4.1  Controller Device
;=========================================================================================
#set    MB91464A        2                       ; MB91460 series
;
#set    MB91467B       10                       ; MB91460 series
;
#set    MB91467C       11                       ; MB91460 series
;
#set    MB91467D        4                       ; MB91460 series
;
#set    MB91469G        6                       ; MB91460 series
;
#set    MB91465K        3                       ; MB91460 series
;
#set    MB91463N        8                       ; MB91460 series
;
#set    MB91461R        1                       ; MB91460 series
#set    MB91467R        5                       ; MB91460 series
;
#set    MB91465X        9                       ; MB91460 series
;
#set    others          7                       ; MB91460 series
;
;
;
#set    DEVICE          MB91467D                ; <<< select device
;
;=========================================================================================
; 4.2  Boot / Flash Security 
;=========================================================================================
;
#set    BOOT_FLASH_SEC  OFF                     ; <<< BOOT and Flash Security Vector    
;
; The flash devices have two flash and two boot security vectors.  It is important to set
; the four vectors correctly.  Otherwise it might be possible,  that the flash device is 
; not accessible any more via the bootrom. Please read carefully the hardware manual.
; 
; OFF:  The security feature is switch off. The section SECURITY_VECTORS is reserved and
;       the vectors are set.
; ON:   IMPORTANT! The  security vectors are  not set. But the  section SECURITY_VECTORS 
;       is reserved.  
;
; Note: This feature is not supported by every device. Please check the data sheet. This 
;       feature is not available on MB91461R.
;
;=========================================================================================
; 4.3  Stack Type and Stack Size
;=========================================================================================
;
#set    USRSTACK        0                       ; user stack:   for main program
#set    SYSSTACK        1                       ; system stack: for main program and 
;                                               ;               interrupts
;
;
#set    STACKUSE        SYSSTACK                ; <<< set active stack
;
#set    STACK_RESERVE   ON                      ; <<< reserve stack area in 
;                                               ;     this module
#set    STACK_SYS_SIZE  2000	                ; <<< byte size of System stack
#set    STACK_USR_SIZE  4                       ; <<< byte size of User stack 
;
#set    STACK_FILL      ON                     ; <<< fills the stack area with pattern
#set    STACK_PATTERN   0x55AA55AA              ; <<< the pattern to write to stack
;
; - If the active stack is set to SYSSTACK,  it is used for main program and interrupts. 
;   In this case,  the user stack  could be set to a dummy size.  If the active stack is 
;   set  to  user  stack,  it is  used  for the  main  program  but the  system stack is 
;   automatically activated,  if an interrupt is serviced.  Both stack areas must have a 
;   reasonable size.
; - If STACK_RESERVE is ON,  the sections USTACK and SSTACK are reserved in this module. 
;   Otherwise, they have to be reserved in other modules.  If STACK_RESERVE is OFF,  the 
;   size definitions STACK_SYS_SIZE and STACK_USR_SIZE have no meaning.
; - Even if  they  are reverved  in other modules,  they are  still initialised  in this 
;   start-up file.
;
; Note: Several library functions require quite a big stack (due to ANSI). 
;       Check the stack information files (*.stk) in the LIB\911 directory.
;
;=========================================================================================
; 4.4  Copy code from Flash to I-RAM
;=========================================================================================
;
#set    I_RAM           OFF                     ; <<< select  if  code  in  section IRAM
;                                                     should be copied
;
; If this option is activated code located in the  section IRAM is copied during startup 
; from ROM to the instruction-RAM. The code is linked for the instruction-RAM.
;
;=========================================================================================
; 4.5  Low-Level Library Interface
;=========================================================================================
;
#set    CLIBINIT        OFF                     ; <<< select ext. libray usage
;
; This option has only to be set,  if  stream-IO/standard-IO function  of the C-libraray 
; have to be used (printf(), fopen()...).  This also requires  low-level functions to be 
; defined by the application software.
; For other library functions like (e.g. sprintf()) all this is not necessary.  However, 
; several functions consume a large amount of stack.
;
;=========================================================================================
; 4.6  C++ start-up 
;=========================================================================================
;
#set    CPLUSPLUS       OFF                     ; <<< activate if c++ files are used
;
; In the  C++ specifications,  when external  or static objects are used,  a constructor 
; must be called followed by  the main function.  Because four-byte pointers to the main 
; function are stored in the EXT_CTOR_DTOR section, call a constructor sequentially from
; the  lower  address  of  the four  addresses  in that  section.  If using C++ sources, 
; activate this function to create the section EXT_CTOR_DTOR. 
;
;=========================================================================================
; 4.7  Clock Configuration
;=========================================================================================
;=========================================================================================
; 4.7.1  Clock Selection
;=========================================================================================
;
; No clock settings
#set    NO_CLOCK                                               0x01
;
; Sub-oscillation input: 32 kHz 
#set    SUB_32KHZ_CPU__32KHZ_PER_32KHZ_EXT_32KHZ_CAN__2MHZ     0x11
;
; Oscillation input: 4 MHz 
#set    MAIN_4MHZ_CPU___2MHZ_PER__1MHZ_EXT__1MHZ_CAN__2MHZ     0x21
#set    PLL_4MHZ__CPU__48MHZ_PER_16MHZ_EXT_24MHZ_CAN_16MHZ     0x22
#set    PLL_4MHZ__CPU__64MHZ_PER_16MHZ_EXT_32MHZ_CAN_16MHZ     0x23
#set    PLL_4MHZ__CPU__80MHZ_PER_20MHZ_EXT_27MHZ_CAN_20MHZ     0x24
#set    PLL_4MHZ__CPU__80MHZ_PER_20MHZ_EXT_40MHZ_CAN_20MHZ     0x25
#set    PLL_4MHZ__CPU__96MHZ_PER_16MHZ_EXT_48MHZ_CAN_16MHZ     0x26  ;not MB91V460, ...
#set    PLL_4MHZ__CPU_100MHZ_PER_20MHZ_EXT_50MHZ_CAN_20MHZ     0x27  ;not MB91V460, ...
;
; MB91461R only: Oscillation input: 10 MHz
#set    PLL_10MHZ_CPU__60MHZ_PER_20MHZ_EXT_30MHZ_CAN_20MHZ     0x41
;
; MB91461R only: Oscillation input: 20 MHz
#set    PLL_20MHZ_CPU__60MHZ_PER_20MHZ_EXT_30MHZ_CAN_20MHZ     0x51
;
; User settings
#set    CLOCK_USER                                             0x61
;
;
;
#set    CLOCKSPEED      PLL_4MHZ__CPU__64MHZ_PER_16MHZ_EXT_32MHZ_CAN_16MHZ
;                                               ; <<< Select clock configuration 
;
; There are different default configurations available, where all necessary settings for 
; clocks and the related  registers are made.  Beside this configurations,  there is the
; possibility   to  define  a  user   configuration   in  the  chapter   "Definition  of 
; Configurations"
; 
; - NO_CLOCK means: 
;   The clock registers are not set by the start-up file.
;
; - PLL_4MHZ__CPU__64MHZ_PER_16MHZ_EXT_32MHZ_CAN_16MHZ means:
;   Main oszillation        =  4 MHz, PLL is activated
;   CPU clock (CLKB)        = 64 MHZ
;   Peripheral clock (CLKP) = 16 MHZ
;   Ext. bus clock (CLKT)   = 32 MHZ
;   CAN clock (CLKCAN)      = 16 MHz, using PLLx 
;
; - CLOCK_USER: 
;   The user configuration definded in the chapter "Definition of Configurations" is set.
;
; Note: Not all  frequencies  are supported  by every device.  Please see  the  hardware 
;       manual.
;
;=========================================================================================
; 4.7.2  Select Clock Modulator  
;=========================================================================================
;
#set    CLOMO           OFF                     ; <<< Enable /disable clock modulator      
;
#set    CMPR            0x026F                  ; <<< Ref. to the data sheet, CMPR
; 
; Please  refer  to the data sheet  of the device  if you  enable clock modulation.  The 
; register CMPR dependant on the PLL-Clock.
;
; Note: If the CLKCAN source is set either to main oscillator or to PLL  output then the
;       clock  for  the CAN  is not influenced by  the clock  modulation.  If the CLKCAN 
;       source is set CPU clock (CLKB) then the clock for the CAN is also modulated  (if 
;       the clock modulator is enabled).
;
; Note: If the clock modulator is enabled,  the wait states  of the  internal flash wait 
;       states  must  be  adapted  to  maximum frequency.  Please check the  wait states 
;       settings.
;
; Note: This feature  is not supported by every device,  e.g. MB91461.  Please check the 
;       data sheet.
;
;=========================================================================================
; 4.8  External Bus Interface
;
;      The rest of the configuration is only applicable for devices with an external bus 
;      interface.
;
;      If the device does not offer an external bus interface,  the configuration can be 
;      stoped at this point.
;
;=========================================================================================
;
#set    EXTBUS          DEFAULT                 ; <<< Ext. Bus on/off
;
;                       ON      - The ext. bus interface is enabled and is configured as
;                                 set below. 
;                             
;                       OFF     - The ext. bus interface is  diabled.  The port function 
;                                 registers  are set to  general I/O.  The registers  of 
;                                 ext. bus interface will not be touched by the start-up 
;                                 file.  
;                                 Be aware, that the device  might be conifgured in ext.
;                                 bus mode by default after reset.
;
;                       DEFAULT - Neither the register nor the respective  port function
;                                 registers are touched by the start-up file.
;                                 Be aware, that the device  might be conifgured in ext. 
;                                 bus mode by default after reset.
;
;
; Note: This feature is not supported by every device. Please check the data sheet.  The 
;       following devices for example do not offer an external bus interface:  MB91464A, 
;       MB91467C, MB91465K, MB91463N, MB91465X.
;
;=========================================================================================
; 4.8.1  Select Chipselect (Only EXTBUS == ON)
;=========================================================================================
;
#set    CS0             OFF                     ; <<< select CS (ON/OFF)
#set    CS1             OFF                     ; <<< select CS (ON/OFF)
#set    CS2             OFF                     ; <<< select CS (ON/OFF)
#set    CS3             OFF                     ; <<< select CS (ON/OFF)
#set    CS4             OFF                     ; <<< select CS (ON/OFF)
#set    CS5             OFF                     ; <<< select CS (ON/OFF)
#set    CS6             OFF                     ; <<< select CS (ON/OFF)
#set    CS7             OFF                     ; <<< select CS (ON/OFF)
#set    SDRAM           OFF                     ; <<< select if a SDRAM is connected 
;
;
#set    ENACSX          B'00000000              ; <<< set CS, ENACSX
;                         ||||||||
;                         ||||||||__ CS0 bit, enable/disable CS0 (1/0)
;                         |||||||___ CS1 bit, enable/disable CS1 (1/0)
;                         ||||||____ CS2 bit, enable/disable CS2 (1/0)
;                         |||||_____ CS3 bit, enable/disable CS3 (1/0)
;                         ||||______ CS4 bit, enable/disable CS4 (1/0)
;                         |||_______ CS5 bit, enable/disable CS5 (1/0) 
;                         ||________ CS6 bit, enable/disable CS6 (1/0)
;                         |_________ CS7 bit, enable/disable CS7 (1/0)
;
; Note: If the SWB Monitor Debugger is used,  set the CS1 (external RAM only) or CS0 and 
;       CS 1 (external RAM and flash) to off.
;
; Note: Not all Chipselects  are supported by  the different devices.  Please check  the 
;       data sheet.
;
;=========================================================================================
; 4.8.2  Set memory addressing for Chipselects (only EXTBUS == ON)
;=========================================================================================
;
#set    AREASEL0        0x0000                  ; <<< set start add. for CS0, ASR0  
#set    AREASEL1        0x0000                  ; <<< set start add. for CS1, ASR1           
#set    AREASEL2        0x0000                  ; <<< set start add. for CS2, ASR2 
#set    AREASEL3        0x0000                  ; <<< set start add. for CS3, ASR3 
#set    AREASEL4        0x0000                  ; <<< set start add. for CS4, ASR4 
#set    AREASEL5        0x0000                  ; <<< set start add. for CS5, ASR5 
#set    AREASEL6        0x0000                  ; <<< set start add. for CS6, ASR6 
#set    AREASEL7        0x0000                  ; <<< set start add. for CS7, ASR7 
;
; Configure the starting address of each used Chipselect. Chipselects which are not used
; (not set to ON in "Select Chipselect") need not be set (setting ignored).
;
; NOTE: Just  the upper 16-bit  of the start address must be set,  e.g. when using start 
;       address 0x00080000 set 0x0008.
;
;=========================================================================================
; 4.8.3  Configure Chipselect Area (only EXTBUS == ON)
;=========================================================================================
;
#set    CONFIGCS0       B'0000000000000000      ; <<< Config. CS0, ACR0
#set    CONFIGCS1       B'0000000000000000      ; <<< Config. CS1, ACR1 
#set    CONFIGCS2       B'0000000000000000      ; <<< Config. CS2, ACR2 
#set    CONFIGCS3       B'0000000000000000      ; <<< Config. CS3, ACR3 
#set    CONFIGCS4       B'0000000000000000      ; <<< Config. CS4, ACR4  
#set    CONFIGCS5       B'0000000000000000      ; <<< Config. CS5, ACR5  
#set    CONFIGCS6       B'0000000000000000      ; <<< Config. CS6, ACR6  
#set    CONFIGCS7       B'0000000000000000      ; <<< Config. CS7, ACR7  
;                         ||||||||||||||||
;                         ||||||||||||||||__ TYP0 bit, TYP0-4 bits select access type
;                         |||||||||||||||___ TYP1 bit
;                         ||||||||||||||____ TYP2 bit
;                         |||||||||||||_____ TYP3 bit
;                         ||||||||||||______ LEND bit, select little '1' or big endian '0'
;                         |||||||||||_______ WREN bit, en-/disable (1/0) Write access
;                         ||||||||||________ PFEN bit, en-/disable (1/0) pre-fetch
;                         |||||||||_________ SREN bit, en-/disable (1/0) share of BRQ & BGRNTX
;                         ||||||||__________ BST0 bit, BSTx bits select burst size
;                         |||||||___________ BST1 bit
;                         ||||||____________ DBW0 bit, DBWx select data bus width
;                         |||||_____________ DBW1 bit
;                         ||||______________ ASZ0 bit, ASZx bits select address size of CS
;                         |||_______________ ASZ1 bit
;                         ||________________ ASZ2 bit
;                         |_________________ ASZ3 bit
;
; Bit description:
;
; TYP3 TYP2 TYP1 TYP0  : Select access type of each CS
; 0    0    X    X     : Normal access (asynchronous SRAM, I/O, 
;                        single/page/busrt-ROM/FLASH) 
; 0    1    X    X     : Address/data multiplexed (8bit / 16bit bus width only)
; 0    X    X    0     : WAIT insertion by RDY disabled
; 0    X    X    1     : WAIT insertion by RDY enabled
; 0    X    0    X     : The WR0X pin to the WR3X pin are used as write strobes 
;                        (WRX is fixed at H-Level)
; 0    X    1    X     : The WRX pin is used as write strobe 
; 1    0    0    0     : Memory type A: SDRAM/FCRAM (Auto pre-charge used)  
; 1    0    0    1     : Memory type B: FCRAM (Auto pre-charge used)  
; 1    0    1    0     : setting not allowed
; 1    0    1    1     : setting not allowed
; 1    1    0    0     : setting not allowed
; 1    1    0    1     : setting not allowed
; 1    1    1    0     : setting not allowed
; 1    1    1    1     : mask area setting
;
;               LEND   : select BYTE ordering 
;                0     : Big endian
;                1     : Little endian
;
;               WREN   : enable or disable write access 
;                0     : disabled 
;                1     : enabled,    
;
;               PFEN   : Enable or disable the pre-fetch
;                0     : disabled 
;                1     : enabled,    
;
;               SREN   : Enable or disable the sharing of BRQ and BGRNTX 
;                0     : disabled 
;                1     : enabled (CSx pin High-Z)
;
;          BST1 BST0   : set burst size of chip select area
;            0   0     : 1 burst (single access)
;            0   1     : 2 bursts (Address boundary 1 bit) 
;            1   0     : 4 bursts (Address boundary 2 bit)
;            1   1     : 8 bursts (Address boundary 3 bit)
;
;          DBW1 DBW0   : Set data bus width
;            0   0     : 8-bit (BYTE access) 
;            0   1     : 16-bit (HALF-WORD access) 
;            1   0     : 32-bit (WORD access) 
;            1   1     : Reserved  
;
; ASZ3 ASZ2 ASZ1 ASZ0  :  Select memory size of each chipselect 
; 0    0    0    0     : 64 Kbyte  (0x01.0000 bytes; use ASR A[31:16] bits) 
; 0    0    0    1     : 128 Kbyte (0x02.0000 bytes; use ASR A[31:17] bits)
; 0    0    1    0     : 256 Kbyte (0x04.0000 bytes; use ASR A[31:18] bits)
; 0    0    1    1     : 512 Kbyte (0x08.0000 bytes; use ASR A[31:19] bits)
; 0    1    0    0     : 1 Mbyte   (0x10.0000 bytes; use ASR A[31:20] bits)
; 0    1    0    1     : 2 Mbyte   (0x20.0000 bytes; use ASR A[31:21] bits)
; 0    1    1    0     : 4 Mbyte   (0x40.0000 bytes; use ASR A[31:22] bits)
; 0    1    1    1     : 8 Mbyte   (0x80.0000 bytes; use ASR A[31:23] bits)
; 1    0    0    0     : 16 Mbyte  (0x100.0000 bytes; use ASR A[31:24] bits)
; 1    0    0    1     : 32 Mbyte  (0x200.0000 bytes; use ASR A[31:25] bits)
; 1    0    1    0     : 64 Mbyte  (0x400.0000 bytes; use ASR A[31:26] bits)
; 1    0    1    1     : 128 Mbyte (0x800.0000 bytes; use ASR A[31:27] bits)
; 1    1    0    0     : 256 Mbyte (0x1000.0000 bytes; use ASR A[31:28] bits)
; 1    1    0    1     : 512 Mbyte (0x2000.0000 bytes; use ASR A[31:29] bits)
; 1    1    1    0     : 1024 Mbyte(0x4000.0000 bytes; use ASR A[31:30] bits)
; 1    1    1    1     : 2048 Mbyte(0x8000.0000 bytes; use ASR A[31] bit)
;
;=========================================================================================
; 4.8.4  Set Wait cycles for Chipselects for ordinary businterface (only EXTBUS == ON)
;=========================================================================================
;
; Ordinary bus interface (w/o SDRAM and FRAM) (ACRx_Type = 0xxx)
;
#set    WAITREG0        B'0000000000000000      ; <<< CS0 Waitstates, AWR0  
#set    WAITREG1        B'0000000000000000      ; <<< CS1 Waitstates, AWR1  
#set    WAITREG2        B'0000000000000000      ; <<< CS2 Waitstates, AWR2 
#set    WAITREG3        B'0000000000000000      ; <<< CS3 Waitstates, AWR3 
#set    WAITREG4        B'0000000000000000      ; <<< CS4 Waitstates, AWR4 
#set    WAITREG5        B'0000000000000000      ; <<< CS5 Waitstates, AWR5 
;                         ||||||||||||||||
;                         ||||||||||||||||__ W00 bit, RDY/WRY-> CSX hold cycle
;                         |||||||||||||||___ W01 bit, CSX->RDX/WRX setup extension cycle
;                         ||||||||||||||____ W02 bit, Address -> CSX Delay selection
;                         |||||||||||||_____ W03 bit, WR0X to WR3X/WRX outout timing 
;                         ||||||||||||______ W04 bit, W04/W05 Write recovery cycle
;                         |||||||||||_______ W05 bit  
;                         ||||||||||________ W06 bit, W06/07 Read -> Write idle cycle 
;                         |||||||||_________ W07 bit          selection
;                         ||||||||__________ W08 bit, W08-W11 Intra-page access cycle 
;                         |||||||___________ W09 bit          select (0-15 cycles)
;                         ||||||____________ W10 bit 
;                         |||||_____________ W11 bit
;                         ||||______________ W12 bit, W12-W15 First access wait cycle  
;                         |||_______________ W13 bit          select (0-15 cycles)
;                         ||________________ W14 bit
;                         |_________________ W15 bit
;
;
; SDRAM and FRAM bus interface (ACRx_Type = 100x) 
;
#set    WAITREG6        B'0000000000000000      ; <<< CS6 Waitstates, AWR6 
#set    WAITREG7        B'0000000000000000      ; <<< CS7 Waitstates, AWR7
;                         ||||||||||||||||
;                         ||||||||||||||||__ W00 bit, W0-W1 RAS precharge cycles
;                         |||||||||||||||___ W01 bit
;                         ||||||||||||||____ W02 bit, W2-W3 RAS active Time
;                         |||||||||||||_____ W03 bit
;                         ||||||||||||______ W04 bit, W4-W5 Write recovery cycle
;                         |||||||||||_______ W05 bit 
;                         ||||||||||________ W06 bit, W6-W7 Read->Write idle cycle
;                         |||||||||_________ W07 bit
;                         ||||||||__________ W08 bit, W8-W10 CAS latency 
;                         |||||||___________ W09 bit
;                         ||||||____________ W10 bit 
;                         |||||_____________ W11 bit, reserved
;                         ||||______________ W12 bit, W12-W16 RAS-CAS delay 
;                         |||_______________ W13 bit
;                         ||________________ W14 bit  
;                         |_________________ W15 bit, reserved
;
;
; The bit meaning depends on the configured bus interface type. The bus interface can be 
; configured for different memory types. Depending on the memory type, the wait register 
; bits have a differnt meaning.  CS0-5 should  be configurable as ordinary bus interface 
; (w/o SDRAM and FRAM)  and CS6-7 should be configurable as  SDRAM and FRAM.  It is also 
; possible and for some devices neccessary to configure  other two chip selects as SDRAM 
; or FRAM interface. In such a case be aware of the bit meanings.
;
;
; Ordinary bus interface (w/o SDRAM and FRAM) (ACRx_Type = 0xxx)
; --------------------------------------------------------------
;
; Bit description:
;
;                W00   : RDY/WRX -> CSX hold extension cycle
;                0     : 0 cycle
;                1     : 1 cycle
;
;                W01   : CSX -> RDX/WRX setup extention cycle
;                0     : 0 cycle
;                1     : 1 cycle
;
;                W02   : Address -> CSX Delay selection
;                0     : no delay selected
;                1     : delay selected
;
;                W03   : WR0X to WR3X/WRX outout timing selection
;                0     : MCLK synchronous write output enable (ASX=L)
;                1     : Asynchronous write strobe output (norma operation)
;
;           W05  W04   : select Write recovery cycle
;           0    0     : 0 cycle
;           0    1     : 1 cycle
;           1    0     : 2 cycles
;           1    1     : 3 cycles
;
;           W07  W06   : Read -> Write idle cycle selection
;           0    0     : 0 cycle
;           0    1     : 1 cycle
;           1    0     : 2 cycles
;           1    1     : 3 cycles
; 
; W11  W10  W09  W08   :  Intra-page access cycle select (0-15 cycles)
; 0    0    0    0     :  0 Wait state
; 0    0    0    1     :  1 Auto-wait cycle
; 0    0    1    0     :  2 Auto-wait cycle
; ....
; 1    1    1    1     :  15 Auto wait cycles
;
; W15  W14  W13  W12   :  First access wait cycle can be set (0-15 cycles)
; 0    0    0    0     :  0 Wait state
; 0    0    0    1     :  1 Auto-wait cycle
; 0    0    1    0     :  2 Auto-wait cycle
; ....
; 1    1    1    1     :  15 Auto wait cycles
;  
;
;
; SDRAM and FRAM bus interface (ACRx_Type = 100x)
; -----------------------------------------------
;
; Bit description:
;
;           W01  W00   : RAS precharge cycles.
;           0    0     : 1 cycle
;           0    1     : 2 cycles
;           1    0     : 5 cycles
;           1    1     : 6 cycles
;
;           W03  W02   : RAS active Time
;           0    0     : 1 cycle
;           0    1     : 2 cycles
;           1    0     : 5 cycles
;           1    1     : 6 cycles
;
;           W05  W04   : set Write recovery cycle (1 - 4 cycles)
;           0    0     : Prohibited
;           0    1     : 2 cycles
;           1    0     : 3 cycles
;           1    1     : 4 cycles
;
;           W07  W06   : set Read -> Write idle Cycle (1 - 4 cycles)
;           0    0     : 1 cycle
;           0    1     : 2 cycles
;           1    0     : 3 cycles
;           1    1     : 4 cycles
;
;      W10  W09  W08   : set CAS latency (1 - 8 cycles)
;      0    0    0     : 1 cycle
;      0    0    1     : 2 cycle
;      ...
;      1    1    1     : 8 cycle
;
;                W11   : RESERVED, ALWAYS WRITE 0 !
;
;      W14  W13  W12   : set RAS-CAS delay (1 - 8 cycles)
;      0    0    0     : 1 cycle
;      0    0    1     : 2 cycle
;      ...
;      1    1    1     : 8 cycle
;
;                W15   : RESERVED, ALWAYS WRITE 0 !
;

; The bit meaning depends on the configured bus interface type
;
;=========================================================================================
; 4.8.5  Configure Chipselects for SDRAM memory only (only EXTBUS == ON and SDRAM)
;=========================================================================================
;
#set    MEMCON           B'00000111             ; <<< set special SDRAM register, MCRA
;                          ||||||||
;                          ||||||||__ ABS0 bit, set max. active banks (ABS1,0)
;                          |||||||___ ABS1 bit
;                          ||||||____ BANK bit, set number of banks connected to CS
;                          |||||_____ WBST bit, Write burst enable/disable
;                          ||||______ PSZ0 bit, Set page size (PSZ2-0)
;                          |||_______ PSZ1 bit 
;                          ||________ PSZ2 bit
;                          |_________ reserved, always write 0 
;
; When connecting  SDRAM/FCRAM TYP3-0=1000  in ACRx register the following register must  
; be setup.
;
; Bit description:
;
;           ABS1  ABS0 : Set maximum number of bank, active at same time
;            0     0   : 1 bank
;            0     1   : 2 banks
;            1     0   : 3 banks
;            1     1   : 4 banks
;
;                 BANK : Set number of connected SDRAM banks
;                  0   : 2 banks
;                  1   : 4 banks
;
;                 WBST : Write burst enable
;                  0   : Single Write
;                  1   : Busrt Write
;
;      PSZ2  PSZ1  PS0 : Select page size of connected memory
;      0     0     0   : 8-bit column address = A0 to A7 
;      0     0     1   : 9-bit column address = A0 to A8 
;      0     1     0   : 10-bit column address = A0 to A9 
;      0     1     1   : 11-bit column address = A0 to A9, A11 
;      1     X     X   : setting disabled
;
;
;=========================================================================================
; 4.8.6  Referesh Control Register RCR (only EXTBUS == ON and SDRAM)
;=========================================================================================
;
#set    REFRESH         B'1110001001000111      ; <<< set Refresh Control Register, RCR
;                         ||||||||||||||||
;                         ||||||||||||||||__ TRC0 bit, set refresh cycle (TRC2-0)
;                         |||||||||||||||___ TRC1 bit
;                         ||||||||||||||____ TRC2 bit
;                         |||||||||||||_____ PON bit, set power-on control
;                         ||||||||||||______ RFC0 bit, set refresh count (RFC2-0)
;                         |||||||||||_______ RFC1 bit 
;                         ||||||||||________ RFC2 bit 
;                         |||||||||_________ BRST bit, set burst refresh control 
;                         ||||||||__________ RFINT0 bit, set auto refresh interval
;                         |||||||___________ RFINT1 bit, (RFINT5-0)
;                         ||||||____________ RFINT2 bit
;                         |||||_____________ RFINT3 bit
;                         ||||______________ RFINT4 bit
;                         |||_______________ RFINT5 bit
;                         ||________________ RRLD bit, counter refresh strat control
;                         |_________________ SELF bit, self refresh control
;
;
; This register sets various SDRAM refresh controls.  When SDRAM control is not set  for 
; any area, the setting of this register is meaningless,  but do not change the register 
; value  at  initial   state.   When  a  read is  performed   using  a read-modify-write 
; instruction, 0 always returns from the SELF, RRLD, and PON bits.
;
; Bit description:
;
;
;    TRC2  TRC1  TRC0  : Refresh Cycle 
;      0     0     0   : 4
;      0     0     1   : 5
;      0     1     0   : 6
;      0     1     1   : 7
;      1     0     0   : 8
;      1     0     1   : 9
;      1     1     0   : 10
;      1     1     1   : 11
;
;                 PON  : Power-on control
;                  0   : disabled
;                  1   : power-on sequence started
;
;     RFC2  RFC1  RFC0 : Refresh Count
;      0     0     0   : 256
;      0     0     1   : 512
;      0     1     0   : 1024
;      0     1     1   : 2048
;      1     0     0   : 4096
;      1     0     1   : 8192
;      1     1     0   : Setting disabled
;      1     1     1   : Refresh disabled
;
;                 BRST : Burst refresh control
;                  0   : Decentralised refresh 
;                  1   : burst refresh
; 
;           RFINT[5-0] : auto refresh interval
;
;                 RRLD : Refresh counter Activation Control
;                  0   : Disabled,  
;                  1   : Autorefresh performed once, then value of RFINT reloaded
;
;                 SELF : Self refresh control
;                  0   : auto refresh or power down
;                  1   : Transitions to self-refresch mode
;
; NOTE: PON bit is set after the above setting. Do not set PON bit to 1 in the 
;       above setting. Otherwise the settings are not correct set.
;
;=========================================================================================
; 4.8.7  Terminal and Timing Control Register (only EXTBUS == ON)
;=========================================================================================
;
#set    TIMECONTR        B'00000000             ; <<< set TCR register, TCR
;                          ||||||||
;                          ||||||||__ RDW0 bit, set wait cycle reduction (RDW0,1)
;                          |||||||___ RDW1 bit
;                          ||||||____ OHT0 bit, set output hold delay (OHT1,0)
;                          |||||_____ OHT1 bit
;                          ||||______ reserved, always write 0 
;                          |||_______ PCLR bit, prefetch buffer clear 
;                          ||________ PSUS bit, prefetch suspend
;                          |_________ BREN bit, BRQ input enable 
;
; This register controls the general functions  of the external bus interface controller 
; such as the common-pin function setting and timing control.
;
; Bit description:
;
;          RDW1  RDW0  : Wait cycle reduction 
;            0     0   : Normal Wait (AWR0 - 7 setting)
;            0     1   : 1/2 of AWR0 - 7 setting value
;            1     0   : 1/4 of AWR0 - 7 setting value
;            1     1   : 1/8 of AWR0 - 7 setting value
;
;          OHT1  OHT0  : Output hold selection bit
;            0     0   : Output performed at falling edge of SYSCLK/MCLK
;            0     1   : Output performed about 3ns after falling edge of SYSCLK/MCLK
;            1     0   : Output performed about 4ns after falling edge of SYSCLK/MCLK
;            1     1   : Output performed about 5ns after falling edge of SYSCLK/MCLK
;
;                PCLR  : Prefetch buffer all clear
;                  0   : normal state
;                  1   : Prefetch buffer cleared
;
;                PSUS  : prefetch suspension bit 
;                  0   : Prefetch enabled
;                  1   : Prefetch disabled
;
;                BREN  : BRQ input enable
;                  0   : disabled, 
;                  1   : enabled, Bus sharing of BRQ/BGRNTX performed
;
; Note: This function is used to prevent an  excessive access cycle wait while operating 
;       at  a low-speed  clock  (such as  while  base  clock  operating at low  speed or 
;       high frequency division rate for external bus clock).
;
;=========================================================================================
; 4.8.8  Enable/Disable I-CACHE (only EXTBUS == ON)
;=========================================================================================
;
#set    C1024           1                       ; CACHE Size: 1024 BYTE
#set    C2048           2                       ; CACHE Size: 2048 BYTE
#set    C4096           3                       ; CACHE Size: 4096 BYTE
;
;
#set    CACHE           OFF                     ; <<< Select use of cache 
#set    CACHE_SIZE      C4096                   ; <<< Select size of cache, ISIZE
;
; It is possible  to use cache  functionality on  the I-Bus on  several devices.  Please 
; check the  corresponidng data sheet  if this feature is  available on a certain device 
; and for the size of the cache. This is the general cache configuration. It is possible 
; to configure for each CS area, if the cache should be used.
;
; Note: This feature is not supported by every device. Please check the data  sheet. The 
;       feature is for example supported by MB91461R, MB91469G.
;
;=========================================================================================
; 4.8.9  Enable CACHE for chipselect (only EXTBUS == ON)
;=========================================================================================
;
#set    CHEENA          B'11111111              ; <<< en-/disable cache, CHER
;                         ||||||||
;                         ||||||||__ CHE0 bit, CS0 area
;                         |||||||___ CHE1 bit, CS1 area
;                         ||||||____ CHE2 bit, CS2 area
;                         |||||_____ CHE3 bit, CS3 area
;                         ||||______ CHE4 bit, CS4 area 
;                         |||_______ CHE5 bit, CS5 area 
;                         ||________ CHE6 bit, CS6 area
;                         |_________ CHE7 bit, CS7 area 
;
; Additional to  the general cache enable setting,  select which CS  area should be used 
; with cache functionality.
;
; Note: Not all  Chipselects are  supported by the  different devices.  Please check the 
;       data sheet.
;
; Note: This feature is not supported by every device.  Please check the data sheet. The 
;       Feature is supported by MB91461R, MB91469G.
;
;=========================================================================================
; 4.8.10  Select External bus mode (Data lines) (only EXTBUS == ON)
;=========================================================================================
;
#set    PFUNC0          B'11111111              ;<<< Data lines or GIO, PFR00
;                         ||||||||
;                         ||||||||__ D24 / P00_0
;                         |||||||___ D25 / P00_1
;                         ||||||____ D26 / P00_2
;                         |||||_____ D27 / P00_3
;                         ||||______ D28 / P00_4
;                         |||_______ D29 / P00_5
;                         ||________ D30 / P00_6
;                         |_________ D31 / P00_7
;
#set    PFUNC1          B'11111111              ;<<< Data lines or GIO, PFR01
;                         ||||||||
;                         ||||||||__ D16 / P01_0
;                         |||||||___ D17 / P01_1
;                         ||||||____ D18 / P01_2
;                         |||||_____ D19 / P01_3
;                         ||||______ D20 / P01_4
;                         |||_______ D21 / P01_5
;                         ||________ D22 / P01_6
;                         |_________ D23 / P01_7
;
#set    PFUNC2          B'11111111              ;<<< Data lines or GIO, PFR02
;                         ||||||||
;                         ||||||||__ D8 / P02_0
;                         |||||||___ D9 / P02_1
;                         ||||||____ D10 / P02_2
;                         |||||_____ D11 / P02_3
;                         ||||______ D12 / P02_4
;                         |||_______ D13 / P02_5
;                         ||________ D14 / P02_6
;                         |_________ D15 / P02_7
;
#set    PFUNC3          B'11111111              ;<<< Data lines or GIO, PFR03
;                         ||||||||
;                         ||||||||__ D0 / P03_0
;                         |||||||___ D1 / P03_1
;                         ||||||____ D2 / P03_2
;                         |||||_____ D3 / P03_3
;                         ||||______ D4 / P03_4
;                         |||_______ D5 / P03_5
;                         ||________ D6 / P03_6
;                         |_________ D7 / P03_7
;
; Select if the ports are set to
;                  1   : External bus mode, I/O for data lines or
;                  0   : General I/O port (GIO)
;
; Note: Not all data-lines are supported by the different devices. Please check the data
;       sheet.
;
;=========================================================================================
; 4.8.11  Select External bus mode (Address lines) (only EXTBUS == ON)
;=========================================================================================
;
#set    PFUNC4          B'11111111              ;<<< Address lines or GIO, PFR04
;                         ||||||||
;                         ||||||||__ A24 / P04_0
;                         |||||||___ A25 / P04_1
;                         ||||||____ A26 / P04_2
;                         |||||_____ A27 / P04_3
;                         ||||______ A28 / P04_4
;                         |||_______ A29 / P04_5
;                         ||________ A30 / P04_6
;                         |_________ A31 / P04_7
;
#set    PFUNC5          B'11111111              ;<<< Address lines or GIO, PFR05
;                         ||||||||
;                         ||||||||__ A16 / P05_0
;                         |||||||___ A17 / P05_1
;                         ||||||____ A18 / P05_2
;                         |||||_____ A19 / P05_3
;                         ||||______ A20 / P05_4
;                         |||_______ A21 / P05_5
;                         ||________ A22 / P05_6
;                         |_________ A23 / P05_7
;
#set    PFUNC6          B'11111111              ;<<< Address lines or GIO, PFR06
;                         ||||||||
;                         ||||||||__ A8 / P06_0
;                         |||||||___ A9 / P06_1
;                         ||||||____ A10 / P06_2
;                         |||||_____ A11 / P06_3
;                         ||||______ A12 / P06_4
;                         |||_______ A13 / P06_5
;                         ||________ A14 / P06_6
;                         |_________ A15 / P06_7
;
#set    PFUNC7          B'11111111              ;<<< Address lines or GIO, PFR07
;                         ||||||||
;                         ||||||||__ A0 / P07_0
;                         |||||||___ A1 / P07_1
;                         ||||||____ A2 / P07_2
;                         |||||_____ A3 / P07_3
;                         ||||______ A4 / P07_4
;                         |||_______ A5 / P07_5
;                         ||________ A6 / P07_6
;                         |_________ A7 / P07_7
;
; Select if the ports are set to
;                  1   : External bus mode, I/O for address lines or
;                  0   : General I/O port (GIO)
;
; Note: Not all address-lines are supported  by the different devices.  Please check the
;       data sheet.
;
;=========================================================================================
; 4.8.12  Select External bus mode (Control signals) (only EXTBUS == ON)
;=========================================================================================
;
#set    PFUNC8          B'11111111              ;<<< Control signals or GIO, PFR08
;                         ||||||||
;                         ||||||||__ WRX0 / P08_0
;                         |||||||___ WRX1 / P08_1
;                         ||||||____ WRX2 / P08_2
;                         |||||_____ WRX3 / P08_3
;                         ||||______ RDX / P08_4
;                         |||_______ BGRNTX / P08_5
;                         ||________ BRQ / P08_6
;                         |_________ RDY / P08_7
;
#set    PFUNC9          B'11111111              ;<<< Control signals or GIO, PFR09
;                         ||||||||
;                         ||||||||__ CSX0 / P09_0
;                         |||||||___ CSX1 / P09_1
;                         ||||||____ CSX2 / P09_2
;                         |||||_____ CSX3 / P09_3
;                         ||||______ CSX4 / P09_4
;                         |||_______ CSX5 / P09_5
;                         ||________ CSX6 / P09_6
;                         |_________ CSX7 / P09_7
;
#set    PFUNC10         B'01011111              ;<<< Control signals or GIO, PFR10
;                         ||||||||
;                         ||||||||__ SYSCLK or !SYSCLK / P10_0 
;                         |||||||___ ASX / P10_1 
;                         ||||||____ BAAX / P10_2 
;                         |||||_____ WEX / P10_3 
;                         ||||______ MCLKO or !MCLKO / P10_4 
;                         |||_______ MCLKI or !MCLKI/ P10_5 
;                         ||________ MCLKE / P10_6
;                         |_________ - 
;
#set    EPFUNC10        B'00000000              ;<<< Control signals or GIO, EPFR10
;                         ||||||||
;                         ||||||||__ 0:SYSCLK / 1:!SYSCLK
;                         |||||||___ - 
;                         ||||||____ -
;                         |||||_____ -
;                         ||||______ 0:MCLKO / 1:!MCLKO
;                         |||_______ 0:MCLKI / 1:!MCLKI
;                         ||________ 0:MCLKI / 1:!MCLKI
;                         |_________ -
;
;
; Select if the ports are set to
;                  1   : External bus mode, I/O for control lines or
;                  0   : General I/O port (GIO)
;
; Note: Not all control-lines are supported  by the different devices.  Please check the
;       data sheet.
;
;=========================================================================================
; 5  Definition of Configurations
;=========================================================================================
;
#set    NOCLOCK         0                       ; do not touch CKSCR register
#set    MAINCLOCK       1                       ; select main clock 
;                                               ; MB91461R : 1/4 of oscillation input
;                                               ; Others:    1/2 of oscillation input
#set    MAINPLLCLOCK    2                       ; select main clock with PLL
#set    SUBCLOCK        3                       ; select subclock (if available)
;
#set    PSCLOCK_CLKB    0x00                    ; select core clock (initial)
#set    PSCLOCK_PLL     0x10                    ; select PLL output (x)
#set    PSCLOCK_MAIN    0x30                    ; select Main Oscillation
;
;=========================================================================================
; 5.1  CLOCKSPEED == CLOCK_USER <<<
;=========================================================================================
; Must be configured only in the case of CLOCKSPEED is set to CLOCK_USER. Please see the 
; corresponding application note.
;
#if (CLOCKSPEED == CLOCK_USER )
  #set  CLOCKSOURCE     MAINPLLCLOCK            ; <<< Clocksource
  #set  ENABLE_SUBCLOCK OFF                     ; <<< Subclock: ON/OFF
  #set  PLLSPEED        0x010F                  ; <<< 0x48Ch, 0x48Dh: PLLDIVM/N ; 64 MHz
  #set  DIV_G           0x0F                    ; <<< 0x48Eh: PLLDIVG; 
  #set  MUL_G           0x0F                    ; <<< 0x48Fh: PLLMULG;     
  ; Clock Divider
  #set  CPUCLOCK        0x00                    ; <<< 0x486h: DIV0R_B;   => /1  ; 64 MHz       
  #set  PERCLOCK        0x03                    ; <<< 0x486h: DIV0R_P;   => /4  ; 16 MHz 
  #set  EXTBUSCLOCK     0x01                    ; <<< 0x487h: DIV1R_T;   => /2  ; 32 MHz 
  ; CAN Clock
  #set  PSCLOCKSOURCE   PSCLOCK_PLL             ; <<< 0x4C0h: CANPRE;    => PLLx;128 MHz
  #set  PSDVC           0x07                    ; <<< 0x4C0h: CANPRE_DVC;=> /8  ; 16 MHz
  #set  CANCLOCK        0x00                    ; <<< 0x4C1h: CANCKD;    
  ; Voltage Regulator 
  #set  REGULATORSEL    0x06                    ; <<< 0x4CEh: REGSEL;
  #set  REGULATORCTRL   0x00                    ; <<< 0x4CFh: REGCTR;
  ; Memory Controller
  #set  FLASHCONTROL    0x032                   ; <<< 0x7002h: FCHCR;
  #set  FLASHREADT      0xC413                  ; <<< 0x7004h: FMWT;
  #set  FLASHMWT2       0x10                    ; <<< 0x7006h: FMWT2;
#endif  
;
;=========================================================================================
; 5.2  CLOCKSPEED == NO_CLOCK
;=========================================================================================
;
#if (CLOCKSPEED == NO_CLOCK )
    #set CLOCKSOURCE       NOCLOCK 
#endif      
;
;=========================================================================================
; 5.2  CLOCKSPEED == SUB_32KHZ_CPU__32KHZ_PER_32KHZ_EXT_32KHZ_CAN__2MHZ 
;=========================================================================================
;
#if (CLOCKSPEED == SUB_32KHZ_CPU__32KHZ_PER_32KHZ_EXT_32KHZ_CAN__2MHZ )
;
; Start restriction; Maximum frequency
  #if (DEVICE == MB91463N) || (DEVICE == MB91461R) 
     #error: Frequency is not supported by this device.
  #endif 
; End restriction
;
  #set  CLOCKSOURCE     SUBCLOCK                ; Clocksource
  #set  ENABLE_SUBCLOCK ON                      ; Subclock: ON/OFF
  #set  PLLSPEED        0x010F                  ; 0x48Ch, 0x48Dh: PLLDIVM/N    ;   n. a.
  #set  DIV_G           0x0F                    ; 0x48Eh: PLLDIVG; 
  #set  MUL_G           0x0F                    ; 0x48Fh: PLLMULG;     
  ; Clock Divider
  #set  CPUCLOCK        0x00                    ; 0x486h: DIV0R_B;    => /1    ;  32 KHz       
  #set  PERCLOCK        0x00                    ; 0x486h: DIV0R_P;    => /1    ;  32 KHz  
  #set  EXTBUSCLOCK     0x00                    ; 0x487h: DIV1R_T;    => /1    ;  32 KHz  
  ; CAN Clock
  #set  PSCLOCKSOURCE   PSCLOCK_MAIN            ; 0x4C0h: CANPRE;     => MAIN  ;   4 MHz
  #set  PSDVC           0x01                    ; 0x4C0h: CANPRE_DVC; => /2    ;   2 MHz
  #set  CANCLOCK        0x00                    ; 0x4C1h: CANCKD; all CAN Clocks enabled
  ; Voltage Regulator 
  #set  REGULATORSEL    0x06                    ; 0x4CEh: REGSEL;
  #set  REGULATORCTRL   0x00                    ; 0x4CFh: REGCTR;
  ; Memory Controller
  #set  FLASHCONTROL    0x032                   ; 0x7002h: FCHCR;
  #set  FLASHREADT      0xC100                  ; 0x7004h: FMWT; 
  #set  FLASHMWT2       0x00                    ; 0x7006h: FMWT2;
#endif 
;
;=========================================================================================
; 5.3  CLOCKSPEED == MAIN__4MHZ_CPU___2MHZ_PER__1MHZ_EXT__1MHZ_CAN__2MHZ 
;=========================================================================================
;
#if (CLOCKSPEED == MAIN_4MHZ_CPU___2MHZ_PER__1MHZ_EXT__1MHZ_CAN__2MHZ )
;
; Start restriction; Maximum frequency
  #if (DEVICE == MB91461R) 
     #error: Frequency is not supported by this device.
  #endif 
; End restriction
;
  #set  CLOCKSOURCE     MAINCLOCK               ; Clocksource
  #set  ENABLE_SUBCLOCK OFF                     ; Subclock: ON/OFF
  #set  PLLSPEED        0x010F                  ; 0x48Ch, 0x48Dh: PLLDIVM/N    ;   n. a.
  #set  DIV_G           0x0F                    ; 0x48Eh: PLLDIVG; 
  #set  MUL_G           0x0F                    ; 0x48Fh: PLLMULG;     
  ; Clock Divider
  #set  CPUCLOCK        0x00                    ; 0x486h: DIV0R_B;    => /1    ;   2 MHz       
  #set  PERCLOCK        0x01                    ; 0x486h: DIV0R_P;    => /2    ;   1 MHz 
  #set  EXTBUSCLOCK     0x01                    ; 0x487h: DIV1R_T;    => /2    ;   1 MHz 
  ; CAN Clock
  #set  PSCLOCKSOURCE   PSCLOCK_MAIN            ; 0x4C0h: CANPRE;     => PLLx  ;   4 MHz
  #set  PSDVC           0x01                    ; 0x4C0h: CANPRE_DVC; => /2    ;   2 MHz
  #set  CANCLOCK        0x00                    ; 0x4C1h: CANCKD; all CAN Clocks enabled
  ; Voltage Regulator 
  #set  REGULATORSEL    0x06                    ; 0x4CEh: REGSEL;
  #set  REGULATORCTRL   0x00                    ; 0x4CFh: REGCTR;
  ; Memory Controller
  #set  FLASHCONTROL    0x032                   ; 0x7002h: FCHCR;
  #set  FLASHREADT      0xC100                  ; 0x7004h: FMWT;
  #set  FLASHMWT2       0x00                    ; 0x7006h: FMWT2;  
#endif           
;
;=========================================================================================
; 5.4  CLOCKSPEED == PLL_4MHZ__CPU__48MHZ_PER_16MHZ_EXT_24MHZ_CAN_16MHZ 
;=========================================================================================
;
#if (CLOCKSPEED == PLL_4MHZ__CPU__48MHZ_PER_16MHZ_EXT_24MHZ_CAN_16MHZ )
;
; Start restriction; Maximum frequency
  #if (DEVICE == MB91461R) 
     #error: Frequency is not supported by this device.
  #endif 
; End restriction
;
  #set  CLOCKSOURCE     MAINPLLCLOCK            ; Clocksource
  #set  ENABLE_SUBCLOCK OFF                     ; Subclock: ON/OFF
  #set  PLLSPEED        0x010B                  ; 0x48Ch, 0x48Dh: PLLDIVM/N    ;  48 MHz
  #set  DIV_G           0x0F                    ; 0x48Eh: PLLDIVG; 
  #set  MUL_G           0x0B                    ; 0x48Fh: PLLMULG;     
  ; Clock Divider
  #set  CPUCLOCK        0x00                    ; 0x486h: DIV0R_B;    => /1    ;  48 MHz       
  #set  PERCLOCK        0x02                    ; 0x486h: DIV0R_P;    => /3    ;  16 MHz 
  #set  EXTBUSCLOCK     0x01                    ; 0x487h: DIV1R_T;    => /2    ;  24 MHz 
  ; CAN Clock
  #set  PSCLOCKSOURCE   PSCLOCK_PLL             ; 0x4C0h: CANPRE;     => PLLx  ;  96 MHz
  #set  PSDVC           0x05                    ; 0x4C0h: CANPRE_DVC; => /6    ;  16 MHz
  #set  CANCLOCK        0x00                    ; 0x4C1h: CANCKD; all CAN Clocks enabled
  ; Voltage Regulator 
  #if (DEVICE == MB91469G) 
   #set REGULATORSEL    0x36                    ; 0x4CEh: REGSEL;
  #else
   #set REGULATORSEL    0x06                    ; 0x4CEh: REGSEL;
  #endif    
  #set REGULATORCTRL    0x00                    ; 0x4CFh: REGCTR;    
   ; Memory Controller
  #set  FLASHCONTROL    0x032                   ; 0x7002h: FCHCR;
  #set  FLASHREADT      0xC201                  ; 0x7004h: FMWT;
  #set  FLASHMWT2       0x00                    ; 0x7006h: FMWT2;   
#endif        
;
;=========================================================================================
; 5.5  CLOCKSPEED == PLL_4MHZ__CPU__64MHZ_PER_16MHZ_EXT_32MHZ_CAN_16MHZ 
;=========================================================================================
;
#if (CLOCKSPEED == PLL_4MHZ__CPU__64MHZ_PER_16MHZ_EXT_32MHZ_CAN_16MHZ )
;
; Start restriction; Maximum frequency
  #if (DEVICE == MB91461R) 
     #error: Frequency is not supported by this device.
  #endif 
; End restriction
;
  #set  CLOCKSOURCE     MAINPLLCLOCK            ; Clocksource
  #set  ENABLE_SUBCLOCK OFF                     ; Subclock: ON/OFF
  #set  PLLSPEED        0x010F                  ; 0x48Ch, 0x48Dh: PLLDIVM/N    ;  64 MHz
  #set  DIV_G           0x0F                    ; 0x48Eh: PLLDIVG; 
  #set  MUL_G           0x0F                    ; 0x48Fh: PLLMULG;     
  ; Clock Divider
  #set  CPUCLOCK        0x00                    ; 0x486h: DIV0R_B;    => /1    ;  64 MHz       
  #set  PERCLOCK        0x03                    ; 0x486h: DIV0R_P;    => /4    ;  16 MHz 
  #set  EXTBUSCLOCK     0x01                    ; 0x487h: DIV1R_T;    => /2    ;  32 MHz 
  ; CAN Clock
  #set  PSCLOCKSOURCE   PSCLOCK_PLL             ; 0x4C0h: CANPRE;     => PLLx  ; 128 MHz
  #set  PSDVC           0x07                    ; 0x4C0h: CANPRE_DVC; => /8    ;  16 MHz
  #set  CANCLOCK        0x00                    ; 0x4C1h: CANCKD; all CAN Clocks enabled
  ; Voltage Regulator 
  #set  REGULATORSEL    0x06                    ; 0x4CEh: REGSEL;
  #set  REGULATORCTRL   0x00                    ; 0x4CFh: REGCTR;
  ; Memory Controller
  #set  FLASHCONTROL    0x032                   ; 0x7002h: FCHCR;
  #set  FLASHREADT      0xC413                  ; 0x7004h: FMWT;
  #set  FLASHMWT2       0x10                    ; 0x7006h: FMWT2;
#endif  
;
;=========================================================================================
; 5.6  CLOCKSPEED == PLL_4MHZ__CPU__80MHZ_PER_20MHZ_EXT_27MHZ_CAN_20MHZ 
;=========================================================================================
;
#if (CLOCKSPEED == PLL_4MHZ__CPU__80MHZ_PER_20MHZ_EXT_27MHZ_CAN_20MHZ )
;
; Start restriction; Maximum frequency
  #if (DEVICE == MB91461R) 
     #error: Frequency is not supported by this device.
  #endif 
; End restriction
;
  #set  CLOCKSOURCE     MAINPLLCLOCK            ; Clocksource
  #set  ENABLE_SUBCLOCK OFF                     ; Subclock: ON/OFF
  #set  PLLSPEED        0x0113                  ; 0x48Ch, 0x48Dh: PLLDIVM/N    ;  80 MHz
  #set  DIV_G           0x0F                    ; 0x48Eh: PLLDIVG; 
  #set  MUL_G           0x13                    ; 0x48Fh: PLLMULG;     
  ; Clock Divider
  #set  CPUCLOCK        0x00                    ; 0x486h: DIV0R_B;    => /1    ;  80 MHz       
  #set  PERCLOCK        0x03                    ; 0x486h: DIV0R_P;    => /4    ;  20 MHz 
  #set  EXTBUSCLOCK     0x02                    ; 0x487h: DIV1R_T;    => /3    ;  27 MHz 
  ; CAN Clock
  #set  PSCLOCKSOURCE   PSCLOCK_PLL             ; 0x4C0h: CANPRE;     => PLLx  ; 160 MHz
  #set  PSDVC           0x07                    ; 0x4C0h: CANPRE_DVC; => /8    ;   8 MHz
  #set  CANCLOCK        0x00                    ; 0x4C1h: CANCKD; all CAN Clocks enabled
  ; Voltage Regulator 
  #set  REGULATORSEL    0x06                    ; 0x4CEh: REGSEL;
  #set  REGULATORCTRL   0x00                    ; 0x4CFh: REGCTR;
  ; Memory Controller
  #set  FLASHCONTROL    0x032                   ; 0x7002h: FCHCR;
  #set  FLASHREADT      0xC413                  ; 0x7004h: FMWT;
  #set  FLASHMWT2       0x10                    ; 0x7006h: FMWT2;
#endif      
;
;=========================================================================================
; 5.7  CLOCKSPEED == PLL_4MHZ__CPU__80MHZ_PER_20MHZ_EXT_40MHZ_CAN_20MHZ 
;=========================================================================================
;
#if (CLOCKSPEED == PLL_4MHZ__CPU__80MHZ_PER_20MHZ_EXT_40MHZ_CAN_20MHZ )
;
; Start restriction; Maximum frequency
  #if (DEVICE == MB91461R) 
     #error: Frequency is not supported by this device.
  #endif 
; End restriction
;
  #set  CLOCKSOURCE     MAINPLLCLOCK            ; Clocksource
  #set  ENABLE_SUBCLOCK OFF                     ; Subclock: ON/OFF
  #set  PLLSPEED        0x0113                  ; 0x48Ch, 0x48Dh: PLLDIVM/N    ;  80 MHz
  #set  DIV_G           0x0F                    ; 0x48Eh: PLLDIVG; 
  #set  MUL_G           0x13                    ; 0x48Fh: PLLMULG;     
  ; Clock Divider
  #set  CPUCLOCK        0x00                    ; 0x486h: DIV0R_B;    => /1    ;  80 MHz       
  #set  PERCLOCK        0x03                    ; 0x486h: DIV0R_P;    => /4    ;  20 MHz 
  #set  EXTBUSCLOCK     0x01                    ; 0x487h: DIV1R_T;    => /2    ;  40 MHz 
  ; CAN Clock
  #set  PSCLOCKSOURCE   PSCLOCK_PLL             ; 0x4C0h: CANPRE;     => PLLx  ; 160 MHz
  #set  PSDVC           0x07                    ; 0x4C0h: CANPRE_DVC; => /8    ;   8 MHz
  #set  CANCLOCK        0x00                    ; 0x4C1h: CANCKD; all CAN Clocks enabled
  ; Voltage Regulator 
  #set  REGULATORSEL    0x06                    ; 0x4CEh: REGSEL;
  #set  REGULATORCTRL   0x00                    ; 0x4CFh: REGCTR;
  ; Memory Controller
  #set  FLASHCONTROL    0x032                   ; 0x7002h: FCHCR;
  #set  FLASHREADT      0xC413                  ; 0x7004h: FMWT;
  #set  FLASHMWT2       0x10                    ; 0x7006h: FMWT2;
#endif      
;
;=========================================================================================
; 5.8  CLOCKSPEED == PLL_4MHZ__CPU__96MHZ_PER_16MHZ_EXT_48MHZ_CAN_16MHZ 
;=========================================================================================
;
#if (CLOCKSPEED == PLL_4MHZ__CPU__96MHZ_PER_16MHZ_EXT_48MHZ_CAN_16MHZ )
;
; Start restriction; Maximum frequency
  #if (DEVICE == MB91464A) || (DEVICE == MB91465K) || (DEVICE == MB91463N) ||\
      (DEVICE == MB91461R) || (DEVICE == MB91467R)
     #error: Frequency is not supported by this device.
  #endif 
; End restriction
;
  #set  CLOCKSOURCE     MAINPLLCLOCK            ; Clocksource
  #set  ENABLE_SUBCLOCK OFF                     ; Subclock: ON/OFF
  #set  PLLSPEED        0x0117                  ; 0x48Ch, 0x48Dh: PLLDIVM/N    ;  96 MHz
  #set  DIV_G           0x0F                    ; 0x48Eh: PLLDIVG; 
  #set  MUL_G           0x17                    ; 0x48Fh: PLLMULG;     
  ; Clock Divider
  #set  CPUCLOCK        0x00                    ; 0x486h: DIV0R_B;    => /1    ;  64 MHz       
  #set  PERCLOCK        0x05                    ; 0x486h: DIV0R_P;    => /6    ;  16 MHz 
  #set  EXTBUSCLOCK     0x01                    ; 0x487h: DIV1R_T;    => /2    ;  32 MHz 
  ; CAN Clock
  #set  PSCLOCKSOURCE   PSCLOCK_PLL             ; 0x4C0h: CANPRE;     => PLLx  ; 192 MHz
  #set  PSDVC           0x0B                    ; 0x4C0h: CANPRE_DVC; => /12   ;  16 MHz
  #set  CANCLOCK        0x00                    ; 0x4C1h: CANCKD; all CAN Clocks enabled
  ; Voltage Regulator 
  #if (DEVICE == MB91469G) 
   #set REGULATORSEL    0x36                    ; 0x4CEh: REGSEL;
  #else
   #set REGULATORSEL    0x06                    ; 0x4CEh: REGSEL;
  #endif    
  #set REGULATORCTRL    0x00                    ; 0x4CFh: REGCTR;    
  ; Memory Controller
  #set FLASHCONTROL     0x032                   ; 0x7002h: FCHCR;
  #set FLASHREADT       0xC413                  ; 0x7004h: FMWT;
  #set FLASHMWT2        0x10                    ; 0x7006h: FMWT2;
#endif        
;
;=========================================================================================
; 5.9  CLOCKSPEED == PLL_4MHZ__CPU_100MHZ_PER_20MHZ_EXT_50MHZ_CAN_20MHZ 
;=========================================================================================
;
#if (CLOCKSPEED == PLL_4MHZ__CPU_100MHZ_PER_20MHZ_EXT_50MHZ_CAN_20MHZ )
;
; Start restriction; Maximum frequency
  #if (DEVICE == MB91464A) || (DEVICE == MB91465K) || (DEVICE == MB91463N) ||\
      (DEVICE == MB91461R) || (DEVICE == MB91467R) || (DEVICE == MB91467D)
     #error: Frequency is not supported by this device.
  #endif 
; End restriction
;
  #set  CLOCKSOURCE     MAINPLLCLOCK            ; Clocksource
  #set  ENABLE_SUBCLOCK OFF                     ; Subclock: ON/OFF
  #set  PLLSPEED        0x0118                  ; 0x48Ch, 0x48Dh: PLLDIVM/N    ; 100 MHz
  #set  DIV_G           0x0F                    ; 0x48Eh: PLLDIVG; 
  #set  MUL_G           0x17                    ; 0x48Fh: PLLMULG;     
  ; Clock Divider
  #set  CPUCLOCK        0x00                    ; 0x486h: DIV0R_B;    => /1    ; 100 MHz       
  #set  PERCLOCK        0x04                    ; 0x486h: DIV0R_P;    => /5    ;  20 MHz 
  #set  EXTBUSCLOCK     0x01                    ; 0x487h: DIV1R_T;    => /2    ;  50 MHz 
  ; CAN Clock
  #set  PSCLOCKSOURCE   PSCLOCK_PLL             ; 0x4C0h: CANPRE;     => PLLx  ; 200 MHz
  #set  PSDVC           0x09                    ; 0x4C0h: CANPRE_DVC; => /10   ;  20 MHz
  #set  CANCLOCK        0x00                    ; 0x4C1h: CANCKD; all CAN Clocks enabled
  ; Voltage Regulator 
  #if (DEVICE == MB91469G) 
   #set REGULATORSEL    0x36                    ; 0x4CEh: REGSEL;
  #else
   #set REGULATORSEL    0x06                    ; 0x4CEh: REGSEL;
  #endif    
  #set  REGULATORCTRL   0x00                    ; 0x4CFh: REGCTR;    
  ; Memory Controller
  #set  FLASHCONTROL    0x032                   ; 0x7002h: FCHCR;
  #set  FLASHREADT      0xC413                  ; 0x7004h: FMWT;
  #set  FLASHMWT2       0x10                    ; 0x7006h: FMWT2;
#endif        
;
;=========================================================================================
; 5.10  CLOCKSPEED == PLL_10MHZ_CPU__60MHZ_PER_20MHZ_EXT_30MHZ_CAN_20MHZ 
;=========================================================================================
;
#if (CLOCKSPEED == PLL_10MHZ_CPU__60MHZ_PER_20MHZ_EXT_30MHZ_CAN_20MHZ )
;
; Start restriction; Maximum frequency
  #if (DEVICE == MB91464A) || (DEVICE == MB91467B) || (DEVICE == MB91467C) ||\
      (DEVICE == MB91467D) || (DEVICE == MB91469G) || (DEVICE == MB91465K) ||\
      (DEVICE == MB91463N) || (DEVICE == MB91467R) || (DEVICE == MB91465X) 
     #error: Frequency is not supported by this device.
  #endif 
; End restriction
;
  #set  CLOCKSOURCE     MAINPLLCLOCK            ; Clocksource
  #set  ENABLE_SUBCLOCK OFF                     ; Subclock: ON/OFF
  #set  PLLSPEED        0x0105                  ; 0x48Ch, 0x48Dh: PLLDIVM/N    ;  60 MHz
  #set  DIV_G           0x0B                    ; 0x48Eh: PLLDIVG; 
  #set  MUL_G           0x1F                    ; 0x48Fh: PLLMULG;     
  ; Clock Divider
  #set  CPUCLOCK        0x00                    ; 0x486h: DIV0R_B;    => /1    ;  60 MHz       
  #set  PERCLOCK        0x02                    ; 0x486h: DIV0R_P;    => /3    ;  20 MHz 
  #set  EXTBUSCLOCK     0x01                    ; 0x487h: DIV1R_T;    => /2    ;  30 MHz 
  ; CAN Clock
  #set  PSCLOCKSOURCE   PSCLOCK_PLL             ; 0x4C0h: CANPRE;     => PLLx  ; 120 MHz
  #set  PSDVC           0x05                    ; 0x4C0h: CANPRE_DVC; => /6    ;  20 MHz
  #set  CANCLOCK        0x00                    ; 0x4C1h: CANCKD; all CAN Clocks enabled
  ; Voltage Regulator 
  ; -
  ; Memory Controller
  ; -
#endif        
;
;=========================================================================================
; 5.11  CLOCKSPEED == PLL_20MHZ_CPU__60MHZ_PER_20MHZ_EXT_30MHZ_CAN_20MHZ 
;=========================================================================================
;
#if (CLOCKSPEED == PLL_20MHZ_CPU__60MHZ_PER_20MHZ_EXT_30MHZ_CAN_20MHZ )
;
; Start restriction; Maximum frequency
  #if (DEVICE == MB91464A) || (DEVICE == MB91467B) || (DEVICE == MB91467C) ||\
      (DEVICE == MB91467D) || (DEVICE == MB91469G) || (DEVICE == MB91465K) ||\
      (DEVICE == MB91463N) || (DEVICE == MB91467R) || (DEVICE == MB91465X) 
     #error: Frequency is not supported by this device.
  #endif 
; End restriction
;
  #set  CLOCKSOURCE     MAINPLLCLOCK            ; Clocksource
  #set  ENABLE_SUBCLOCK OFF                     ; Subclock: ON/OFF
  #set  PLLSPEED        0x0102                  ; 0x48Ch, 0x48Dh: PLLDIVM/N    ; 60 MHz
  #set  DIV_G           0x0F                    ; 0x48Eh: PLLDIVG; 
  #set  MUL_G           0x1F                    ; 0x48Fh: PLLMULG;     
  ; Clock Divider
  #set  CPUCLOCK        0x00                    ; 0x486h: DIV0R_B;    => /1    ;  60 MHz       
  #set  PERCLOCK        0x02                    ; 0x486h: DIV0R_P;    => /3    ;  20 MHz 
  #set  EXTBUSCLOCK     0x01                    ; 0x487h: DIV1R_T;    => /2    ;  30 MHz 
  ; CAN Clock
  #set  PSCLOCKSOURCE   PSCLOCK_PLL             ; 0x4C0h: CANPRE;     => PLLx  ; 120 MHz
  #set  PSDVC           0x05                    ; 0x4C0h: CANPRE_DVC; => /6    ;  20 MHz
  #set  CANCLOCK        0x00                    ; 0x4C1h: CANCKD; all CAN Clocks enabled
  ; Voltage Regulator 
  ; -
  ; Memory Controller
  ; -
#endif  
;      
;=========================================================================================
; 6  Section and Data Declaration
;=========================================================================================

        .export __start             
        .import _main
        .import _RAM_INIT
        .import _ROM_INIT
        
#if CLIBINIT == ON    
        .export __exit 
        .import _exit
        .import __stream_init
#endif

#if CPLUSPLUS == ON
        .export __abort
        .import ___call_dtors
        .import _atexit
#endif
;=========================================================================================
; 6.1  Define Stack Size
;=========================================================================================
 .SECTION  SSTACK, STACK, ALIGN=4
#if STACK_RESERVE == ON
        .EXPORT         __systemstack, __systemstack_top
 __systemstack:
        .RES.B          STACK_SYS_SIZE
 __systemstack_top: 
#endif
 
        .SECTION  USTACK, STACK, ALIGN=4
#if STACK_RESERVE == ON
         .EXPORT        __userstack, __userstack_top
 __userstack:
        .RES.B          STACK_USR_SIZE
 __userstack_top:
 
#endif
;=========================================================================================
; 6.2  Define Sections
;=========================================================================================
        .section        DATA,  data,  align=4
        .section        INIT,  data,  align=4
        .section        IRAM,  code,  align=4
        .section        CONST, const, align=4
        .section        INTVECT, const, align=4 
        
#if I_RAM 
        .import _RAM_IRAM
        .import _ROM_IRAM
#endif
                    
#if (DEVICE != MB91461R)
    #if (DEVICE == MB91469G)
        .section        SECURITY_VECTORS, code, locate = 0x248000
    #else 
        .section        SECURITY_VECTORS, code, locate = 0x148000
    #endif
    
    #if (BOOT_FLASH_SEC == OFF)        
        .data.w 0xFFFFFFFF
        .data.w 0xFFFFFFFF
        .data.w 0xFFFFFFFF
        .data.w 0xFFFFFFFF       
    #else
        .res.w          4
    #endif         
#endif     
   
#if CPLUSPLUS == ON
        .section        EXT_CTOR_DTOR, const, align=4  ; C++ constructors
#endif        
       
;-----------------------------------------------------------------------------------------
; MACRO Clear RC Watchdog
;-----------------------------------------------------------------------------------------
#macro  ClearRCwatchdog
        LDI             #0x4C7,R7               ; clear RC watchdog
        BANDL           #0x7,@R7
#endm
;-----------------------------------------------------------------------------------------
; MACRO WAIT_LOOP
;-----------------------------------------------------------------------------------------
#macro wait_loop loop_number
#local _wait64_loop
        LDI             #loop_number, R0
_wait64_loop:
        ADD             #-1, R0
        BNE             _wait64_loop
#endm
        .section        CODE, code, align=4
        .section        CODE_START, code, align=4


;=========================================================================================
; 7.  S T A R T 
;=========================================================================================
__start:                                        ; start point   
startnop: 
        NOP       
;   
        ANDCCR          #0xEF                   ; disable interrupts   
        STILM           #LOW_PRIOR              ; set interrupt level to low prior
        ClearRCwatchdog                         ; clear harware watchdog

;=========================================================================================
; 7.1  Initialise Stack Pointer and Table Base Register
;=========================================================================================
#if STACKUSE == SYSSTACK       
        ORCCR           #0x20
        LDI             #__userstack_top, SP    ; initialize SP
        ANDCCR          #0xDF
        LDI             #__systemstack_top, SP  ; initialize SP
#endif

#if STACKUSE == USRSTACK
        ANDCCR          #0xDF
        LDI             #__systemstack_top, SP  ; initialize SP
        ORCCR           #0x20
        LDI             #__userstack_top, SP    ; initialize SP
#endif

        LDI             #INTVECT, R0            ; set Table Base
smd_tbr: 
        MOV             R0, TBR         

#if (CLOCKSOURCE != NOCLOCK)                                          
;=========================================================================================
; 7.2  Check for CSV reset and set CSV
;=========================================================================================
; Start restriction; No clock supervisor (CSV)
#if (DEVICE != MB91461R) && (DEVICE != MB91467R) && (DEVICE != MB91463N)
; End restriction
        LDI:20          #0x04AD, R0             ; CSVCR
        BORL            #0x8, @R0               ; Enable Main Osc CSV
        BTSTH           #0x4, @R0               ; Check for Main Osc missing
        BEQ             NoMAINCSVreset          ; Main osc available -> branch 
                                                ;   to NoCSVreset
        BANDL           #0x7, @R0               ; Disable Main Osc CSV
        
        LDI             #noClockStartup, R0     ; Main Clock missing -> no
        JMP             @R0                     ; clock startup
                                                
NoMAINCSVreset: 


        BORL            #0x4, @R0               ; Enable Sub Osc CSV
        BTSTH           #0x2, @R0               ; Check for Sub Osc missing
        BEQ             NoSUBCSVreset           ; Sub osc available -> branch 
                                                ;   to NoCSVreset
        BANDL           #0xB, @R0               ; Disable Sub Osc SCSV
#if (CLOCKSOURCE == SUBCLOCK)
        LDI             #noClockStartup, R0     ; Sub Clock missing -> no
        JMP             @R0                     ; clock startup
#endif                                                
NoSUBCSVreset:       
#endif        
;=========================================================================================
; 7.3  Check Clock Condition
;=========================================================================================
        LDI             #0x484, R0              ; Check for Default Values
        LDI             #0x0F, R1               
        ANDB            R1, @R0
        BEQ             clock_startup 

;=========================================================================================
; 7.4  Restore Default Settings after Reset
;=========================================================================================
;=========================================================================================
; 7.4.1  Disable Clock Modulator
;=========================================================================================
        LDI             #0x04BB, R0             ; Clock Modulator Control Reg
        BANDL           #0xD, @R0               ; Disable Frequency modulation
FMODwait:        
        BTSTL           #8, @R0                 ; Wait until Frequency modulation
        BNE             FMODwait                ; is disabled
        
        BANDL           #0xE, @R0               ; Power down clock modulator

;=========================================================================================
; 7.4.2  Check if running on Sub Clock, change to Main Clock
;=========================================================================================
        LDI:20          #0x0484,R12             ; Check if running on sub clock
        LDUB            @R12,R0
        LDI:8           #0x3,R1
        AND             R1,R0
        CMP             #0x3,R0
        BNE             notOnSubClock
        
        LDI:20          #0x04CC,R12             ; Check if Main Clock is stopped
        BTSTL           #1, @R12
        BEQ             mainNotStopped

        BANDL           #0xE, @R12              ; Start Main Oscillation
                        
        LDI             #0x4C8, R0              ; Main Stabilisation Wait Time
        LDI             #0x04, R1               ; 32.7 ms
        AND             R1, @R0  
        BORH            #0x02, @R0      
        
        mainStabTime:                           ; Wait for stabilisation time
        ClearRCwatchdog                         ; clear harware watchdog
        BTSTH           #8, @R0
        BEQ             mainStabTime
        LDI             #0x0, R1
        STB             R1, @R0

mainNotStopped:        
        LDI:20          #0x0484, R12            ; disable sub clock as source
        BANDL           #0xD, @R12              ; Clock source = 0x01 (Main/2)  
                                                       
notOnSubClock:
;=========================================================================================
; 7.4.3  Disable Sub Clock
;=========================================================================================
#if ENABLE_SUBCLOCK != ON
        LDI             #0x0484, R0             ; Clock source control reg CLKR
        BANDL           #0x7, @R0               ; Disable PLL
#endif       

;=========================================================================================
; 7.4.4  Check if running on PLL, Gear Down PLL
;=========================================================================================
        LDI:20          #0x0484,R12             ; Check if running on PLL
        LDUB            @R12,R0
        LDI:8           #0x3,R1
        AND             R1,R0
        CMP             #0x2,R0
        BNE             notOnPll
                    
        LDI:20          #0x0490, R11            ; clear flags  
        LDI:8           #0x0,R1        
        STB             R1, @R11
        LDI             #0x04,R1
        STB             R1, @R11                ; Set Flag for Simulator; no Effekt on
                                                ; Emulator      

        BANDL           #0xC, @R12              ; disable PLL as clock source  
                                                ; Clock Source = 0x00 (Main/2)
                                                    
        LDI:20          #0x048E,R12             ; check if DivG != 0
        LDUB            @R12, R0
        LDI:8           #0xFF,R1
        AND             R1,R0
        BEQ             notOnPll
                                                                                          
gearDownLoop:    
        ClearRCwatchdog                         ; clear harware watchdog
        BTSTL           #4, @R11                ; Gear Down
        BEQ             gearDownLoop            ; 
 
        LDI             #0x00,R1                ; Clear Flags
        STB             R1, @R11                ;       
        
notOnPll:
;=========================================================================================
; 7.4.5  Disable PLL
;=========================================================================================
        LDI             #0x0484, R0             ; Clock source control reg CLKR
        BANDL           #0xB, @R0               ; Disable PLL
        
;=========================================================================================
; 7.4.6  Set to Main Clock
;=========================================================================================
        LDI:20          #0x0484,R12             ; Check if running on PLL
        BANDL           #0xC, @R12              ; disable PLL as clock source  
                                                ; Clock Source = 0x00 (Main/2)

clock_startup:
;=========================================================================================
; 7.5  Set Memory Controller
;=========================================================================================
; Start restriction; No embedded flash
#if DEVICE != MB91461R
; End restriction
        LDI             #0x7002, R1             ; FLASH Controller Reg.
        LDI             #FLASHCONTROL, R2       ; Flash Controller Settings
        STH             R2, @R1                 ; set register
        LDI             #0x7004, R1             ; FLASH Memory Wait Timing Reg.
        LDI             #FLASHREADT, R2         ; wait settings
        STH             R2, @R1                 ; set register
        LDI             #0x7006, R1             ; FLASH Memory Wait Timing Reg.
        LDI             #FLASHMWT2, R2          ; wait settings
        STB             R2, @R1                 ; set register               
#endif                
        ClearRCwatchdog   
                                                       
;=========================================================================================
; 7.6  Clock startup
;=========================================================================================
;=========================================================================================
; 7.6.1  Set Voltage Regulator Settings
;=========================================================================================
; Start restriction; No regulator settings
#if DEVICE != MB91461R
; End restriction
        LDI             #0x04CF, R0             ; REGCTR
        LDI             #REGULATORCTRL, R1
        STB             R1, @R0

        LDI             #0x04CE, R0             ; REGSEL
        LDI             #REGULATORSEL, R1
        STB             R1, @R0
#endif

;=========================================================================================
; 7.6.2  Power on Clock Modulator - Clock Modulator Part I
;=========================================================================================
#if CLOMO == ON 
        LDI             #0x04BB, R0             ; Clock Modulator Control Reg
        LDI             #0x11, R1               ; Load value to Power on CM
        ORB             R1, @R0                 ; Power on clock modulaor
#endif

;=========================================================================================
; 7.6.3  Set CLKR Register w/o Clock Mode
;=========================================================================================
; Set Clock source (Base Clock) for the three clock tree selections
; This select Base clock is used to select afterwards the 3
; Clocks for the diffenrent internal trees.
; When PLL is used, first pll multiplication ratio is set and PLL is
; enabled. After waiting the PLL stabilisation time via timebase
; timer, PLL clock is selected as clock source. 
        LDI             #0x048C, R0             ; PLL Cntl Reg. PLLDIVM/N
        LDI:20          #PLLSPEED, R1
        STH             R1, @R0

        LDI             #0x048E, R0             ; PLL Cntl Reg. PLLDIVG
        LDI             #DIV_G, R1
        STB             R1, @R0

        LDI             #0x048F, R0             ; PLL Cntl Reg. PLLMULG
        LDI             #MUL_G, R1
        STB             R1, @R0

;=========================================================================================
; 7.6.4  Start PLL 
;=========================================================================================
#if ( ( CLOCKSOURCE == MAINPLLCLOCK ) || ( PSCLOCKSOURCE == PSCLOCK_PLL ) )
        LDI             #0x0484, R0             ; Clock source control reg CLKR
        LDI             #0x04, R1               ; Use PLL x1, enable PLL 
        ORB             R1, @R0                 ; store data to CLKR register
#endif
       
       
#if ENABLE_SUBCLOCK == ON
        LDI             #0x0484, R0             ; Clock source control reg CLKR
        LDI             #0x08, R1               ; enable subclock operation
        ORB             R1, @R0                 ; store data to CLKR register
        LDI             #0x4CA, R0              ; Sub Clock oszilation 
        LDI             #0x00, R1               ; stabilitsation time = 32 ms
        AND             R1, @R0  
        BORH            #0x02, @R0      
#endif      
      
;=========================================================================================
; 7.6.5  Wait for PLL oscillation stabilisation
;=========================================================================================
#if ((CLOCKSOURCE==MAINPLLCLOCK)||(PSCLOCKSOURCE==PSCLOCK_PLL))
        LDI             #0x0482, R12            ; TimeBaseTimer TBCR
        LDI             #0x00, R1               ; set 1024 us @ 2 MHz 
        STB             R1, @R12

        BANDH           #7, @R12                ; clear interrupt flag
        
        LDI             #0x0483, R0             ; clearTimeBaseTimer CTBR
        LDI             #0xA5, R1                 
        STB             R1, @R0
        LDI             #0x5A, R1                 
        STB             R1, @R0
        
        BANDH           #7, @R12                ; clear interrupt flag
        BORH            #8, @R12                ; set interrupt flag for simulator

PLLwait:        
        ClearRCwatchdog                         ; clear harware watchdog
        BTSTH           #8, @R12
        BEQ             PLLwait
#endif

;=========================================================================================
; 7.6.6  Set clocks 
;=========================================================================================
;=========================================================================================
; 7.6.6.1  Set CPU and peripheral clock 
;=========================================================================================
; CPU and peripheral clock are set in one register
        LDI             #0x0486, R2             ; Set DIVR0 (CPU-clock (CLKB)  
        LDI             #((CPUCLOCK << 4) + PERCLOCK), R3 ; Load CPU clock setting
        STB             R3, @R2               
;=========================================================================================
; 7.6.6.2  Set External Bus interface clock
;=========================================================================================
; set External Bus clock
; Be aware to do smooth clock setting, to avoid wrong clock setting
; Take care, always write 0 to the lower 4 bits of DIVR1 register
        LDI             #0x0487, R2             ; Set DIVR1  
        LDI             #(EXTBUSCLOCK << 4), R3 ; Load Peripheral clock setting
        STB             R3, @R2 
        
;=========================================================================================
; 7.6.6.3  Set CAN clock prescaler
;=========================================================================================
; Set CAN Prescaler, only clock relevant parameter 
        LDI             #0x04C0, R0             ; Set CAN ClockParameter Register
        LDI             #(PSCLOCKSOURCE + PSDVC), R1     ; Load Divider
        STB             R1, @R0                          ; Set Divider
; enable CAN clocks
        LDI             #0x04c1, R0             ; Set CAN Clock enable Register
        LDI             #CANCLOCK, R1           ; Load CANCLOCK
        STB             R1, @R0                 ; set CANCLOCK

;=========================================================================================
; 7.6.6.4  Switch Main Clock Mode
;=========================================================================================
#if CLOCKSOURCE == MAINCLOCK

;=========================================================================================
; 7.6.6.5  Switch Subclock Mode
;=========================================================================================
#elif ( (CLOCKSOURCE == SUBCLOCK) )
    #if ENABLE_SUBCLOCK == ON
        LDI             #0x4CA, R12
subStabTime:        
        ClearRCwatchdog                         ; clear harware watchdog
        BTSTH           #8, @R12                ; wait until sub clock stabilisation
        BEQ             subStabTime             ; time is over
        LDI             #0x0, R1
        STB             R1, @R12

        LDI             #0x0484, R0             ; Clock source control reg CLKR
        LDI             #0x01, R1               ; load value to select main clock
        ORB             R1, @R0                 ; enable main clock (1/2 external)        
        LDI             #0x03, R1               ; load value to select subclock
        ORB             R1, @R0                 ; enable subclock as clock source       
    #else
        #error: Wrong setting! The clock source is subclock, but the subclock is disabled.
    #endif

;=========================================================================================
; 7.6.7  Switch to PLL Mode
;=========================================================================================
#elif ( (CLOCKSOURCE == MAINPLLCLOCK) )

#if (DIV_G != 0x00)
        LDI             #0x0490, R0             ; PLL Ctrl Register   
        LDI             #0x00,R1
        STB             R1, @R0                 ; Clear Flag
        LDI             #0x01,R1
        STB             R1, @R0                 ; Set Flag for Simulator; no Effekt on
#endif                                                ; Emulator
 
        LDI             #0x0484, R3             ; Clock source control reg CLKR
        BORL            #0x2, @R3               ; enable PLL as clock source                                               
                                                
#if (DIV_G != 0x00)                                                
gearUpLoop:    
        ClearRCwatchdog                         ; clear harware watchdog
        LDUB            @R0, R2                 ; LOAD PLLCTR to R2
        AND             R1, R2                  ; GRUP, counter reach 0
        BEQ             gearUpLoop

        LDI             #0x00,R1
        STB             R1, @R0                 ; Clear Gear-Up Flag
#endif         
     
#endif

;=========================================================================================
; 7.6.8  Enable Frequncy Modulation - Clock Modulator Part II
;=========================================================================================
#if CLOMO == ON                                 ; Only applicable if Modulator is on
        LDI             #0x04B8, R0             ; Clock Modulation Parameter Reg
        LDI             #CMPR, R1               ; Load CMP value
        STH             R1, @R0                 ; Store CMP value in CMPR

        LDI             #0x04BB, R0             ; Clock Modulator Control Reg
        LDI             #0x13, R1               ; Load value to FM on CM
        ORB             R1, @R0                 ; FM on 
#endif

#endif
noClockStartup:

;=========================================================================================
; 7.7  Set BusInterface
;=========================================================================================
; Start restriction; No ext. bus interface
#if (DEVICE != MB91464A) && (DEVICE != MB91467C) && (DEVICE != MB91465K) &&  \
    (DEVICE != MB91463N) && (DEVICE != MB91465X)
; End restriction
#if (EXTBUS == ON) 
;=========================================================================================
; 7.7.1  Disable all CS
;=========================================================================================
; Start restriction; Flashless device
#if(DEVICE != MB91461R)
; End restriction
        LDI             #0x0680, R3             ; chip select enable register CSER
        LDI             #(0x00), R2             ; load disable settings                                                    
smd_cs:                                                    
        ANDB            R2, @R3                 ; set register          
#endif        

;=========================================================================================
; 7.7.2  Clear TCR Register
;=========================================================================================
        LDI             #0x0683, R1             ; Pin/Timing Control Register TCR
        BORH            #0x6,@R1                ; load timing settings 

;=========================================================================================
; 7.7.3  Set CS0
;=========================================================================================
#if CS0
        LDI             #0x0640, R1             ; area select reg ASR0, ACR0      
        LDI             #(AREASEL0<<16)+CONFIGCS0, R0  ; load settings
        ST              R0, @R1                 ; set registers
 
        LDI             #0x660, R1              ; area wait register awr0
        LDI             #WAITREG0, R2           ; wait settings
        STH             R2, @R1                 ; set register
#endif

;=========================================================================================
; 7.7.4  Set CS1  
;=========================================================================================
#if CS1  
        LDI             #0x0644, R1             ; area select reg ASR1, ACR1      
        LDI             #(AREASEL1<<16)+CONFIGCS1, R0  ; load settings
        ST              R0, @R1                 ; set registers

        LDI             #0x662, R1              ; area wait register awr1
        LDI             #WAITREG1, R2           ; wait settings
        STH             R2, @R1                 ; set register
#endif
smd_cs_mb91461r:
;=========================================================================================
; 7.7.5  Set CS2  
;=========================================================================================
#if CS2
        LDI             #0x0648, R1             ; area select reg ASR2, ACR2      
        LDI             #(AREASEL2<<16)+CONFIGCS2, R0  ; load settings
        ST              R0, @R1                 ; set registers
        LDI             #0x664, R1              ; area wait register awr2
        LDI             #WAITREG2, R2           ; wait settings
        STH             R2, @R1                 ; set register
#endif
;=========================================================================================
; 7.7.6  Set CS3  
;=========================================================================================
#if CS3
        LDI             #0x064C, R1             ; area select reg ASR3, ACR3      
        LDI             #(AREASEL3<<16)+CONFIGCS3, R0  ; load settings
        ST              R0, @R1                 ; set registers
        LDI             #0x666, R1              ; area wait register awr3
        LDI             #WAITREG3, R2           ; wait settings
        STH             R2, @R1                 ; set register
#endif
;=========================================================================================
; 7.7.7  Set CS4  
;=========================================================================================
#if CS4
        LDI             #0x0650, R1             ; area select reg ASR4, ACR4      
        LDI             #(AREASEL4<<16)+CONFIGCS4, R0  ; load settings
        ST              R0, @R1                 ; set registers
        LDI             #0x668, R1              ; area wait register awr4
        LDI             #WAITREG4, R2           ; wait settings
        STH             R2, @R1                 ; set register
#endif
;=========================================================================================
; 7.7.8  Set CS5  
;=========================================================================================
#if CS5
        LDI             #0x0654, R1             ; area select reg ASR5, ACR5      
        LDI             #(AREASEL5<<16)+CONFIGCS5, R0  ; load settings
        ST              R0, @R1                 ; set registers
        LDI             #0x66A, R1              ; area wait register awr5
        LDI             #WAITREG5, R2           ; wait settings
        STH             R2, @R1                 ; set register
#endif
;=========================================================================================
; 7.7.9  Set CS6
;=========================================================================================
#if (CS6)  
        LDI             #0x0658, R1             ; area select reg ASR6, ACR6      
        LDI             #(AREASEL6<<16)+CONFIGCS6, R0  ; load settings
        ST              R0, @R1                 ; set registers
        LDI             #0x66C, R1              ; area wait register awr6
        LDI             #WAITREG6, R2           ; wait settings
        STH             R2, @R1                 ; set register
#endif
;=========================================================================================
; 7.7.10  Set CS7  
;=========================================================================================
#if CS7
        LDI             #0x065C, R1             ; area select reg ASR7, ACR7     
        LDI             #(AREASEL7<<16)+CONFIGCS7, R0  ; load settings
        ST              R0, @R1                 ; set registers
        LDI             #0x66E, R1              ; area wait register awr7
        LDI             #WAITREG7, R2           ; wait settings
        STH             R2, @R1                 ; set register
#endif             
;=========================================================================================
; 7.7.11  Set special SDRAM config register  
;=========================================================================================
#if (SDRAM)
        LDI             #0x670, R1              ; SDRAM memory config register
        LDI             #MEMCON, R2             ; wait settings
        STB             R2, @R1                 ; set register
#endif

;=========================================================================================
; 7.7.12  set Port Function Register
;=========================================================================================
;=========================================================================================
; 7.7.12.1  set PFR00 Register. External bus mode (D[24-31]) or General purpose port
;=========================================================================================
        LDI             #0x0D80, R1             ; Port Function Register 0, (PFR00)
        LDI             #PFUNC0, R0             ; load port settings 
        STB             R0, @R1                 ; set register    
;=========================================================================================
; 7.7.12.2  set PFR01 Register. External bus mode (D[16-23]) or General purpose port
;=========================================================================================
        LDI             #0x0D81, R1             ; Port Function Register 1, (PFR01)
        LDI             #PFUNC1, R0             ; load port settings 
        STB             R0, @R1                 ; set register 
;=========================================================================================
; 7.7.12.3  set PFR02 Register. External bus mode (D[8-15]) or General purpose port
;=========================================================================================
        LDI             #0x0D82, R1             ; Port Function Register 2, (PFR02)
        LDI             #PFUNC2, R0             ; load port settings 
        STB             R0, @R1                 ; set register 
;=========================================================================================
; 7.7.12.4  set PFR03 Register. External bus mode (D[0-7]) or General purpose port
;=========================================================================================
        LDI             #0x0D83, R1             ; Port Function Register 3, (PFR03)
        LDI             #PFUNC3, R0             ; load port settings 
        STB             R0, @R1                 ; set register 
;=========================================================================================
; 7.7.12.5  set PFR04 Register. External bus mode (Adr[24-31]) or General purpose port
;=========================================================================================
        LDI             #0x0D84, R1             ; Port Function Register 4, (PFR04)
        LDI             #PFUNC4, R0             ; load port settings 
        STB             R0, @R1                 ; set register 
;=========================================================================================
; 7.7.12.6  set PFR05 Register. External bus mode (Adr[16-23]) or General purpose port
;=========================================================================================
        LDI             #0x0D85, R1             ; Port Function Register 5, (PFR05)
        LDI             #PFUNC5, R0             ; load port settings 
        STB             R0, @R1                 ; set register 
;=========================================================================================
; 7.7.12.7  set PFR06 Register. External bus mode (Adr[8-15]) or General purpose port
;=========================================================================================
        LDI             #0x0D86, R1             ; Port Function Register 6, (PFR06)
        LDI             #PFUNC6, R0             ; load port settings 
        STB             R0, @R1                 ; set register 
;=========================================================================================
; 7.7.12.8  set PFR07 Register. External bus mode (Adr[0-7]) or General purpose port
;=========================================================================================
        LDI             #0x0D87, R1             ; Port Function Register 7, (PFR07)
        LDI             #PFUNC7, R0             ; load port settings 
        STB             R0, @R1                 ; set register 
;=========================================================================================
; 7.7.12.9  set PFR08 Register. External bus mode (Control Signals) or GIO port
;=========================================================================================
        LDI             #0x0D88, R1             ; Port Function Register 8, (PFR08)
        LDI             #PFUNC8, R0             ; load port settings 
        STB             R0, @R1                 ; set register 
;=========================================================================================
; 7.7.12.10  set PFR09 Register. External bus mode (Control Signals) or GIO port
;=========================================================================================
        LDI             #0x0D89, R1             ; Port Function Register 9, (PFR09)
        LDI             #PFUNC9, R0             ; load port settings 
        STB             R0, @R1                 ; set register 
;=========================================================================================
; 7.7.12.11  set PFR10 Register. External bus mode (Control Signals) or GIO port
;=========================================================================================
        LDI             #0x0D8A, R1             ; Port Function Register 10, (PFR10)
        LDI             #PFUNC10, R0            ; load port settings 
        STB             R0, @R1                 ; set register 
;=========================================================================================
; 7.7.12.12  set EPFR10 Register. External bus mode (Control Signals) or GIO port
;=========================================================================================
        LDI             #0x0DCA, R1             ; Extended PFR 10, (EPFR10)
        LDI             #EPFUNC10, R0           ; load port settings 
        STB             R0, @R1                 ; set register 
;=========================================================================================
; 7.7.13  Set TCR Register
;=========================================================================================
        LDI             #0x0683, R1             ; Pin/Timing Control Register TCR
        LDI             #TIMECONTR, R0          ; load timing settings 
        STB             R0, @R1                 ; set register
;=========================================================================================
; 7.7.14  Enable CACHE for selected CS
;=========================================================================================
        LDI             #0x0681, R3             ; chip select enable register CSER
        LDI             #CHEENA, R2 
        ORB             R2, @R3      
;=========================================================================================
; 7.7.15 set SDRAM  Referesh Control Register
;=========================================================================================
#if (SDRAM)
        LDI             #0x0684, R1             ; Refresh Control Register RCR
        LDI             #REFRESH, R0            ; load refresh settings 
        STH             R0, @R1                 ; set register    
        LDI             #0x0008, R2
        OR              R2, R0                  ; Set PON bit to 1     
        STH             R0, @R1                 ; set register 
#endif
;=========================================================================================
; 7.7.16  Enable used CS
;=========================================================================================
        LDI             #0x0680, R3             ; chip select enable register CSER
        LDI             #ENACSX, R2 
; Start restriction; Flashless device
#if (DEVICE == MB91461R)
; End restriction
emu_sram_cs_mb91461r:    
        ANDB            R2, @R3                 ; set register
#else    
        ORB             R2, @R3
#endif   
;=========================================================================================
; 7.7.17  I-cache on/off
;=========================================================================================
; Start restriction; No cache
#if (DEVICE == MB91461R) || (DEVICE == MB91469G) || (DEVICE == others)         
; End restriction
    #if CACHE
        #if CACHE_SIZE  == C1024
        LDI             #0x03C7, R1             ; Cache size register ISIZE
        LDI             #0x00, R2
        STB             R2, @R1
        LDI             #0x03E7, R1             ; Cache control reg   ICHCR
        LDI             #0x07, R2               ; Release entry locks, flush and enable 
        STB             R2, @R1                 ; cache  
        #elif CACHE_SIZE  == C2048
        LDI             #0x03C7, R1             ; Cache size register ISIZE
        LDI             #0x01, R2
        STB             R2, @R1
        LDI             #0x03E7, R1             ; Cache control reg   ICHCR
        LDI             #0x07, R2               ; Release entry locks, flush and enable 
        STB             R2, @R1                 ; cache
        #elif CACHE_SIZE  == C4096
        LDI             #0x03C7, R1             ; Cache size register ISIZE
        LDI             #0x02, R2
        STB             R2, @R1
        LDI             #0x03E7, R1             ; Cache control reg   ICHCR
        LDI             #0x07, R2               ; Release entry locks, flush and enable 
        STB             R2, @R1                 ; cache
        #else    
        #error: Wrong Cache size selected!
        #endif          
     #else
        LDI             #0x03E7, R1             ; Cache control reg   ICHCR
        LDI             #0x06, R2               ; Release entry locks, flush and disable
        STB             R2, @R1                 ; cache
    #endif
#endif
#elif (EXTBUS == OFF) 
;=========================================================================================
; 7.7.18  set Port Function Register to general as I/O-Port
;=========================================================================================
;=========================================================================================
; 7.7.18.1  set PFR00 Register. External bus mode as General purpose port
;=========================================================================================
        LDI             #0x0D80, R1             ; Port Function Register 0, (PFR00)
        LDI             #0x00, R0               ; load port settings 
        STB             R0, @R1                 ; set register    
;=========================================================================================
; 7.7.18.2  set PFR01 Register. External bus mode as General purpose port
;=========================================================================================
        LDI             #0x0D81, R1             ; Port Function Register 1, (PFR01)
        LDI             #0x00, R0               ; load port settings 
        STB             R0, @R1                 ; set register 
;=========================================================================================
; 7.7.18.3  set PFR02 Register. External bus mode as General purpose port
;=========================================================================================
        LDI             #0x0D82, R1             ; Port Function Register 2, (PFR02)
        LDI             #0x00, R0               ; load port settings 
        STB             R0, @R1                 ; set register 
;=========================================================================================
; 7.7.18.4  set PFR03 Register. External bus mode as General purpose port
;=========================================================================================
        LDI             #0x0D83, R1             ; Port Function Register 3, (PFR03)
        LDI             #0x00, R0               ; load port settings 
        STB             R0, @R1                 ; set register 
;=========================================================================================
; 7.7.18.5  set PFR04 Register. External bus mode as General purpose port
;=========================================================================================
        LDI             #0x0D84, R1             ; Port Function Register 4, (PFR04)
        LDI             #0x00, R0               ; load port settings 
        STB             R0, @R1                 ; set register 
;=========================================================================================
; 7.7.18.6  set PFR05 Register. External bus mode as General purpose port
;=========================================================================================
        LDI             #0x0D85, R1             ; Port Function Register 5, (PFR05)
        LDI             #0x00, R0               ; load port settings 
        STB             R0, @R1                 ; set register 
;=========================================================================================
; 7.7.18.7  set PFR06 Register. External bus mode as General purpose port
;=========================================================================================
        LDI             #0x0D86, R1             ; Port Function Register 6, (PFR06)
        LDI             #0x00, R0               ; load port settings 
        STB             R0, @R1                 ; set register 
;=========================================================================================
; 7.7.18.8  set PFR07 Register. External bus mode as General purpose port
;=========================================================================================
        LDI             #0x0D87, R1             ; Port Function Register 7, (PFR07)
        LDI             #0x00, R0               ; load port settings 
        STB             R0, @R1                 ; set register 
;=========================================================================================
; 7.7.18.9  set PFR08 Register. External bus mode as General purpose port
;=========================================================================================
        LDI             #0x0D88, R1             ; Port Function Register 8, (PFR08)
        LDI             #0x00, R0               ; load port settings 
        STB             R0, @R1                 ; set register 
;=========================================================================================
; 7.7.18.10  set PFR09 Register. External bus mode as General purpose port
;=========================================================================================
        LDI             #0x0D89, R1             ; Port Function Register 9, (PFR09)
        LDI             #0x00, R0               ; load port settings 
        STB             R0, @R1                 ; set register 
;=========================================================================================
; 7.7.18.11  set PFR10 Register. External bus mode as General purpose port
;=========================================================================================
        LDI             #0x0D8A, R1             ; Port Function Register 10, (PFR10)
        LDI             #0x00, R0               ; load port settings 
        STB             R0, @R1                 ; set register 
;=========================================================================================
; 7.7.18.12  set EPFR10 Register. External bus mode as General purpose port
;=========================================================================================
        LDI             #0x0DCA, R1             ; Extended PFR10, (EPFR10)
        LDI             #0x00, R0               ; load port settings 
        STB             R0, @R1                 ; set register 
;=========================================================================================

#elif (EXTBUS == DEFAULT)
        NOP
smd_cs_mb91461r:
emu_sram_cs_mb91461r:
smd_cs:
#endif                                          ; #endif (EXTBUS)
#endif                                          ; #endif (excl. devices)
        ClearRCwatchdog

;=========================================================================================
; 7.8  Copy code from Flash to I-RAM 
;=========================================================================================
#if I_RAM == ON
        LDI             #_RAM_IRAM, R0
        LDI             #_ROM_IRAM, R1
        LDI             #sizeof(IRAM), R13
        CMP             #0, R13
        BEQ             copy_iram_end
copy_iram1: 
        ADD             #-1, R13
        LDUB            @(R13, R1), R12
        BNE:D           copy_iram1
        STB             R12, @(R13, R0)
copy_iram_end: 
        ClearRCwatchdog
#endif

;=========================================================================================
; 7.9  Fill stacks
;=========================================================================================
#if STACK_FILL == ON
        LDI             #STACK_PATTERN, R0
        LDI             #SSTACK, R1
        LDI             #sizeof(SSTACK), R2
        CMP             #0, R2
        BEQ:D           fill_sstack_end
        MOV             R2, R13
        LDI             #3, R12
        AND             R2, R12
        BEQ:D           fill_sstack2
        MOV             R2, R3
        SUB             R12, R3
        LDI             #0x3, R4
        SUB             R12, R4
        LSL             #0x3, R4 
        LDI             #STACK_PATTERN, R5
        LSR             R4, R5 
        LDI             #0x8, R4
fill_sstack1:
        ADD             #-1, R13
        LSR             R4, R5 
        CMP             R3, R13
        BHI:D           fill_sstack1
        STB             R5, @(R13, R1)
        CMP             #0, R3
        BEQ:D           fill_sstack_end
fill_sstack2:
        ADD             #-4, R13
        BGT:D           fill_sstack2
        ST              R0, @(R13, R1)
fill_sstack_end:

        LDI             #STACK_PATTERN, R0
        LDI             #USTACK, R1
        LDI             #sizeof(USTACK), R2
        CMP             #0, R2
        BEQ:D           fill_ustack_end
        MOV             R2, R13
        LDI             #3, R12
        AND             R2, R12
        BEQ:D           fill_ustack2
        MOV             R2, R3
        SUB             R12, R3
        LDI             #0x3, R4
        SUB             R12, R4
        LSL             #0x3, R4 
        LDI             #STACK_PATTERN, R5
        LSR             R4, R5 
        LDI             #0x8, R4
fill_ustack1:
        ADD             #-1, R13
        LSR             R4, R5 
        CMP             R3, R13
        BHI:D           fill_ustack1
        STB             R5, @(R13, R1)
        CMP             #0, R3
        BEQ:D           fill_ustack_end
fill_ustack2:
        ADD             #-4, R13
        BGT:D           fill_ustack2
        ST              R0, @(R13, R1)
fill_ustack_end:
        ClearRCwatchdog
#endif 

;=========================================================================================
; Standard C startup
;=========================================================================================
;=========================================================================================
; 7.10  Clear data 
;=========================================================================================
; clear DATA section
; According to ANSI, the DATA section must be cleared during start-up
        LDI:8           #0, R0
        LDI             #sizeof DATA &~0x3, R1
        LDI             #DATA, R13
        CMP             #0, R1
        BEQ             data_clr1
data_clr0:
        ADD2            #-4, R1
        BNE:D           data_clr0
        ST              R0, @(R13, R1)
data_clr1:
        LDI:8           #sizeof DATA & 0x3, R1
        LDI             #DATA + (sizeof DATA & ~0x3), R13

        CMP             #0, R1
        BEQ             data_clr_end
data_clr2:
        ADD2            #-1, R1
        BNE:D           data_clr2
        STB             R0, @(R13, R1)
data_clr_end:
        ClearRCwatchdog
        
;=========================================================================================
; 7.11  Copy Init section from ROM to RAM
;=========================================================================================
; copy rom
; All initialised data's (e.g. int i=1) must be stored in ROM/FLASH area. 
; (start value)
; The Application must copy the Section (Init) into the RAM area.
        LDI             #_RAM_INIT, R0
        LDI             #_ROM_INIT, R1
        LDI             #sizeof(INIT), R2
        CMP             #0, R2
        BEQ:D           copy_rom_end
        LDI             #3, R12
        AND             R2, R12
        BEQ:D           copy_rom2
        MOV             R2, R13
        MOV             R2, R3
        SUB             R12, R3
copy_rom1:
        ADD             #-1, R13
        LDUB            @(R13, R1), R12
        CMP             R3, R13
        BHI:D           copy_rom1
        STB             R12, @(R13, R0)
        CMP             #0, R3
        BEQ:D           copy_rom_end
copy_rom2:
        ADD             #-4, R13
        LD              @(R13, R1), R12
        BGT:D           copy_rom2
        ST              R12, @(R13, R0)
copy_rom_end:
        ClearRCwatchdog

;=========================================================================================
; 7.12 C library initialization
;=========================================================================================
#if CLIBINIT == ON
       CALL32          __stream_init, r12         ; initialise library 
#endif
;=========================================================================================
; 7.13  call C++ constructors
;=========================================================================================
#if CPLUSPLUS == ON
       LDI              #___call_dtors, r4
       CALL32           _atexit, r12

       LDI              #EXT_CTOR_DTOR, r8
       LDI              #EXT_CTOR_DTOR + sizeof(EXT_CTOR_DTOR), r9
       CMP              r9, r8
       BEQ              L1
L0:
       LD               @r8, r10
       CALL:D           @r10
       ADD              #4, r8
       CMP              r9, r8
       BC               L0
L1:
#endif

start_main:
;=========================================================================================
; 7.14  call main routine
;=========================================================================================
       ClearRCwatchdog                            ; clear harware watchdog
       LDI:8            #0, r4                    ; Set the 1st parameter for main to 0.
       CALL32:d         _main, r12
       LDI:8            #0, r5                    ; Set the 2nd parameter for main to 0.
#if CLIBINIT == ON
       CALL32           _exit, r12
       __exit:
#endif

#if CPLUSPLUS == ON
       __abort:
#endif

;=========================================================================================
; 7.15  Return from main function
;=========================================================================================
end: 
        BRA            end  
        .end            __start
        
