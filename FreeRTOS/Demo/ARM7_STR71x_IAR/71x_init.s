;******************** (C) COPYRIGHT 2003 STMicroelectronics ********************
;* File Name          : 71x_init.s
;* Author             : MCD Application Team
;* Date First Issued  : 06/23/2004
;* Description        : This is the first code executed after RESET.
;*                      This code used to initialize system stacks
;*                      and critical peripherals before entering the C code.
;*******************************************************************************
;* History:
;*  13/01/2006 : V3.1
;*  24/05/2005 : V3.0
;*  30/11/2004 : V2.0
;*  14/07/2004 : V1.3
;*  01/01/2004 : V1.2
;*******************************************************************************
; THE PRESENT SOFTWARE WHICH IS FOR GUIDANCE ONLY AIMS AT PROVIDING CUSTOMERS WITH
; CODING INFORMATION REGARDING THEIR PRODUCTS IN ORDER FOR THEM TO SAVE TIME.
; AS A RESULT, STMICROELECTRONICS SHALL NOT BE HELD LIABLE FOR ANY DIRECT, INDIRECT
; OR CONSEQUENTIAL DAMAGES WITH RESPECT TO ANY CLAIMS ARISING FROM THE CONTENT
; OF SUCH SOFTWARE AND/OR THE USE MADE BY CUSTOMERS OF THE CODING INFORMATION
; CONTAINED HEREIN IN CONNECTION WITH THEIR PRODUCTS.
;*******************************************************************************/


; --- Standard definitions of mode bits and interrupt (I & F) flags in PSRs

Mode_USR           EQU   0x10
Mode_FIQ           EQU   0x11
Mode_IRQ           EQU   0x12
Mode_SVC           EQU   0x13
Mode_ABT           EQU   0x17
Mode_UNDEF         EQU   0x1B
Mode_SYS           EQU   0x1F ; available on ARM Arch 4 and later

I_Bit              EQU   0x80 ; when I bit is set, IRQ is disabled
F_Bit              EQU   0x40 ; when F bit is set, FIQ is disabled



EIC_Base_addr      EQU   0xFFFFF800; EIC base address
ICR_off_addr       EQU   0x00      ; Interrupt Control register offset
CIPR_off_addr      EQU   0x08      ; Current Interrupt Priority Register offset
IVR_off_addr       EQU   0x18      ; Interrupt Vector Register offset
FIR_off_addr       EQU   0x1C      ; Fast Interrupt Register offset
IER_off_addr       EQU   0x20      ; Interrupt Enable Register offset
IPR_off_addr       EQU   0x40      ; Interrupt Pending Bit Register offset
SIR0_off_addr      EQU   0x60      ; Source Interrupt Register 0

EMI_Base_addr      EQU   0x6C000000; EMI base address
BCON0_off_addr     EQU   0x00      ; Bank 0 configuration register offset
BCON1_off_addr     EQU   0x04      ; Bank 1 configuration register offset
BCON2_off_addr     EQU   0x08      ; Bank 2 configuration register offset
BCON3_off_addr     EQU   0x0C      ; Bank 3 configuration register offset

EMI_ENABLE         EQU   0x8000
EMI_SIZE_16        EQU   0x0001

GPIO2_Base_addr    EQU   0xE0005000; GPIO2 base address
PC0_off_addr       EQU   0x00      ; Port Configuration Register 0 offset
PC1_off_addr       EQU   0x04      ; Port Configuration Register 1 offset
PC2_off_addr       EQU   0x08      ; Port Configuration Register 2 offset
PD_off_addr        EQU   0x0C      ; Port Data Register offset

CPM_Base_addr      EQU   0xA0000040; CPM Base Address
BOOTCR_off_addr    EQU   0x10      ; CPM - Boot Configuration Register
FLASH_mask         EQU   0x0000    ; to remap FLASH at 0x0
RAM_mask           EQU   0x0002    ; to remap RAM at 0x0

;|----------------------------------------------------------------------------------|
;| - APB Bridge  (System Peripheral)                                               |
;|----------------------------------------------------------------------------------|
APB1_base_addr     EQU   0xC0000000          ; APB Bridge1 Base Address
APB2_base_addr     EQU   0xE0000000          ; APB Bridge2 Base Address
CKDIS_off_addr     EQU   0x10                ; APB Bridge1 - Clock Disable  Register
SWRES_off_addr     EQU   0x14                ; APB Bridge1 - Software Reset Register
CKDIS1_config_all  EQU   0x27FB              ; To enable/disable clock of all APB1's peripherals
SWRES1_config_all  EQU   0x27FB              ; To reset all APB1's peripherals
CKDIS2_config_all  EQU   0x7FDD              ; To enable/disable clock of all APB2's peripherals
SWRES2_config_all  EQU   0x7FDD              ; To reset all APB2's peripherals



;---------------------------------------------------------------
; ?program_start
;---------------------------------------------------------------
		MODULE	?program_start
                SECTION	IRQ_STACK:DATA:NOROOT(3)
		SECTION	FIQ_STACK:DATA:NOROOT(3)
		SECTION	UND_STACK:DATA:NOROOT(3)
		SECTION	ABT_STACK:DATA:NOROOT(3)	
		SECTION	SVC_STACK:DATA:NOROOT(3)
		SECTION	CSTACK:DATA:NOROOT(3)
		SECTION	.text:CODE(2)
		PUBLIC	__iar_program_start
		EXTERN	?main
		EXTERN	?main
                CODE32


;*******************************************************************************
;*******                         -- MACROS --                            *******
;*******************************************************************************
;*******************************************************************************
;* Macro Name     : EMI_INIT
;* Description    : This macro Initialize EMI bank 1: 16-bit 7 wait state
;* Input          : None.
;* Output         : None.
;*******************************************************************************
EMI_INIT  MACRO
        LDR     r0, =GPIO2_Base_addr      ; Configure P2.0 -> 3 in AF_PP mode
        LDR     r2, [r0, #PC0_off_addr]
        ORR     r2, r2,#0x0000000F
        STR     r2, [r0, #PC0_off_addr]
        LDR     r2, [r0, #PC1_off_addr]
        ORR     r2, r2,#0x0000000F
        STR     r2, [r0, #PC1_off_addr]
        LDR     r2, [r0, #PC2_off_addr]
        ORR     r2, r2,#0x0000000F
        STR     r2, [r0, #PC2_off_addr]
        LDR     r0, =EMI_Base_addr
        LDR     r1, =0x18|EMI_ENABLE|EMI_SIZE_16
        STR     r1, [r0, #BCON1_off_addr] ; Enable bank 1 16-bit 7 wait state
        ENDM
;*******************************************************************************
;* Macro Name     : EIC_INIT
;* Description    : This macro Initialize the EIC as following :
;                 - IRQ disabled
;                 - FIQ disabled
;                 - IVR contain the load PC opcode (0xE59FFXXX)
;                 - Current priority level equal to 0
;                 - All channels are disabled
;                 - All channels priority equal to 0
;                 - All SIR registers contain offset to the related IRQ
;                   table entry
;* Input          : None.
;* Output         : None.
;*******************************************************************************
EIC_INIT   MACRO

        LDR     r3, =EIC_Base_addr
        LDR     r4, =0xE59F0000
        STR     r4, [r3, #IVR_off_addr]; Write the LDR pc,[pc,#offset]
                                       ; instruction code in IVR[31:16]
        LDR     r2, =32                ; 32 Channel to initialize
        LDR     r0, =T0TIMI_Addr       ; Read the address of the IRQs
                                       ; address table
        LDR     r1, =0x00000FFF
        AND     r0,r0,r1
        LDR     r5, =SIR0_off_addr     ; Read SIR0 address
        SUB     r4,r0,#8               ; subtract 8 for prefetch
        LDR     r1, =0xF7E8            ; Add the offset from IVR to 0x00000000
                                       ; address(IVR address + 7E8 = 0x00000000)
                                       ; 0xF7E8 used to complete the
                                       ; LDR pc,[pc,#offset] opcode (0xE59FFXXX)
        ADD     r1,r4,r1               ; Compute the jump offset from IVR to the
                                       ; IRQ table entry.
EIC_INI MOV     r4, r1, LSL #16        ; Left shift the result
        STR     r4, [r3, r5]           ; Store the result in SIRx register
        ADD     r1, r1, #4             ; Next IRQ address
        ADD     r5, r5, #4             ; Next SIR
        SUBS    r2, r2, #1             ; Decrement the number of SIR registers
                                       ; to initialize
        BNE     EIC_INI                ; If more then continue
        ENDM
;*******************************************************************************
;* Macro Name     : PERIPHERAL_INIT
;* Description    : This macro reset all device peripherals.
;* Input          : None.
;* Output         : None.
;*******************************************************************************
PERIPHERAL_INIT MACRO

        LDR     r1, =APB1_base_addr      ; r0= APB1 base address
        LDR     r2, =APB2_base_addr      ; r0= APB2 base address
        LDR     r0, =CKDIS1_config_all
        STRH    r0, [r1, #CKDIS_off_addr]; Clock Disabling for all APB1 peripherals
        LDR     r0, =CKDIS2_config_all
        STRH    r0, [r2, #CKDIS_off_addr]; Clock Disabling for all APB2 peripherals
        LDR     r0, =SWRES1_config_all
        STRH    r0, [r1, #SWRES_off_addr]; Keep all APB1 peripherals under reset
        LDR     r0, =SWRES2_config_all
        STRH    r0, [r2, #SWRES_off_addr]; Keep all APB2 peripherals under reset
        MOV     r7, #10                  ; Wait that the selected macrocells exit from reset
loop1   SUBS    r7, r7, #1
        BNE     loop1
        MOV     r0, #0
        STRH    r0, [r1, #SWRES_off_addr]; Enable all all APB1 peripherals
        STRH    r0, [r2, #SWRES_off_addr]; Enable all all APB2 peripherals
        STRH    r0, [r1, #CKDIS_off_addr]; Clock Enabling for all APB1 peripherals
        STRH    r0, [r2, #CKDIS_off_addr]; Clock Enabling for all APB2 peripherals
        MOV     r7, #10                  ; Wait that the selected macrocells exit from reset
loop2   SUBS    r7, r7, #1
        BNE     loop2
        ENDM
;********************************************************************************************

; define remapping
; If you need to remap memory before entring the main program
; uncomment next ligne
;            #define   remapping

; Then define which memory to remap to address 0x00000000
;  Uncomment next line if you want to remap RAM
;         #define  remap_ram

;  Uncomment next line if you want to remap FLASH
;         #define remap_flash


        IMPORT  T0TIMI_Addr
__iar_program_start
         LDR     pc, =NextInst
NextInst
		NOP		; Wait for OSC stabilization
		NOP
		NOP
		NOP
		NOP
		NOP
		NOP
		NOP
		NOP

        MSR     CPSR_c, #Mode_ABT|F_Bit|I_Bit
        ldr      sp,=SFE(ABT_STACK)     ; End of ABT_STACK

        MSR     CPSR_c, #Mode_UNDEF|F_Bit|I_Bit
        ldr      sp,=SFE(UND_STACK)     ; End of UNDEF_STACK

        MSR     CPSR_c, #Mode_SVC|F_Bit|I_Bit
       ldr      sp,=SFE(SVC_STACK)      ; End of SVC_STACK



; Uncomment next ligne if you need to reset all device pripherals
 ;      PERIPHERAL_INIT           ; Reset all device peripherals

; Uncomment next ligne if you need to enable the EMI Bank 1
   ;    EMI_INIT                  ; Initialize EIM Bank 1

;Uncomment next ligne if you need to initialize the EIC
        EIC_INIT                  ; Initialize EIC

;******************************************************************************
;REMAPPING
;Description  : Remapping  memory whether RAM,FLASH
;               at Address 0x0 after the application has started executing.
;               Remapping is generally done to allow RAM  to replace FLASH
;               at 0x0.
;               the remapping of RAM allow copying of vector table into RAM
;               To enable the memory remapping uncomment: (see above)
;               #define  remapping to enable memory remapping
;                  AND
;               #define  remap_ram to remap RAM
;                  OR
;               #define  remap_flash to remap FLASH
;******************************************************************************
#ifdef remapping
    #ifdef remap_flash
        MOV     r0, #FLASH_mask
    #endif
    #ifdef remap_ram
        MOV     r0, #RAM_mask
    #endif

        LDR     r1, =CPM_Base_addr
        LDRH    r2, [r1, #BOOTCR_off_addr]; Read BOOTCR Register
        BIC     r2, r2, #0x03             ; Reset the two LSB bits of BOOTCR
        ORR     r2, r2, r0                ; change the two LSB bits of BOOTCR
        STRH    r2, [r1, #BOOTCR_off_addr]; Write BOOTCR Register
#endif

       	MSR     CPSR_c, #Mode_FIQ|I_Bit; Change to FIQ mode
        ldr      sp,=SFE(FIQ_STACK)      ; End of FIQ_STACK

       	MSR     CPSR_c, #Mode_IRQ|I_Bit; Change to IRQ mode
        ldr      sp,=SFE(IRQ_STACK)    ; End of IRQ_STACK

        MSR     CPSR_c, #Mode_SYS         ; Change to system mode, Enable IRQ and FIQ
       ldr     sp,=SFE(CSTACK)        ; End of CSTACK(user)



; --- Now branches to a C lib function that copies RO data from their
;     load region to their execute region, create the RW and ZI regions
;     then jumps to user C main program.

		; main() must be called from Supervisor mode
		MSR     CPSR_c, #Mode_SVC|F_Bit|I_Bit

        b ?main   ; Note : use B not BL, because an application will
                         ; never return this way

        LTORG

        END
;******************* (C) COPYRIGHT 2003 STMicroelectronics *****END OF FILE****
