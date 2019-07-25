/****************************************************************************//**
 * @file     startup_M2351.S
 * @version  V1.00
 * @brief    CMSIS Device Startup File
 *
 * @copyright (C) 2018 Nuvoton Technology Corp. All rights reserved.
 *****************************************************************************/



    .syntax unified
    .arch   armv8 - m.base
    
    .section .stack
    .align  3
#ifndef Stack_Size
    .equ    Stack_Size, 0x00000800
#endif
    .global __StackTop
    .global __StackLimit
__StackLimit:
    .space  Stack_Size
    .size   __StackLimit, . - __StackLimit
__StackTop:
    .size   __StackTop, . - __StackTop
    
    .section .heap
    .align  3
#ifndef Heap_Size
    .equ    Heap_Size, 0x00000100
#endif
    
    .global __HeapBase
    .global __HeapLimit
__HeapBase:
    .if Heap_Size
    .space  Heap_Size
    .endif
    .size   __HeapBase, . - __HeapBase
__HeapLimit:
    .size   __HeapLimit, . - __HeapLimit
    
    .section .vectors
    .align  2
    .global __Vectors
__Vectors:
    .long   __StackTop            /* Top of Stack */
    .long   Reset_Handler         /* Reset Handler */
    .long   NMI_Handler           /* NMI Handler */
    .long   HardFault_Handler     /* Hard Fault Handler */
    .long   0                     /* Reserved */
    .long   0                     /* Reserved */
    .long   0                     /* Reserved */
    .long   0                     /* Reserved */
    .long   0                     /* Reserved */
    .long   0                     /* Reserved */
    .long   0                     /* Reserved */
    .long   SVC_Handler           /* SVCall Handler */
    .long   0                     /* Reserved */
    .long   0                     /* Reserved */
    .long   PendSV_Handler        /* PendSV Handler */
    .long   SysTick_Handler       /* SysTick Handler */
    
    /* External interrupts */
    .long   BOD_IRQHandler        /* 0   */
    .long   IRC_IRQHandler        /* 1   */
    .long   PWRWU_IRQHandler      /* 2   */
    .long   SRAM_IRQHandler       /* 3   */
    .long   CLKFAIL_IRQHandler    /* 4   */
    .long   Default_Handler    /* 5   */
    .long   RTC_IRQHandler        /* 6   */
    .long   TAMPER_IRQHandler     /* 7   */
    .long   WDT_IRQHandler        /* 8   */
    .long   WWDT_IRQHandler       /* 9   */
    .long   EINT0_IRQHandler      /* 10  */
    .long   EINT1_IRQHandler      /* 11  */
    .long   EINT2_IRQHandler      /* 12  */
    .long   EINT3_IRQHandler      /* 13  */
    .long   EINT4_IRQHandler      /* 14  */
    .long   EINT5_IRQHandler      /* 15  */
    .long   GPA_IRQHandler        /* 16  */
    .long   GPB_IRQHandler        /* 17  */
    .long   GPC_IRQHandler        /* 18  */
    .long   GPD_IRQHandler        /* 19  */
    .long   GPE_IRQHandler        /* 20  */
    .long   GPF_IRQHandler        /* 21  */
    .long   QSPI0_IRQHandler      /* 22  */
    .long   SPI0_IRQHandler       /* 23  */
    .long   BRAKE0_IRQHandler     /* 24  */
    .long   EPWM0_P0_IRQHandler   /* 25  */
    .long   EPWM0_P1_IRQHandler   /* 26  */
    .long   EPWM0_P2_IRQHandler   /* 27  */
    .long   BRAKE1_IRQHandler     /* 28  */
    .long   EPWM1_P0_IRQHandler   /* 29  */
    .long   EPWM1_P1_IRQHandler   /* 30  */
    .long   EPWM1_P2_IRQHandler   /* 31  */
    .long   TMR0_IRQHandler       /* 32  */
    .long   TMR1_IRQHandler       /* 33  */
    .long   TMR2_IRQHandler       /* 34  */
    .long   TMR3_IRQHandler       /* 35  */
    .long   UART0_IRQHandler      /* 36  */
    .long   UART1_IRQHandler      /* 37  */
    .long   I2C0_IRQHandler       /* 38  */
    .long   I2C1_IRQHandler       /* 39  */
    .long   PDMA0_IRQHandler      /* 40  */
    .long   DAC_IRQHandler        /* 41  */
    .long   EADC0_IRQHandler      /* 42  */
    .long   EADC1_IRQHandler      /* 43  */
    .long   ACMP01_IRQHandler     /* 44  */
    .long   Default_Handler    /* 45  */
    .long   EADC2_IRQHandler      /* 46  */
    .long   EADC3_IRQHandler      /* 47  */
    .long   UART2_IRQHandler      /* 48  */
    .long   UART3_IRQHandler      /* 49  */
    .long   Default_Handler    /* 50  */
    .long   SPI1_IRQHandler       /* 51  */
    .long   SPI2_IRQHandler       /* 52  */
    .long   USBD_IRQHandler       /* 53  */
    .long   USBH_IRQHandler       /* 54  */
    .long   USBOTG_IRQHandler     /* 55  */
    .long   CAN0_IRQHandler       /* 56  */
    .long   Default_Handler    /* 57  */
    .long   SC0_IRQHandler        /* 58  */
    .long   SC1_IRQHandler        /* 59  */
    .long   SC2_IRQHandler        /* 60  */
    .long   Default_Handler    /* 61  */
    .long   SPI3_IRQHandler       /* 62  */
    .long   Default_Handler    /* 63  */
    .long   SDH0_IRQHandler       /* 64  */
    .long   Default_Handler    /* 65  */
    .long   Default_Handler    /* 66  */
    .long   Default_Handler    /* 67  */
    .long   I2S0_IRQHandler       /* 68  */
    .long   Default_Handler    /* 69  */
    .long   OPA0_IRQHandler       /* 70  */
    .long   CRPT_IRQHandler       /* 71  */
    .long   GPG_IRQHandler        /* 72  */
    .long   EINT6_IRQHandler      /* 73  */
    .long   UART4_IRQHandler      /* 74  */
    .long   UART5_IRQHandler      /* 75  */
    .long   USCI0_IRQHandler      /* 76  */
    .long   USCI1_IRQHandler      /* 77  */
    .long   BPWM0_IRQHandler      /* 78  */
    .long   BPWM1_IRQHandler      /* 79  */
    .long   Default_Handler    /* 80  */
    .long   Default_Handler    /* 81  */
    .long   I2C2_IRQHandler       /* 82  */
    .long   Default_Handler    /* 83  */
    .long   QEI0_IRQHandler       /* 84  */
    .long   QEI1_IRQHandler       /* 85  */
    .long   ECAP0_IRQHandler      /* 86  */
    .long   ECAP1_IRQHandler      /* 87  */
    .long   GPH_IRQHandler        /* 88  */
    .long   EINT7_IRQHandler      /* 89  */
    .long   Default_Handler    /* 90  */
    .long   Default_Handler    /* 91  */
    .long   Default_Handler    /* 92  */
    .long   Default_Handler    /* 93  */
    .long   Default_Handler    /* 94  */
    .long   Default_Handler    /* 95  */
    .long   Default_Handler    /* 96  */
    .long   Default_Handler    /* 97  */
    .long   PDMA1_IRQHandler      /* 98  */
    .long   SCU_IRQHandler        /* 99  */
    .long   Default_Handler    /* 100 */
    .long   TRNG_IRQHandler       /* 101 */
    
    
    .size   __Vectors, . - __Vectors
    
    
    
    .text
    .thumb
    .thumb_func
    .align  2
    .global Reset_Handler
    .type   Reset_Handler, % function
    
    
Reset_Handler:
    /*  Firstly it copies data from read only memory to RAM. There are two schemes
     *  to copy. One can copy more than one sections. Another can only copy
     *  one section.  The former scheme needs more instructions and read-only
     *  data to implement than the latter.
     *  Macro __STARTUP_COPY_MULTIPLE is used to choose between two schemes.  */
    
#ifdef __STARTUP_COPY_MULTIPLE
    /*  Multiple sections scheme.
     *
     *  Between symbol address __copy_table_start__ and __copy_table_end__,
     *  there are array of triplets, each of which specify:
     *    offset 0: LMA of start of a section to copy from
     *    offset 4: VMA of start of a section to copy to
     *    offset 8: size of the section to copy. Must be multiply of 4
     *
     *  All addresses must be aligned to 4 bytes boundary.
     */
    ldr r4, = __copy_table_start__
    ldr r5, = __copy_table_end__
    
.L_loop0:
    cmp r4, r5
    bge .L_loop0_done
    ldr r1, [r4]
    ldr r2, [r4, #4]
    ldr r3, [r4, #8]
    
.L_loop0_0:
    subs    r3, #4
    blt .L_loop0_0_done
    ldr r0, [r1, r3]
    str r0, [r2, r3]
    b   .L_loop0_0
    
.L_loop0_0_done:
    adds    r4, #12
    b   .L_loop0
    
.L_loop0_done:
#else
    /*  Single section scheme.
     *
     *  The ranges of copy from/to are specified by following symbols
     *    __etext: LMA of start of the section to copy from. Usually end of text
     *    __data_start__: VMA of start of the section to copy to
     *    __data_end__: VMA of end of the section to copy to
     *
     *  All addresses must be aligned to 4 bytes boundary.
     */
    ldr r1, = __etext
    ldr r2, = __data_start__
    ldr r3, = __data_end__
    
    subs    r3, r2
    ble .L_loop1_done
    
.L_loop1:
    subs    r3, #4
    ldr r0, [r1, r3]
    str r0, [r2, r3]
    bgt .L_loop1
    
.L_loop1_done:
#endif /*__STARTUP_COPY_MULTIPLE */
    
    /*  This part of work usually is done in C library startup code. Otherwise,
     *  define this macro to enable it in this startup.
     *
     *  There are two schemes too. One can clear multiple BSS sections. Another
     *  can only clear one section. The former is more size expensive than the
     *  latter.
     *
     *  Define macro __STARTUP_CLEAR_BSS_MULTIPLE to choose the former.
     *  Otherwise efine macro __STARTUP_CLEAR_BSS to choose the later.
     */
#ifdef __STARTUP_CLEAR_BSS_MULTIPLE
    /*  Multiple sections scheme.
     *
     *  Between symbol address __copy_table_start__ and __copy_table_end__,
     *  there are array of tuples specifying:
     *    offset 0: Start of a BSS section
     *    offset 4: Size of this BSS section. Must be multiply of 4
     */
    ldr r3, = __zero_table_start__
    ldr r4, = __zero_table_end__
    
.L_loop2:
    cmp r3, r4
    bge .L_loop2_done
    ldr r1, [r3]
    ldr r2, [r3, #4]
    movs    r0, 0
    
.L_loop2_0:
    subs    r2, #4
    blt .L_loop2_0_done
    str r0, [r1, r2]
    b   .L_loop2_0
.L_loop2_0_done:
    
    adds    r3, #8
    b   .L_loop2
.L_loop2_done:

#elif defined (__STARTUP_CLEAR_BSS)
    /*  Single BSS section scheme.
     *
     *  The BSS section is specified by following symbols
     *    __bss_start__: start of the BSS section.
     *    __bss_end__: end of the BSS section.
     *
     *  Both addresses must be aligned to 4 bytes boundary.
     */
    ldr r1, = __bss_start__
    ldr r2, = __bss_end__

    movs    r0, 0

    subs    r2, r1
    ble .L_loop3_done

.L_loop3:
    subs    r2, #4
    str r0, [r1, r2]
    bgt .L_loop3
.L_loop3_done:
#endif /* __STARTUP_CLEAR_BSS_MULTIPLE || __STARTUP_CLEAR_BSS */
    
    
    
#ifndef __NO_SYSTEM_INIT
    bl  SystemInit
#endif
    
    
#ifndef __START
#define __START _start
#endif
    bl  __START
    
    .pool
    .size   Reset_Handler, . - Reset_Handler
    
    .align  1
    .thumb_func
    .weak   Default_Handler
    .type   Default_Handler, % function
    
Default_Handler:
    b   .
    .size   Default_Handler, . - Default_Handler
    
    /*    Macro to define default handlers. Default handler
     *    will be weak symbol and just dead loops. They can be
     *    overwritten by other handlers */
     
    .macro  def_irq_handler handler_name
    .weak   \handler_name
    .set    \handler_name, Default_Handler
    .endm
    
    def_irq_handler NMI_Handler
    def_irq_handler HardFault_Handler
    def_irq_handler SVC_Handler
    def_irq_handler PendSV_Handler
    def_irq_handler SysTick_Handler
    
    def_irq_handler BOD_IRQHandler
    def_irq_handler IRC_IRQHandler
    def_irq_handler PWRWU_IRQHandler
    def_irq_handler SRAM_IRQHandler
    def_irq_handler CLKFAIL_IRQHandler
    
    def_irq_handler RTC_IRQHandler
    def_irq_handler TAMPER_IRQHandler
    def_irq_handler WDT_IRQHandler
    def_irq_handler WWDT_IRQHandler
    def_irq_handler EINT0_IRQHandler
    def_irq_handler EINT1_IRQHandler
    def_irq_handler EINT2_IRQHandler
    def_irq_handler EINT3_IRQHandler
    def_irq_handler EINT4_IRQHandler
    def_irq_handler EINT5_IRQHandler
    def_irq_handler GPA_IRQHandler
    def_irq_handler GPB_IRQHandler
    def_irq_handler GPC_IRQHandler
    def_irq_handler GPD_IRQHandler
    def_irq_handler GPE_IRQHandler
    def_irq_handler GPF_IRQHandler
    def_irq_handler QSPI0_IRQHandler
    def_irq_handler SPI0_IRQHandler
    def_irq_handler BRAKE0_IRQHandler
    def_irq_handler EPWM0_P0_IRQHandler
    def_irq_handler EPWM0_P1_IRQHandler
    def_irq_handler EPWM0_P2_IRQHandler
    def_irq_handler BRAKE1_IRQHandler
    def_irq_handler EPWM1_P0_IRQHandler
    def_irq_handler EPWM1_P1_IRQHandler
    def_irq_handler EPWM1_P2_IRQHandler
    def_irq_handler TMR0_IRQHandler
    def_irq_handler TMR1_IRQHandler
    def_irq_handler TMR2_IRQHandler
    def_irq_handler TMR3_IRQHandler
    def_irq_handler UART0_IRQHandler
    def_irq_handler UART1_IRQHandler
    def_irq_handler I2C0_IRQHandler
    def_irq_handler I2C1_IRQHandler
    def_irq_handler PDMA0_IRQHandler
    def_irq_handler DAC_IRQHandler
    def_irq_handler EADC0_IRQHandler
    def_irq_handler EADC1_IRQHandler
    def_irq_handler ACMP01_IRQHandler
    
    def_irq_handler EADC2_IRQHandler
    def_irq_handler EADC3_IRQHandler
    def_irq_handler UART2_IRQHandler
    def_irq_handler UART3_IRQHandler
    
    def_irq_handler SPI1_IRQHandler
    def_irq_handler SPI2_IRQHandler
    def_irq_handler USBD_IRQHandler
    def_irq_handler USBH_IRQHandler
    def_irq_handler USBOTG_IRQHandler
    def_irq_handler CAN0_IRQHandler
    
    def_irq_handler SC0_IRQHandler
    def_irq_handler SC1_IRQHandler
    def_irq_handler SC2_IRQHandler
    
    def_irq_handler SPI3_IRQHandler
    
    def_irq_handler SDH0_IRQHandler
    
    
    
    def_irq_handler I2S0_IRQHandler
    
    def_irq_handler OPA0_IRQHandler
    def_irq_handler CRPT_IRQHandler
    def_irq_handler GPG_IRQHandler
    def_irq_handler EINT6_IRQHandler
    def_irq_handler UART4_IRQHandler
    def_irq_handler UART5_IRQHandler
    def_irq_handler USCI0_IRQHandler
    def_irq_handler USCI1_IRQHandler
    def_irq_handler BPWM0_IRQHandler
    def_irq_handler BPWM1_IRQHandler
    
    
    def_irq_handler I2C2_IRQHandler
    
    def_irq_handler QEI0_IRQHandler
    def_irq_handler QEI1_IRQHandler
    def_irq_handler ECAP0_IRQHandler
    def_irq_handler ECAP1_IRQHandler
    def_irq_handler GPH_IRQHandler
    def_irq_handler EINT7_IRQHandler
    
    
    
    
    
    


    def_irq_handler PDMA1_IRQHandler
    def_irq_handler SCU_IRQHandler
    
    def_irq_handler TRNG_IRQHandler
    
    
    
    /* ;int32_t SH_DoCommand(int32_t n32In_R0, int32_t n32In_R1, int32_t *pn32Out_R0) */
    .align 2
    .thumb_func
    .type SH_DoCommand, % function
    
SH_DoCommand:
    
    BKPT   0xAB                /* ; Wait ICE or HardFault */
    LDR    R3, = SH_Return
    MOV    R4, lr
    BLX    R3                  /* ; Call SH_Return. The return value is in R0 */
    BX     R4                  /* ; Return value = R0 */
    .size  SH_DoCommand, . - SH_DoCommand
    
    .align  2
    .thumb_func
    .global __PC
    .type   __PC, % function
__PC:
    
    MOV     r0, lr
    BLX     lr
    .size   __PC, . - __PC
    
    
    .end
