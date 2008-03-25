/*****************************************************************************
 * Copyright (c) 2001, 2002 Rowley Associates Limited.                       *
 *                                                                           *
 * This file may be distributed under the terms of the License Agreement     *
 * provided with this software.                                              *
 *                                                                           *
 * THIS FILE IS PROVIDED AS IS WITH NO WARRANTY OF ANY KIND, INCLUDING THE   *
 * WARRANTY OF DESIGN, MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE. *
 *****************************************************************************/
  .section .init, "ax"
  .code 32
  .align 0
                
  .weak _start
  .global __start
  .global __gccmain
  .extern main
  .extern exit

/*****************************************************************************
 * Function    : _start                                                      *
 * Description : Main entry point and startup code for C system.             *
 *****************************************************************************/
_start:
__start:                        
  mrs r0, cpsr
  bic r0, r0, #0x1F

  /* Setup stacks */ 
  orr r1, r0, #0x1B /* Undefined mode */
  msr cpsr_cxsf, r1
  ldr sp, =__stack_und_end__
  
  orr r1, r0, #0x17 /* Abort mode */
  msr cpsr_cxsf, r1
  ldr sp, =__stack_abt_end__

  orr r1, r0, #0x12 /* IRQ mode */
  msr cpsr_cxsf, r1
  ldr sp, =__stack_irq_end__

  orr r1, r0, #0x11 /* FIQ mode */
  msr cpsr_cxsf, r1
  ldr sp, =__stack_fiq_end__

  orr r1, r0, #0x13 /* Supervisor mode */
  msr cpsr_cxsf, r1
  ldr sp, =__stack_svc_end__
#ifdef SUPERVISOR_START
  /* Start application in supervisor mode */
  ldr r1, =__stack_end__ /* Setup user/system mode stack */ 
  mov r2, sp
  stmfd r2!, {r1}
  ldmfd r2, {sp}^
#else
  /* Start application in system mode */
  orr r1, r0, #0x1F /* System mode */
  msr cpsr_cxsf, r1
  ldr sp, =__stack_end__
#endif
  
  /* Copy from initialised data section to data section (if necessary). */
  ldr r0, =__data_load_start__
  ldr r1, =__data_start__
  cmp r0, r1
  beq copy_data_end
  
  ldr r2, =__data_end__
  subs r2, r2, r1
  beq copy_data_end
  
copy_data_loop:
  ldrb r3, [r0], #+1
  strb r3, [r1], #+1
  subs r2, r2, #1
  bne copy_data_loop
copy_data_end:  

  /* Copy from initialised text section to text section (if necessary). */
  ldr r0, =__text_load_start__
  ldr r1, =__text_start__
  cmp r0, r1
  beq copy_text_end
  
  ldr r2, =__text_end__
  subs r2, r2, r1
  beq copy_text_end
  
copy_text_loop:
  ldrb r3, [r0], #+1
  strb r3, [r1], #+1
  subs r2, r2, #1
  bne copy_text_loop
copy_text_end:  

  /* Copy from initialised fast_text section to fast_text section (if necessary). */
  ldr r0, =__fast_load_start__
  ldr r1, =__fast_start__
  cmp r0, r1
  beq copy_fast_end
  
  ldr r2, =__fast_end__
  subs r2, r2, r1
  beq copy_fast_end
  
copy_fast_loop:
  ldrb r3, [r0], #+1
  strb r3, [r1], #+1
  subs r2, r2, #1
  bne copy_fast_loop
copy_fast_end:  

  /* Zero the bss. */
  ldr r0, =__bss_start__
  ldr r1, =__bss_end__
  mov r2, #0
zero_bss_loop:
  cmp r0, r1
  beq zero_bss_end
  strb r2, [r0], #+1
  b zero_bss_loop
zero_bss_end:    

#ifdef CHECK  
  /* Check data */
  ldr r0, =__data_load_start__
  ldr r1, =__data_start__
  cmp r0, r1
  beq check_data_end
  ldr r2, =__data_end__
  subs r2, r2, r1
  beq check_data_end
  
check_data_loop:
  ldrb r3, [r0], #+1
  ldrb r4, [r1], #+1
  cmp r3, r4
  bne data_error_loop
  subs r2, r2, #1
  bne check_data_loop
check_data_end:  

  /* Check text */
  ldr r0, =__text_load_start__
  ldr r1, =__text_start__
  cmp r0, r1
  beq check_text_end
  ldr r2, =__text_end__
  subs r2, r2, r1
  beq check_text_end
  
check_text_loop:
  ldrb r3, [r0], #+1
  ldrb r4, [r1], #+1
  cmp r3, r4
  bne text_error_loop
  subs r2, r2, #1
  bne check_text_loop
check_text_end:  

  /* Check fast */
  ldr r0, =__fast_load_start__
  ldr r1, =__fast_start__
  cmp r0, r1
  beq check_fast_end
  ldr r2, =__fast_end__
  subs r2, r2, r1
  beq check_fast_end
  
check_fast_loop:
  ldrb r3, [r0], #+1
  ldrb r4, [r1], #+1
  cmp r3, r4
  bne fast_error_loop
  subs r2, r2, #1
  bne check_fast_loop
check_fast_end:  

  /* Check bss */
  ldr r0, =__bss_start__
  ldr r1, =__bss_end__
  mov r2, #0
check_bss_loop:
  cmp r0, r1
  beq check_bss_end
  ldrb r2, [r0], #+1
  cmp r2, #0
  bne bss_error_loop  
  b check_bss_loop
check_bss_end:    
#endif

  /* Initialise the heap */
  ldr r0, = __heap_start__
  ldr r1, = __heap_end__
  sub r1, r1, r0     /* r1 = r1-r0 */ 
  mov r2, #0
  str r2, [r0], #+4 /* *r0++ = 0 */
  str r1, [r0]      /* *r0 = __heap_end__ - __heap_start__ */

  /* Call constructors */
  ldr r0, =__ctors_start__
  ldr r1, =__ctors_end__
ctor_loop:
  cmp r0, r1
  beq ctor_end
  ldr r2, [r0], #+4
  stmfd sp!, {r0-r1}
  mov lr, pc
  mov pc, r2
  ldmfd sp!, {r0-r1}
  b ctor_loop
ctor_end:

  /* Setup initial call frame */
  mov lr, #4
  mov r12, sp
  stmfd sp!, {r11-r12, lr-pc}
  sub r11, r12, #0x00000004

start:
  /* Jump to main entry point */
  mov r0, #0
  mov r1, #0
  ldr r2, =main
  mov lr, pc
#ifdef __ARM_ARCH_3__
  mov pc, r2
#else    
  bx r2
#endif

  /* Call destructors */
  ldr r0, =__dtors_start__
  ldr r1, =__dtors_end__
dtor_loop:
  cmp r0, r1
  beq dtor_end
  ldr r2, [r0], #+4
  stmfd sp!, {r0-r1}
  mov lr, pc
  mov pc, r2
  ldmfd sp!, {r0-r1}
  b dtor_loop
dtor_end:

  /* Return from main, loop forever. */
exit_loop:
  b exit_loop

#ifdef CHECK
data_error_loop:
  b data_error_loop

text_error_loop:
  b text_error_loop
  
fast_error_loop:
  b fast_error_loop
  
bss_error_loop:
  b bss_error_loop  
#endif
  
                  
