#-------------------------------------------------------------------------------
# (c) Copyright 2007-2013 Microsemi SoC Products Group. All rights reserved.
# 
# Interrupt disabling/restoration for critical section protection.
#
# SVN $Revision: 5258 $
# SVN $Date: 2013-03-21 12:41:02 +0000 (Thu, 21 Mar 2013) $
#
    .text
    .global HAL_disable_interrupts
    .global HAL_restore_interrupts
    .code 16
    .syntax unified
    .type HAL_disable_interrupts, function
    .type HAL_restore_interrupts, function
#-------------------------------------------------------------------------------
# 
#
HAL_disable_interrupts:    
    mrs r0, PRIMASK
    cpsid I
    bx lr

#-------------------------------------------------------------------------------
#
#
HAL_restore_interrupts:    
    msr PRIMASK, r0
    bx lr

.end
