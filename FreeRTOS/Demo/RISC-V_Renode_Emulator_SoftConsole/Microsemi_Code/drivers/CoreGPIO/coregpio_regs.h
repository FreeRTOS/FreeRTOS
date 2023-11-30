/*******************************************************************************
 * (c) Copyright 2009-2015 Microsemi SoC Products Group. All rights reserved.
 * 
 * SVN $Revision: 7964 $
 * SVN $Date: 2015-10-09 18:26:53 +0530 (Fri, 09 Oct 2015) $
 */
#ifndef __CORE_GPIO_REGISTERS_H
#define __CORE_GPIO_REGISTERS_H		1

/*------------------------------------------------------------------------------
 * 
 */
#define IRQ_REG_OFFSET          0x80

#define IRQ0_REG_OFFSET         0x80
#define IRQ1_REG_OFFSET         0x84
#define IRQ2_REG_OFFSET         0x88
#define IRQ3_REG_OFFSET         0x8C

/*------------------------------------------------------------------------------
 * 
 */
#define GPIO_IN_REG_OFFSET      0x90

#define GPIO_IN0_REG_OFFSET     0x90
#define GPIO_IN1_REG_OFFSET     0x94
#define GPIO_IN2_REG_OFFSET     0x98
#define GPIO_IN3_REG_OFFSET     0x9C

/*------------------------------------------------------------------------------
 * 
 */
#define GPIO_OUT_REG_OFFSET     0xA0

#define GPIO_OUT0_REG_OFFSET    0xA0
#define GPIO_OUT1_REG_OFFSET    0xA4
#define GPIO_OUT2_REG_OFFSET    0xA8
#define GPIO_OUT3_REG_OFFSET    0xAC

#endif /* __CORE_GPIO_REGISTERS_H */
