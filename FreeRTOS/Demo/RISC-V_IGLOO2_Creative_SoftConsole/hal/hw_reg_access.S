/***************************************************************************//**
 * (c) Copyright 2007-2018 Microsemi SoC Products Group. All rights reserved.
 *
 * Hardware registers access functions.
 * The implementation of these function is platform and toolchain specific.
 * The functions declared here are implemented using assembler as part of the
 * processor/toolchain specific HAL.
 *
 * SVN $Revision: 9661 $
 * SVN $Date: 2018-01-15 16:13:33 +0530 (Mon, 15 Jan 2018) $
 */

.section .text
    .globl HW_set_32bit_reg
    .globl HW_get_32bit_reg
    .globl HW_set_32bit_reg_field
    .globl HW_get_32bit_reg_field
    .globl HW_set_16bit_reg
    .globl HW_get_16bit_reg
    .globl HW_set_16bit_reg_field
    .globl HW_get_16bit_reg_field
    .globl HW_set_8bit_reg
    .globl HW_get_8bit_reg
    .globl HW_set_8bit_reg_field
    .globl HW_get_8bit_reg_field


/***************************************************************************//**
 * HW_set_32bit_reg is used to write the content of a 32 bits wide peripheral
 * register.
 *
 * a0:   addr_t reg_addr
 * a1:   uint32_t value
 */
HW_set_32bit_reg:
    sw a1, 0(a0)
    ret

/***************************************************************************//**
 * HW_get_32bit_reg is used to read the content of a 32 bits wide peripheral
 * register.
 *
 * R0:   addr_t reg_addr
 * @return          32 bits value read from the peripheral register.
 */
HW_get_32bit_reg:
    lw a0, 0(a0)
    ret

/***************************************************************************//**
 * HW_set_32bit_reg_field is used to set the content of a field in a 32 bits
 * wide peripheral register.
 *
 * a0:   addr_t reg_addr
 * a1:   int_fast8_t shift
 * a2:   uint32_t mask
 * a3:   uint32_t value
 */
HW_set_32bit_reg_field:
    mv t3, a3
    sll t3, t3, a1
    and  t3, t3, a2
    lw t1, 0(a0)
    mv t2, a2
    not t2, t2
    and t1, t1, t2
    or t1, t1, t3
    sw t1, 0(a0)
    ret

/***************************************************************************//**
 * HW_get_32bit_reg_field is used to read the content of a field out of a
 * 32 bits wide peripheral register.
 *
 * a0:   addr_t reg_addr
 * a1:   int_fast8_t shift
 * a2:   uint32_t mask
 *
 * @return          32 bits value containing the register field value specified
 *                  as parameter.
 */
HW_get_32bit_reg_field:
    lw a0, 0(a0)
    and a0, a0, a2
    srl a0, a0, a1
    ret

/***************************************************************************//**
 * HW_set_16bit_reg is used to write the content of a 16 bits wide peripheral
 * register.
 *
 * a0:   addr_t reg_addr
 * a1:   uint_fast16_t value
 */
HW_set_16bit_reg:
    sh a1, 0(a0)
    ret

/***************************************************************************//**
 * HW_get_16bit_reg is used to read the content of a 16 bits wide peripheral
 * register.
 *
 * a0:   addr_t reg_addr
 * @return          16 bits value read from the peripheral register.
 */
HW_get_16bit_reg:
    lh a0, (a0)
    ret

/***************************************************************************//**
 * HW_set_16bit_reg_field is used to set the content of a field in a 16 bits
 * wide peripheral register.
 *
 * a0:   addr_t reg_addr
 * a1:   int_fast8_t shift
 * a2:   uint_fast16_t mask
 * a3:   uint_fast16_t value
 * @param value     Value to be written in the specified field.
 */
HW_set_16bit_reg_field:
    mv t3, a3
    sll t3, t3, a1
    and  t3, t3, a2
    lh t1, 0(a0)
    mv t2, a2
    not t2, t2
    and t1, t1, t2
    or t1, t1, t3
    sh t1, 0(a0)
    ret

/***************************************************************************//**
 * HW_get_16bit_reg_field is used to read the content of a field from a
 * 16 bits wide peripheral register.
 *
 * a0:   addr_t reg_addr
 * a1:   int_fast8_t shift
 * a2:   uint_fast16_t mask
 *
 * @return          16 bits value containing the register field value specified
 *                  as parameter.
 */
HW_get_16bit_reg_field:
    lh a0, 0(a0)
    and a0, a0, a2
    srl a0, a0, a1
    ret

/***************************************************************************//**
 * HW_set_8bit_reg is used to write the content of a 8 bits wide peripheral
 * register.
 *
 * a0:   addr_t reg_addr
 * a1:   uint_fast8_t value
 */
HW_set_8bit_reg:
    sb a1, 0(a0)
    ret

/***************************************************************************//**
 * HW_get_8bit_reg is used to read the content of a 8 bits wide peripheral
 * register.
 *
 * a0:   addr_t reg_addr
 * @return          8 bits value read from the peripheral register.
 */
HW_get_8bit_reg:
    lb a0, 0(a0)
    ret

/***************************************************************************//**
 * HW_set_8bit_reg_field is used to set the content of a field in a 8 bits
 * wide peripheral register.
 *
 * a0:   addr_t reg_addr,
 * a1:   int_fast8_t shift
 * a2:   uint_fast8_t mask
 * a3:   uint_fast8_t value
 */
HW_set_8bit_reg_field:
    mv t3, a3
    sll t3, t3, a1
    and  t3, t3, a2
    lb t1, 0(a0)
    mv t2, a2
    not t2, t2
    and t1, t1, t2
    or t1, t1, t3
    sb t1, 0(a0)
    ret

/***************************************************************************//**
 * HW_get_8bit_reg_field is used to read the content of a field from a
 * 8 bits wide peripheral register.
 *
 * a0:   addr_t reg_addr
 * a1:   int_fast8_t shift
 * a2:   uint_fast8_t mask
 *
 * @return          8 bits value containing the register field value specified
 *                  as parameter.
 */
HW_get_8bit_reg_field:
    lb a0, 0(a0)
    and a0, a0, a2
    srl a0, a0, a1
    ret

.end
