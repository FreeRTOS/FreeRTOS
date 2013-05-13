/*******************************************************************************
 * (c) Copyright 2008-2013 Microsemi SoC Products Group. All rights reserved.
 * 
 * SVN $Revision: 5258 $
 * SVN $Date: 2013-03-21 12:41:02 +0000 (Thu, 21 Mar 2013) $
 */

    .text
    .global HW_set_32bit_reg
    .global HW_get_32bit_reg
    .global HW_set_32bit_reg_field
    .global HW_get_32bit_reg_field
    .global HW_set_16bit_reg
    .global HW_get_16bit_reg
    .global HW_set_16bit_reg_field
    .global HW_get_16bit_reg_field
    .global HW_set_8bit_reg
    .global HW_get_8bit_reg
    .global HW_set_8bit_reg_field
    .global HW_get_8bit_reg_field
    .code 16
    .syntax unified
    .type HW_set_32bit_reg, function
    .type HW_get_32bit_reg, function
    .type HW_set_32bit_reg_field, function
    .type HW_get_32bit_reg_field, function
    .type HW_set_16bit_reg, function
    .type HW_get_16bit_reg, function
    .type HW_set_16bit_reg_field, function
    .type HW_get_16bit_reg_field, function
    .type HW_set_8bit_reg, function
    .type HW_get_8bit_reg, function
    .type HW_set_8bit_reg_field, function
    .type HW_get_8bit_reg_field, function

/*------------------------------------------------------------------------------
 * R0:   addr_t reg_addr
 * R1:   uint32_t value
 */
HW_set_32bit_reg:
    STR R1, [R0]
    BX LR

/*------------------------------------------------------------------------------
 * R0:   addr_t reg_addr
 */      
HW_get_32bit_reg:
    LDR R0, [R0]
    BX LR

/*------------------------------------------------------------------------------
 * R0:   addr_t reg_addr
 * R1:   int_fast8_t shift
 * R2:   uint32_t mask
 * R3:   uint32_t value
 */
HW_set_32bit_reg_field:
    PUSH {R1,R2,R3,LR}
    LSL.W R3, R3, R1
    AND.W R3, R3, R2
    LDR R1, [R0]
    MVN.W R2, R2
    AND.W R1, R1, R2
    ORR.W R1, R1, R3
    STR R1, [R0]
    POP {R1,R2,R3,PC}

/*------------------------------------------------------------------------------
 * R0:   addr_t reg_addr
 * R1:   int_fast8_t shift
 * R2:   uint32_t mask
 */
HW_get_32bit_reg_field:
    LDR R0, [R0]
    AND.W R0, R0, R2
    LSR.W R0, R0, R1
    BX LR

/*------------------------------------------------------------------------------
 * R0:   addr_t reg_addr
 * R1:   uint_fast16_t value
 */
HW_set_16bit_reg:
    STRH R1, [R0]
    BX LR
        
/*------------------------------------------------------------------------------
 * R0:   addr_t reg_addr
 */
HW_get_16bit_reg:
    LDRH R0, [R0]
    BX LR

/*------------------------------------------------------------------------------
 * R0:   addr_t reg_addr
 * R1:   int_fast8_t shift
 * R2:   uint_fast16_t mask
 * R3:   uint_fast16_t value
 */
HW_set_16bit_reg_field:
    PUSH {R1,R2,R3,LR}
    LSL.W R3, R3, R1
    AND.W R3, R3, R2
    LDRH R1, [R0]
    MVN.W R2, R2
    AND.W R1, R1, R2
    ORR.W R1, R1, R3
    STRH R1, [R0]
    POP {R1,R2,R3,PC}

/*------------------------------------------------------------------------------
 * R0:   addr_t reg_addr
 * R1:   int_fast8_t shift
 * R2:   uint_fast16_t mask
 */
HW_get_16bit_reg_field:
    LDRH R0, [R0]
    AND.W R0, R0, R2
    LSR.W R0, R0, R1
    BX LR

/*------------------------------------------------------------------------------
 * R0:   addr_t reg_addr
 * R1:   uint_fast8_t value
 */
HW_set_8bit_reg:
    STRB R1, [R0]
    BX LR
        
/*------------------------------------------------------------------------------
 * R0:   addr_t reg_addr
 */
HW_get_8bit_reg:
    LDRB R0, [R0]
    BX LR

/*------------------------------------------------------------------------------
 * R0:   addr_t reg_addr,
 * R1:   int_fast8_t shift
 * R2:   uint_fast8_t mask
 * R3:   uint_fast8_t value
 */
HW_set_8bit_reg_field:
    PUSH {R1,R2,R3,LR}
    LSL.W R3, R3, R1
    AND.W R3, R3, R2
    LDRB R1, [R0]
    MVN.W R2, R2
    AND.W R1, R1, R2
    ORR.W R1, R1, R3
    STRB R1, [R0]
    POP {R1,R2,R3,PC}

/*------------------------------------------------------------------------------
 * R0:   addr_t reg_addr
 * R1:   int_fast8_t shift
 * R2:   uint_fast8_t mask
 */
HW_get_8bit_reg_field:
    LDRB R0, [R0]
    AND.W R0, R0, R2
    LSR.W R0, R0, R1
    BX LR

.end
