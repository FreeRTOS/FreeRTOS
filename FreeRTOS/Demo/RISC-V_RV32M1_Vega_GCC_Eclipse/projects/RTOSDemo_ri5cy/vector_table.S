/* ------------------------------------------------------------------------- */
/*  @file:    startup_RV32M1_ri5cy.s                                         */
/*  @purpose: RI5CY Core Device Startup File                                 */
/*            RV32M1_ri5cy                                                   */
/*  @version: 1.0                                                            */
/*  @date:    2018-10-2                                                      */
/*  @build:   b180926                                                        */
/* ------------------------------------------------------------------------- */
/*                                                                           */
/* Copyright 1997-2016 Freescale Semiconductor, Inc.                         */
/* Copyright 2016-2018 NXP                                                   */
/* All rights reserved.                                                      */
/*                                                                           */
/* SPDX-License-Identifier: BSD-3-Clause                                     */


// Copyright 2017 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

.extern freertos_risc_v_trap_handler

.text
.section .vectors, "ax"
.option norvc
.global freertos_vector_table
freertos_vector_table:
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler
    jal x0, freertos_risc_v_trap_handler

    // reset vector
    jal x0, Reset_Handler

    // Illegal instrution exception
    jal x0, IllegalInstruction_Handler

    // ecall handler
    jal x0, freertos_risc_v_trap_handler

    // LSU error
    jal x0, LSU_Handler
