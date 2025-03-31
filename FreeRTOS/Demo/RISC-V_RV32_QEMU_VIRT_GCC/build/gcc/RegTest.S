/*
 * FreeRTOS V202212.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

    .extern ulRegTest1LoopCounter
    .extern ulRegTest2LoopCounter

    .global vRegTest1Implementation
    .global vRegTest2Implementation

/*-----------------------------------------------------------*/

/*
 * The register check tasks are described in the comments at the top of
 * main_full.c.
 */

.align( 8 )
vRegTest1Implementation:

    /* Fill the core registers with known values. */
    li x5, 0x5
    li x6, 0x6
    li x7, 0x7
    li x8, 0x8
    li x9, 0x9
    li x10, 0xa
    li x11, 0xb
    li x12, 0xc
    li x13, 0xd
    li x14, 0xe
#ifndef __riscv_32e
    li x16, 0x10
    li x17, 0x11
    li x18, 0x12
    li x19, 0x13
    li x20, 0x14
    li x21, 0x15
    li x22, 0x16
    li x23, 0x17
    li x24, 0x18
    li x25, 0x19
    li x26, 0x1a
    li x27, 0x1b
    li x28, 0x1c
    li x29, 0x1d
    li x30, 0x1e
    li x31, 0x1f
#endif
#if configENABLE_FPU == 1
    li x15, 0xC030000000000000 // -16
    fmv.d.x f0, x15
    li x15, 0xC02E000000000000 // -15
    fmv.d.x f1, x15
    li x15, 0xC02C000000000000 // -14
    fmv.d.x f2, x15
    li x15, 0xc02a000000000000 // -13
    fmv.d.x f3, x15
    li x15, 0xC028000000000000 // -12
    fmv.d.x f4, x15
    li x15, 0xC026000000000000 // -11
    fmv.d.x f5, x15
    li x15, 0xc024000000000000 // -10
    fmv.d.x f6, x15
    li x15, 0xc022000000000000 // -9
    fmv.d.x f7, x15
    li x15, 0xc020000000000000 // -8
    fmv.d.x f8, x15
    li x15, 0xc01c000000000000 // -7
    fmv.d.x f9, x15
    li x15, 0xc018000000000000 // -6
    fmv.d.x f10, x15
    li x15, 0xc014000000000000 // -5
    fmv.d.x f11, x15
    li x15, 0xc010000000000000 // -4
    fmv.d.x f12, x15
    li x15, 0xc008000000000000 // -3
    fmv.d.x f13, x15
    li x15, 0xc000000000000000 // -2
    fmv.d.x f14, x15
    li x15, 0xbff0000000000000 // -1
    fmv.d.x f15, x15
    li x15, 0                  // 0
    fmv.d.x f16, x15
    li x15, 0x3ff0000000000000 // 1
    fmv.d.x f17, x15
    li x15, 0x4000000000000000 // 2
    fmv.d.x f18, x15
    li x15, 0x4008000000000000 // 3
    fmv.d.x f19, x15
    li x15, 0x4010000000000000 // 4
    fmv.d.x f20, x15
    li x15, 0x4014000000000000 // 5
    fmv.d.x f21, x15
    li x15, 0x4018000000000000 // 6
    fmv.d.x f22, x15
    li x15, 0x401c000000000000 // 7
    fmv.d.x f23, x15
    li x15, 0x4020000000000000 // 8
    fmv.d.x f24, x15
    li x15, 0x4022000000000000 // 9
    fmv.d.x f25, x15
    li x15, 0x4024000000000000 // 10
    fmv.d.x f26, x15
    li x15, 0x4026000000000000 // 11
    fmv.d.x f27, x15
    li x15, 0x4028000000000000 // 12
    fmv.d.x f28, x15
    li x15, 0x402a000000000000 // 13
    fmv.d.x f29, x15
    li x15, 0x402C000000000000 // 14
    fmv.d.x f30, x15
#endif
#if configENABLE_VPU == 1
    /* Set the vector length to maximum available */
    li x15, -1
    vsetvli x0, x15, e8, m1, ta, ma  /* Use 64-bit elements, mask and tail agnostic */
    /* Initialize each vector register with different values */
    vid.v v0             // v0 = [0,1,2,3...]
    vadd.vi v1, v0, -15  // v1 = [-15, -14, -13, -12...]
    vadd.vi v2, v0, -14  // v2 = [-14, -13, -12, -11...]
    vadd.vi v3, v0, -13  // v3 = [-13, -12, -11, -10...]
    vadd.vi v4, v0, -12  // v4 = [-12, -11, -10, -9...]
    vadd.vi v5, v0, -11  // v5 = [-11, -10, -9, -8...]
    vadd.vi v6, v0, -10  // v6 = [-10, -9, -8, -7...]
    vadd.vi v7, v0, -9   // v7 = [-9, -8, -7, -6...]
    vadd.vi v8, v0, -8   // v8 = [-8, -7, -6, -5...]
    vadd.vi v9, v0, -7   // v9 = [-7, -6, -5, -4...]
    vadd.vi v10, v0, -6  // v10 = [-6, -5, -4, -3...]
    vadd.vi v11, v0, -5  // v11 = [-5, -4, -3, -2...]
    vadd.vi v12, v0, -4  // v12 = [-4, -3, -2, -1...]
    vadd.vi v13, v0, -3  // v13 = [-3, -2, -1, 0...]
    vadd.vi v14, v0, -2  // v14 = [-2, -1, 0, 1...]
    vadd.vi v15, v0, -1  // v15 = [-1, 0, 1, 2...]
    vadd.vi v16, v0, 1   // v16 = [1, 2, 3, 4...]
    vadd.vi v17, v0, 2   // v17 = [2, 3, 4, 5...]
    vadd.vi v18, v0, 3   // v18 = [3, 4, 5, 6...]
    vadd.vi v19, v0, 4   // v19 = [4, 5, 6, 7...]
    vadd.vi v20, v0, 5   // v20 = [5, 6, 7, 8...]
    vadd.vi v21, v0, 6   // v21 = [6, 7, 8, 9...]
    vadd.vi v22, v0, 7   // v22 = [7, 8, 9, 10...]
    vadd.vi v23, v0, 8   // v23 = [8, 9, 10, 11...]
    vadd.vi v24, v0, 9   // v24 = [9, 10, 11, 12...]
    vadd.vi v25, v0, 10  // v25 = [10, 11, 12, 13...]
    vadd.vi v26, v0, 11  // v26 = [11, 12, 13, 14...]
    vadd.vi v27, v0, 12  // v27 = [12, 13, 14, 15...]
    vadd.vi v28, v0, 13  // v28 = [13, 14, 15, 16...]
    vadd.vi v29, v0, 14  // v29 = [14, 15, 16, 17...]
    vadd.vi v30, v0, 15  // v30 = [15, 16, 17, 18...]
    vadd.vi v31, v0, 0   // v31 = [0,1,2,3...]
#endif

reg1_loop:

    /* Check each register still contains the expected known value.
    vRegTest1Implementation uses x15 as the temporary, vRegTest2Implementation
    uses x5 as the temporary. */
    li x15, 0x5
    bne x15, x5, reg1_error_loop
    li x15, 0x6
    bne x15, x6, reg1_error_loop
    li x15, 0x7
    bne x15, x7, reg1_error_loop
    li x15, 0x8
    bne x15, x8, reg1_error_loop
    li x15, 0x9
    bne x15, x9, reg1_error_loop
    li x15, 0xa
    bne x15, x10, reg1_error_loop
    li x15, 0xb
    bne x15, x11, reg1_error_loop
    li x15, 0xc
    bne x15, x12, reg1_error_loop
    li x15, 0xd
    bne x15, x13, reg1_error_loop
    li x15, 0xe
    bne x15, x14, reg1_error_loop
#ifndef __riscv_32e
    li x15, 0x10
    bne x15, x16, reg1_error_loop
    li x15, 0x11
    bne x15, x17, reg1_error_loop
    li x15, 0x12
    bne x15, x18, reg1_error_loop
    li x15, 0x13
    bne x15, x19, reg1_error_loop
    li x15, 0x14
    bne x15, x20, reg1_error_loop
    li x15, 0x15
    bne x15, x21, reg1_error_loop
    li x15, 0x16
    bne x15, x22, reg1_error_loop
    li x15, 0x17
    bne x15, x23, reg1_error_loop
    li x15, 0x18
    bne x15, x24, reg1_error_loop
    li x15, 0x19
    bne x15, x25, reg1_error_loop
    li x15, 0x1a
    bne x15, x26, reg1_error_loop
    li x15, 0x1b
    bne x15, x27, reg1_error_loop
    li x15, 0x1c
    bne x15, x28, reg1_error_loop
    li x15, 0x1d
    bne x15, x29, reg1_error_loop
    li x15, 0x1e
    bne x15, x30, reg1_error_loop
    li x15, 0x1f
    bne x15, x31, reg1_error_loop
#endif
#if configENABLE_FPU == 1
    li x15, 0xC030000000000000 // -16
    fmv.d.x f31, x15
    feq.d x15, f0, f31
    beqz x15, reg1_error_loop
    li x15, 0xC02E000000000000 // -15
    fmv.d.x f31, x15
    feq.d x15, f1, f31
    beqz x15, reg1_error_loop
    li x15, 0xC02C000000000000 // -14
    fmv.d.x f31, x15
    feq.d x15, f2, f31
    beqz x15, reg1_error_loop
    li x15, 0xc02a000000000000 // -13
    fmv.d.x f31, x15
    feq.d x15, f3, f31
    beqz x15, reg1_error_loop
    li x15, 0xC028000000000000 // -12
    fmv.d.x f31, x15
    feq.d x15, f4, f31
    beqz x15, reg1_error_loop
    li x15, 0xC026000000000000 // -11
    fmv.d.x f31, x15
    feq.d x15, f5, f31
    beqz x15, reg1_error_loop
    li x15, 0xc024000000000000 // -10
    fmv.d.x f31, x15
    feq.d x15, f6, f31
    beqz x15, reg1_error_loop
    li x15, 0xc022000000000000 // -9
    fmv.d.x f31, x15
    feq.d x15, f7, f31
    beqz x15, reg1_error_loop
    li x15, 0xc020000000000000 // -8
    fmv.d.x f31, x15
    feq.d x15, f8, f31
    beqz x15, reg1_error_loop
    li x15, 0xc01c000000000000 // -7
    fmv.d.x f31, x15
    feq.d x15, f9, f31
    beqz x15, reg1_error_loop
    li x15, 0xc018000000000000 // -6
    fmv.d.x f31, x15
    feq.d x15, f10, f31
    beqz x15, reg1_error_loop
    li x15, 0xc014000000000000 // -5
    fmv.d.x f31, x15
    feq.d x15, f11, f31
    beqz x15, reg1_error_loop
    li x15, 0xc010000000000000 // -4
    fmv.d.x f31, x15
    feq.d x15, f12, f31
    beqz x15, reg1_error_loop
    li x15, 0xc008000000000000 // -3
    fmv.d.x f31, x15
    feq.d x15, f13, f31
    beqz x15, reg1_error_loop
    li x15, 0xc000000000000000 // -2
    fmv.d.x f31, x15
    feq.d x15, f14, f31
    beqz x15, reg1_error_loop
    li x15, 0xbff0000000000000 // -1
    fmv.d.x f31, x15
    feq.d x15, f15, f31
    beqz x15, reg1_error_loop
    li x15, 0                  // 0
    fmv.d.x f31, x15
    feq.d x15, f16, f31
    beqz x15, reg1_error_loop
    li x15, 0x3ff0000000000000 // 1
    fmv.d.x f31, x15
    feq.d x15, f17, f31
    beqz x15, reg1_error_loop
    li x15, 0x4000000000000000 // 2
    fmv.d.x f31, x15
    feq.d x15, f18, f31
    beqz x15, reg1_error_loop
    li x15, 0x4008000000000000 // 3
    fmv.d.x f31, x15
    feq.d x15, f19, f31
    beqz x15, reg1_error_loop
    li x15, 0x4010000000000000 // 4
    fmv.d.x f31, x15
    feq.d x15, f20, f31
    beqz x15, reg1_error_loop
    li x15, 0x4014000000000000 // 5
    fmv.d.x f31, x15
    feq.d x15, f21, f31
    beqz x15, reg1_error_loop
    li x15, 0x4018000000000000 // 6
    fmv.d.x f31, x15
    feq.d x15, f22, f31
    beqz x15, reg1_error_loop
    li x15, 0x401c000000000000 // 7
    fmv.d.x f31, x15
    feq.d x15, f23, f31
    beqz x15, reg1_error_loop
    li x15, 0x4020000000000000 // 8
    fmv.d.x f31, x15
    feq.d x15, f24, f31
    beqz x15, reg1_error_loop
    li x15, 0x4022000000000000 // 9
    fmv.d.x f31, x15
    feq.d x15, f25, f31
    beqz x15, reg1_error_loop
    li x15, 0x4024000000000000 // 10
    fmv.d.x f31, x15
    feq.d x15, f26, f31
    beqz x15, reg1_error_loop
    li x15, 0x4026000000000000 // 11
    fmv.d.x f31, x15
    feq.d x15, f27, f31
    beqz x15, reg1_error_loop
    li x15, 0x4028000000000000 // 12
    fmv.d.x f31, x15
    feq.d x15, f28, f31
    beqz x15, reg1_error_loop
    li x15, 0x402a000000000000 // 13
    fmv.d.x f31, x15
    feq.d x15, f29, f31
    beqz x15, reg1_error_loop
    li x15, 0x402C000000000000 // 14
    fmv.d.x f31, x15
    feq.d x15, f30, f31
    beqz x15, reg1_error_loop
#endif
#if configENABLE_VPU == 1
    vid.v v0                // v0 = [0,1,2,3...]
    vadd.vi v0, v0, -15     // v0 = [-15, -14, -13, -12...]
    vsub.vv v0, v1, v0      // Compare v1 to the expected value, v0
    vredor.vs v0, v0, v0    // Reduce the mask to a single value, 0 if all elements were equal
    vmv.x.s x15, v0         // Move the result to a scalar register
    bnez x15, reg1_error_loop

    vid.v v0
    vadd.vi v0, v0, -14
    vsub.vv v0, v2, v0
    vredor.vs v0, v0, v0
    vmv.x.s x15, v0
    bnez x15, reg1_error_loop

    vid.v v0
    vadd.vi v0, v0, -13
    vsub.vv v0, v3, v0
    vredor.vs v0, v0, v0
    vmv.x.s x15, v0
    bnez x15, reg1_error_loop

    vid.v v0
    vadd.vi v0, v0, -12
    vsub.vv v0, v4, v0
    vredor.vs v0, v0, v0
    vmv.x.s x15, v0
    bnez x15, reg1_error_loop

    vid.v v0
    vadd.vi v0, v0, -11
    vsub.vv v0, v5, v0
    vredor.vs v0, v0, v0
    vmv.x.s x15, v0
    bnez x15, reg1_error_loop

    vid.v v0
    vadd.vi v0, v0, -10
    vsub.vv v0, v6, v0
    vredor.vs v0, v0, v0
    vmv.x.s x15, v0
    bnez x15, reg1_error_loop

    vid.v v0
    vadd.vi v0, v0, -9
    vsub.vv v0, v7, v0
    vredor.vs v0, v0, v0
    vmv.x.s x15, v0
    bnez x15, reg1_error_loop

    vid.v v0
    vadd.vi v0, v0, -8
    vsub.vv v0, v8, v0
    vredor.vs v0, v0, v0
    vmv.x.s x15, v0
    bnez x15, reg1_error_loop

    vid.v v0
    vadd.vi v0, v0, -7
    vsub.vv v0, v9, v0
    vredor.vs v0, v0, v0
    vmv.x.s x15, v0
    bnez x15, reg1_error_loop

    vid.v v0
    vadd.vi v0, v0, -6
    vsub.vv v0, v10, v0
    vredor.vs v0, v0, v0
    vmv.x.s x15, v0
    bnez x15, reg1_error_loop

    vid.v v0
    vadd.vi v0, v0, -5
    vsub.vv v0, v11, v0
    vredor.vs v0, v0, v0
    vmv.x.s x15, v0
    bnez x15, reg1_error_loop

    vid.v v0
    vadd.vi v0, v0, -4
    vsub.vv v0, v12, v0
    vredor.vs v0, v0, v0
    vmv.x.s x15, v0
    bnez x15, reg1_error_loop

    vid.v v0
    vadd.vi v0, v0, -3
    vsub.vv v0, v13, v0
    vredor.vs v0, v0, v0
    vmv.x.s x15, v0
    bnez x15, reg1_error_loop

    vid.v v0
    vadd.vi v0, v0, -2
    vsub.vv v0, v14, v0
    vredor.vs v0, v0, v0
    vmv.x.s x15, v0
    bnez x15, reg1_error_loop

    vid.v v0
    vadd.vi v0, v0, -1
    vsub.vv v0, v15, v0
    vredor.vs v0, v0, v0
    vmv.x.s x15, v0
    bnez x15, reg1_error_loop

    vid.v v0
    vadd.vi v0, v0, 1
    vsub.vv v0, v16, v0
    vredor.vs v0, v0, v0
    vmv.x.s x15, v0
    bnez x15, reg1_error_loop

    vid.v v0
    vadd.vi v0, v0, 2
    vsub.vv v0, v17, v0
    vredor.vs v0, v0, v0
    vmv.x.s x15, v0
    bnez x15, reg1_error_loop

    vid.v v0
    vadd.vi v0, v0, 3
    vsub.vv v0, v18, v0
    vredor.vs v0, v0, v0
    vmv.x.s x15, v0
    bnez x15, reg1_error_loop

    vid.v v0
    vadd.vi v0, v0, 4
    vsub.vv v0, v19, v0
    vredor.vs v0, v0, v0
    vmv.x.s x15, v0
    bnez x15, reg1_error_loop

    vid.v v0
    vadd.vi v0, v0, 5
    vsub.vv v0, v20, v0
    vredor.vs v0, v0, v0
    vmv.x.s x15, v0
    bnez x15, reg1_error_loop

    vid.v v0
    vadd.vi v0, v0, 6
    vsub.vv v0, v21, v0
    vredor.vs v0, v0, v0
    vmv.x.s x15, v0
    bnez x15, reg1_error_loop

    vid.v v0
    vadd.vi v0, v0, 7
    vsub.vv v0, v22, v0
    vredor.vs v0, v0, v0
    vmv.x.s x15, v0
    bnez x15, reg1_error_loop

    vid.v v0
    vadd.vi v0, v0, 8
    vsub.vv v0, v23, v0
    vredor.vs v0, v0, v0
    vmv.x.s x15, v0
    bnez x15, reg1_error_loop

    vid.v v0
    vadd.vi v0, v0, 9
    vsub.vv v0, v24, v0
    vredor.vs v0, v0, v0
    vmv.x.s x15, v0
    bnez x15, reg1_error_loop

    vid.v v0
    vadd.vi v0, v0, 10
    vsub.vv v0, v25, v0
    vredor.vs v0, v0, v0
    vmv.x.s x15, v0
    bnez x15, reg1_error_loop

    vid.v v0
    vadd.vi v0, v0, 11
    vsub.vv v0, v26, v0
    vredor.vs v0, v0, v0
    vmv.x.s x15, v0
    bnez x15, reg1_error_loop

    vid.v v0
    vadd.vi v0, v0, 12
    vsub.vv v0, v27, v0
    vredor.vs v0, v0, v0
    vmv.x.s x15, v0
    bnez x15, reg1_error_loop

    vid.v v0
    vadd.vi v0, v0, 13
    vsub.vv v0, v28, v0
    vredor.vs v0, v0, v0
    vmv.x.s x15, v0
    bnez x15, reg1_error_loop

    vid.v v0
    vadd.vi v0, v0, 14
    vsub.vv v0, v29, v0
    vredor.vs v0, v0, v0
    vmv.x.s x15, v0
    bnez x15, reg1_error_loop

    vid.v v0
    vadd.vi v0, v0, 15
    vsub.vv v0, v30, v0
    vredor.vs v0, v0, v0
    vmv.x.s x15, v0
    bnez x15, reg1_error_loop

    vid.v v0
    vadd.vi v0, v0, 0
    vsub.vv v0, v31, v0
    vredor.vs v0, v0, v0
    vmv.x.s x15, v0
    bnez x15, reg1_error_loop
#endif

    /* Everything passed, increment the loop counter. */
#if __riscv_xlen == 64
    ld x15, ulRegTest1LoopCounterConst
    ld x14, 0(x15)
    addi x14, x14, 1
    sd x14, 0(x15)
#else
    lw x15, ulRegTest1LoopCounterConst
    lw x14, 0(x15)
    addi x14, x14, 1
    sw x14, 0(x15)
#endif

    /* Restore clobbered register reading for next loop. */
    li x14, 0xe

    /* Yield to increase code coverage. */
    ecall

    /* Start again. */
    jal reg1_loop

reg1_error_loop:
    /* Busy loop which holds the task. */
    jal reg1_error_loop

.align( 8 )
ulRegTest1LoopCounterConst: .dword ulRegTest1LoopCounter

/*-----------------------------------------------------------*/

.align( 8 )
vRegTest2Implementation:

    /* Fill the core registers with known values. */
    li x6, 0x61
    li x7, 0x71
    li x8, 0x81
    li x9, 0x91
    li x10, 0xa1
    li x11, 0xb1
    li x12, 0xc1
    li x13, 0xd1
    li x14, 0xe1
    li x15, 0xf1
#ifndef __riscv_32e
    li x16, 0x20
    li x17, 0x21
    li x18, 0x22
    li x19, 0x23
    li x20, 0x24
    li x21, 0x25
    li x22, 0x26
    li x23, 0x27
    li x24, 0x28
    li x25, 0x29
    li x26, 0x2a
    li x27, 0x2b
    li x28, 0x2c
    li x29, 0x2d
    li x30, 0x2e
    li x31, 0x2f
#endif
#if configENABLE_FPU == 1
    li x5, 0x402E000000000000 // 15
    fmv.d.x f1, x5
    li x5, 0x402C000000000000 // 14
    fmv.d.x f2, x5
    li x5, 0x402a000000000000 // 13
    fmv.d.x f3, x5
    li x5, 0x4028000000000000 // 12
    fmv.d.x f4, x5
    li x5, 0x4026000000000000 // 11
    fmv.d.x f5, x5
    li x5, 0x4024000000000000 // 10
    fmv.d.x f6, x5
    li x5, 0x4022000000000000 // 9
    fmv.d.x f7, x5
    li x5, 0x4020000000000000 // 8
    fmv.d.x f8, x5
    li x5, 0x401c000000000000 // 7
    fmv.d.x f9, x5
    li x5, 0x4018000000000000 // 6
    fmv.d.x f10, x5
    li x5, 0x4014000000000000 // 5
    fmv.d.x f11, x5
    li x5, 0x4010000000000000 // 4
    fmv.d.x f12, x5
    li x5, 0x4008000000000000 // 3
    fmv.d.x f13, x5
    li x5, 0x4000000000000000 // 2
    fmv.d.x f14, x5
    li x5, 0x3ff0000000000000 // 1
    fmv.d.x f15, x5
    li x5, 0                  // 0
    fmv.d.x f16, x5
    li x5, 0xbff0000000000000 // -1
    fmv.d.x f17, x5
    li x5, 0xc000000000000000 // -2
    fmv.d.x f18, x5
    li x5, 0xc008000000000000 // -3
    fmv.d.x f19, x5
    li x5, 0xc010000000000000 // -4
    fmv.d.x f20, x5
    li x5, 0xc014000000000000 // -5
    fmv.d.x f21, x5
    li x5, 0xc018000000000000 // -6
    fmv.d.x f22, x5
    li x5, 0xc01c000000000000 // -7
    fmv.d.x f23, x5
    li x5, 0xc020000000000000 // -8
    fmv.d.x f24, x5
    li x5, 0xc022000000000000 // -9
    fmv.d.x f25, x5
    li x5, 0xc024000000000000 // -10
    fmv.d.x f26, x5
    li x5, 0xC026000000000000 // -11
    fmv.d.x f27, x5
    li x5, 0xC028000000000000 // -12
    fmv.d.x f28, x5
    li x5, 0xC02A000000000000 // -13
    fmv.d.x f29, x5
    li x5, 0xC02C000000000000 // -14
    fmv.d.x f30, x5
    li x5, 0xC02E000000000000 // -15
    fmv.d.x f31, x5
#endif
#if configENABLE_VPU == 1
    /* Set the vector length to maximum available */
    li x5, -1
    vsetvli x0, x5, e8, m1, ta, ma  /* Use 64-bit elements, mask and tail agnostic */
    /* Initialize each vector register with different values */
    vid.v v31             // v31 = [0,1,2,3...]
    vadd.vi v1, v31, 8    // v1 = [8, 9, 10, 11...]
    vadd.vi v2, v31, -8   // v2 = [-8, -7, -6, -5...]
    vadd.vi v3, v31, 7    // v3 = [7, 8, 9, 10...]
    vadd.vi v4, v31, -7   // v4 = [-7, -6, -5, -4...]
    vadd.vi v5, v31, 6    // v5 = [6, 7, 8, 9...]
    vadd.vi v6, v31, -6   // v6 = [-6, -5, -4, -3...]
    vadd.vi v7, v31, 5    // v7 = [5, 6, 7, 8...]
    vadd.vi v8, v31, -5   // v8 = [-5, -4, -3, -2...]
    vadd.vi v9, v31, 4    // v9 = [4, 5, 6, 7...]
    vadd.vi v10, v31, -4  // v10 = [-4, -3, -2, -1...]
    vadd.vi v11, v31, 3   // v11 = [3, 4, 5, 6...]
    vadd.vi v12, v31, -3  // v12 = [-3, -2, -1, 0...]
    vadd.vi v13, v31, 2   // v13 = [2, 3, 4, 5...]
    vadd.vi v14, v31, -2  // v14 = [-2, -1, 0, 1...]
    vadd.vi v15, v31, 1   // v15 = [1, 2, 3, 4...]
    vadd.vi v16, v31, -1  // v16 = [-1, 0, 1, 2...]
    vadd.vi v17, v31, 0   // v17 = [0,1,2,3...]
    vadd.vi v18, v31, 9   // v18 = [9, 10, 11, 12...]
    vadd.vi v19, v31, -9  // v19 = [-9, -8, -7, -6...]
    vadd.vi v20, v31, 10  // v20 = [10, 11, 12, 13...]
    vadd.vi v21, v31, -10 // v21 = [-10, -9, -8, -7...]
    vadd.vi v22, v31, 11  // v22 = [11, 12, 13, 14...]
    vadd.vi v23, v31, -11 // v23 = [-11, -10, -9, -8...]
    vadd.vi v24, v31, 12  // v24 = [12, 13, 14, 15...]
    vadd.vi v25, v31, -12 // v25 = [-12, -11, -10, -9...]
    vadd.vi v26, v31, 13  // v26 = [13, 14, 15, 16...]
    vadd.vi v27, v31, -13 // v27 = [-13, -12, -11, -10...]
    vadd.vi v28, v31, 14  // v28 = [14, 15, 16, 17...]
    vadd.vi v29, v31, -14 // v29 = [-14, -13, -12, -11...]
    vadd.vi v30, v31, -15 // v30 = [-15, -14, -13, -12...]
    vadd.vi v0, v31, 15   // v0 = [15, 16, 17, 18...]
#endif

Reg2_loop:

    /* Check each register still contains the expected known value.
    vRegTest2Implementation uses x5 as the temporary, vRegTest1Implementation
    uses x31 as the temporary. */
    li x5, 0x61
    bne x5, x6, reg2_error_loop
    li x5, 0x71
    bne x5, x7, reg2_error_loop
    li x5, 0x81
    bne x5, x8, reg2_error_loop
    li x5, 0x91
    bne x5, x9, reg2_error_loop
    li x5, 0xa1
    bne x5, x10, reg2_error_loop
    li x5, 0xb1
    bne x5, x11, reg2_error_loop
    li x5, 0xc1
    bne x5, x12, reg2_error_loop
    li x5, 0xd1
    bne x5, x13, reg2_error_loop
    li x5, 0xe1
    bne x5, x14, reg2_error_loop
    li x5, 0xf1
    bne x5, x15, reg2_error_loop
#ifndef __riscv_32e
    li x5, 0x20
    bne x5, x16, reg2_error_loop
    li x5, 0x21
    bne x5, x17, reg2_error_loop
    li x5, 0x22
    bne x5, x18, reg2_error_loop
    li x5, 0x23
    bne x5, x19, reg2_error_loop
    li x5, 0x24
    bne x5, x20, reg2_error_loop
    li x5, 0x25
    bne x5, x21, reg2_error_loop
    li x5, 0x26
    bne x5, x22, reg2_error_loop
    li x5, 0x27
    bne x5, x23, reg2_error_loop
    li x5, 0x28
    bne x5, x24, reg2_error_loop
    li x5, 0x29
    bne x5, x25, reg2_error_loop
    li x5, 0x2a
    bne x5, x26, reg2_error_loop
    li x5, 0x2b
    bne x5, x27, reg2_error_loop
    li x5, 0x2c
    bne x5, x28, reg2_error_loop
    li x5, 0x2d
    bne x5, x29, reg2_error_loop
    li x5, 0x2e
    bne x5, x30, reg2_error_loop
    li x5, 0x2f
    bne x5, x31, reg2_error_loop
#endif
#if configENABLE_FPU == 1
    li x5, 0x402E000000000000 // 15
    fmv.d.x f0, x5
    feq.d x5, f1, f0
    beqz x5, reg2_error_loop
    li x5, 0x402C000000000000 // 14
    fmv.d.x f0, x5
    feq.d x5, f2, f0
    beqz x5, reg2_error_loop
    li x5, 0x402a000000000000 // 13
    fmv.d.x f0, x5
    feq.d x5, f3, f0
    beqz x5, reg2_error_loop
    li x5, 0x4028000000000000 // 12
    fmv.d.x f0, x5
    feq.d x5, f4, f0
    beqz x5, reg2_error_loop
    li x5, 0x4026000000000000 // 11
    fmv.d.x f0, x5
    feq.d x5, f5, f0
    beqz x5, reg2_error_loop
    li x5, 0x4024000000000000 // 10
    fmv.d.x f0, x5
    feq.d x5, f6, f0
    beqz x5, reg2_error_loop
    li x5, 0x4022000000000000 // 9
    fmv.d.x f0, x5
    feq.d x5, f7, f0
    beqz x5, reg2_error_loop
    li x5, 0x4020000000000000 // 8
    fmv.d.x f0, x5
    feq.d x5, f8, f0
    beqz x5, reg2_error_loop
    li x5, 0x401c000000000000 // 7
    fmv.d.x f0, x5
    feq.d x5, f9, f0
    beqz x5, reg2_error_loop
    li x5, 0x4018000000000000 // 6
    fmv.d.x f0, x5
    feq.d x5, f10, f0
    beqz x5, reg2_error_loop
    li x5, 0x4014000000000000 // 5
    fmv.d.x f0, x5
    feq.d x5, f11, f0
    beqz x5, reg2_error_loop
    li x5, 0x4010000000000000 // 4
    fmv.d.x f0, x5
    feq.d x5, f12, f0
    beqz x5, reg2_error_loop
    li x5, 0x4008000000000000 // 3
    fmv.d.x f0, x5
    feq.d x5, f13, f0
    beqz x5, reg2_error_loop
    li x5, 0x4000000000000000 // 2
    fmv.d.x f0, x5
    feq.d x5, f14, f0
    beqz x5, reg2_error_loop
    li x5, 0x3ff0000000000000 // 1
    fmv.d.x f0, x5
    feq.d x5, f15, f0
    beqz x5, reg2_error_loop
    li x5, 0                  // 0
    fmv.d.x f0, x5
    feq.d x5, f16, f0
    beqz x5, reg2_error_loop
    li x5, 0xbff0000000000000 // -1
    fmv.d.x f0, x5
    feq.d x5, f17, f0
    beqz x5, reg2_error_loop
    li x5, 0xc000000000000000 // -2
    fmv.d.x f0, x5
    feq.d x5, f18, f0
    beqz x5, reg2_error_loop
    li x5, 0xc008000000000000 // -3
    fmv.d.x f0, x5
    feq.d x5, f19, f0
    beqz x5, reg2_error_loop
    li x5, 0xc010000000000000 // -4
    fmv.d.x f0, x5
    feq.d x5, f20, f0
    beqz x5, reg2_error_loop
    li x5, 0xc014000000000000 // -5
    fmv.d.x f0, x5
    feq.d x5, f21, f0
    beqz x5, reg2_error_loop
    li x5, 0xc018000000000000 // -6
    fmv.d.x f0, x5
    feq.d x5, f22, f0
    beqz x5, reg2_error_loop
    li x5, 0xc01c000000000000 // -7
    fmv.d.x f0, x5
    feq.d x5, f23, f0
    beqz x5, reg2_error_loop
    li x5, 0xc020000000000000 // -8
    fmv.d.x f0, x5
    feq.d x5, f24, f0
    beqz x5, reg2_error_loop
    li x5, 0xc022000000000000 // -9
    fmv.d.x f0, x5
    feq.d x5, f25, f0
    beqz x5, reg2_error_loop
    li x5, 0xc024000000000000 // -10
    fmv.d.x f0, x5
    feq.d x5, f26, f0
    beqz x5, reg2_error_loop
    li x5, 0xC026000000000000 // -11
    fmv.d.x f0, x5
    feq.d x5, f27, f0
    beqz x5, reg2_error_loop
    li x5, 0xC028000000000000 // -12
    fmv.d.x f0, x5
    feq.d x5, f28, f0
    beqz x5, reg2_error_loop
    li x5, 0xC02A000000000000 // -13
    fmv.d.x f0, x5
    feq.d x5, f29, f0
    beqz x5, reg2_error_loop
    li x5, 0xC02C000000000000 // -14
    fmv.d.x f0, x5
    feq.d x5, f30, f0
    beqz x5, reg2_error_loop
    li x5, 0xC02E000000000000 // -15
    fmv.d.x f0, x5
    feq.d x5, f31, f0
    beqz x5, reg2_error_loop
#endif
#if configENABLE_VPU == 1
    vid.v v31               // v31 = [0,1,2,3...]
    vadd.vi v31, v31, 8     // v31 = [-15, -14, -13, -12...]
    vsub.vv v31, v1, v31    // Compare v1 to the expected value, v31
    vredor.vs v31, v31, v31 // Reduce the mask to a single value, 0 if all elements were equal
    vmv.x.s x5, v31         // Move the result to a scalar register
    bnez x5, reg2_error_loop

    vid.v v31
    vadd.vi v31, v31, -8
    vsub.vv v31, v2, v31
    vredor.vs v31, v31, v31
    vmv.x.s x5, v31
    bnez x5, reg2_error_loop

    vid.v v31
    vadd.vi v31, v31, 7
    vsub.vv v31, v3, v31
    vredor.vs v31, v31, v31
    vmv.x.s x5, v31
    bnez x5, reg2_error_loop

    vid.v v31
    vadd.vi v31, v31, -7
    vsub.vv v31, v4, v31
    vredor.vs v31, v31, v31
    vmv.x.s x5, v31
    bnez x5, reg2_error_loop

    vid.v v31
    vadd.vi v31, v31, 6
    vsub.vv v31, v5, v31
    vredor.vs v31, v31, v31
    vmv.x.s x5, v31
    bnez x5, reg2_error_loop

    vid.v v31
    vadd.vi v31, v31, -6
    vsub.vv v31, v6, v31
    vredor.vs v31, v31, v31
    vmv.x.s x5, v31
    bnez x5, reg2_error_loop

    vid.v v31
    vadd.vi v31, v31, 5
    vsub.vv v31, v7, v31
    vredor.vs v31, v31, v31
    vmv.x.s x5, v31
    bnez x5, reg2_error_loop

    vid.v v31
    vadd.vi v31, v31, -5
    vsub.vv v31, v8, v31
    vredor.vs v31, v31, v31
    vmv.x.s x5, v31
    bnez x5, reg2_error_loop

    vid.v v31
    vadd.vi v31, v31, 4
    vsub.vv v31, v9, v31
    vredor.vs v31, v31, v31
    vmv.x.s x5, v31
    bnez x5, reg2_error_loop

    vid.v v31
    vadd.vi v31, v31, -4
    vsub.vv v31, v10, v31
    vredor.vs v31, v31, v31
    vmv.x.s x5, v31
    bnez x5, reg2_error_loop

    vid.v v31
    vadd.vi v31, v31, 3
    vsub.vv v31, v11, v31
    vredor.vs v31, v31, v31
    vmv.x.s x5, v31
    bnez x5, reg2_error_loop

    vid.v v31
    vadd.vi v31, v31, -3
    vsub.vv v31, v12, v31
    vredor.vs v31, v31, v31
    vmv.x.s x5, v31
    bnez x5, reg2_error_loop

    vid.v v31
    vadd.vi v31, v31, 2
    vsub.vv v31, v13, v31
    vredor.vs v31, v31, v31
    vmv.x.s x5, v31
    bnez x5, reg2_error_loop

    vid.v v31
    vadd.vi v31, v31, -2
    vsub.vv v31, v14, v31
    vredor.vs v31, v31, v31
    vmv.x.s x5, v31
    bnez x5, reg2_error_loop

    vid.v v31
    vadd.vi v31, v31, 1
    vsub.vv v31, v15, v31
    vredor.vs v31, v31, v31
    vmv.x.s x5, v31
    bnez x5, reg2_error_loop

    vid.v v31
    vadd.vi v31, v31, -1
    vsub.vv v31, v16, v31
    vredor.vs v31, v31, v31
    vmv.x.s x5, v31
    bnez x5, reg2_error_loop

    vid.v v31
    vadd.vi v31, v31, 0
    vsub.vv v31, v17, v31
    vredor.vs v31, v31, v31
    vmv.x.s x5, v31
    bnez x5, reg2_error_loop

    vid.v v31
    vadd.vi v31, v31, 9
    vsub.vv v31, v18, v31
    vredor.vs v31, v31, v31
    vmv.x.s x5, v31
    bnez x5, reg2_error_loop

    vid.v v31
    vadd.vi v31, v31, -9
    vsub.vv v31, v19, v31
    vredor.vs v31, v31, v31
    vmv.x.s x5, v31
    bnez x5, reg2_error_loop

    vid.v v31
    vadd.vi v31, v31, 10
    vsub.vv v31, v20, v31
    vredor.vs v31, v31, v31
    vmv.x.s x5, v31
    bnez x5, reg2_error_loop

    vid.v v31
    vadd.vi v31, v31, -10
    vsub.vv v31, v21, v31
    vredor.vs v31, v31, v31
    vmv.x.s x5, v31
    bnez x5, reg2_error_loop

    vid.v v31
    vadd.vi v31, v31, 11
    vsub.vv v31, v22, v31
    vredor.vs v31, v31, v31
    vmv.x.s x5, v31
    bnez x5, reg2_error_loop

    vid.v v31
    vadd.vi v31, v31, -11
    vsub.vv v31, v23, v31
    vredor.vs v31, v31, v31
    vmv.x.s x5, v31
    bnez x5, reg2_error_loop

    vid.v v31
    vadd.vi v31, v31, 12
    vsub.vv v31, v24, v31
    vredor.vs v31, v31, v31
    vmv.x.s x5, v31
    bnez x5, reg2_error_loop

    vid.v v31
    vadd.vi v31, v31, -12
    vsub.vv v31, v25, v31
    vredor.vs v31, v31, v31
    vmv.x.s x5, v31
    bnez x5, reg2_error_loop

    vid.v v31
    vadd.vi v31, v31, 13
    vsub.vv v31, v26, v31
    vredor.vs v31, v31, v31
    vmv.x.s x5, v31
    bnez x5, reg2_error_loop

    vid.v v31
    vadd.vi v31, v31, -13
    vsub.vv v31, v27, v31
    vredor.vs v31, v31, v31
    vmv.x.s x5, v31
    bnez x5, reg2_error_loop

    vid.v v31
    vadd.vi v31, v31, 14
    vsub.vv v31, v28, v31
    vredor.vs v31, v31, v31
    vmv.x.s x5, v31
    bnez x5, reg2_error_loop

    vid.v v31
    vadd.vi v31, v31, -14
    vsub.vv v31, v29, v31
    vredor.vs v31, v31, v31
    vmv.x.s x5, v31
    bnez x5, reg2_error_loop

    vid.v v31
    vadd.vi v31, v31, -15
    vsub.vv v31, v30, v31
    vredor.vs v31, v31, v31
    vmv.x.s x5, v31
    bnez x5, reg2_error_loop

    vid.v v31
    vadd.vi v31, v31, 15
    vsub.vv v31, v0, v31
    vredor.vs v31, v31, v31
    vmv.x.s x5, v31
    bnez x5, reg2_error_loop
#endif

    /* Everything passed, increment the loop counter. */
#if __riscv_xlen == 64
    ld x5, ulRegTest2LoopCounterConst
    ld x6, 0(x5)
    addi x6, x6, 1
    sd x6, 0(x5)
#else
    lw x5, ulRegTest2LoopCounterConst
    lw x6, 0(x5)
    addi x6, x6, 1
    sw x6, 0(x5)
#endif

    /* Restore clobbered register reading for next loop. */
    li x6, 0x61

    /* Start again. */
    jal Reg2_loop

reg2_error_loop:
    /* Busy loop which holds the task. */
    jal reg2_error_loop

.align( 8 )
ulRegTest2LoopCounterConst: .dword ulRegTest2LoopCounter
