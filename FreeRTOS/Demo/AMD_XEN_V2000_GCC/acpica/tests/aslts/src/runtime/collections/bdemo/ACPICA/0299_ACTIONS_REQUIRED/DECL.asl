    /*
     * Some or all of this work - Copyright (c) 2006 - 2021, Intel Corp.
     * All rights reserved.
     *
     * Redistribution and use in source and binary forms, with or without modification,
     * are permitted provided that the following conditions are met:
     *
     * Redistributions of source code must retain the above copyright notice,
     * this list of conditions and the following disclaimer.
     * Redistributions in binary form must reproduce the above copyright notice,
     * this list of conditions and the following disclaimer in the documentation
     * and/or other materials provided with the distribution.
     * Neither the name of Intel Corporation nor the names of its contributors
     * may be used to endorse or promote products derived from this software
     * without specific prior written permission.
     *
     * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
     * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
     * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
     * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
     * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
     * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
     * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
     * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
     * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
     * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
     */
    /*
     * Bug 299:
     *
     * SUMMARY: Many outstanding allocations on abnormal termination of AcpiDsCallControlMethod
     *
     *
     * [ACPI Debug]  String: [0x29] "========= ROOT METHODS SUMMARY (max 600):"
     * [ACPI Debug]  String: [0x3E] ":STST:bug-demo:Demo of bug 299:m1e8:FAIL:Errors # 01 00 00 00:"
     * [ACPI Debug]  String: [0x0E] "========= END."
     * [ACPI Debug]  String: [0x5B] "TEST ACPICA: 64-bit : FAIL : Errors # 0x0000000000000001, Failed tests # 0x0000000000000001"
     * Outstanding: 0x14 allocations after execution
     * Execution of \MAIN returned object 00327E40 Buflen 10
     *   [Integer] = 0000000000000001
     * - q
     * 0047DDE8 Len 0028   utcache-414 [Operand]      Integer R1
     * 0047DE48 Len 0028   utcache-414 [Operand]      Integer R1
     * 0047DEA8 Len 0028   utcache-414 [Operand]      Integer R1
     * 0047DF08 Len 0028   utcache-414 [Operand]      Integer R1
     * 0047DF68 Len 0028   utcache-414 [Operand]      Integer R1
     * 0047DFC8 Len 0028   utcache-414 [Operand]      Integer R1
     * 0047C988 Len 0028   utcache-414 [Operand]      Integer R1
     * 0047C9E8 Len 0028   utcache-414 [Operand]      Integer R1
     * 0047CA48 Len 0028   utcache-414 [Operand]      Integer R1
     * 0047CAA8 Len 0028   utcache-414 [Operand]      Integer R1
     * 0047CB08 Len 0028   utcache-414 [Operand]      Integer R1
     * 0047CB68 Len 0028   utcache-414 [Operand]      Integer R1
     * 0047C328 Len 0028   utcache-414 [Operand]      Integer R1
     * 0047C848 Len 0028   utcache-414 [Operand]      Integer R1
     * 0047B398 Len 0028   utcache-414 [Operand]      Integer R1
     * 0047A128 Len 0028   utcache-414 [Operand]      Integer R1
     * ACPI Error (uttrack-0719): 16(10) Outstanding allocations [20061215]
     */
    Method (M1E8, 0, NotSerialized)
    {
        Method (M306, 2, Serialized)
        {
            Name (I000, 0x00)
            Name (I001, 0x00)
            Name (I002, 0x34)
            Name (I003, 0xABCD0003)
            Name (I004, 0xABCD0004)
            Method (M000, 1, Serialized)
            {
                If (Arg0)
                {
                    I004 = 0x00
                }
                Else
                {
                    I003 = 0x00
                }

                MM00 (0x07, I000, I001)
            }

            Method (M001, 1, Serialized, 1)
            {
                If (Arg0)
                {
                    I004 = 0x01
                }
                Else
                {
                    I003 = 0x01
                }

                MM00 (0x08, I000, I001)
            }

            Method (MM00, 3, NotSerialized)
            {
                Local0 = I002 /* \M1E8.M306.I002 */
                I002++
                If ((I002 > 0x36))
                {
                    Return (Zero)
                }

                If (Arg0)
                {
                    Local1 = Arg2
                }
                Else
                {
                    Local1 = Arg1
                }

                If ((Local1 == 0x00))
                {
                    M000 (Local0)
                }
                Else
                {
                    M001 (Local0)
                }
            }

            I000 = Arg0
            I001 = Arg1
            MM00 (0x00, I000, I001)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        M306 (0x09, 0x00)
        M306 (0x09, 0x00)
        M306 (0x09, 0x00)
        M306 (0x09, 0x00)
        M306 (0x09, 0x00)
        M306 (0x09, 0x00)
        M306 (0x09, 0x00)
        M306 (0x09, 0x00)
        M306 (0x09, 0x00)
        M306 (0x09, 0x00)
        M306 (0x09, 0x00)
        M306 (0x09, 0x00)
        M306 (0x09, 0x00)
        M306 (0x09, 0x00)
        M306 (0x09, 0x00)
        M306 (0x09, 0x00)
        CH04 (__METHOD__, 0x01, 0x40, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_MUTEX_ORDER */
        /*
         * The problem is not automatically detected,
         * so remove this error report after the problem has been resolved.
         */
        ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
    }
