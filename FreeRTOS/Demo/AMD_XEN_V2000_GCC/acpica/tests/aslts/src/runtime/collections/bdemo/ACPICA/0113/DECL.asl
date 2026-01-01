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
     * Bug 113:
     *
     * SUMMARY: Unexpected dereference of Index reference immediately passed to Method
     */
    Method (ME79, 6, NotSerialized)
    {
        Debug = Arg0
        Debug = Arg1
        Debug = Arg2
        Debug = Arg3
        Debug = Arg4
        Debug = Arg5
        Debug = "Test 0"
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Store ((Arg0 + 0x01), Local5)
        CH04 (__METHOD__, 0x01, 0x2F, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
        Debug = "Test 1"
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Store ((Arg1 + 0x01), Local5)
        CH04 (__METHOD__, 0x01, 0x2F, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
        Debug = "Test 2"
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Store ((Arg2 + 0x01), Local5)
        CH04 (__METHOD__, 0x01, 0x2F, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
        Debug = "Test 3"
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Store ((Arg3 + 0x01), Local5)
        CH04 (__METHOD__, 0x01, 0x2F, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
        Debug = "Test 4"
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Store ((Arg4 + 0x01), Local5)
        CH04 (__METHOD__, 0x01, 0x2F, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
        Debug = "Test 5"
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Store ((Arg5 + 0x01), Local5)
        CH04 (__METHOD__, 0x01, 0x2F, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
    }

    Method (ME7A, 0, Serialized)
    {
        Name (P000, Package (0x05)
        {
            0x00,
            0x01,
            0x02,
            0x03,
            0x04
        })
        Name (P001, Package (0x05)
        {
            0x10,
            0x11,
            0x12,
            0x13,
            0x14
        })
        Name (P002, Package (0x05)
        {
            0x20,
            0x21,
            0x22,
            0x23,
            0x24
        })
        Name (P003, Package (0x05)
        {
            0x30,
            0x31,
            0x32,
            0x33,
            0x34
        })
        Name (P004, Package (0x05)
        {
            0x40,
            0x41,
            0x42,
            0x43,
            0x44
        })
        Store (P002 [0x02], Local0)
        Local1 = P003 [0x03]
        Local3 = Local2 = P004 [0x04]
        ME79 (P000 [0x00], Local4 = P001 [0x01], Local0, Local1, Local2,
            Local3)
        Debug = Local4
    }
