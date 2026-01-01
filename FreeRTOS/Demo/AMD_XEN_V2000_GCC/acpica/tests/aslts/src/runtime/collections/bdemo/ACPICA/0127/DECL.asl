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
     * Bug 127:
     *
     * SUMMARY: Unexpectedly CopyObject of immediately passed Index reference is not reference
     */
    /* Store */
    Method (MF13, 0, NotSerialized)
    {
        Local1 = Local0 = PD11 [0x00]
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Store ((Local0 + 0x00), Local2)
        CH04 (__METHOD__, 0x01, 0x2F, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Store ((Local1 + 0x00), Local2)
        CH04 (__METHOD__, 0x01, 0x2F, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
        Local1 = Local0 = PD11 [0x01]
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Store ((Local0 + 0x00), Local2)
        CH04 (__METHOD__, 0x01, 0x2F, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Store ((Local1 + 0x00), Local2)
        CH04 (__METHOD__, 0x01, 0x2F, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
    }

    /* CopyObject */

    Method (MF14, 0, NotSerialized)
    {
        CopyObject (Local0 = PD11 [0x00], Local1)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Store ((Local0 + 0x00), Local2)
        CH04 (__METHOD__, 0x01, 0x2F, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Store ((Local1 + 0x00), Local2)
        CH04 (__METHOD__, 0x01, 0x2F, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
    }

    Method (MF15, 0, NotSerialized)
    {
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        CopyObject (Local0 = PD11 [0x01], Local1)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Store ((Local0 + 0x00), Local2)
        CH04 (__METHOD__, 0x01, 0x2F, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Store ((Local1 + 0x00), Local2)
        CH04 (__METHOD__, 0x01, 0x2F, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
    }

    Method (MF16, 0, NotSerialized)
    {
        If (0x01)
        {
            MF13 ()
        }

        If (0x01)
        {
            MF14 ()
        }

        If (0x01)
        {
            MF15 ()
        }
    }
