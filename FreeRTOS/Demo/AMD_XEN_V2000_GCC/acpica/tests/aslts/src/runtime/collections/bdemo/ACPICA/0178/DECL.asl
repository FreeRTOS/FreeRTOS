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
     * Bug 178:
     *
     * SUMMARY: Unexpected exception occurs on access to the Fields specified by BankField
     */
    Method (MF0A, 0, Serialized)
    {
        OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
        Field (R000, ByteAcc, NoLock, Preserve)
        {
            BNK0,   2
        }

        BankField (R000, BNK0, 0x04, ByteAcc, NoLock, Preserve)
        {
            BKF0,   9
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = BKF0 /* \MF0A.BKF0 */
        If (Y263)
        {
            /*
             * After the bug 263 fixed we started actually
             * have there several exceptions:
             * - on evaluation of f001 stage
             * - and on Store-to-debug stage
             * Check opcode of the last exception.
             */
            CH04 (__METHOD__, 0x02, 0x44, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_REGISTER_LIMIT */
        }
        Else
        {
            CH04 (__METHOD__, 0x00, 0x44, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_REGISTER_LIMIT */
        }
    }

    Method (MF0B, 0, Serialized)
    {
        Name (I000, 0x04)
        OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
        Field (R000, ByteAcc, NoLock, Preserve)
        {
            BNK0,   2
        }

        BankField (R000, BNK0, I000, ByteAcc, NoLock, Preserve)
        {
            BKF0,   9
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = BKF0 /* \MF0B.BKF0 */
        CH04 (__METHOD__, 0x00, 0x44, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_REGISTER_LIMIT */
    }

    Method (MF0C, 0, Serialized)
    {
        OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
        Field (R000, ByteAcc, NoLock, Preserve)
        {
            BNK0,   2
        }

        BankField (R000, BNK0, 0x00, ByteAcc, NoLock, Preserve)
        {
            BKF0,   9
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = BKF0 /* \MF0C.BKF0 */
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
    }

    Method (MF0D, 0, Serialized)
    {
        Name (I000, 0x00)
        OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
        Field (R000, ByteAcc, NoLock, Preserve)
        {
            BNK0,   2
        }

        BankField (R000, BNK0, (I000 + 0x00), ByteAcc, NoLock, Preserve)
        {
            BKF0,   9
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = BKF0 /* \MF0D.BKF0 */
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
    }

    Method (MF0E, 0, Serialized)
    {
        Name (I000, 0x00)
        OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
        Field (R000, ByteAcc, NoLock, Preserve)
        {
            BNK0,   2
        }

        BankField (R000, BNK0, I000, ByteAcc, NoLock, Preserve)
        {
            BKF0,   9
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = BKF0 /* \MF0E.BKF0 */
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
    }
