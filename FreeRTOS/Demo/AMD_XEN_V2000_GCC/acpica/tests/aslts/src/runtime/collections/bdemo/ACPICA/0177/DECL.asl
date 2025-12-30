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
     * Bug 177:
     *
     * SUMMARY: Exception BUFFER_LIMIT occurs instead of STRING_LIMIT one
     */
    Method (MF07, 0, Serialized)
    {
        Name (I000, 0x01)
        OperationRegion (R000, SystemMemory, 0x00, I000)
        Field (R000, ByteAcc, NoLock, Preserve)
        {
            F000,   8
        }

        Field (R000, ByteAcc, NoLock, Preserve)
        {
            F001,   9
        }

        Name (P000, Package (0x02)
        {
            0x00,
            0x01
        })
        Name (B000, Buffer (0x03)
        {
             0x02, 0x03, 0x04                                 // ...
        })
        Name (S000, "5678")
        Name (I001, 0x00)
        OperationRegion (R001, SystemMemory, 0x0100, 0x0100)
        Field (R001, ByteAcc, NoLock, Preserve)
        {
            BNK0,   2
        }

        BankField (R001, BNK0, 0x04, ByteAcc, NoLock, Preserve)
        {
            BKF0,   9
        }

        /* Named */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Store (P000 [0x02], Local1)
        CH04 (__METHOD__, 0x01, 0x37, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_PACKAGE_LIMIT */
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Store (B000 [0x03], Local1)
        CH04 (__METHOD__, 0x01, 0x36, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_BUFFER_LIMIT */
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Store (S000 [0x04], Local1)
        CH04 (__METHOD__, 0x01, 0x3D, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_STRING_LIMIT */
        /* Immediate */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Store (Index (Package (0x02)
                {
                    0x00,
                    0x01
                }, 0x02), Local1)
        If (Y900)
        {
            CH04 (__METHOD__, 0x01, 0x37, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_PACKAGE_LIMIT */
        }
        Else
        {
            CH04 (__METHOD__, 0x00, 0x55, 0x00, __LINE__, 0x00, 0x00) /* AE_INDEX_TO_NOT_ATTACHED */
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Store (Index (Buffer (0x03)
                {
                     0x02, 0x03, 0x04                                 // ...
                }, 0x03), Local1)
        If (Y900)
        {
            CH04 (__METHOD__, 0x01, 0x36, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_BUFFER_LIMIT */
        }
        Else
        {
            CH04 (__METHOD__, 0x00, 0x55, 0x00, __LINE__, 0x00, 0x00) /* AE_INDEX_TO_NOT_ATTACHED */
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Store (Index ("5678", 0x04), Local1)
        If (Y900)
        {
            CH04 (__METHOD__, 0x01, 0x3D, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_STRING_LIMIT */
        }
        Else
        {
            CH04 (__METHOD__, 0x00, 0x55, 0x00, __LINE__, 0x00, 0x00) /* AE_INDEX_TO_NOT_ATTACHED */
        }

        /* Fields */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = F000 /* \MF07.F000 */
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = F001 /* \MF07.F001 */
        If (Y263)
        {
            /*
             * After the bug 263 fixed we started actually
             * have there several exceptions:
             * - on evaluation of f001 stage
             * - and on Store-to-debug stage
             * Check opcode of the last exception.
             */
            CH04 (__METHOD__, 0x02, 0x35, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_REGION_LIMIT */
        }
        Else
        {
            CH04 (__METHOD__, 0x00, 0x35, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_REGION_LIMIT */
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = BKF0 /* \MF07.BKF0 */
        If (Y263)
        {
            /* See comment to sub-test above */

            CH04 (__METHOD__, 0x02, 0x44, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_REGISTER_LIMIT */
        }
        Else
        {
            CH04 (__METHOD__, 0x00, 0x44, 0x00, __LINE__, 0x00, 0x00) /* AE_AML_REGISTER_LIMIT */
        }
    }
