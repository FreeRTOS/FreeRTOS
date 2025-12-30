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
     * Bug 292:
     *
     * SUMMARY: Different second and third UnLoad execution with the same argument behavior
     */
    Device (D292)
    {
        Name (BUF4, Buffer (0x44)
        {
            /* 0000 */  0x53, 0x53, 0x44, 0x54, 0x44, 0x00, 0x00, 0x00,  // SSDTD...
            /* 0008 */  0x02, 0x08, 0x69, 0x41, 0x53, 0x4C, 0x54, 0x53,  // ..iASLTS
            /* 0010 */  0x4C, 0x54, 0x42, 0x4C, 0x30, 0x30, 0x30, 0x31,  // LTBL0001
            /* 0018 */  0x01, 0x00, 0x00, 0x00, 0x49, 0x4E, 0x54, 0x4C,  // ....INTL
            /* 0020 */  0x15, 0x12, 0x06, 0x20, 0x10, 0x1F, 0x5C, 0x00,  // ... ..\.
            /* 0028 */  0x08, 0x5F, 0x58, 0x54, 0x32, 0x0D, 0x61, 0x62,  // ._XT2.ab
            /* 0030 */  0x73, 0x6F, 0x6C, 0x75, 0x74, 0x65, 0x20, 0x6C,  // solute l
            /* 0038 */  0x6F, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x20,  // ocation
            /* 0040 */  0x6F, 0x62, 0x6A, 0x00                           // obj.
        })
        OperationRegion (IST4, SystemMemory, 0x0600, 0x44)
        Field (IST4, ByteAcc, NoLock, Preserve)
        {
            RFU4,   544
        }

        Method (TST0, 0, Serialized)
        {
            Name (DDB0, 0x00)
            RFU4 = BUF4 /* \D292.BUF4 */
            Load (RFU4, DDB0) /* \D292.TST0.DDB0 */
            Debug = "SSDT loaded"
            Unload (DDB0)
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Debug = "SSDT unloaded"
            Unload (DDB0)
            CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
            Unload (DDB0)
            CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        }
    }

    Method (M292, 0, NotSerialized)
    {
        \D292.TST0 ()
    }
