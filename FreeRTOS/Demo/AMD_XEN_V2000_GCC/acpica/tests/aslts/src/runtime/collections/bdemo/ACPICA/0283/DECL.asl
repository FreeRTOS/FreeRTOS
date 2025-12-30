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
     * Bug 283:
     *
     * SUMMARY: When the Object parameter of Load is a Field the checksum
     *          of the supplied SSDT should be verified
     */
    Device (D283)
    {
        Name (BUF0, Buffer (0x34)
        {
            /* 0000 */  0x53, 0x53, 0x44, 0x54, 0x34, 0x00, 0x00, 0x00,  // SSDT4...
            /* 0008 */  0x02, 0xEB, 0x49, 0x6E, 0x74, 0x65, 0x6C, 0x00,  // ..Intel.
            /* 0010 */  0x4D, 0x61, 0x6E, 0x79, 0x00, 0x00, 0x00, 0x00,  // Many....
            /* 0018 */  0x01, 0x00, 0x00, 0x00, 0x49, 0x4E, 0x54, 0x4C,  // ....INTL
            /* 0020 */  0x08, 0x12, 0x06, 0x20, 0x14, 0x0F, 0x5C, 0x53,  // ... ..\S
            /* 0028 */  0x53, 0x30, 0x30, 0x00, 0xA4, 0x0D, 0x5C, 0x53,  // S00...\S
            /* 0030 */  0x53, 0x30, 0x30, 0x00                           // S00.
        })
        OperationRegion (IST0, SystemMemory, 0x00, 0x34)
        Field (IST0, ByteAcc, NoLock, Preserve)
        {
            RFU0,   416
        }

        Field (IST0, ByteAcc, NoLock, Preserve)
        {
            SIG,    32,
            LENG,   32,
            REV,    8,
            SUM,    8
        }

        Method (TST0, 0, Serialized)
        {
            Name (HI0, 0x00)
            RFU0 = BUF0 /* \D283.BUF0 */
            /* Spoil the CheckSum */

            Store ((SUM + 0x01), SUM) /* \D283.SUM_ */
            /* "Incorrect checksum" ACPI warning is expected */

            Load (RFU0, HI0) /* \D283.TST0.HI0_ */
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Unload (HI0)
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        }
    }

    Method (M283, 0, NotSerialized)
    {
        \D283.TST0 ()
    }
