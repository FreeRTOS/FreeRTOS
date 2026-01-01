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
     * Bug 294:
     *
     * SUMMARY: _ERR method can not be evaluated when AE_OWNER_ID_LIMIT is emitted
     */
    Device (D294)
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
        Name (BUF1, Buffer (0x5F)
        {
            /* 0000 */  0x53, 0x53, 0x44, 0x54, 0x5F, 0x00, 0x00, 0x00,  // SSDT_...
            /* 0008 */  0x02, 0x33, 0x49, 0x6E, 0x74, 0x65, 0x6C, 0x00,  // .3Intel.
            /* 0010 */  0x4D, 0x61, 0x6E, 0x79, 0x00, 0x00, 0x00, 0x00,  // Many....
            /* 0018 */  0x01, 0x00, 0x00, 0x00, 0x49, 0x4E, 0x54, 0x4C,  // ....INTL
            /* 0020 */  0x15, 0x12, 0x06, 0x20, 0x10, 0x1F, 0x5C, 0x00,  // ... ..\.
            /* 0028 */  0x08, 0x4E, 0x41, 0x42, 0x53, 0x0D, 0x61, 0x62,  // .NABS.ab
            /* 0030 */  0x73, 0x6F, 0x6C, 0x75, 0x74, 0x65, 0x20, 0x6C,  // solute l
            /* 0038 */  0x6F, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x20,  // ocation
            /* 0040 */  0x6F, 0x62, 0x6A, 0x00, 0x08, 0x4E, 0x43, 0x52,  // obj..NCR
            /* 0048 */  0x52, 0x0D, 0x63, 0x75, 0x72, 0x72, 0x65, 0x6E,  // R.curren
            /* 0050 */  0x74, 0x20, 0x6C, 0x6F, 0x63, 0x61, 0x74, 0x69,  // t locati
            /* 0058 */  0x6F, 0x6E, 0x20, 0x6F, 0x62, 0x6A, 0x00         // on obj.
        })
        OperationRegion (IST1, SystemMemory, 0x0100, 0x5F)
        Field (IST1, ByteAcc, NoLock, Preserve)
        {
            RFU1,   760
        }

        Name (BUF3, Buffer (0x011F)
        {
            /* 0000 */  0x53, 0x53, 0x44, 0x54, 0x1F, 0x01, 0x00, 0x00,  // SSDT....
            /* 0008 */  0x02, 0x58, 0x49, 0x6E, 0x74, 0x65, 0x6C, 0x00,  // .XIntel.
            /* 0010 */  0x4D, 0x61, 0x6E, 0x79, 0x00, 0x00, 0x00, 0x00,  // Many....
            /* 0018 */  0x01, 0x00, 0x00, 0x00, 0x49, 0x4E, 0x54, 0x4C,  // ....INTL
            /* 0020 */  0x15, 0x12, 0x06, 0x20, 0x5B, 0x82, 0x49, 0x0F,  // ... [.I.
            /* 0028 */  0x41, 0x55, 0x58, 0x44, 0x08, 0x49, 0x4E, 0x54,  // AUXD.INT
            /* 0030 */  0x30, 0x0E, 0x10, 0x32, 0x54, 0x76, 0x98, 0xBA,  // 0..2Tv..
            /* 0038 */  0xDC, 0xFE, 0x08, 0x53, 0x54, 0x52, 0x30, 0x0D,  // ...STR0.
            /* 0040 */  0x73, 0x6F, 0x75, 0x72, 0x63, 0x65, 0x20, 0x73,  // source s
            /* 0048 */  0x74, 0x72, 0x69, 0x6E, 0x67, 0x30, 0x00, 0x08,  // tring0..
            /* 0050 */  0x42, 0x55, 0x46, 0x30, 0x11, 0x0C, 0x0A, 0x09,  // BUF0....
            /* 0058 */  0x09, 0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02,  // ........
            /* 0060 */  0x01, 0x08, 0x50, 0x41, 0x43, 0x30, 0x12, 0x27,  // ..PAC0.'
            /* 0068 */  0x03, 0x0E, 0x1F, 0x32, 0x54, 0x76, 0x98, 0xBA,  // ...2Tv..
            /* 0070 */  0xDC, 0xFE, 0x0D, 0x74, 0x65, 0x73, 0x74, 0x20,  // ...test
            /* 0078 */  0x70, 0x61, 0x63, 0x6B, 0x61, 0x67, 0x65, 0x30,  // package0
            /* 0080 */  0x00, 0x11, 0x0C, 0x0A, 0x09, 0x13, 0x12, 0x11,  // ........
            /* 0088 */  0x10, 0x0F, 0x0E, 0x0D, 0x0C, 0x0B, 0x5B, 0x81,  // ......[.
            /* 0090 */  0x0B, 0x4F, 0x50, 0x52, 0x30, 0x01, 0x46, 0x4C,  // .OPR0.FL
            /* 0098 */  0x55, 0x30, 0x20, 0x5B, 0x82, 0x10, 0x44, 0x45,  // U0 [..DE
            /* 00A0 */  0x56, 0x30, 0x08, 0x53, 0x30, 0x30, 0x30, 0x0D,  // V0.S000.
            /* 00A8 */  0x44, 0x45, 0x56, 0x30, 0x00, 0x5B, 0x02, 0x45,  // DEV0.[.E
            /* 00B0 */  0x56, 0x45, 0x30, 0x14, 0x09, 0x4D, 0x4D, 0x4D,  // VE0..MMM
            /* 00B8 */  0x30, 0x00, 0xA4, 0x0A, 0x00, 0x5B, 0x01, 0x4D,  // 0....[.M
            /* 00C0 */  0x54, 0x58, 0x30, 0x00, 0x5B, 0x80, 0x4F, 0x50,  // TX0.[.OP
            /* 00C8 */  0x52, 0x30, 0x00, 0x0C, 0x21, 0x43, 0x65, 0x07,  // R0..!Ce.
            /* 00D0 */  0x0A, 0x98, 0x5B, 0x84, 0x13, 0x50, 0x57, 0x52,  // ..[..PWR
            /* 00D8 */  0x30, 0x00, 0x00, 0x00, 0x08, 0x53, 0x30, 0x30,  // 0....S00
            /* 00E0 */  0x30, 0x0D, 0x50, 0x57, 0x52, 0x30, 0x00, 0x5B,  // 0.PWR0.[
            /* 00E8 */  0x83, 0x16, 0x43, 0x50, 0x55, 0x30, 0x00, 0xFF,  // ..CPU0..
            /* 00F0 */  0xFF, 0xFF, 0xFF, 0x00, 0x08, 0x53, 0x30, 0x30,  // .....S00
            /* 00F8 */  0x30, 0x0D, 0x43, 0x50, 0x55, 0x30, 0x00, 0x5B,  // 0.CPU0.[
            /* 0100 */  0x85, 0x10, 0x54, 0x5A, 0x4E, 0x30, 0x08, 0x53,  // ..TZN0.S
            /* 0108 */  0x30, 0x30, 0x30, 0x0D, 0x54, 0x5A, 0x4E, 0x30,  // 000.TZN0
            /* 0110 */  0x00, 0x5B, 0x13, 0x42, 0x55, 0x46, 0x30, 0x0A,  // .[.BUF0.
            /* 0118 */  0x00, 0x0A, 0x45, 0x42, 0x46, 0x4C, 0x30         // ..EBFL0
        })
        OperationRegion (IST3, SystemMemory, 0x0400, 0x011F)
        Field (IST3, ByteAcc, NoLock, Preserve)
        {
            RFU3,   2296
        }

        Name (SNML, "0123456789ABCDEF")
        Name (NNML, 0x10) /* <= sizeof (SNML) */
        /* Take into account AE_OWNER_ID_LIMIT */

        Name (HI0M, 0x0100) /* <= (NNML * NNML) */
        Name (HI0N, 0x00)
        Name (INIF, 0x00)
        Method (_ERR, 3, NotSerialized)
        {
            Debug = "_ERR exception handler"
            Return (0x00)
        }

        Method (CHSM, 2, Serialized)
        {
            Name (LPN0, 0x00)
            Name (LPC0, 0x00)
            Local0 = 0x00 /* sum */
            LPN0 = Arg1
            LPC0 = 0x00
            While (LPN0)
            {
                Local1 = DerefOf (Arg0 [LPC0])
                Local0 += Local1
                Local0 %= 0x0100
                LPN0--
                LPC0++
            }

            Local0 = (0x00 - Local0)
            Local0 %= 0x0100
            Debug = "checksum"
            Debug = Local0
            Return (Local0)
        }

        /* Initializes multiple Tables Load test */

        Method (INIT, 0, NotSerialized)
        {
            Local0 = SizeOf (SNML)
            If ((NNML > Local0))
            {
                Debug = Concatenate ("INIT: test error, check NNML <= Sizeof(SNML):", ToDecimalString (Local0))
                Return (0x01)
            }

            Local0 *= Local0
            If ((HI0M > Local0))
            {
                Debug = Concatenate ("INIT: test error, check HI0M <= 0x", Local0)
                Return (0x01)
            }

            Return (0x00)
        }

        /* Prepares and Loads the next Table of multiple Tables Load test */

        Method (LD, 0, Serialized)
        {
            If ((HI0N >= HI0M))
            {
                Debug = "LD: too many tables loaded"
                Return (0x01)
            }

            Local2 = (HI0N * 0x30)
            OperationRegion (IST0, SystemMemory, Local2, 0x34)
            Field (IST0, ByteAcc, NoLock, Preserve)
            {
                RFU0,   416
            }

            Field (IST0, ByteAcc, NoLock, Preserve)
            {
                SIG,    32,
                LENG,   32,
                REV,    8,
                SUM,    8,
                OID,    48,
                OTID,   64,
                OREV,   32,
                CID,    32,
                CREV,   32,
                Offset (0x27),
                SSNM,   32,
                Offset (0x2F),
                SSRT,   32
            }

            RFU0 = BUF0 /* \D294.BUF0 */
            /* Modify Revision field of SSDT */

            Store ((CREV + 0x01), CREV) /* \D294.LD__.CREV */
            /* Modify SSNM Object Name */

            Divide (HI0N, NNML, Local0, Local1)
            Local1 = DerefOf (SNML [Local1])
            Local1 <<= 0x10
            Local0 = DerefOf (SNML [Local0])
            Local0 <<= 0x18
            Local0 += Local1
            Local0 += 0x5353
            SSNM = Local0
            Debug = SSNM /* \D294.LD__.SSNM */
            /* Modify SSNM Method Return String */

            SSRT = Local0
            /* Recalculate and save CheckSum */

            Local0 = RFU0 /* \D294.LD__.RFU0 */
            Store ((SUM + CHSM (Local0, SizeOf (Local0))), SUM) /* \D294.LD__.SUM_ */
            Load (RFU0, Local3)
            HI0N++
            Debug = "LD: SSDT Loaded"
            Return (0x00)
        }

        Method (TST0, 0, Serialized)
        {
            Name (MAXT, 0xFA)
            Name (DDB1, 0x00)
            Name (DDB3, 0x00)
            If (INIT ())
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, 0x00, 0x00)
                Return (0x01)
            }

            RFU1 = BUF1 /* \D294.BUF1 */
            RFU3 = BUF3 /* \D294.BUF3 */
            Local0 = MAXT /* \D294.TST0.MAXT */
            While (Local0)
            {
                /*			Store(HI0N, Debug) */

                If (LD ())
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, HI0N)
                    Return (0x01)
                }

                Local0--
            }

            /* Methods can not be called after the following Load */
            /* (OWNER_ID is exhausted) */
            Load (RFU1, DDB1) /* \D294.TST0.DDB1 */
            Debug = "SSDT1 Loaded"
            /* The following Load should cause AE_OWNER_ID_LIMIT */

            Load (RFU3, DDB3) /* \D294.TST0.DDB3 */
            CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
            Return (0x00)
        }
    }

    Method (M294, 0, NotSerialized)
    {
        \D294.TST0 ()
    }
