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
     * Bug 278:
     *
     * SUMMARY: "Namespace location to be relative" functionality of Load operator issue
     */
    Device (D278)
    {
        Name (SSDT, Buffer (0x5F)
        {
            /* 0000 */  0x53, 0x53, 0x44, 0x54, 0x5F, 0x00, 0x00, 0x00,  // SSDT_...
            /* 0008 */  0x02, 0x2D, 0x49, 0x6E, 0x74, 0x65, 0x6C, 0x00,  // .-Intel.
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
        OperationRegion (IST0, SystemMemory, 0x00, 0x5F)
        Field (IST0, ByteAcc, NoLock, Preserve)
        {
            RFU0,   760
        }

        Name (DDBH, 0x00)
        Method (TST0, 0, NotSerialized)
        {
            /* Check absence */

            If (CondRefOf (NABS, Local0))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, "NABS", 0x01)
            }

            If (CondRefOf (NCRR, Local0))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, "NCRR", 0x01)
            }

            RFU0 = SSDT /* \D278.SSDT */
            Load (RFU0, DDBH) /* \D278.DDBH */
            Debug = "SSDT loaded"
            /* Check existence */

            If (CondRefOf (NABS, Local0))
            {
                If (("absolute location obj" != DerefOf (Local0)))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, "absolute location NABS", 0x01)
                }
            }
            Else
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, "NABS", 0x00)
            }

            If (CondRefOf (NCRR, Local0))
            {
                If (("current location obj" != DerefOf (Local0)))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, "current location NCRR", 0x01)
                }
            }
            Else
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, "NCRR", 0x00)
            }

            /* Check location */

            If (CondRefOf (\NABS, Local0)){}
            Else
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, "\\NABS", 0x00)
            }

            If (CondRefOf (\NCRR, Local0))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, "\\NCRR", 0x01)
            }

            If (CondRefOf (\D278.NCRR, Local0))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, "\\D278.NCRR", 0x01)
            }

            If (CondRefOf (\D278.TST0.NCRR, Local0)){}
            Else
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, "\\D278.TST0.NCRR", 0x00)
            }

            Unload (DDBH)
            Debug = "SSDT unloaded"
            /* Check absence */

            If (CondRefOf (NABS, Local0))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, "NABS", 0x01)
            }

            If (CondRefOf (NCRR, Local0))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, "NCRR", 0x01)
            }
        }
    }

    Method (M278, 0, NotSerialized)
    {
        \D278.TST0 ()
    }
