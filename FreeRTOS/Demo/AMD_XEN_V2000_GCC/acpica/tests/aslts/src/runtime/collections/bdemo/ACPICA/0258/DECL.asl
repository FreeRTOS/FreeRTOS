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
     * Bug 258:
     *
     * SUMMARY: Load operator should fail if its Object parameter being a Region
     *          is not in SystemMemory
     */
    /*
     * Original source code:
     DefinitionBlock("ssdt.aml", "SSDT", 0x02, "Intel", "Many", 0x00000001)
     {
     Device(AUXD)
     {
     Method(M000)
     {
     Return ("\\AUXD.M000 ()")
     }
     }
     }
     */
    Name (B258, Buffer (0x42)
    {
        /* 0000 */  0x53, 0x53, 0x44, 0x54, 0x42, 0x00, 0x00, 0x00,  // SSDTB...
        /* 0008 */  0x02, 0x81, 0x49, 0x6E, 0x74, 0x65, 0x6C, 0x00,  // ..Intel.
        /* 0010 */  0x4D, 0x61, 0x6E, 0x79, 0x00, 0x00, 0x00, 0x00,  // Many....
        /* 0018 */  0x01, 0x00, 0x00, 0x00, 0x49, 0x4E, 0x54, 0x4C,  // ....INTL
        /* 0020 */  0x11, 0x10, 0x06, 0x20, 0x5B, 0x82, 0x1C, 0x41,  // ... [..A
        /* 0028 */  0x55, 0x58, 0x44, 0x14, 0x16, 0x4D, 0x30, 0x30,  // UXD..M00
        /* 0030 */  0x30, 0x00, 0xA4, 0x0D, 0x5C, 0x41, 0x55, 0x58,  // 0...\AUX
        /* 0038 */  0x44, 0x2E, 0x4D, 0x30, 0x30, 0x30, 0x20, 0x28,  // D.M000 (
        /* 0040 */  0x29, 0x00                                       // ).
    })
    Name (H258, 0x00)
    OperationRegion (R258, 0x80, 0x00, 0x42)
    Field (R258, ByteAcc, NoLock, Preserve)
    {
        F258,   528
    }

    Method (M17E, 0, NotSerialized)
    {
        F258 = B258 /* \B258 */
        If (CondRefOf (\AUXD, Local0))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, "\\AUXD", 0x01)
            Return (Zero)
        }

        If (CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00))
        {
            Return (Zero)
        }

        Load (R258, H258) /* \H258 */
        If (CH04 (__METHOD__, 0x00, 0x08, 0x00, __LINE__, 0x00, 0x00))
        {
            Return (            /* AE_TYPE */

Zero)
        }

        If (CondRefOf (\AUXD, Local0)){}
        Else
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, "\\AUXD", 0x00)
            Return (Zero)
        }

        Local1 = ObjectType (Local0)
        If ((Local1 != 0x06))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local1, 0x06)
            Return (Zero)
        }

        Local0 = ObjectType (\AUXD.M000)
        If ((Local0 != 0x08))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x08)
            Return (Zero)
        }

        Unload (H258)
        If (CondRefOf (\AUXD, Local0))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, "\\AUXD", 0x01)
        }
    }
