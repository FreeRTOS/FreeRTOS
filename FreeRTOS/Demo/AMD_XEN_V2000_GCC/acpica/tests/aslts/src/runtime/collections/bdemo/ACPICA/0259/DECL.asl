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
     * Bug 259:
     *
     * SUMMARY: _REG method execution during Load operator processing issue
     */
    Name (B259, Buffer (0xD1)
    {
        /* 0000 */  0x53, 0x53, 0x44, 0x54, 0xD1, 0x00, 0x00, 0x00,  // SSDT....
        /* 0008 */  0x02, 0xE1, 0x49, 0x6E, 0x74, 0x65, 0x6C, 0x00,  // ..Intel.
        /* 0010 */  0x4D, 0x61, 0x6E, 0x79, 0x00, 0x00, 0x00, 0x00,  // Many....
        /* 0018 */  0x01, 0x00, 0x00, 0x00, 0x49, 0x4E, 0x54, 0x4C,  // ....INTL
        /* 0020 */  0x11, 0x10, 0x06, 0x20, 0x5B, 0x82, 0x4B, 0x0A,  // ... [.K.
        /* 0028 */  0x41, 0x55, 0x58, 0x44, 0x5B, 0x80, 0x4F, 0x50,  // AUXD[.OP
        /* 0030 */  0x52, 0x30, 0x80, 0x0A, 0x00, 0x0A, 0x04, 0x5B,  // R0.....[
        /* 0038 */  0x81, 0x0B, 0x4F, 0x50, 0x52, 0x30, 0x03, 0x52,  // ..OPR0.R
        /* 0040 */  0x46, 0x30, 0x30, 0x20, 0x08, 0x52, 0x45, 0x47,  // F00 .REG
        /* 0048 */  0x43, 0xFF, 0x08, 0x52, 0x45, 0x47, 0x50, 0x0A,  // C..REGP.
        /* 0050 */  0x00, 0x14, 0x33, 0x5F, 0x52, 0x45, 0x47, 0x02,  // ..3_REG.
        /* 0058 */  0x70, 0x0D, 0x5C, 0x41, 0x55, 0x58, 0x44, 0x2E,  // p.\AUXD.
        /* 0060 */  0x5F, 0x52, 0x45, 0x47, 0x3A, 0x00, 0x5B, 0x31,  // _REG:.[1
        /* 0068 */  0x70, 0x68, 0x5B, 0x31, 0x70, 0x69, 0x5B, 0x31,  // ph[1pi[1
        /* 0070 */  0xA0, 0x14, 0x93, 0x68, 0x0A, 0x80, 0x70, 0x52,  // ...h..pR
        /* 0078 */  0x45, 0x47, 0x43, 0x52, 0x45, 0x47, 0x50, 0x70,  // EGCREGPp
        /* 0080 */  0x69, 0x52, 0x45, 0x47, 0x43, 0x14, 0x4B, 0x04,  // iREGC.K.
        /* 0088 */  0x41, 0x43, 0x43, 0x30, 0x00, 0x70, 0x0D, 0x5C,  // ACC0.p.\
        /* 0090 */  0x41, 0x55, 0x58, 0x44, 0x2E, 0x41, 0x43, 0x43,  // AUXD.ACC
        /* 0098 */  0x30, 0x3A, 0x00, 0x5B, 0x31, 0x70, 0x52, 0x46,  // 0:.[1pRF
        /* 00A0 */  0x30, 0x30, 0x5B, 0x31, 0x70, 0x52, 0x45, 0x47,  // 00[1pREG
        /* 00A8 */  0x50, 0x5B, 0x31, 0xA0, 0x25, 0x92, 0x93, 0x52,  // P[1.%..R
        /* 00B0 */  0x45, 0x47, 0x43, 0x0A, 0x01, 0x70, 0x0D, 0x45,  // EGC..p.E
        /* 00B8 */  0x72, 0x72, 0x6F, 0x72, 0x3A, 0x20, 0x52, 0x45,  // rror: RE
        /* 00C0 */  0x47, 0x43, 0x20, 0x21, 0x3D, 0x20, 0x31, 0x00,  // GC != 1.
        /* 00C8 */  0x5B, 0x31, 0x70, 0x52, 0x45, 0x47, 0x43, 0x5B,  // [1pREGC[
        /* 00D0 */  0x31                                             // 1
    })
    Name (H259, 0x00)
    OperationRegion (R259, SystemMemory, 0x00, 0xD1)
    Field (R259, ByteAcc, NoLock, Preserve)
    {
        F259,   1672
    }

    Method (M17F, 0, NotSerialized)
    {
        External (\AUXD.REGC, UnknownObj)
        F259 = B259 /* \B259 */
        If (CondRefOf (\AUXD, Local0))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, "\\AUXD", 0x01)
            Return (Zero)
        }

        If (CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00))
        {
            Return (Zero)
        }

        Load (R259, H259) /* \H259 */
        If (CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00))
        {
            Return (Zero)
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

        Local0 = \AUXD.REGC /* External reference */
        If ((Local0 != 0x01))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x01)
            Return (Zero)
        }

        Unload (H259)
        If (CondRefOf (\AUXD, Local0))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, "\\AUXD", 0x01)
        }
    }
