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
     * Create Buffer Field operators
     */
    /*
     * !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
     * Clean up method m218 after that when errors 65,66,68,69
     * (in 32-bit mode) will be investigated and resolved
     * !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
     *
     * Update needed: 1) add "Common features", see below ...
     *                2) tune parameters in m21d
     */
    Name (Z001, 0x01)
    Name (BS00, 0x0100)
    /* Benchmark Buffers */

    Name (B000, Buffer (BS00){})
    Name (B0FF, Buffer (BS00)
    {
        /* 0000 */  0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,  // ........
        /* 0008 */  0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,  // ........
        /* 0010 */  0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,  // ........
        /* 0018 */  0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,  // ........
        /* 0020 */  0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,  // ........
        /* 0028 */  0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,  // ........
        /* 0030 */  0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,  // ........
        /* 0038 */  0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,  // ........
        /* 0040 */  0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,  // ........
        /* 0048 */  0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,  // ........
        /* 0050 */  0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,  // ........
        /* 0058 */  0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,  // ........
        /* 0060 */  0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,  // ........
        /* 0068 */  0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,  // ........
        /* 0070 */  0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,  // ........
        /* 0078 */  0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,  // ........
        /* 0080 */  0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,  // ........
        /* 0088 */  0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,  // ........
        /* 0090 */  0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,  // ........
        /* 0098 */  0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,  // ........
        /* 00A0 */  0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,  // ........
        /* 00A8 */  0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,  // ........
        /* 00B0 */  0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,  // ........
        /* 00B8 */  0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,  // ........
        /* 00C0 */  0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,  // ........
        /* 00C8 */  0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,  // ........
        /* 00D0 */  0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,  // ........
        /* 00D8 */  0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,  // ........
        /* 00E0 */  0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,  // ........
        /* 00E8 */  0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,  // ........
        /* 00F0 */  0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,  // ........
        /* 00F8 */  0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF   // ........
    })
    Name (B256, Buffer (BS00)
    {
        /* 0000 */  0x00, 0x00, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,  // ........
        /* 0008 */  0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F,  // ........
        /* 0010 */  0x00, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,  // ........
        /* 0018 */  0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F,  // ........
        /* 0020 */  0x10, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27,  // .!"#$%&'
        /* 0028 */  0x28, 0x29, 0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F,  // ()*+,-./
        /* 0030 */  0x20, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37,  //  1234567
        /* 0038 */  0x38, 0x39, 0x3A, 0x3B, 0x3C, 0x3D, 0x3E, 0x3F,  // 89:;<=>?
        /* 0040 */  0x30, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47,  // 0ABCDEFG
        /* 0048 */  0x48, 0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F,  // HIJKLMNO
        /* 0050 */  0x40, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57,  // @QRSTUVW
        /* 0058 */  0x58, 0x59, 0x5A, 0x5B, 0x5C, 0x5D, 0x5E, 0x5F,  // XYZ[\]^_
        /* 0060 */  0x50, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67,  // Pabcdefg
        /* 0068 */  0x68, 0x69, 0x6A, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F,  // hijklmno
        /* 0070 */  0x60, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77,  // `qrstuvw
        /* 0078 */  0x78, 0x79, 0x7A, 0x7B, 0x7C, 0x7D, 0x7E, 0x7F,  // xyz{|}~.
        /* 0080 */  0x80, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87,  // ........
        /* 0088 */  0x88, 0x89, 0x8A, 0x8B, 0x8C, 0x8D, 0x8E, 0x8F,  // ........
        /* 0090 */  0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97,  // ........
        /* 0098 */  0x98, 0x99, 0x9A, 0x9B, 0x9C, 0x9D, 0x9E, 0x9F,  // ........
        /* 00A0 */  0xA0, 0xA1, 0xA2, 0xA3, 0xA4, 0xA5, 0xA6, 0xA7,  // ........
        /* 00A8 */  0xA8, 0xA9, 0xAA, 0xAB, 0xAC, 0xAD, 0xAE, 0xAF,  // ........
        /* 00B0 */  0xB0, 0xB1, 0xB2, 0xB3, 0xB4, 0xB5, 0xB6, 0xB7,  // ........
        /* 00B8 */  0xB8, 0xB9, 0xBA, 0xBB, 0xBC, 0xBD, 0xBE, 0xBF,  // ........
        /* 00C0 */  0xC0, 0xC1, 0xC2, 0xC3, 0xC4, 0xC5, 0xC6, 0xC7,  // ........
        /* 00C8 */  0xC8, 0xC9, 0xCA, 0xCB, 0xCC, 0xCD, 0xCE, 0xCF,  // ........
        /* 00D0 */  0xD0, 0xD1, 0xD2, 0xD3, 0xD4, 0xD5, 0xD6, 0xD7,  // ........
        /* 00D8 */  0xD8, 0xD9, 0xDA, 0xDB, 0xDC, 0xDD, 0xDE, 0xDF,  // ........
        /* 00E0 */  0xE0, 0xE1, 0xE2, 0xE3, 0xE4, 0xE5, 0xE6, 0xE7,  // ........
        /* 00E8 */  0xE8, 0xE9, 0xEA, 0xEB, 0xEC, 0xED, 0xEE, 0xEF,  // ........
        /* 00F0 */  0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6, 0xF7,  // ........
        /* 00F8 */  0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE, 0xFF   // ........
    })
    /* Generated benchmark buffers for comparison with */

    Name (B010, Buffer (BS00){})
    Name (B101, Buffer (BS00){})
    Name (B0B0, Buffer (BS00){})
    /* Buffer for filling the ground */

    Name (B0G0, Buffer (BS00){})
    /* Buffer for filling the field (over the ground) */

    Name (B0F0, Buffer (BS00){})
    /* CreateBitField */
    /* */
    /* <test name>, */
    /* <index of bit>, */
    /* <buf: 00>, */
    /* <buf: ff>, */
    /* <buf: 010>, */
    /* <buf: 101>, */
    /* <byte size of buf> */
    Method (M210, 7, Serialized)
    {
        Name (PR00, 0x00)
        If (PR00)
        {
            Debug = "========:"
        }

        Name (B001, Buffer (Arg6){})
        Name (B002, Buffer (Arg6){})
        CreateBitField (B001, Arg1, F001)
        /*////////////// A. 1->0 (010->000) */

        B001 = Arg4
        If (PR00)
        {
            Debug = B001 /* \M210.B001 */
        }

        F001 = 0xFFFFFFFFFFFFFFFE
        Local0 = F001 /* \M210.F001 */
        If ((Local0 != 0x00))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        B002 = Arg2
        If ((B001 != B002))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If (PR00)
        {
            Debug = B001 /* \M210.B001 */
        }

        /*////////////// B. 1->0 (111->101) */

        B001 = Arg3
        If (PR00)
        {
            Debug = B001 /* \M210.B001 */
        }

        F001 = 0x00
        Local0 = F001 /* \M210.F001 */
        If ((Local0 != 0x00))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        B002 = Arg5
        If ((B001 != B002))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If (PR00)
        {
            Debug = B001 /* \M210.B001 */
        }

        /*////////////// C. 0->1 (101->111) */

        B001 = Arg5
        If (PR00)
        {
            Debug = B001 /* \M210.B001 */
        }

        F001 = 0x01
        Local0 = F001 /* \M210.F001 */
        If ((Local0 != 0x01))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, 0x01)
        }

        B002 = Arg3
        If ((B001 != B002))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If (PR00)
        {
            Debug = B001 /* \M210.B001 */
        }

        /*////////////// D. 0->1 (000->010) */

        B001 = Arg2
        If (PR00)
        {
            Debug = B001 /* \M210.B001 */
        }

        F001 = 0xFFFFFFFFFFFFFFFF
        Local0 = F001 /* \M210.F001 */
        If ((Local0 != 0x01))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, 0x01)
        }

        B002 = Arg4
        If ((B001 != B002))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If (PR00)
        {
            Debug = B001 /* \M210.B001 */
        }

        /* Common features */

        Local0 = SizeOf (B001)
        If ((Local0 != Arg6))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, Arg6)
        }

        Local0 = SizeOf (B002)
        If ((Local0 != Arg6))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, Arg6)
        }

        Local0 = ObjectType (F001)
        If ((Local0 != C016))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, C016)
        }

        If (PR00)
        {
            Debug = Local0
        }
    }

    Method (M211, 0, Serialized)
    {
        Debug = "TEST: m211, Create 1-Bit Buffer Field:"
        /* Size of buffer (in bytes) */

        Name (BSZ0, 0x00)
        BSZ0 = BS00 /* \BS00 */
        /* Max steps to check */

        Name (BSZ1, 0x00)
        /* How many elements to check */

        Name (N000, 0x00)
        Name (NCUR, 0x00)
        N000 = (BSZ0 * 0x08)
        BSZ1 = N000 /* \M211.N000 */
        While (N000)
        {
            If ((NCUR >= BSZ1))
            {
                ERR (__METHOD__, Z001, __LINE__, 0x00, 0x00, NCUR, BSZ1)
                Break
            }

            B010 = B000 /* \B000 */
            B101 = B0FF /* \B0FF */
            Divide (NCUR, 0x08, Local1, Local0)
            Local2 = (0x01 << Local1)
            B010 [Local0] = Local2
            Local3 = ~Local2
            B101 [Local0] = Local3
            M210 (__METHOD__, NCUR, B000, B0FF, B010, B101, BSZ0)
            N000--
            NCUR++
        }
    }

    /* CreateByteField */
    /* */
    /* <test name>, */
    /* <index of byte>, */
    /* <byte size of buf> */
    Method (M212, 3, Serialized)
    {
        Name (PR00, 0x00)
        If (PR00)
        {
            Debug = "========:"
        }

        Name (B001, Buffer (Arg2){})
        Name (B002, Buffer (Arg2){})
        /*////////////// A. 1->0 (010->000) */

        CreateByteField (B001, Arg1, F001)
        B001 = B010 /* \B010 */
        If (PR00)
        {
            Debug = B001 /* \M212.B001 */
        }

        F001 = 0xFFFFFFFFFFFFFF00
        Local0 = F001 /* \M212.F001 */
        If ((Local0 != 0x00))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        B002 = B000 /* \B000 */
        If ((B001 != B002))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If (PR00)
        {
            Debug = B001 /* \M212.B001 */
        }

        /*////////////// B. 1->0 (111->101) */

        B001 = B0FF /* \B0FF */
        If (PR00)
        {
            Debug = B001 /* \M212.B001 */
        }

        F001 = 0x00
        Local0 = F001 /* \M212.F001 */
        If ((Local0 != 0x00))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        B002 = B101 /* \B101 */
        If ((B001 != B002))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If (PR00)
        {
            Debug = B001 /* \M212.B001 */
        }

        /*////////////// C. 0->1 (101->111) */

        B001 = B101 /* \B101 */
        If (PR00)
        {
            Debug = B001 /* \M212.B001 */
        }

        F001 = 0xFF
        Local0 = F001 /* \M212.F001 */
        If ((Local0 != 0xFF))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, 0xFF)
        }

        B002 = B0FF /* \B0FF */
        If ((B001 != B002))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If (PR00)
        {
            Debug = B001 /* \M212.B001 */
        }

        /*////////////// D. 0->1 (000->010) */

        B001 = B000 /* \B000 */
        If (PR00)
        {
            Debug = B001 /* \M212.B001 */
        }

        F001 = 0xFFFFFFFFFFFFFFFF
        Local0 = F001 /* \M212.F001 */
        If ((Local0 != 0xFF))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, 0xFF)
        }

        B002 = B010 /* \B010 */
        If ((B001 != B002))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If (PR00)
        {
            Debug = B001 /* \M212.B001 */
        }

        /*////////////// E. 0->1 (000->010) */

        B001 = B000 /* \B000 */
        If (PR00)
        {
            Debug = B001 /* \M212.B001 */
        }

        F001 = 0xFFFFFFFFFFFFFF96
        Local0 = F001 /* \M212.F001 */
        If ((Local0 != 0x96))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, 0x96)
        }

        B002 = B0B0 /* \B0B0 */
        If ((B001 != B002))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If (PR00)
        {
            Debug = B001 /* \M212.B001 */
        }

        /* Common features */

        Local0 = SizeOf (B001)
        If ((Local0 != Arg2))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, Arg2)
        }

        Local0 = SizeOf (B002)
        If ((Local0 != Arg2))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, Arg2)
        }

        Local0 = ObjectType (F001)
        If ((Local0 != C016))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, C016)
        }

        If (PR00)
        {
            Debug = Local0
        }
    }

    Method (M213, 0, Serialized)
    {
        Debug = "TEST: m213, Create 8-Bit Buffer Field:"
        /* Size of buffer (in bytes) */

        Name (BSZ0, 0x00)
        BSZ0 = BS00 /* \BS00 */
        /* Max steps to check */

        Name (BSZ1, 0x00)
        /* How many elements to check */

        Name (N000, 0x00)
        Name (NCUR, 0x00)
        N000 = BSZ0 /* \M213.BSZ0 */
        BSZ1 = N000 /* \M213.N000 */
        While (N000)
        {
            If ((NCUR >= BSZ1))
            {
                ERR (__METHOD__, Z001, __LINE__, 0x00, 0x00, NCUR, BSZ1)
                Break
            }

            B010 = B000 /* \B000 */
            B0B0 = B000 /* \B000 */
            B101 = B0FF /* \B0FF */
            B010 [NCUR] = 0xFF
            B0B0 [NCUR] = 0x96
            B101 [NCUR] = 0x00
            M212 (__METHOD__, NCUR, BSZ0)
            N000--
            NCUR++
        }
    }

    /* CreateWordField */
    /* */
    /* <test name>, */
    /* <index of byte>, */
    /* <byte size of buf> */
    Method (M214, 3, Serialized)
    {
        Name (PR00, 0x00)
        If (PR00)
        {
            Debug = "========:"
            Debug = Arg1
            Debug = Arg2
        }

        Name (B001, Buffer (Arg2){})
        Name (B002, Buffer (Arg2){})
        CreateWordField (B001, Arg1, F001)
        /*////////////// A. 1->0 (010->000) */

        B001 = B010 /* \B010 */
        If (PR00)
        {
            Debug = B001 /* \M214.B001 */
        }

        F001 = 0xFFFFFFFFFFFF0000
        Local0 = F001 /* \M214.F001 */
        If ((Local0 != 0x00))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        B002 = B000 /* \B000 */
        If ((B001 != B002))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If (PR00)
        {
            Debug = B001 /* \M214.B001 */
        }

        /*////////////// B. 1->0 (111->101) */

        B001 = B0FF /* \B0FF */
        If (PR00)
        {
            Debug = B001 /* \M214.B001 */
        }

        F001 = 0x00
        Local0 = F001 /* \M214.F001 */
        If ((Local0 != 0x00))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        B002 = B101 /* \B101 */
        If ((B001 != B002))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If (PR00)
        {
            Debug = B001 /* \M214.B001 */
        }

        /*////////////// C. 0->1 (101->111) */

        B001 = B101 /* \B101 */
        If (PR00)
        {
            Debug = B001 /* \M214.B001 */
        }

        F001 = 0xFFFF
        Local0 = F001 /* \M214.F001 */
        If ((Local0 != 0xFFFF))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, 0xFFFF)
        }

        B002 = B0FF /* \B0FF */
        If ((B001 != B002))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If (PR00)
        {
            Debug = B001 /* \M214.B001 */
        }

        /*////////////// D. 0->1 (000->010) */

        B001 = B000 /* \B000 */
        If (PR00)
        {
            Debug = B001 /* \M214.B001 */
        }

        F001 = 0xFFFFFFFFFFFFFFFF
        Local0 = F001 /* \M214.F001 */
        If ((Local0 != 0xFFFF))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, 0xFFFF)
        }

        B002 = B010 /* \B010 */
        If ((B001 != B002))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If (PR00)
        {
            Debug = B001 /* \M214.B001 */
        }

        Local0 = SizeOf (B001)
        If ((Local0 != Arg2))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, Arg2)
        }

        Local0 = SizeOf (B002)
        If ((Local0 != Arg2))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, Arg2)
        }

        /*////////////// E. 0->1 (000->010) */

        B001 = B000 /* \B000 */
        If (PR00)
        {
            Debug = B001 /* \M214.B001 */
        }

        F001 = 0xFFFFFFFFFFFF7698
        Local0 = F001 /* \M214.F001 */
        If ((Local0 != 0x7698))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, 0x7698)
        }

        B002 = B0B0 /* \B0B0 */
        If ((B001 != B002))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If (PR00)
        {
            Debug = B001 /* \M214.B001 */
        }

        /* Common features */

        Local0 = SizeOf (B001)
        If ((Local0 != Arg2))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, Arg2)
        }

        Local0 = SizeOf (B002)
        If ((Local0 != Arg2))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, Arg2)
        }

        Local0 = ObjectType (F001)
        If ((Local0 != C016))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, C016)
        }

        If (PR00)
        {
            Debug = Local0
        }
    }

    Method (M215, 0, Serialized)
    {
        Debug = "TEST: m215, Create 16-Bit Buffer Field:"
        /* Size of buffer (in bytes) */

        Name (BSZ0, 0x00)
        BSZ0 = BS00 /* \BS00 */
        /* Max steps to check */

        Name (BSZ1, 0x00)
        /* How many elements to check */

        Name (N000, 0x00)
        Name (NCUR, 0x00)
        N000 = (BSZ0 - 0x01)
        BSZ1 = N000 /* \M215.N000 */
        While (N000)
        {
            If ((NCUR >= BSZ1))
            {
                ERR (__METHOD__, Z001, __LINE__, 0x00, 0x00, NCUR, BSZ1)
                Break
            }

            B010 = B000 /* \B000 */
            B0B0 = B000 /* \B000 */
            B101 = B0FF /* \B0FF */
            Local0 = NCUR /* \M215.NCUR */
            B010 [Local0] = 0xFF
            B0B0 [Local0] = 0x98
            B101 [Local0] = 0x00
            Local0++
            B010 [Local0] = 0xFF
            B0B0 [Local0] = 0x76
            B101 [Local0] = 0x00
            M214 (__METHOD__, NCUR, BSZ0)
            N000--
            NCUR++
        }
    }

    /* CreateDWordField */
    /* */
    /* <test name>, */
    /* <index of byte>, */
    /* <byte size of buf> */
    Method (M216, 3, Serialized)
    {
        Name (PR00, 0x00)
        If (PR00)
        {
            Debug = "========:"
            Debug = Arg1
            Debug = Arg2
        }

        Name (B001, Buffer (Arg2){})
        Name (B002, Buffer (Arg2){})
        CreateDWordField (B001, Arg1, F001)
        /*////////////// A. 1->0 (010->000) */

        B001 = B010 /* \B010 */
        If (PR00)
        {
            Debug = B001 /* \M216.B001 */
        }

        F001 = 0xFFFFFFFF00000000
        Local0 = F001 /* \M216.F001 */
        If ((Local0 != 0x00))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        B002 = B000 /* \B000 */
        If ((B001 != B002))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If (PR00)
        {
            Debug = B001 /* \M216.B001 */
        }

        /*////////////// B. 1->0 (111->101) */

        B001 = B0FF /* \B0FF */
        If (PR00)
        {
            Debug = B001 /* \M216.B001 */
        }

        F001 = 0x00
        Local0 = F001 /* \M216.F001 */
        If ((Local0 != 0x00))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        B002 = B101 /* \B101 */
        If ((B001 != B002))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If (PR00)
        {
            Debug = B001 /* \M216.B001 */
        }

        /*////////////// C. 0->1 (101->111) */

        B001 = B101 /* \B101 */
        If (PR00)
        {
            Debug = B001 /* \M216.B001 */
        }

        F001 = 0xFFFFFFFF
        Local0 = F001 /* \M216.F001 */
        If ((Local0 != 0xFFFFFFFF))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, 0xFFFFFFFF)
        }

        B002 = B0FF /* \B0FF */
        If ((B001 != B002))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If (PR00)
        {
            Debug = B001 /* \M216.B001 */
        }

        /*////////////// D. 0->1 (000->010) */

        B001 = B000 /* \B000 */
        If (PR00)
        {
            Debug = B001 /* \M216.B001 */
        }

        F001 = 0xFFFFFFFFFFFFFFFF
        Local0 = F001 /* \M216.F001 */
        If ((Local0 != 0xFFFFFFFF))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, 0xFFFFFFFF)
        }

        B002 = B010 /* \B010 */
        If ((B001 != B002))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If (PR00)
        {
            Debug = B001 /* \M216.B001 */
        }

        Local0 = SizeOf (B001)
        If ((Local0 != Arg2))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, Arg2)
        }

        Local0 = SizeOf (B002)
        If ((Local0 != Arg2))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, Arg2)
        }

        /*////////////// E. 0->1 (000->010) */

        B001 = B000 /* \B000 */
        If (PR00)
        {
            Debug = B001 /* \M216.B001 */
        }

        F001 = 0xFFFFFFFF32547698
        Local0 = F001 /* \M216.F001 */
        If ((Local0 != 0x32547698))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, 0x32547698)
        }

        B002 = B0B0 /* \B0B0 */
        If ((B001 != B002))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If (PR00)
        {
            Debug = B001 /* \M216.B001 */
        }

        /* Common features */

        Local0 = SizeOf (B001)
        If ((Local0 != Arg2))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, Arg2)
        }

        Local0 = SizeOf (B002)
        If ((Local0 != Arg2))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, Arg2)
        }

        Local0 = ObjectType (F001)
        If ((Local0 != C016))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, C016)
        }

        If (PR00)
        {
            Debug = Local0
        }
    }

    Method (M217, 0, Serialized)
    {
        Debug = "TEST: m217, Create 32-Bit Buffer Field:"
        /* Size of buffer (in bytes) */

        Name (BSZ0, 0x00)
        BSZ0 = BS00 /* \BS00 */
        /* Max steps to check */

        Name (BSZ1, 0x00)
        /* How many elements to check */

        Name (N000, 0x00)
        Name (NCUR, 0x00)
        N000 = (BSZ0 - 0x03)
        BSZ1 = N000 /* \M217.N000 */
        While (N000)
        {
            If ((NCUR >= BSZ1))
            {
                ERR (__METHOD__, Z001, __LINE__, 0x00, 0x00, NCUR, BSZ1)
                Break
            }

            B010 = B000 /* \B000 */
            B0B0 = B000 /* \B000 */
            B101 = B0FF /* \B0FF */
            Local0 = NCUR /* \M217.NCUR */
            B010 [Local0] = 0xFF
            B0B0 [Local0] = 0x98
            B101 [Local0] = 0x00
            Local0++
            B010 [Local0] = 0xFF
            B0B0 [Local0] = 0x76
            B101 [Local0] = 0x00
            Local0++
            B010 [Local0] = 0xFF
            B0B0 [Local0] = 0x54
            B101 [Local0] = 0x00
            Local0++
            B010 [Local0] = 0xFF
            B0B0 [Local0] = 0x32
            B101 [Local0] = 0x00
            M216 (__METHOD__, NCUR, BSZ0)
            N000--
            NCUR++
        }
    }

    /* CreateQWordField */
    /* */
    /* <test name>, */
    /* <index of byte>, */
    /* <byte size of buf> */
    Method (M218, 3, Serialized)
    {
        Name (PR00, 0x00)
        Name (ERR0, 0x00)
        ERR0 = ERRS /* \ERRS */
        Name (BB00, Buffer (0x08){})
        /*	Name(bb01, Buffer(8) {0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff}) */

        Name (BB01, Buffer (0x08)
        {
             0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00   // ........
        })
        /*	Name(bb02, Buffer(8) {0x98,0x76,0x54,0x32,0x10,0xAB,0xCD,0xEF}) */

        Name (BB02, Buffer (0x08)
        {
             0x98, 0x76, 0x54, 0x32, 0x00, 0x00, 0x00, 0x00   // .vT2....
        })
        If (PR00)
        {
            Debug = "========:"
            Debug = Arg1
            Debug = Arg2
        }

        Name (B001, Buffer (Arg2){})
        Name (B002, Buffer (Arg2){})
        CreateQWordField (B001, Arg1, F001)
        /*
         * Create Field to the part of b002 which is set to
         * zero by storing Integer into f001 in 32-bit mode.
         */
        CreateDWordField (B002, (Arg1 + 0x04), F321)
        /*////////////// A. 1->0 (010->000) */

        B001 = B010 /* \B010 */
        If (PR00)
        {
            Debug = "======== 1:"
            Debug = B001 /* \M218.B001 */
        }

        F001 = 0x00
        Local0 = F001 /* \M218.F001 */
        If ((F64 == 0x01))
        {
            If ((Local0 != 0x00))
            {
                ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, 0x00)
            }
        }
        ElseIf ((Local0 != BB00))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        B002 = B000 /* \B000 */
        If ((B001 != B002))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If (PR00)
        {
            Debug = "======== 2:"
            Debug = B001 /* \M218.B001 */
        }

        /*////////////// B. 1->0 (111->101) */

        B001 = B0FF /* \B0FF */
        If (PR00)
        {
            Debug = "======== 3:"
            Debug = B001 /* \M218.B001 */
        }

        F001 = 0x00
        Local0 = F001 /* \M218.F001 */
        If ((F64 == 0x01))
        {
            If ((Local0 != 0x00))
            {
                ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, 0x00)
            }
        }
        ElseIf ((Local0 != BB00))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        B002 = B101 /* \B101 */
        If ((B001 != B002))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If (PR00)
        {
            Debug = "======== 4:"
            Debug = B001 /* \M218.B001 */
        }

        /*////////////// C. 0->1 (101->111) */

        B001 = B101 /* \B101 */
        If (PR00)
        {
            Debug = "======== 5:"
            Debug = B001 /* \M218.B001 */
        }

        F001 = 0xFFFFFFFFFFFFFFFF
        /*	Store(bb01, f001) */

        Local0 = F001 /* \M218.F001 */
        If ((F64 == 0x01))
        {
            If ((Local0 != 0xFFFFFFFFFFFFFFFF))
            {
                ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, 0xFFFFFFFFFFFFFFFF)
            }
        }
        ElseIf ((Local0 != BB01))
        {
            If (PR00)
            {
                Debug = "=========================:"
                Debug = Local0
                Debug = BB01 /* \M218.BB01 */
                Debug = "=========================."
            }

            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        B002 = B0FF /* \B0FF */
        If ((F64 == 0x00))
        {
            /* 32-bit mode update of b002 */

            F321 = 0x00
        }

        If ((B001 != B002))
        {
            If (PR00)
            {
                Debug = "=========================:"
                Debug = B001 /* \M218.B001 */
                Debug = B002 /* \M218.B002 */
                Debug = "=========================."
            }

            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If (PR00)
        {
            Debug = "======== 6:"
            Debug = B001 /* \M218.B001 */
        }

        /*////////////// D. 0->1 (000->010) */

        B001 = B000 /* \B000 */
        If (PR00)
        {
            Debug = "======== 7:"
            Debug = F001 /* \M218.F001 */
            Debug = B001 /* \M218.B001 */
            Debug = BB01 /* \M218.BB01 */
        }

        F001 = 0xFFFFFFFFFFFFFFFF
        /*	Store(bb01, f001) */
        /*	Store(0xefcdab1032547698, f001) */
        /*	Store(0x8888888888888888, f001) */
        /*	Store(0x7777777777777777, f001) */
        /*	Store(0x0f0f0f0f0f0f0f0f, f001) */
        /*	Store(0xf0f0f0f0f0f0f0f0, f001) */
        /*	Store(0x7fffffffffffffff, f001) */
        If (PR00)
        {
            Debug = "======== 8:"
            Debug = Local0
            Debug = F001 /* \M218.F001 */
            Debug = B001 /* \M218.B001 */
            Debug = BB01 /* \M218.BB01 */
        }

        Local0 = F001 /* \M218.F001 */
        If ((F64 == 0x01))
        {
            If ((Local0 != 0xFFFFFFFFFFFFFFFF))
            {
                ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, 0xFFFFFFFFFFFFFFFF)
            }
        }
        ElseIf ((Local0 != BB01))
        {
            If (PR00)
            {
                Debug = "=========================:"
                Debug = Local0
                Debug = BB01 /* \M218.BB01 */
                Debug = "=========================."
            }

            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        B002 = B010 /* \B010 */
        If ((F64 == 0x00))
        {
            /* 32-bit mode update of b002 */

            F321 = 0x00
        }

        If ((B001 != B002))
        {
            If (PR00)
            {
                Debug = "=========================:"
                Debug = B001 /* \M218.B001 */
                Debug = B002 /* \M218.B002 */
                Debug = "=========================."
            }

            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If (PR00)
        {
            Debug = "======== 9:"
            Debug = B001 /* \M218.B001 */
        }

        Local0 = SizeOf (B001)
        If ((Local0 != Arg2))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, Arg2)
        }

        Local0 = SizeOf (B002)
        If ((Local0 != Arg2))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, Arg2)
        }

        /*////////////// E. 0->1 (000->010) */

        B001 = B000 /* \B000 */
        If (PR00)
        {
            Debug = "======== 10:"
            Debug = F001 /* \M218.F001 */
            Debug = B001 /* \M218.B001 */
            Debug = BB02 /* \M218.BB02 */
        }

        F001 = 0xEFCDAB1032547698
        /*	Store(0xffffffffffffffff, f001) */

        Local0 = F001 /* \M218.F001 */
        If (PR00)
        {
            Debug = "======== 11:"
            Debug = Local0
            Debug = F001 /* \M218.F001 */
            Debug = B001 /* \M218.B001 */
            Debug = BB02 /* \M218.BB02 */
        }

        If ((F64 == 0x01))
        {
            If ((Local0 != 0xEFCDAB1032547698))
            {
                ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, 0xEFCDAB1032547698)
            }
        }
        ElseIf ((Local0 != BB02))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        B002 = B0B0 /* \B0B0 */
        If ((F64 == 0x00))
        {
            /* 32-bit mode update of b002 */

            F321 = 0x00
        }

        If ((B001 != B002))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        If (PR00)
        {
            Debug = "======== 12:"
            Debug = B001 /* \M218.B001 */
            Debug = B002 /* \M218.B002 */
        }

        /* Common features */

        Local0 = SizeOf (B001)
        If ((Local0 != Arg2))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, Arg2)
        }

        Local0 = SizeOf (B002)
        If ((Local0 != Arg2))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, Arg2)
        }

        Local0 = ObjectType (F001)
        If ((Local0 != C016))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, C016)
        }

        If (PR00)
        {
            Debug = "======== 13:"
            Debug = Local0
        }

        If ((ERRS != ERR0))
        {
            Local0 = 0x01
        }
        Else
        {
            Local0 = 0x00
        }

        Return (Local0)
    }

    Method (M219, 0, Serialized)
    {
        Debug = "TEST: m219, Create 64-Bit Buffer Field:"
        /* Size of buffer (in bytes) */

        Name (BSZ0, 0x00)
        BSZ0 = BS00 /* \BS00 */
        /* Max steps to check */

        Name (BSZ1, 0x00)
        /* How many elements to check */

        Name (N000, 0x00)
        Name (NCUR, 0x00)
        N000 = (BSZ0 - 0x07)
        BSZ1 = N000 /* \M219.N000 */
        While (N000)
        {
            If ((NCUR >= BSZ1))
            {
                ERR (__METHOD__, Z001, __LINE__, 0x00, 0x00, NCUR, BSZ1)
                Break
            }

            B010 = B000 /* \B000 */
            B0B0 = B000 /* \B000 */
            B101 = B0FF /* \B0FF */
            Local0 = NCUR /* \M219.NCUR */
            B010 [Local0] = 0xFF
            B0B0 [Local0] = 0x98
            B101 [Local0] = 0x00
            Local0++
            B010 [Local0] = 0xFF
            B0B0 [Local0] = 0x76
            B101 [Local0] = 0x00
            Local0++
            B010 [Local0] = 0xFF
            B0B0 [Local0] = 0x54
            B101 [Local0] = 0x00
            Local0++
            B010 [Local0] = 0xFF
            B0B0 [Local0] = 0x32
            B101 [Local0] = 0x00
            Local0++
            B010 [Local0] = 0xFF
            B0B0 [Local0] = 0x10
            B101 [Local0] = 0x00
            Local0++
            B010 [Local0] = 0xFF
            B0B0 [Local0] = 0xAB
            B101 [Local0] = 0x00
            Local0++
            B010 [Local0] = 0xFF
            B0B0 [Local0] = 0xCD
            B101 [Local0] = 0x00
            Local0++
            B010 [Local0] = 0xFF
            B0B0 [Local0] = 0xEF
            B101 [Local0] = 0x00
            If (M218 (__METHOD__, NCUR, BSZ0))
            {
                Return (0x01)
            }

            N000--
            NCUR++
        }

        Return (0x00)
    }

    /* CreateField */
    /* */
    /* <test name>, */
    /* <name of test-package>, */
    /* <index of bit>, */
    /* <num of bits>, */
    /* <byte size of buf> */
    /* <the benchmark buffer for Field comparison with> */
    Method (M21A, 6, Serialized)
    {
        Name (PR00, 0x00)
        If (PR00)
        {
            Debug = "========:"
            Debug = Arg2
            Debug = Arg3
        }

        Name (B001, Buffer (Arg4){})
        Name (B002, Buffer (Arg4){})
        /* Flag of Integer */

        Name (INT1, 0x00)
        CreateField (B001, Arg2, Arg3, F001)

        /* Check Type */

        Local0 = ObjectType (F001)
        If ((Local0 != C016))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, Local0, C016)
        }

        /* Fill the entire buffer (ground) */

        B001 = B0G0 /* \B0G0 */
        If (PR00)
        {
            Debug = B001 /* \M21A.B001 */
        }

        /* Fill into the field of buffer */

        F001 = B0F0 /* \B0F0 */
        Local0 = F001 /* \M21A.F001 */
        /* Crash for 20041105 [Nov  5 2004] */
        /* Store("!!!!!!!!!!!! test is crashing */
        /* here when attempting access pr00:", Debug) */
        If (PR00)
        {
            Debug = "============ 0:"
            Debug = B0G0 /* \B0G0 */
            Debug = B0F0 /* \B0F0 */
            Debug = B0B0 /* \B0B0 */
            Debug = Local0
            Debug = B001 /* \M21A.B001 */
            Debug = "============."
        }

        /* Check the contents of field */

        If (Local0 != Arg5)
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        /* Check the contents of Buffer */

        B002 = B0B0 /* \B0B0 */
        If ((B001 != B002))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, 0x00, 0x00)
            If (PR00)
            {
                Debug = "EEEEEEEEEEEEEEEEEEEEEEEEEEEEEEE:"
                Debug = B0G0 /* \B0G0 */
                Debug = B0F0 /* \B0F0 */
                Debug = B0B0 /* \B0B0 */
                Debug = B001 /* \M21A.B001 */
                Debug = "RRRRRRRRRRRRRRRRRRRRRRRRRRRRRRR."
            }
        }

        /* Common features */
        /* Add "Common features" here too. */
        Return (Zero)
    }

    /* <test name>, */
    /* <name of test-package>, */
    /* <index of bit>, */
    /* <num of bits>, */
    /* <opcode of buffer to fill the ground> */
    /* <opcode of buffer to fill the field> */
    Method (M21B, 6, Serialized)
    {
        Name (PR00, 0x00)
        Name (INT2, 0x00)
        /* For loop 1 */

        Name (LPN1, 0x00)
        Name (LPC1, 0x00)
        /* For loop 2 */

        Name (LPN2, 0x00)
        Name (LPC2, 0x00)
        /* <entire byte size of buffer> */

        Name (BSZ0, 0x00)
        BSZ0 = BS00 /* \BS00 */
        /* byte size of field */

        Name (BSF0, 0x00)
        /* byte size of buffer affected by field */

        Name (BSB0, 0x00)
        /* index of the first byte of field in the buffer */

        Name (FB00, 0x00)
        /* index of the last byte of field in the buffer */

        Name (LB00, 0x00)
        /* Num of bits have to be non-zero */

        If ((Arg3 == 0x00))
        {
            ERR (Arg0, Z001, __LINE__, 0x00, 0x00, 0x00, 0x00)
            Return (Ones)
        }

        BSB0 = MBS0 (Arg2, Arg3)
        /* ========================================= */
        /* Prepare the buffer for filling the ground */
        /* ========================================= */
        Switch (ToInteger (Arg4))
        {
            Case (0x00)
            {
                B0G0 = B000 /* \B000 */
            }
            Case (0x01)
            {
                B0G0 = B0FF /* \B0FF */
            }
            Default
            {
                B0G0 = B256 /* \B256 */
            }

        }

        /* ========================================================== */
        /* Prepare the buffer for filling the field (over the ground) */
        /* ========================================================== */
        Switch (ToInteger (Arg5))
        {
            Case (0x00)
            {
                B0F0 = B000 /* \B000 */
            }
            Case (0x01)
            {
                B0F0 = B0FF /* \B0FF */
            }
            Default
            {
                B0F0 = B256 /* \B256 */
            }

        }

        /* ====================================================== */
        /* Prepare the benchmark buffer for Field COMPARISON with */
        /* Result in Local6 */
        /* ====================================================== */
        /* lpN1 - number of bytes minus one */
        Local0 = Arg3
        Local0--
        Divide (Local0, 0x08, Local7, LPN1) /* \M21B.LPN1 */
        Divide (Arg3, 0x08, Local7, Local0)
        BSF0 = LPN1 /* \M21B.LPN1 */
        BSF0++
        Local6 = Buffer (BSF0){}
        Local0 = DerefOf (B0F0 [LPN1])
        If (Local7)
        {
            Local1 = (0x08 - Local7)
            Local2 = (Local0 << Local1)
            Local3 = (Local2 & 0xFF)
            Local0 = (Local3 >> Local1)
        }

        Local6 [LPN1] = Local0
        LPC1 = 0x00
        While (LPN1)
        {
            Local0 = DerefOf (B0F0 [LPC1])
            Local6 [LPC1] = Local0
            LPN1--
            LPC1++
        }

        /* ================================================ */
        /* Prepare the benchmark buffer for comparison with */
        /* ================================================ */
        B0B0 = B0G0 /* \B0G0 */
        Divide (Arg2, 0x08, Local1, FB00) /* \M21B.FB00 */
        Local2 = DerefOf (B0B0 [FB00])
        LB00 = BSB0 /* \M21B.BSB0 */
        LB00--
        Local3 = DerefOf (B0B0 [LB00])
        Local0 = SFT1 (Local6, Local1, Arg3, Local2, Local3)
        Local2 = FB00 /* \M21B.FB00 */
        LPN2 = SizeOf (Local0)
        LPC2 = 0x00
        While (LPN2)
        {
            Local1 = DerefOf (Local0 [LPC2])
            B0B0 [Local2] = Local1
            Local2++
            LPN2--
            LPC2++
        }

        M21A (Arg0, Arg1, Arg2, Arg3, BSZ0, Local6)
        Return (Zero)
    }

    Method (M21C, 4, Serialized)
    {
        /* For loop 0 */

        Name (LPN0, 0x00)
        Name (LPC0, 0x00)
        /* For loop 1 */

        Name (LPN1, 0x00)
        Name (LPC1, 0x00)
        /* For loop 2 */

        Name (LPN2, 0x00)
        Name (LPC2, 0x00)
        /* Index of bit */

        Name (IB00, 0x00)
        /* Number of bits */

        Name (NB00, 0x00)
        LPN0 = Arg1
        LPC0 = 0x00
        While (LPN0)
        {
            /* Operands */

            Local6 = (LPC0 * 0x06)
            IB00 = DerefOf (Arg3 [Local6])
            Local6++
            LPN1 = DerefOf (Arg3 [Local6])
            Local6++
            Local0 = DerefOf (Arg3 [Local6])
            Local6++
            Local1 = DerefOf (Arg3 [Local6])
            Local6++
            Local2 = DerefOf (Arg3 [Local6])
            Local6++
            Local3 = DerefOf (Arg3 [Local6])
            LPC1 = 0x00
            While (LPN1)
            {
                NB00 = Local0
                LPN2 = Local1
                LPC2 = 0x00
                While (LPN2)
                {
                    M21B (Arg0, Arg2, IB00, NB00, Local2, Local3)
                    NB00++
                    LPN2--
                    LPC2++
                }

                IB00++
                LPN1--
                LPC1++
            }

            LPC0++
            LPN0--
        }
    }

    Method (M21D, 0, Serialized)
    {
        Debug = "TEST: m21d, Create Arbitrary Length Buffer Field:"
        /* Layout of Package: */
        /* - <first index of bit>, */
        /* - <num of indexes of bits>, */
        /* - <first num of bits>, */
        /* - <num of num of bits>, */
        /* - opcode of buffer to fill the ground */
        /* - opcode of buffer to fill the field */
        /*   Opcodes of buffers: */
        /*     0 - all zeros */
        /*     1 - all units */
        /*     2 - some mix */
        Name (P000, Package (0x06)
        {
            0x00,
            0x08,
            0x01,
            0x50,
            0x01,
            0x02
                /* try for 32-bit, 64-bit: */
        /*		1, 1, 0x28, 1, 1, 2, */
        /*		1, 1, 0x48, 1, 1, 2, */
        /* try for 32-bit, 64-bit: */
        /*		4, 1, 0x200, 1, 1, 2, */
        /*		6, 1, 0x69, 1, 1, 2, */
        /* examines the whole range possible for the size */
        /* of the unerlying 256-byte Buffer: */
        /*		0, 17, 1, 2032, 1, 2, */
        /*		0, 1, 1, 1, 1, 2, */
        /*		0, 10, 1, 30, 1, 2, */
        /*		1, 1, 1, 90, 1, 2, */
        /*		1, 1, 40, 1, 1, 2, */
        /*		1, 1, 1, 39, 1, 2, */
        /*		1, 1, 1, 40, 1, 2, */
        /*		1, 1, 40, 1, 0, 2, */
        /*		0, 1, 1, 65, 0, 1, */
        })
        M21C (__METHOD__, 0x01, "p000", P000)
    }

    /* Run-method */

    Method (CBF0, 0, NotSerialized)
    {
        SRMT ("m211")
        M211 ()
        SRMT ("m213")
        M213 ()
        SRMT ("m215")
        M215 ()
        SRMT ("m217")
        M217 ()
        SRMT ("m219")
        M219 ()
        SRMT ("m21d")
        M21D ()
    }
