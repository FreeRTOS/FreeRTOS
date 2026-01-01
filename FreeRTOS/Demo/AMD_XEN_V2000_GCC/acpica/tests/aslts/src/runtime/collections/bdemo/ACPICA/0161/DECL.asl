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
     * Bug 161:
     *
     * SUMMARY: Named object passed as a BitIndex or NumBits to CreateField causes hang
     *
     * ROOT CAUSE
     */
    /* Global CreateField declarations */
    Method (MD8F, 0, NotSerialized)
    {
        If ((BF32 != Buffer(){0x14}))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, BF32, Buffer(){0x14})
        }

        If ((BF33 != Buffer(){0x15, 0x16}))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, BF33, Buffer(){0x15, 0x16})
        }
    }

    Method (MD90, 0, NotSerialized)
    {
        If ((BF34 != Buffer() {0x18}))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, BF34, Buffer(){0x18})
        }

        If ((BF35 != Buffer() {0x19}))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, BF35, Buffer(){0x19})
        }
    }

    Method (MD91, 0, NotSerialized)
    {
        If ((BF36 != Buffer() {0x1A}))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, BF36, Buffer(){0x1A})
        }

        If ((BF37 != Buffer(){0x1B, 0x1C}))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, BF37, Buffer(){0x1B, 0x1C})
        }
    }

    /* Local CreateField declarations, another buffer than used in md8f-md91 */

    Method (MD92, 0, NotSerialized)
    {
        CreateField (BD02, 0x20, ID03, BF32)
        CreateField (BD02, 0x28, (ID03 + 0x08), BF33)
        If ((BF32 != Buffer(){0x14}))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, BF32, Buffer(){0x14})
        }

        If ((BF33 != Buffer(){0x15, 0x16}))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, BF33, Buffer(){0x15, 0x16})
        }
    }

    Method (MD93, 0, NotSerialized)
    {
        CreateField (BD02, ID04, 0x08, BF34)
        CreateField (BD02, (ID04 + 0x08), 0x08, BF35)
        If ((BF34 != Buffer() {0x18}))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, BF34, Buffer(){0x18})
        }

        If ((BF35 != Buffer() {0x19}))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, BF35, Buffer(){0x19})
        }
    }

    Method (MD94, 0, NotSerialized)
    {
        CreateField (BD02, ID05, ID06, BF36)
        CreateField (BD02, (ID07 + 0x08), (ID08 + 0x08), BF37)
        If ((BF36 != Buffer() {0x1A}))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, BF36, Buffer(){0x1A})
        }

        If ((BF37 != Buffer(){0x1B, 0x1C}))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, BF37, Buffer(){0x1B, 0x1C})
        }
    }

    /* Local CreateField declarations, the same buffer that used in md8f-md91 */

    Method (MD95, 0, NotSerialized)
    {
        CreateField (BD03, 0x20, ID03, BF32)
        CreateField (BD03, 0x28, (ID03 + 0x08), BF33)
        If ((BF32 != Buffer(){0x14}))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, BF32, Buffer(){0x14})
        }

        If ((BF33 != Buffer(){0x15, 0x16}))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, BF33, Buffer(){0x15, 0x16})
        }
    }

    Method (MD96, 0, NotSerialized)
    {
        CreateField (BD03, ID04, 0x08, BF34)
        CreateField (BD03, (ID04 + 0x08), 0x08, BF35)
        If ((BF34 != Buffer() {0x18}))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, BF34, Buffer(){0x18})
        }

        If ((BF35 != Buffer() {0x19}))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, BF35, Buffer(){0x19})
        }
    }

    Method (MD97, 0, NotSerialized)
    {
        CreateField (BD03, ID05, ID06, BF36)
        CreateField (BD03, (ID07 + 0x08), (ID08 + 0x08), BF37)
        If ((BF36 != Buffer() {0x1A}))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, BF36, Buffer(){0x1A})
        }

        If ((BF37 != Buffer(){0x1B, 0x1C}))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, BF37, Buffer(){0x1B, 0x1C})
        }
    }

    Method (M075, 6, Serialized)
    {
        Name (B000, Buffer (0x08)
        {
             0x5D, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18   // ].......
        })
        If ((Arg0 != 0x01))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Arg0, 0x01)
        }

        If ((Arg1 != 0x5D))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Arg1, 0x5D)
        }

        If ((Arg2 != 0x125D))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Arg2, 0x125D)
        }

        If ((Arg3 != 0x1413125D))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Arg3, 0x1413125D)
        }

        If (F64)
        {
            If ((Arg4 != 0x181716151413125D))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Arg4, 0x181716151413125D)
            }
        }
        ElseIf ((Arg4 != B000))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Arg4, B000)
        }

        If ((Arg5 != Buffer(){0x5D}))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Arg5, Buffer(){0x5D})
        }
    }

    Method (M076, 2, NotSerialized)
    {
        If ((Arg0 != Buffer(){0x5D}))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Arg0, Buffer(){0x5D})
        }

        If ((Arg1 != Buffer(){0x5D}))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Arg1, Buffer(){0x5D})
        }
    }

    Method (MD98, 0, NotSerialized)
    {
        MD8F ()
        MD90 ()
        MD91 ()
        MD92 ()
        MD93 ()
        MD94 ()
        MD95 ()
        MD96 ()
        MD97 ()
    }

    Method (MF7F, 0, NotSerialized)
    {
        SRMT ("mf7f-0")
        M075 (BF40, BF41, BF42, BF43, BF44, BF45)
        SRMT ("mf7f-1")
        M075 (BF46, BF47, BF48, BF49, BF4A, BF4B)
        M076 (BF4C, BF4D)
    }

    Method (M077, 0, Serialized)
    {
        CreateBitField (BD03, 0x08, BF40)
        CreateByteField (BD03, 0x01, BF41)
        CreateWordField (BD03, 0x01, BF42)
        CreateDWordField (BD03, 0x01, BF43)
        CreateQWordField (BD03, 0x01, BF44)
        CreateField (BD03, 0x08, 0x08, BF45)
        Name (ID21, 0x01)
        Name (ID22, 0x08)
        CreateBitField (BD03, ID22, BF46)
        CreateByteField (BD03, ID21, BF47)
        CreateWordField (BD03, ID21, BF48)
        CreateDWordField (BD03, ID21, BF49)
        CreateQWordField (BD03, ID21, BF4A)
        CreateField (BD03, 0x08, ID22, BF4B)
        CreateField (BD03, ID22, 0x08, BF4C)
        CreateField (BD03, ID22, ID22, BF4D)
        SRMT ("m077-0")
        M075 (BF40, BF41, BF42, BF43, BF44, BF45)
        SRMT ("m077-1")
        M075 (BF46, BF47, BF48, BF49, BF4A, BF4B)
        M076 (BF4C, BF4D)
    }

    Method (MF83, 0, NotSerialized)
    {
        Local0 = 0x01
        Local1 = 0x08
        CreateBitField (BD03, Local1, BF46)
        CreateByteField (BD03, Local0, BF47)
        CreateWordField (BD03, Local0, BF48)
        CreateDWordField (BD03, Local0, BF49)
        CreateQWordField (BD03, Local0, BF4A)
        CreateField (BD03, 0x08, Local1, BF4B)
        CreateField (BD03, Local1, 0x08, BF4C)
        CreateField (BD03, Local1, Local1, BF4D)
        SRMT ("mf83")
        M075 (BF46, BF47, BF48, BF49, BF4A, BF4B)
        M076 (BF4C, BF4D)
    }

    Method (MF84, 2, NotSerialized)
    {
        CreateBitField (BD03, Arg1, BF46)
        CreateByteField (BD03, Arg0, BF47)
        CreateWordField (BD03, Arg0, BF48)
        CreateDWordField (BD03, Arg0, BF49)
        CreateQWordField (BD03, Arg0, BF4A)
        CreateField (BD03, 0x08, Arg1, BF4B)
        CreateField (BD03, Arg1, 0x08, BF4C)
        CreateField (BD03, Arg1, Arg1, BF4D)
        SRMT ("mf84")
        M075 (BF46, BF47, BF48, BF49, BF4A, BF4B)
        M076 (BF4C, BF4D)
    }
