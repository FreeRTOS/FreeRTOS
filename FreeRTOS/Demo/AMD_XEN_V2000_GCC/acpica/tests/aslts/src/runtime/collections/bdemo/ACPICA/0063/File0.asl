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
     * ToInteger(<0x-hex-dec>)
     */
    Method (MF92, 0, NotSerialized)
    {
        /* Hex: 0x - dec */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        ToInteger ("0x0", Local0)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        ToInteger ("0x0000000", Local0)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        ToInteger ("0x1", Local0)
        If ((Local0 != 0x01))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x01)
        }

        ToInteger ("0x12345678", Local0)
        If ((Local0 != 0x12345678))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x12345678)
        }

        ToInteger ("0x12345", Local0)
        If ((Local0 != 0x00012345))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00012345)
        }

        If (F64)
        {
            Local1 = "0x1234567890123456"
            ToInteger (Local1, Local0)
            If ((Local0 != 0x1234567890123456))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1234567890123456)
            }

            Local1 = "0x123456789012345"
            ToInteger (Local1, Local0)
            If ((Local0 != 0x0123456789012345))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x0123456789012345)
            }
        }

        /* Hex: 0x - hex */

        ToInteger ("0xabcdefef", Local0)
        If ((Local0 != 0xABCDEFEF))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xABCDEFEF)
        }

        ToInteger ("0xabcdef", Local0)
        If ((Local0 != 0x00ABCDEF))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00ABCDEF)
        }

        If (F64)
        {
            Local1 = "0xabcdefefadefbcdf"
            ToInteger (Local1, Local0)
            If ((Local0 != 0xABCDEFEFADEFBCDF))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xABCDEFEFADEFBCDF)
            }

            Local1 = "0xabcdefefadefbcd"
            ToInteger (Local1, Local0)
            If ((Local0 != 0x0ABCDEFEFADEFBCD))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x0ABCDEFEFADEFBCD)
            }
        }

        /* Hex: 0x - dec/hex */

        ToInteger ("0x1ab2cd34", Local0)
        If ((Local0 != 0x1AB2CD34))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1AB2CD34)
        }

        If (F64)
        {
            Local1 = "0x1ab2cd340fe05678"
            ToInteger (Local1, Local0)
            If ((Local0 != 0x1AB2CD340FE05678))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1AB2CD340FE05678)
            }

            Local1 = "0x1ab2cd340fe0"
            ToInteger (Local1, Local0)
            If ((Local0 != 0x00001AB2CD340FE0))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00001AB2CD340FE0)
            }
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
    }

    /*
     * ToInteger(<dec>)
     */
    Method (MF93, 0, NotSerialized)
    {
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        ToInteger ("0", Local0)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        ToInteger ("0000000", Local0)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        ToInteger ("000000000000000", Local0)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        ToInteger ("000000000000000000000000000000000000000000", Local0)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        ToInteger ("1", Local0)
        If ((Local0 != 0x01))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x01)
        }

        ToInteger ("1234567890", Local0)
        If ((Local0 != 0x499602D2))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x499602D2)
        }

        ToInteger ("1234567", Local0)
        If ((Local0 != 0x0012D687))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x0012D687)
        }

        ToInteger ("4294967295", Local0)
        If ((Local0 != 0xFFFFFFFF))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xFFFFFFFF)
        }

        If (F64)
        {
            Local1 = "18446744073709551615"
            ToInteger (Local1, Local0)
            If ((Local0 != 0xFFFFFFFFFFFFFFFF))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xFFFFFFFFFFFFFFFF)
            }
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
    }

    /*
     * White space before image of Data is skipped
     * (all examples above).
     */
    Method (MF94, 0, NotSerialized)
    {
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        ToInteger ("                    0x0", Local0)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        ToInteger ("                    0x00000", Local0)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        ToInteger (" 0x1", Local0)
        If ((Local0 != 0x01))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x01)
        }

        ToInteger ("  0x12345678", Local0)
        If ((Local0 != 0x12345678))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x12345678)
        }

        ToInteger ("   0x12345", Local0)
        If ((Local0 != 0x00012345))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00012345)
        }

        If (F64)
        {
            Local1 = "    0x1234567890123456"
            ToInteger (Local1, Local0)
            If ((Local0 != 0x1234567890123456))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1234567890123456)
            }

            Local1 = "    0x123456789012345"
            ToInteger (Local1, Local0)
            If ((Local0 != 0x0123456789012345))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x0123456789012345)
            }
        }

        ToInteger ("     0xabcdefef", Local0)
        If ((Local0 != 0xABCDEFEF))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xABCDEFEF)
        }

        ToInteger ("      0xabcdef", Local0)
        If ((Local0 != 0x00ABCDEF))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00ABCDEF)
        }

        ToInteger ("\t0xabcdef", Local0)
        If ((Local0 != 0x00ABCDEF))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00ABCDEF)
        }

        If (F64)
        {
            Local1 = "       0xabcdefefadefbcdf"
            ToInteger (Local1, Local0)
            If ((Local0 != 0xABCDEFEFADEFBCDF))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xABCDEFEFADEFBCDF)
            }

            Local1 = "       0xabcdefefadefbcd"
            ToInteger (Local1, Local0)
            If ((Local0 != 0x0ABCDEFEFADEFBCD))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x0ABCDEFEFADEFBCD)
            }
        }

        ToInteger ("        0x1ab2cd34", Local0)
        If ((Local0 != 0x1AB2CD34))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1AB2CD34)
        }

        If (F64)
        {
            Local1 = "         0x1ab2cd340fe05678"
            ToInteger (Local1, Local0)
            If ((Local0 != 0x1AB2CD340FE05678))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1AB2CD340FE05678)
            }

            Local1 = "         0x1ab2cd340fe0"
            ToInteger (Local1, Local0)
            If ((Local0 != 0x00001AB2CD340FE0))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00001AB2CD340FE0)
            }
        }

        ToInteger ("          0", Local0)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        ToInteger (" \t0000000", Local0)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        ToInteger ("\t000000000000000", Local0)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        ToInteger (" 000000000000000000000000000000000000000000", Local0)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        ToInteger ("           1", Local0)
        If ((Local0 != 0x01))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x01)
        }

        ToInteger ("            1234567890", Local0)
        If ((Local0 != 0x499602D2))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x499602D2)
        }

        ToInteger ("\t1234567890", Local0)
        If ((Local0 != 0x499602D2))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x499602D2)
        }

        ToInteger ("\t\t\t\t\t\t\t\t\t1234567890", Local0)
        If ((Local0 != 0x499602D2))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x499602D2)
        }

        ToInteger ("  \t           1234567", Local0)
        If ((Local0 != 0x0012D687))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x0012D687)
        }

        ToInteger ("     \t         4294967295", Local0)
        If ((Local0 != 0xFFFFFFFF))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xFFFFFFFF)
        }

        If (F64)
        {
            Local1 = "               \t18446744073709551615"
            ToInteger (Local1, Local0)
            If ((Local0 != 0xFFFFFFFFFFFFFFFF))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xFFFFFFFFFFFFFFFF)
            }
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
    }

    /*
     * Zeros before significant characters in image without '0x' are skipped).
     */
    Method (MF95, 0, NotSerialized)
    {
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        ToInteger ("          0", Local0)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        ToInteger ("          2", Local0)
        If ((Local0 != 0x02))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x02)
        }

        ToInteger ("          0xa", Local0)
        If ((Local0 != 0x0A))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x0A)
        }

        ToInteger ("          04294967295", Local0)
        If ((Local0 != 0xFFFFFFFF))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xFFFFFFFF)
        }

        ToInteger ("04294967295", Local0)
        If ((Local0 != 0xFFFFFFFF))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xFFFFFFFF)
        }

        ToInteger ("000000000000000000004294967295", Local0)
        If ((Local0 != 0xFFFFFFFF))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xFFFFFFFF)
        }

        ToInteger (" 000000000000000000004294967295", Local0)
        If ((Local0 != 0xFFFFFFFF))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xFFFFFFFF)
        }

        ToInteger ("\t000000000000000000004294967295", Local0)
        If ((Local0 != 0xFFFFFFFF))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xFFFFFFFF)
        }

        ToInteger ("\t \t \t \t \t000000000000000000004294967295", Local0)
        If ((Local0 != 0xFFFFFFFF))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xFFFFFFFF)
        }

        ToInteger ("\t \t \t \t \t04294967295", Local0)
        If ((Local0 != 0xFFFFFFFF))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xFFFFFFFF)
        }

        ToInteger ("\t \t \t \t \t0123456789", Local0)
        If ((Local0 != 0x075BCD15))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x075BCD15)
        }

        ToInteger ("0123456789", Local0)
        If ((Local0 != 0x075BCD15))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x075BCD15)
        }

        ToInteger ("00123456789", Local0)
        If ((Local0 != 0x075BCD15))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x075BCD15)
        }

        If (F64)
        {
            Local1 = "               \t018446744073709551615"
            ToInteger (Local1, Local0)
            If ((Local0 != 0xFFFFFFFFFFFFFFFF))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            Local1 = "018446744073709551615"
            ToInteger (Local1, Local0)
            If ((Local0 != 0xFFFFFFFFFFFFFFFF))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xFFFFFFFFFFFFFFFF)
            }

            Local1 = "000000000000000000000000000000000000000018446744073709551615"
            ToInteger (Local1, Local0)
            If ((Local0 != 0xFFFFFFFFFFFFFFFF))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xFFFFFFFFFFFFFFFF)
            }
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
    }

    /*
     * ToInteger, exceptions
     */
    Method (MF96, 0, NotSerialized)
    {
        /* 5. "1234cd" (non-decimal character in dec-image) */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local1 = "1234cd"
        ToInteger (Local1, Local0)
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        /* 6. "000x1234" (non-decimal character in dec-image) */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local1 = "000x1234"
        ToInteger (Local1, Local0)
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        /* 7. "0x1234cdQ" (non-hex character in '0x'-image) */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local1 = "0x1234cdQ"
        ToInteger (Local1, Local0)
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local1 = "0x0x12345"
        ToInteger (Local1, Local0)
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        /* 8. "1234 " (white space in dec image) */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local1 = "1234 "
        ToInteger (Local1, Local0)
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        /* 9. "0x1234cd " (white space in '0x'-image) */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local1 = "0x1234cd "
        ToInteger (Local1, Local0)
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        /* 10. "0x 1234cdQ" (white space after '0x') */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local1 = "0x 1234"
        ToInteger (Local1, Local0)
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local1 = "0x0x 1234"
        ToInteger (Local1, Local0)
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local1 = "0x0x 0x 1234"
        ToInteger (Local1, Local0)
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local1 = "0x 0x 1234"
        ToInteger (Local1, Local0)
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        /* 11. (decimal image exceeding maximal) */
        /*     32-bit mode – the value exceeding "4294967295" */
        If (!F64)
        {
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local1 = "4294967296"
            ToInteger (Local1, Local0)
            CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local1 = "123456789012345678904294967296"
            ToInteger (Local1, Local0)
            CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local1 = " \t \t\t00004294967296"
            ToInteger (Local1, Local0)
            CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local1 = "\t0123456789012345678904294967296"
            ToInteger (Local1, Local0)
            CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local1 = "0123456789012345678904294967296"
            ToInteger (Local1, Local0)
            CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local1 = " 123456789012345678904294967296"
            ToInteger (Local1, Local0)
            CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local1 = "\t123456789012345678904294967296"
            ToInteger (Local1, Local0)
            CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        }

        /*     64-bit mode – the value exceeding "18446744073709551615" */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local1 = "18446744073709551616"
        ToInteger (Local1, Local0)
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local1 = "\t18446744073709551616"
        ToInteger (Local1, Local0)
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local1 = " 18446744073709551616"
        ToInteger (Local1, Local0)
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local1 = "018446744073709551616"
        ToInteger (Local1, Local0)
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local1 = " \t000000000018446744073709551616"
        ToInteger (Local1, Local0)
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        /* 12. "0x12345678901234567" (hex image exceeding maximal) */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local1 = "0x12345678901234567"
        ToInteger (Local1, Local0)
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        /* 13. "0x00000000000001234" (hex image exceeding maximal; no matter that zeros) */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local1 = "0x00000000000001234"
        ToInteger (Local1, Local0)
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local1 = "0x0000000000000000000001234"
        ToInteger (Local1, Local0)
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        /* 14. "0x123456789" (hex image exceeding maximal; for 32-bit mode only) */

        If (!F64)
        {
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local1 = "0x123456789"
            ToInteger (Local1, Local0)
            CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        }

        /* 15. "0x" (incomplete '0x' image) */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local1 = "0x"
        ToInteger (Local1, Local0)
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local1 = "0x "
        ToInteger (Local1, Local0)
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local1 = "0x\t"
        ToInteger (Local1, Local0)
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local1 = "0x 1234"
        ToInteger (Local1, Local0)
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local1 = "0x\t1234"
        ToInteger (Local1, Local0)
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
        /* 16. Empty string */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local1 = ""
        ToInteger (Local1, Local0)
        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
    }
