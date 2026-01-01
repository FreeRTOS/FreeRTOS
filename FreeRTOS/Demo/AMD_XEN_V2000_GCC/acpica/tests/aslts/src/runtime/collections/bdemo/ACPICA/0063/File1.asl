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
     * Implicit String to Integer (<0x-hex-dec>)
     */
    Method (MF97, 0, NotSerialized)
    {
        /* Hex: 0x - dec */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        Local0 = ("0x0" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        Local0 = ("0x1" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        Local0 = ("0x12345678" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        Local0 = ("0x1234567890123456" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        /* Hex: 0x - hex */

        Local0 = ("0xabcdefef" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        Local0 = ("0xabcdefefadefbcdf" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        /* Hex: 0x - dec/hex */

        Local0 = ("0x1ab2cd340fe05678" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("0x1ab2cd340fe0567823456789123456789987" + 0x00)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
    }

    /*
     * Implicit String to Integer (<dec>)
     */
    Method (MF98, 0, NotSerialized)
    {
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("0" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("0000000" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("000000000000000000000000000000" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("1" + 0x00)
        If ((Local0 != 0x01))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x01)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("12345678" + 0x00)
        If ((Local0 != 0x12345678))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x12345678)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
    }

    /*
     * Implicit String to Integer (<hex-dec>)
     */
    Method (MF99, 0, NotSerialized)
    {
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        /* Hex: 0x - dec */

        Local0 = ("1234567890123456" + 0x00)
        If (F64)
        {
            If ((Local0 != 0x1234567890123456))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1234567890123456)
            }
        }
        ElseIf ((Local0 != 0x12345678))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x12345678)
        }

        /* Hex: 0x - hex */

        Local0 = ("abcdefef" + 0x00)
        If ((Local0 != 0xABCDEFEF))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xABCDEFEF)
        }

        Local0 = ("abcdefe" + 0x00)
        If ((Local0 != 0x0ABCDEFE))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x0ABCDEFE)
        }

        Local0 = ("abcdefefadefbcdf" + 0x00)
        If (F64)
        {
            If ((Local0 != 0xABCDEFEFADEFBCDF))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xABCDEFEFADEFBCDF)
            }
        }
        ElseIf ((Local0 != 0xABCDEFEF))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xABCDEFEF)
        }

        /* Hex: 0x - dec/hex */

        Local0 = ("1ab2cd340fe05678" + 0x00)
        If (F64)
        {
            If ((Local0 != 0x1AB2CD340FE05678))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1AB2CD340FE05678)
            }
        }
        ElseIf ((Local0 != 0x1AB2CD34))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1AB2CD34)
        }

        Local0 = ("1ab2cd340fe05" + 0x00)
        If (F64)
        {
            If ((Local0 != 0x0001AB2CD340FE05))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x0001AB2CD340FE05)
            }
        }
        ElseIf ((Local0 != 0x1AB2CD34))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1AB2CD34)
        }

        Local0 = ("1a" + 0x00)
        If ((Local0 != 0x1A))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1A)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
    }

    /*
     * No exceptions in special cases which force exceptions on ToInteger
     */
    Method (MF9A, 0, NotSerialized)
    {
        /* 5. "1234cd" (non-decimal character in dec-image) */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("1234cd" + 0x00)
        If ((Local0 != 0x001234CD))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x001234CD)
        }

        /* 6. "000x1234" (non-decimal character in dec-image) */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("000x1234" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        /* 7. "0x1234cdQ" (non-hex character in '0x'-image) */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("0x1234cdQ" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("1234cdQ" + 0x00)
        If ((Local0 != 0x001234CD))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x001234CD)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("0x0x12345" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        /* 8. "1234 " (white space in dec image) */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("1234 " + 0x00)
        If ((Local0 != 0x1234))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1234)
        }

        /* 9. "0x1234cd " (white space in '0x'-image) */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("1234cd " + 0x00)
        If ((Local0 != 0x001234CD))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x001234CD)
        }

        /* 10. "0x 1234cdQ" (white space after '0x') */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("0x 1234" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("0x0x 1234" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("0x0x 0x 1234" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("0x 0x 1234" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        /* 11. (decimal image exceeding maximal) */
        /*     32-bit mode – the value exceeding "4294967295" */
        If (0x01)
        {
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local0 = ("4294967296" + 0x00)
            If (F64)
            {
                If ((Local0 != 0x0000004294967296))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x0000004294967296)
                }
            }
            ElseIf ((Local0 != 0x42949672))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x42949672)
            }

            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local0 = ("123456789012345678904294967296" + 0x00)
            If (F64)
            {
                If ((Local0 != 0x1234567890123456))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1234567890123456)
                }
            }
            ElseIf ((Local0 != 0x12345678))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x12345678)
            }

            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local0 = (" \t \t\t00004294967296" + 0x00)
            If (F64)
            {
                If ((Local0 != 0x0000004294967296))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x0000004294967296)
                }
            }
            ElseIf ((Local0 != 0x42949672))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x42949672)
            }

            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local0 = ("\t0123456789012345678904294967296" + 0x00)
            If (F64)
            {
                If ((Local0 != 0x1234567890123456))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1234567890123456)
                }
            }
            ElseIf ((Local0 != 0x12345678))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x12345678)
            }

            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local0 = ("0123456789012345678904294967296" + 0x00)
            If (F64)
            {
                If ((Local0 != 0x1234567890123456))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1234567890123456)
                }
            }
            ElseIf ((Local0 != 0x12345678))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x12345678)
            }

            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local0 = (" 123456789012345678904294967296" + 0x00)
            If (F64)
            {
                If ((Local0 != 0x1234567890123456))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1234567890123456)
                }
            }
            ElseIf ((Local0 != 0x12345678))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x12345678)
            }

            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local0 = ("\t123456789012345678904294967296" + 0x00)
            If (F64)
            {
                If ((Local0 != 0x1234567890123456))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1234567890123456)
                }
            }
            ElseIf ((Local0 != 0x12345678))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x12345678)
            }
        }

        /*     64-bit mode – the value exceeding "18446744073709551615" */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("18446744073709551616" + 0x00)
        If (F64)
        {
            If ((Local0 != 0x1844674407370955))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1844674407370955)
            }
        }
        ElseIf ((Local0 != 0x18446744))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x18446744)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("\t18446744073709551616" + 0x00)
        If (F64)
        {
            If ((Local0 != 0x1844674407370955))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1844674407370955)
            }
        }
        ElseIf ((Local0 != 0x18446744))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x18446744)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = (" 18446744073709551616" + 0x00)
        If (F64)
        {
            If ((Local0 != 0x1844674407370955))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1844674407370955)
            }
        }
        ElseIf ((Local0 != 0x18446744))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x18446744)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("018446744073709551616" + 0x00)
        If (F64)
        {
            If ((Local0 != 0x1844674407370955))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1844674407370955)
            }
        }
        ElseIf ((Local0 != 0x18446744))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x18446744)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = (" \t000000000018446744073709551616" + 0x00)
        If (F64)
        {
            If ((Local0 != 0x1844674407370955))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1844674407370955)
            }
        }
        ElseIf ((Local0 != 0x18446744))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x18446744)
        }

        /* 12. "0x12345678901234567" (hex image exceeding maximal) */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("0x12345678901234567" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        /* 13. "0x00000000000001234" (hex image exceeding maximal; no matter that zeros) */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("0x00000000000001234" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("0x0000000000000000000001234" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        /* 14. "0x123456789" (hex image exceeding maximal; for 32-bit mode only) */

        If (0x01)
        {
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local0 = ("0x123456789" + 0x00)
            If ((Local0 != 0x00))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
            }
        }

        /* 15. "0x" (incomplete '0x' image) */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("0x" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
    }

    /*
     * 2. " 0x1234cd" (white space before image of Data is skipped)
     *
     * All the above examples but with the white space before image of Data.
     */
    Method (MF9B, 0, NotSerialized)
    {
        /* Hex: 0x - dec */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = (" 0x0" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        Local0 = ("\t0x1" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        Local0 = ("\t 0x12345678" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        Local0 = (" \t0x1234567890123456" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        /* Hex: 0x - hex */

        Local0 = ("  0xabcdefef" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        Local0 = ("\t\t0xabcdefefadefbcdf" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        /* Hex: 0x - dec/hex */

        Local0 = (" \t \t \t \t \t0x1ab2cd340fe05678" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("\t \t \t \t \t \t0x1ab2cd340fe0567823456789123456789987" + 0x00)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        /*
         * Implicit String to Integer (<dec>)
         *
         * Method(mf98)
         */
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("                       0" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("\t\t\t\t\t\t0000000" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("                                 000000000000000000000000000000" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("\t\t\t\t\t\t\t000000000000000000000000000000" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = (" \t\t 1" + 0x00)
        If ((Local0 != 0x01))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x01)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = (" \t \t \t12345678" + 0x00)
        If ((Local0 != 0x12345678))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x12345678)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        /*
         * Implicit String to Integer (<hex-dec>)
         *
         * Method(mf99)
         */
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        /* Hex: 0x - dec */

        Local0 = ("\t\t\t\t1234567890123456" + 0x00)
        If (F64)
        {
            If ((Local0 != 0x1234567890123456))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1234567890123456)
            }
        }
        ElseIf ((Local0 != 0x12345678))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x12345678)
        }

        /* Hex: 0x - hex */

        Local0 = ("\t\t\t\tabcdefef" + 0x00)
        If ((Local0 != 0xABCDEFEF))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xABCDEFEF)
        }

        Local0 = ("     abcdefe" + 0x00)
        If ((Local0 != 0x0ABCDEFE))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x0ABCDEFE)
        }

        Local0 = ("             abcdefefadefbcdf" + 0x00)
        If (F64)
        {
            If ((Local0 != 0xABCDEFEFADEFBCDF))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xABCDEFEFADEFBCDF)
            }
        }
        ElseIf ((Local0 != 0xABCDEFEF))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xABCDEFEF)
        }

        /* Hex: 0x - dec/hex */

        Local0 = ("\t     \t\t\t \t   1ab2cd340fe05678" + 0x00)
        If (F64)
        {
            If ((Local0 != 0x1AB2CD340FE05678))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1AB2CD340FE05678)
            }
        }
        ElseIf ((Local0 != 0x1AB2CD34))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1AB2CD34)
        }

        Local0 = (" 1ab2cd340fe05" + 0x00)
        If (F64)
        {
            If ((Local0 != 0x0001AB2CD340FE05))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x0001AB2CD340FE05)
            }
        }
        ElseIf ((Local0 != 0x1AB2CD34))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1AB2CD34)
        }

        Local0 = ("\t1a" + 0x00)
        If ((Local0 != 0x1A))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1A)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        /*
         * No exceptions in special cases which force exceptions on ToInteger
         *
         * Method(mf9a)
         */
        /* 5. "1234cd" (non-decimal character in dec-image) */
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("\t1234cd" + 0x00)
        If ((Local0 != 0x001234CD))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x001234CD)
        }

        /* 6. "000x1234" (non-decimal character in dec-image) */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = (" \t \t\t\t 000x1234" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        /* 7. "0x1234cdQ" (non-hex character in '0x'-image) */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = (" \t  \t\t\t\t 0x1234cdQ" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = (" 1234cdQ" + 0x00)
        If ((Local0 != 0x001234CD))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x001234CD)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("   \t\t0x0x12345" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        /* 8. "1234 " (white space in dec image) */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("   \t\t1234 " + 0x00)
        If ((Local0 != 0x1234))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1234)
        }

        /* 9. "0x1234cd " (white space in '0x'-image) */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("\t\t\t  1234cd " + 0x00)
        If ((Local0 != 0x001234CD))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x001234CD)
        }

        /* 10. "0x 1234cdQ" (white space after '0x') */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("\t\t\t\t   \t \t \t\t0x 1234" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = (" \t   \t \t\t \t0x0x 1234" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = (" \t \t \t    \t\t0x0x 0x 1234" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("\t \t    \t      \t\t 0x 0x 1234" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        /* 11. (decimal image exceeding maximal) */
        /*     32-bit mode – the value exceeding "4294967295" */
        If (0x01)
        {
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local0 = ("\t\t4294967296" + 0x00)
            If (F64)
            {
                If ((Local0 != 0x0000004294967296))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x0000004294967296)
                }
            }
            ElseIf ((Local0 != 0x42949672))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x42949672)
            }

            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local0 = ("    \t\t    \t\t\t123456789012345678904294967296" + 0x00)
            If (F64)
            {
                If ((Local0 != 0x1234567890123456))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1234567890123456)
                }
            }
            ElseIf ((Local0 != 0x12345678))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x12345678)
            }

            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local0 = (" \t \t\t00004294967296" + 0x00)
            If (F64)
            {
                If ((Local0 != 0x0000004294967296))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x0000004294967296)
                }
            }
            ElseIf ((Local0 != 0x42949672))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x42949672)
            }

            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local0 = ("\t0123456789012345678904294967296" + 0x00)
            If (F64)
            {
                If ((Local0 != 0x1234567890123456))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1234567890123456)
                }
            }
            ElseIf ((Local0 != 0x12345678))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x12345678)
            }

            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local0 = ("\t0123456789012345678904294967296" + 0x00)
            If (F64)
            {
                If ((Local0 != 0x1234567890123456))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1234567890123456)
                }
            }
            ElseIf ((Local0 != 0x12345678))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x12345678)
            }

            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local0 = (" 123456789012345678904294967296" + 0x00)
            If (F64)
            {
                If ((Local0 != 0x1234567890123456))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1234567890123456)
                }
            }
            ElseIf ((Local0 != 0x12345678))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x12345678)
            }

            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local0 = ("\t123456789012345678904294967296" + 0x00)
            If (F64)
            {
                If ((Local0 != 0x1234567890123456))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1234567890123456)
                }
            }
            ElseIf ((Local0 != 0x12345678))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x12345678)
            }
        }

        /*     64-bit mode – the value exceeding "18446744073709551615" */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("\t\t\t18446744073709551616" + 0x00)
        If (F64)
        {
            If ((Local0 != 0x1844674407370955))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1844674407370955)
            }
        }
        ElseIf ((Local0 != 0x18446744))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x18446744)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("\t18446744073709551616" + 0x00)
        If (F64)
        {
            If ((Local0 != 0x1844674407370955))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1844674407370955)
            }
        }
        ElseIf ((Local0 != 0x18446744))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x18446744)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = (" 18446744073709551616" + 0x00)
        If (F64)
        {
            If ((Local0 != 0x1844674407370955))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1844674407370955)
            }
        }
        ElseIf ((Local0 != 0x18446744))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x18446744)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("   \t018446744073709551616" + 0x00)
        If (F64)
        {
            If ((Local0 != 0x1844674407370955))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1844674407370955)
            }
        }
        ElseIf ((Local0 != 0x18446744))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x18446744)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = (" \t000000000018446744073709551616" + 0x00)
        If (F64)
        {
            If ((Local0 != 0x1844674407370955))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1844674407370955)
            }
        }
        ElseIf ((Local0 != 0x18446744))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x18446744)
        }

        /* 12. "0x12345678901234567" (hex image exceeding maximal) */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("\t\t0x12345678901234567" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        /* 13. "0x00000000000001234" (hex image exceeding maximal; no matter that zeros) */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("           0x00000000000001234" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("          \t\t0x0000000000000000000001234" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        /* 14. "0x123456789" (hex image exceeding maximal; for 32-bit mode only) */

        If (0x01)
        {
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local0 = ("0x123456789" + 0x00)
            If ((Local0 != 0x00))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
            }
        }

        /* 15. "0x" (incomplete '0x' image) */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("\t0x" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = (" 0x" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
    }

    /*
     * 4. "0000000000000000000000001234"
     * (zeros before significant characters in image without '0x' are skipped).
     *
     * Examples: mf9b + 000000000
     *
     * All the above examples but
     *
     *    with the white space before image of Data
     *  + 000000000 zeros before image
     */
    Method (MF9C, 0, NotSerialized)
    {
        /* Hex: 0x - dec */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = (" 0000000000x0" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        Local0 = ("\t0000000000x1" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        Local0 = ("\t 0000000000x12345678" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        Local0 = (" \t0000000000x1234567890123456" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        /* Hex: 0x - hex */

        Local0 = ("  0000000000xabcdefef" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        Local0 = ("\t\t0000000000xabcdefefadefbcdf" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        /* Hex: 0x - dec/hex */

        Local0 = (" \t \t \t \t \t0000000000x1ab2cd340fe05678" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("\t \t \t \t \t \t0000000000x1ab2cd340fe0567823456789123456789987" + 0x00)
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        /*
         * Implicit String to Integer (<dec>)
         *
         * Method(mf98)
         */
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("                       0000000000" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("\t\t\t\t\t\t0000000000000000" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("                                 000000000000000000000000000000000000000" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("\t\t\t\t\t\t\t000000000000000000000000000000000000000" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = (" \t\t 0000000001" + 0x00)
        If ((Local0 != 0x01))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x01)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = (" \t \t \t00000000012345678" + 0x00)
        If ((Local0 != 0x12345678))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x12345678)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        /*
         * Implicit String to Integer (<hex-dec>)
         *
         * Method(mf99)
         */
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        /* Hex: 0x - dec */

        Local0 = ("\t\t\t\t0000000001234567890123456" + 0x00)
        If (F64)
        {
            If ((Local0 != 0x1234567890123456))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1234567890123456)
            }
        }
        ElseIf ((Local0 != 0x12345678))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x12345678)
        }

        /* Hex: 0x - hex */

        Local0 = ("\t\t\t\t000000000abcdefef" + 0x00)
        If ((Local0 != 0xABCDEFEF))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xABCDEFEF)
        }

        Local0 = ("     000000000abcdefe" + 0x00)
        If ((Local0 != 0x0ABCDEFE))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x0ABCDEFE)
        }

        Local0 = ("             000000000abcdefefadefbcdf" + 0x00)
        If (F64)
        {
            If ((Local0 != 0xABCDEFEFADEFBCDF))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xABCDEFEFADEFBCDF)
            }
        }
        ElseIf ((Local0 != 0xABCDEFEF))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xABCDEFEF)
        }

        /* Hex: 0x - dec/hex */

        Local0 = ("\t     \t\t\t \t   0000000001ab2cd340fe05678" + 0x00)
        If (F64)
        {
            If ((Local0 != 0x1AB2CD340FE05678))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1AB2CD340FE05678)
            }
        }
        ElseIf ((Local0 != 0x1AB2CD34))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1AB2CD34)
        }

        Local0 = (" 0000000001ab2cd340fe05" + 0x00)
        If (F64)
        {
            If ((Local0 != 0x0001AB2CD340FE05))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x0001AB2CD340FE05)
            }
        }
        ElseIf ((Local0 != 0x1AB2CD34))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1AB2CD34)
        }

        Local0 = ("\t0000000001a" + 0x00)
        If ((Local0 != 0x1A))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1A)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        /*
         * No exceptions in special cases which force exceptions on ToInteger
         *
         * Method(mf9a)
         */
        /* 5. "1234cd" (non-decimal character in dec-image) */
        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("\t0000000001234cd" + 0x00)
        If ((Local0 != 0x001234CD))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x001234CD)
        }

        /* 6. "000x1234" (non-decimal character in dec-image) */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = (" \t \t\t\t 000000000000x1234" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        /* 7. "0x1234cdQ" (non-hex character in '0x'-image) */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = (" \t  \t\t\t\t 0000000000x1234cdQ" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = (" 0000000001234cdQ" + 0x00)
        If ((Local0 != 0x001234CD))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x001234CD)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("   \t\t0000000000x0x12345" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        /* 8. "1234 " (white space in dec image) */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("   \t\t0000000001234 " + 0x00)
        If ((Local0 != 0x1234))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1234)
        }

        /* 9. "0x1234cd " (white space in '0x'-image) */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("\t\t\t  0000000001234cd " + 0x00)
        If ((Local0 != 0x001234CD))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x001234CD)
        }

        /* 10. "0x 1234cdQ" (white space after '0x') */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("\t\t\t\t   \t \t \t\t0000000000x 1234" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = (" \t   \t \t\t \t0000000000x0x 1234" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = (" \t \t \t    \t\t0000000000x0x 0x 1234" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("\t \t    \t      \t\t 0000000000x 0x 1234" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        /* 11. (decimal image exceeding maximal) */
        /*     32-bit mode – the value exceeding "4294967295" */
        If (0x01)
        {
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local0 = ("\t\t0000000004294967296" + 0x00)
            If (F64)
            {
                If ((Local0 != 0x0000004294967296))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x0000004294967296)
                }
            }
            ElseIf ((Local0 != 0x42949672))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x42949672)
            }

            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local0 = ("    \t\t    \t\t\t000000000123456789012345678904294967296" + 0x00)
            If (F64)
            {
                If ((Local0 != 0x1234567890123456))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1234567890123456)
                }
            }
            ElseIf ((Local0 != 0x12345678))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x12345678)
            }

            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local0 = (" \t \t\t00000000000004294967296" + 0x00)
            If (F64)
            {
                If ((Local0 != 0x0000004294967296))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x0000004294967296)
                }
            }
            ElseIf ((Local0 != 0x42949672))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x42949672)
            }

            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local0 = ("\t0000000000123456789012345678904294967296" + 0x00)
            If (F64)
            {
                If ((Local0 != 0x1234567890123456))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1234567890123456)
                }
            }
            ElseIf ((Local0 != 0x12345678))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x12345678)
            }

            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local0 = ("\t0000000000123456789012345678904294967296" + 0x00)
            If (F64)
            {
                If ((Local0 != 0x1234567890123456))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1234567890123456)
                }
            }
            ElseIf ((Local0 != 0x12345678))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x12345678)
            }

            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local0 = (" 000000000123456789012345678904294967296" + 0x00)
            If (F64)
            {
                If ((Local0 != 0x1234567890123456))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1234567890123456)
                }
            }
            ElseIf ((Local0 != 0x12345678))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x12345678)
            }

            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local0 = ("\t000000000123456789012345678904294967296" + 0x00)
            If (F64)
            {
                If ((Local0 != 0x1234567890123456))
                {
                    ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1234567890123456)
                }
            }
            ElseIf ((Local0 != 0x12345678))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x12345678)
            }
        }

        /*     64-bit mode – the value exceeding "18446744073709551615" */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("\t\t\t00000000018446744073709551616" + 0x00)
        If (F64)
        {
            If ((Local0 != 0x1844674407370955))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1844674407370955)
            }
        }
        ElseIf ((Local0 != 0x18446744))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x18446744)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("\t00000000018446744073709551616" + 0x00)
        If (F64)
        {
            If ((Local0 != 0x1844674407370955))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1844674407370955)
            }
        }
        ElseIf ((Local0 != 0x18446744))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x18446744)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = (" 00000000018446744073709551616" + 0x00)
        If (F64)
        {
            If ((Local0 != 0x1844674407370955))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1844674407370955)
            }
        }
        ElseIf ((Local0 != 0x18446744))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x18446744)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("   \t000000000018446744073709551616" + 0x00)
        If (F64)
        {
            If ((Local0 != 0x1844674407370955))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1844674407370955)
            }
        }
        ElseIf ((Local0 != 0x18446744))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x18446744)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = (" \t000000000000000000018446744073709551616" + 0x00)
        If (F64)
        {
            If ((Local0 != 0x1844674407370955))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1844674407370955)
            }
        }
        ElseIf ((Local0 != 0x18446744))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x18446744)
        }

        /* 12. "0x12345678901234567" (hex image exceeding maximal) */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("\t\t0000000000x12345678901234567" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        /* 13. "0x00000000000001234" (hex image exceeding maximal; no matter that zeros) */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("           0000000000x00000000000001234" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("          \t\t0000000000x0000000000000000000001234" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        /* 14. "0x123456789" (hex image exceeding maximal; for 32-bit mode only) */

        If (0x01)
        {
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local0 = ("0x123456789" + 0x00)
            If ((Local0 != 0x00))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
            }
        }

        /* 15. "0x" (incomplete '0x' image) */

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = ("\t0000000000x" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        Local0 = (" 0000000000x" + 0x00)
        If ((Local0 != 0x00))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
    }
