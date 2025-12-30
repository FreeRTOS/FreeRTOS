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
     * Bug 63:
     *
     * SUMMARY
     *
     * String to Integer conversion contradicts new April 2005 Conversion Rules
     *
     * EXAMPLES
     *
     *    Add("0x1111", 0) returns 0x1111 but 0 is expected
     *    Add("12345678901234560", 0x1111111111111111) causes AE_BAD_HEX_CONSTANT
     *    Add("00000000000012345678", 0) returns 0x12345678 but 0x1234 is expected
     *
     * ROOT CAUSE
     *
     * SPECS (NEW, March 12 2005)
     *
     * String --> Integer
     *
     * If no integer object exists, a new integer is created.
     * The integer is initialized to the value zero and the ASCII
     * string is interpreted as a hexadecimal constant. Each string
     * character is interpreted as a hexadecimal value (‘0’-‘9’, ‘A’-‘F’, ‘a’-‘f’),
     * starting with the first character as the most significant digit and ending
     * with the first non-hexadecimal character, end-of-string, or when the size
     * of an integer is reached (8 characters for 32-bit integers and 16 characters
     * for 64-bit integers). Note: the first non-hex character terminates the
     * conversion without error, and a “0x” prefix is not allowed.
     */
    /*
     * To be completed !!!!!!!
     *
     * What to do else below:
     *
     * 1. Set correct results in 32 and 64 bit modes (now it is not done!)
     * 2. Change places of operands, that is use both:
     Add("12345678", 0x11111111, Local0)
     Add(0x11111111, "12345678", Local0)
     * 3. Pass operators by parameters !!!!
     * 4. Issues:
     *    1) octal - 01232211
     *    2) zeros at the beginning - 0000000abcdef
     *    3) large hex image - abcdef123456789123456789
     */
    /*
     Store("VVVVVVVVVVVVVVVVVVVVVVVVVV", Debug)
     Store(0123, Debug)
     Store(83, Debug)
     Add(0x1234, 83, Local0)
     Store(Local0, Debug)
     return
     */
    /*
     * All the possible attempts to confuse calculation
     */
    Method (MD74, 0, Serialized)
    {
        /* 8 decimal */

        Local0 = ("12345678" + 0x11111111)
        If ((Local0 != 0x23456789))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x23456789)
        }

        /* 8 hex */

        Local0 = ("abcdefab" + 0x11111111)
        If ((Local0 != 0xBCDF00BC))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xBCDF00BC)
        }

        /* 16 decimal */

        Local0 = ("1234567890876543" + 0x1111111111111111)
        If ((Local0 != 0x23456789A1987654))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x23456789A1987654)
        }

        /* 16 hex */

        Local0 = ("abcdefababcdfead" + 0x1111111111111111)
        If ((Local0 != 0xBCDF00BCBCDF0FBE))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xBCDF00BCBCDF0FBE)
        }

        /* 17 hex */

        Local0 = ("1234567890123456z" + 0x1111111111111111)
        If ((Local0 != 0x23456789A1234567))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x23456789A1234567)
        }

        /* 17 hex (caused AE_BAD_HEX_CONSTANT, 28.09.2005) */

        Local0 = ("12345678901234560" + 0x1111111111111111)
        If ((Local0 != 0x23456789A1234567))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x23456789A1234567)
        }

        /* Looks like octal, but should be treated as hex */

        Local0 = ("01111" + 0x2222)
        If ((Local0 != 0x3333))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x3333)
        }

        /* The first zeros each must be put into value */

        Local0 = ("000010234" + 0x00)
        If ((Local0 != 0x00010234))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00010234)
        }

        Local0 = ("000000000000000010234" + 0x00)
        If ((Local0 != 0x00010234))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00010234)
        }

        Local0 = ("00000000000000010234" + 0x00)
        If ((Local0 != 0x00010234))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00010234)
        }

        Local0 = ("0000000010234" + 0x00)
        If ((Local0 != 0x00010234))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00010234)
        }

        Local0 = ("000000010234" + 0x00)
        If ((Local0 != 0x00010234))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00010234)
        }

        /* Non-complete 4 hex, should be extended with zeros */

        Local0 = ("abcd" + 0x1111)
        If ((Local0 != 0xBCDE))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xBCDE)
        }

        /* Non-complete 5 decimal, should be extended with zeros */

        Local0 = ("12345" + 0x1111)
        If ((Local0 != 0x00013456))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00013456)
        }

        CH03 (__METHOD__, ZFFF, __LINE__, 0x00, 0x00)
        /* Too large, all hex, should be trancated */

        Local0 = ("abcdef0123456789112233445566778890" + 0x00)
        If (F64)
        {
            If ((Local0 != 0xABCDEF0123456789))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xABCDEF0123456789)
            }
        }
        ElseIf ((Local0 != 0xABCDEF01))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xABCDEF01)
        }

        CH03 (__METHOD__, ZFFF, __LINE__, 0x00, 0x00)
        /* Large, all hex, looks like octal, should be trancated */

        Local0 = ("0abcdef0123456789112233445566778890" + 0x1234)
        If (F64)
        {
            If ((Local0 != 0xABCDEF0123456789))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xABCDEF0123456789)
            }
        }
        ElseIf ((Local0 != 0xABCDEF01))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xABCDEF01)
        }

        CH03 (__METHOD__, ZFFF, __LINE__, 0x00, 0x00)
        /* Looks like usual hex, but 'x' terminates conversion */

        Local0 = ("0x1111" + 0x2222)
        If ((Local0 != 0x2222))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x2222)
        }

        CH03 (__METHOD__, ZFFF, __LINE__, 0x00, 0x00)
        /* Empty string, no action - the relevant parameter of Add remains zero */

        Local0 = ("" + 0xDE)
        If ((Local0 != 0xDE))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xDE)
        }

        CH03 (__METHOD__, ZFFF, __LINE__, 0x00, 0x00)
        /* Blank string, no action - the relevant parameter of Add remains zero */

        Local0 = (" " + 0x0333)
        If ((Local0 != 0x0333))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x0333)
        }

        CH03 (__METHOD__, ZFFF, __LINE__, 0x00, 0x00)
        /* Blank string, no action - the relevant parameter of Add remains zero */

        Local0 = ("                                " + 0x92)
        If ((Local0 != 0x92))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x92)
        }

        CH03 (__METHOD__, ZFFF, __LINE__, 0x00, 0x00)
        /* Conversion is terminated just by the first symbol (non-hex) though followed by hex-es, remains zero */

        Local0 = ("k1234567" + 0x01E9)
        If ((Local0 != 0x01E9))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x01E9)
        }

        /* Conversion is terminated just by the first symbol (non-hex), single */

        Local0 = ("k" + 0x000000ABCDEF0000)
        If ((Local0 != 0x000000ABCDEF0000))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x000000ABCDEF0000)
        }

        CH03 (__METHOD__, ZFFF, __LINE__, 0x00, 0x00)
        /* Looks like designation of hex (terminated by x) */

        Local0 = ("0x" + 0x12345678)
        If ((Local0 != 0x12345678))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x12345678)
        }

        CH03 (__METHOD__, ZFFF, __LINE__, 0x00, 0x00)
        /* Special symbol in the hex designation (terminated by x) */

        Local0 = ("x" + 0x00BC614E)
        If ((Local0 != 0x00BC614E))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00BC614E)
        }

        /* Starts with the special symbol in the hex designation (terminated by x) */

        Local0 = ("x12345" + 0x6F)
        If ((Local0 != 0x6F))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x6F)
        }

        /* No one hex, conversion is terminated just by the first symbol Z */

        Local0 = ("ZZZZ" + 0x0001E240)
        If ((Local0 != 0x0001E240))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x0001E240)
        }

        /* Short <= 8, conversion is terminated by non-hex symbol Z */

        Local0 = ("abcdZZZZ" + 0x11)
        If ((Local0 != 0xABDE))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xABDE)
        }

        /* Short <= 8, hex in the middle (terminated by Z) */

        Local0 = ("ZQ123MMM" + 0x0001E240)
        If ((Local0 != 0x0001E240))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x0001E240)
        }

        /* Short <= 8, hex at the end (terminated by Z) */

        Local0 = ("ZQMMM123" + 0x0001E240)
        If ((Local0 != 0x0001E240))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x0001E240)
        }

        /* Long exceeding 16, no one hex */

        Local0 = ("zxswqrrrrrrrrrrrrrrtttttttttttttttttttttttttyyyyyyyyyyyyyyyyyyuuuuuuuuuuuuuuuuuuuuuuu" + 0x7B)
        If ((Local0 != 0x7B))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x7B)
        }

        /* Long exceeding 16, hex at the beginning */

        Local0 = ("1234zxswqrrrrrrrrrrrrrrtttttttttttttttttttttttttyyyyyyyyyyyyyyyyyyuuuuuuuuuuuuuuuuuuuuuuu" + 0x53)
        If ((Local0 != 0x1287))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x1287)
        }

        /* Long exceeding 16, hex everywhere */

        Local0 = ("123z4s5qr6rr7rrrrrrrrr8ttttttt9ttttttattttbttttcyyyydyyeyyyyyyyyuuuuuuuuuuuuuuuuuuuuf" + 0x53)
        If ((Local0 != 0x0176))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x0176)
        }

        /* Long exceeding 16, hex at the end */

        Local0 = ("zxswqrrrrrrrrrrrrrrtttttttttttttttttttttttttyyyyyyyyyyyyyyyyyyuuuuuuuuuuuuuuuuuuuuuuu1234" + 0x14D1)
        If ((Local0 != 0x14D1))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x14D1)
        }

        /* Long exceeding 16, hex in the middle inside the possible Integer */

        Local0 = ("zx1234swqrrrrrrrrrrrrrrtttttttttttttttttttttttttyyyyyyyyyyyyyyyyyyuuuuuuuuuuuuuuuuuuuuuuu" + 0x00012321)
        If ((Local0 != 0x00012321))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x00012321)
        }

        /* Long exceeding 16, hex in the middle beyond the bounds of the possible Integer */

        Local0 = ("zxswqrrrrrrrrrrrrrrtttttttttttttttttttttttttyyyyyyyyyyyyyyyyyyuuuuuuuuuuuuuuuuuuuuu1234uu" + 0x3021)
        If ((Local0 != 0x3021))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0x3021)
        }

        CH03 (__METHOD__, ZFFF, __LINE__, 0x00, 0x00)
        /* Only decimal, much more than 16 */

        Store (("123456789012345601112223334446667788990087654" + 0x00), Local1)
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

        CH03 (__METHOD__, ZFFF, __LINE__, 0x00, 0x00)
        /* Only hex, much more than 16 */

        Store (("abcdefabcdefabcdefabcdefabcdefabcdefabcdefabc" + 0x00), Local1)
        If (F64)
        {
            If ((Local0 != 0xABCDEFABCDEFABCD))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xABCDEFABCDEFABCD)
            }
        }
        ElseIf ((Local0 != 0xABCDEFAB))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xABCDEFAB)
        }

        CH03 (__METHOD__, ZFFF, __LINE__, 0x00, 0x00)
        /* Only decimal, much more than 16, non-hex at the end */

        Store (("123456789012345601112223334446667788990087654ZZZZ" + 0x00), Local1)
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

        CH03 (__METHOD__, ZFFF, __LINE__, 0x00, 0x00)
        /* Only hex, much more than 16, non-hex at the end */

        Store (("abcdefabcdefabcdefabcdefabcdefabcdefabcdefabcZZZZ" + 0x00), Local1)
        If (F64)
        {
            If ((Local0 != 0xABCDEFABCDEFABCD))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xABCDEFABCDEFABCD)
            }
        }
        ElseIf ((Local0 != 0xABCDEFAB))
        {
            ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, 0xABCDEFAB)
        }

        CH03 (__METHOD__, ZFFF, __LINE__, 0x00, 0x00)
    }

    Method (MD75, 0, NotSerialized)
    {
        /* Do here the same as md74 but store Result by Store */
    }

    Method (MD76, 0, Serialized)
    {
        CH03 (__METHOD__, ZFFF, __LINE__, 0x00, 0x00)
        MD74 ()
        CH03 (__METHOD__, ZFFF, __LINE__, 0x00, 0x00)
        MD75 ()
        CH03 (__METHOD__, ZFFF, __LINE__, 0x00, 0x00)
    }
