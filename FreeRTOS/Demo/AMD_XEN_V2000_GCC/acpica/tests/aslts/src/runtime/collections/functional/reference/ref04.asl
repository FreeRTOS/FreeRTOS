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
     * References
     *
     *          (named objects, if present, are the global objects (from DefinitionBlock))
     *
     * TABLE 2: all the legal ways to generate references to the
     *          named objects
     * TABLE 4: all the legal ways to generate references to the
     *          named objects being elements of Package
     *
     * Producing Reference operators:
     *
     *    Index, RefOf, CondRefOf
     */
    /*
     ??????????????
     SEE: PUT everywhere APPROPREATE arg6 - number of checking for diagnostics
     !!!!!!!!!!!!!!
     SEE: add verification of Field Unit (in all files)
     SEE: run the tests two times - to check that the data are not corrupted
     SEE: uncomment runs after bug fixing
     */
    Name (Z080, 0x50)
    /* /////////////////////////////////////////////////////////////////////////// */
    /* */
    /* TABLE 2: all the legal ways to generate references to the named objects */
    /* */
    /* /////////////////////////////////////////////////////////////////////////// */
    /* m169 but with global data */
    Method (M190, 0, NotSerialized)
    {
        If (Y100)
        {
            TS00 ("m190")
        }
        Else
        {
            Debug = "m190"
        }

        /* T2:I2-I4 */

        If (Y114)
        {
            /* Remove this after the bug fixing */

            Store (M902 () [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x00)
        }

        /* Computational Data */

        Store (S900 [0x00], Local0)
        M1A2 (Local0, C016, 0x00, 0x00, C009, 0x31, __LINE__)
        Store (S901 [0x02], Local0)
        M1A2 (Local0, C016, 0x00, 0x00, C009, 0x72, __LINE__)
        Store (B900 [0x03], Local0)
        M1A2 (Local0, C016, 0x00, 0x00, C009, 0xB3, __LINE__)
        /* Elements of Package are Uninitialized */

        If (Y104)
        {
            Store (P900 [0x00], Local0)
            M1A0 (Local0, C008, Ones, 0x04)
        }

        /* Elements of Package are Computational Data */

        Store (P901 [0x00], Local0)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xABCD0004, __LINE__)
        Store (P901 [0x01], Local0)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0x1122334455660005, __LINE__)
        Store (P902 [0x00], Local0)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "12340006", __LINE__)
        Store (P902 [0x01], Local0)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "q1w2e3r4t5y6u7i80007", __LINE__)
        Store (P903 [0x00], Local0)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "qwrtyuiop0008", __LINE__)
        Store (P903 [0x01], Local0)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "1234567890abdef0250009", __LINE__)
        Store (P904 [0x00], Local0)
        M1A2 (Local0, C00B, 0x00, 0x00, C00B, Buffer (0x03)
            {
                 0xB5, 0xB6, 0xB7                                 // ...
            }, 0x0B)
        Store (P905 [0x00], Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0x0ABC000A, __LINE__)
        Store (P905 [0x00], Local0)
        M1A2 (Local0, C00C, 0x01, 0x01, C00A, "0xabc000b", __LINE__)
        Store (P906 [0x00], Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "abc000d", __LINE__)
        Store (P907 [0x00], Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "aqwevbgnm000e", __LINE__)
        Store (P908 [0x00], Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C00B, Buffer (0x05)
            {
                 0xBA, 0xBB, 0xBC, 0xBD, 0xBE                     // .....
            }, 0x10)
        Store (P909 [0x00], Local0)
        M1A2 (Local0, C00C, 0x02, 0x00, C009, 0x0ABC000F, __LINE__)
        Store (P90A [0x00], Local0)
        M1A2 (Local0, C00C, 0x02, 0x00, C00A, "12340010", __LINE__)
        Store (P90B [0x00], Local0)
        M1A2 (Local0, C00C, 0x02, 0x00, C00A, "zxswefas0011", __LINE__)
        Store (P90C [0x00], Local0)
        M1A2 (Local0, C00C, 0x02, 0x00, C00B, Buffer (0x03)
            {
                 0xBF, 0xC0, 0xC1                                 // ...
            }, 0x14)
        Store (P90D [0x00], Local0)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xFE7CB391D65A0000, __LINE__)
        Store (P90E [0x00], Local0)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xC1790001, __LINE__)
        Store (P90F [0x00], Local0)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "12340002", __LINE__)
        Store (P910 [0x00], Local0)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "qwrtyu0003", __LINE__)
        Store (P911 [0x00], Local0)
        M1A2 (Local0, C00B, 0x00, 0x00, C00B, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            }, 0x19)
        If (Y118)
        {
            Store (P912 [0x00], Local0)
            M1A2 (Local0, C00D, 0x00, 0x00, C00D, 0x00, __LINE__)
            Store (P913 [0x00], Local0)
            M1A2 (Local0, C00D, 0x00, 0x00, C00D, 0x00, __LINE__)
            Store (P914 [0x00], Local0)
            M1A2 (Local0, C00D, 0x00, 0x00, C00D, 0x00, __LINE__)
            Store (P915 [0x00], Local0)
            M1A2 (Local0, C016, 0x00, 0x00, C016, 0xB0, __LINE__)
        }

        /* Elements of Package are NOT Computational Data */

        Store (P916 [0x00], Local0)
        M1A0 (Local0, C00E, Ones, 0x1E)
        Store (P917 [0x00], Local0)
        M1A0 (Local0, C00F, Ones, 0x1F)
        Store (P918 [0x00], Local0)
        M1A0 (Local0, C011, Ones, 0x20)
        Store (P919 [0x00], Local0)
        M1A0 (Local0, C012, Ones, 0x21)
        Store (P91A [0x00], Local0)
        M1A0 (Local0, C013, Ones, 0x22)
        Store (P91B [0x00], Local0)
        M1A0 (Local0, C014, Ones, 0x23)
        Store (P91C [0x00], Local0)
        M1A0 (Local0, C015, Ones, 0x24)
        /* Elements of Package are Methods */

        If (Y105)
        {
            Store (P91D [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x25)
            Store (P91E [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x26)
            Store (P91F [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x27)
            Store (P920 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x28)
            Store (P921 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x29)
            Store (P922 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x2A)
            Store (P923 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x2B)
            Store (P924 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x2C)
            Store (P925 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x2D)
            Store (P926 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x2E)
            Store (P927 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x2F)
            Store (P928 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x30)
            Store (P929 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x31)
            Store (P92A [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x32)
            Store (P92B [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x33)
            Store (P92C [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x34)
            Store (P92D [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x35)
            Store (P92E [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x36)
            Store (P92F [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x37)
            Store (P930 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x38)
            Store (P931 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x39)
            Store (P932 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x3A)
            Store (P933 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x3B)
            Store (P934 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x3C)
            If (Y103)
            {
                Store (P935 [0x00], Local0)
                M1A0 (Local0, C010, Ones, 0x3D)
            }

            Store (P936 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x3E)
            Store (P937 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x3F)
            Store (P938 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x40)
            Store (P939 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x41)
            Store (P93A [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x42)
            Store (P93B [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x43)
            Store (P93C [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x44)
            Store (P93D [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x45)
            Store (P93E [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x46)
            Store (P93F [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x47)
            Store (P940 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x48)
            Store (P941 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x49)
            Store (P942 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x4A)
            Store (P943 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x4B)
            Store (P944 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x4C)
            Store (P945 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x4D)
            Store (P946 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x4E)
            Store (P947 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x4F)
            Store (P948 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x50)
            Store (P949 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x51)
            Store (P94A [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x52)
            Store (P94B [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x53)
            Store (P94C [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x54)
            Store (P94D [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x55)
            Store (P94E [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x56)
            Store (P94F [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x57)
            Store (P950 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x58)
            Store (P951 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x59)
            Store (P952 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x5A)
        }

        /* T2:IR2-IR4 */
        /* Computational Data */
        Local0 = Local1 = S900 [0x00]
        M1A2 (Local0, C016, 0x00, 0x00, C009, 0x31, __LINE__)
        M1A2 (Local1, C016, 0x00, 0x00, C009, 0x31, __LINE__)
        Local0 = Local1 = S901 [0x02]
        M1A2 (Local0, C016, 0x00, 0x00, C009, 0x72, __LINE__)
        M1A2 (Local1, C016, 0x00, 0x00, C009, 0x72, __LINE__)
        Local0 = Local1 = B900 [0x04]
        M1A2 (Local0, C016, 0x00, 0x00, C009, 0xB4, __LINE__)
        M1A2 (Local1, C016, 0x00, 0x00, C009, 0xB4, __LINE__)
        /* Elements of Package are Uninitialized */

        If (Y104)
        {
            Local0 = Local1 = P900 [0x00]
            M1A0 (Local0, C008, Ones, 0x61)
            M1A0 (Local1, C008, Ones, 0x62)
        }

        /* Elements of Package are Computational Data */

        Local0 = Local1 = P901 [0x00]
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xABCD0004, __LINE__)
        M1A2 (Local1, C009, 0x00, 0x00, C009, 0xABCD0004, __LINE__)
        Local0 = Local1 = P901 [0x01]
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0x1122334455660005, __LINE__)
        M1A2 (Local1, C009, 0x00, 0x00, C009, 0x1122334455660005, __LINE__)
        Local0 = Local1 = P902 [0x00]
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "12340006", __LINE__)
        M1A2 (Local1, C00A, 0x00, 0x00, C00A, "12340006", __LINE__)
        Local0 = Local1 = P902 [0x01]
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "q1w2e3r4t5y6u7i80007", __LINE__)
        M1A2 (Local1, C00A, 0x00, 0x00, C00A, "q1w2e3r4t5y6u7i80007", __LINE__)
        Local0 = Local1 = P903 [0x00]
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "qwrtyuiop0008", __LINE__)
        M1A2 (Local1, C00A, 0x00, 0x00, C00A, "qwrtyuiop0008", __LINE__)
        Local0 = Local1 = P903 [0x01]
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "1234567890abdef0250009", __LINE__)
        M1A2 (Local1, C00A, 0x00, 0x00, C00A, "1234567890abdef0250009", __LINE__)
        Local0 = Local1 = P904 [0x00]
        M1A2 (Local0, C00B, 0x00, 0x00, C00B, Buffer (0x03)
            {
                 0xB5, 0xB6, 0xB7                                 // ...
            }, 0x6F)
        M1A2 (Local1, C00B, 0x00, 0x00, C00B, Buffer (0x03)
            {
                 0xB5, 0xB6, 0xB7                                 // ...
            }, 0x70)
        Local0 = Local1 = P905 [0x00]
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0x0ABC000A, __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x00, C009, 0x0ABC000A, __LINE__)
        Local0 = Local1 = P905 [0x00]
        M1A2 (Local0, C00C, 0x01, 0x01, C00A, "0xabc000b", __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x01, C00A, "0xabc000b", __LINE__)
        Local0 = Local1 = P906 [0x00]
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "abc000d", __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x00, C00A, "abc000d", __LINE__)
        Local0 = Local1 = P907 [0x00]
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "aqwevbgnm000e", __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x00, C00A, "aqwevbgnm000e", __LINE__)
        Local0 = Local1 = P908 [0x00]
        M1A2 (Local0, C00C, 0x01, 0x00, C00B, Buffer (0x05)
            {
                 0xBA, 0xBB, 0xBC, 0xBD, 0xBE                     // .....
            }, 0x79)
        M1A2 (Local1, C00C, 0x01, 0x00, C00B, Buffer (0x05)
            {
                 0xBA, 0xBB, 0xBC, 0xBD, 0xBE                     // .....
            }, 0x7A)
        Local0 = Local1 = P909 [0x00]
        M1A2 (Local0, C00C, 0x02, 0x00, C009, 0x0ABC000F, __LINE__)
        M1A2 (Local1, C00C, 0x02, 0x00, C009, 0x0ABC000F, __LINE__)
        Local0 = Local1 = P90A [0x00]
        M1A2 (Local0, C00C, 0x02, 0x00, C00A, "12340010", __LINE__)
        M1A2 (Local1, C00C, 0x02, 0x00, C00A, "12340010", __LINE__)
        Local0 = Local1 = P90B [0x00]
        M1A2 (Local0, C00C, 0x02, 0x00, C00A, "zxswefas0011", __LINE__)
        M1A2 (Local1, C00C, 0x02, 0x00, C00A, "zxswefas0011", __LINE__)
        Local0 = Local1 = P90C [0x00]
        M1A2 (Local0, C00C, 0x02, 0x00, C00B, Buffer (0x03)
            {
                 0xBF, 0xC0, 0xC1                                 // ...
            }, 0x81)
        M1A2 (Local1, C00C, 0x02, 0x00, C00B, Buffer (0x03)
            {
                 0xBF, 0xC0, 0xC1                                 // ...
            }, 0x82)
        Local0 = Local1 = P90D [0x00]
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xFE7CB391D65A0000, __LINE__)
        M1A2 (Local1, C009, 0x00, 0x00, C009, 0xFE7CB391D65A0000, __LINE__)
        Local0 = Local1 = P90E [0x00]
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xC1790001, __LINE__)
        M1A2 (Local1, C009, 0x00, 0x00, C009, 0xC1790001, __LINE__)
        Local0 = Local1 = P90F [0x00]
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "12340002", __LINE__)
        M1A2 (Local1, C00A, 0x00, 0x00, C00A, "12340002", __LINE__)
        Local0 = Local1 = P910 [0x00]
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "qwrtyu0003", __LINE__)
        M1A2 (Local1, C00A, 0x00, 0x00, C00A, "qwrtyu0003", __LINE__)
        Local0 = Local1 = P911 [0x00]
        M1A2 (Local0, C00B, 0x00, 0x00, C00B, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            }, 0x8B)
        M1A2 (Local1, C00B, 0x00, 0x00, C00B, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            }, 0x8C)
        If (Y118)
        {
            Local0 = Local1 = P912 [0x00]
            M1A2 (Local0, C00D, 0x00, 0x00, C00D, 0x00, __LINE__)
            M1A2 (Local1, C00D, 0x00, 0x00, C00D, 0x00, __LINE__)
            Local0 = Local1 = P913 [0x00]
            M1A2 (Local0, C00D, 0x00, 0x00, C00D, 0x00, __LINE__)
            M1A2 (Local1, C00D, 0x00, 0x00, C00D, 0x00, __LINE__)
            Local0 = Local1 = P914 [0x00]
            M1A2 (Local0, C00D, 0x00, 0x00, C00D, 0x00, __LINE__)
            M1A2 (Local1, C00D, 0x00, 0x00, C00D, 0x00, __LINE__)
            Local0 = Local1 = P915 [0x00]
            M1A2 (Local0, C016, 0x00, 0x00, C016, 0xB0, __LINE__)
            M1A2 (Local1, C016, 0x00, 0x00, C016, 0xB0, __LINE__)
        }

        /* Elements of Package are NOT Computational Data */

        Local0 = Local1 = P916 [0x00]
        M1A0 (Local0, C00E, Ones, 0x95)
        M1A0 (Local1, C00E, Ones, 0x96)
        Local0 = Local1 = P917 [0x00]
        M1A0 (Local0, C00F, Ones, 0x97)
        M1A0 (Local1, C00F, Ones, 0x98)
        Local0 = Local1 = P918 [0x00]
        M1A0 (Local0, C011, Ones, 0x99)
        M1A0 (Local1, C011, Ones, 0x9A)
        Local0 = Local1 = P919 [0x00]
        M1A0 (Local0, C012, Ones, 0x9B)
        M1A0 (Local1, C012, Ones, 0x9C)
        Local0 = Local1 = P91A [0x00]
        M1A0 (Local0, C013, Ones, 0x9D)
        M1A0 (Local1, C013, Ones, 0x9E)
        Local0 = Local1 = P91B [0x00]
        M1A0 (Local0, C014, Ones, 0x9F)
        M1A0 (Local1, C014, Ones, 0xA0)
        Local0 = Local1 = P91C [0x00]
        M1A0 (Local0, C015, Ones, 0xA1)
        M1A0 (Local1, C015, Ones, 0xA2)
        /* Elements of Package are Methods */

        If (Y105)
        {
            Local0 = Local1 = P91D [0x00]
            M1A0 (Local0, C010, Ones, 0xA3)
            M1A0 (Local1, C010, Ones, 0xA4)
            Local0 = Local1 = P91E [0x00]
            M1A0 (Local0, C010, Ones, 0xA5)
            M1A0 (Local1, C010, Ones, 0xA6)
            Local0 = Local1 = P91F [0x00]
            M1A0 (Local0, C010, Ones, 0xA7)
            M1A0 (Local1, C010, Ones, 0xA8)
            Local0 = Local1 = P920 [0x00]
            M1A0 (Local0, C010, Ones, 0xA9)
            M1A0 (Local1, C010, Ones, 0xAA)
            Local0 = Local1 = P921 [0x00]
            M1A0 (Local0, C010, Ones, 0xAB)
            M1A0 (Local1, C010, Ones, 0xAC)
            Local0 = Local1 = P922 [0x00]
            M1A0 (Local0, C010, Ones, 0xAD)
            M1A0 (Local1, C010, Ones, 0xAE)
            Local0 = Local1 = P923 [0x00]
            M1A0 (Local0, C010, Ones, 0xAF)
            M1A0 (Local1, C010, Ones, 0xB0)
            Local0 = Local1 = P924 [0x00]
            M1A0 (Local0, C010, Ones, 0xB1)
            M1A0 (Local1, C010, Ones, 0xB2)
            Local0 = Local1 = P925 [0x00]
            M1A0 (Local0, C010, Ones, 0xB3)
            M1A0 (Local1, C010, Ones, 0xB4)
            Local0 = Local1 = P926 [0x00]
            M1A0 (Local0, C010, Ones, 0xB5)
            M1A0 (Local1, C010, Ones, 0xB6)
            Local0 = Local1 = P927 [0x00]
            M1A0 (Local0, C010, Ones, 0xB7)
            M1A0 (Local1, C010, Ones, 0xB8)
            Local0 = Local1 = P928 [0x00]
            M1A0 (Local0, C010, Ones, 0xB9)
            M1A0 (Local1, C010, Ones, 0xBA)
            Local0 = Local1 = P929 [0x00]
            M1A0 (Local0, C010, Ones, 0xBB)
            M1A0 (Local1, C010, Ones, 0xBC)
            Local0 = Local1 = P92A [0x00]
            M1A0 (Local0, C010, Ones, 0xBD)
            M1A0 (Local1, C010, Ones, 0xBE)
            Local0 = Local1 = P92B [0x00]
            M1A0 (Local0, C010, Ones, 0xBF)
            M1A0 (Local1, C010, Ones, 0xC0)
            Local0 = Local1 = P92C [0x00]
            M1A0 (Local0, C010, Ones, 0xC1)
            M1A0 (Local1, C010, Ones, 0xC2)
            Local0 = Local1 = P92D [0x00]
            M1A0 (Local0, C010, Ones, 0xC3)
            M1A0 (Local1, C010, Ones, 0xC4)
            Local0 = Local1 = P92E [0x00]
            M1A0 (Local0, C010, Ones, 0xC5)
            M1A0 (Local1, C010, Ones, 0xC6)
            Local0 = Local1 = P92F [0x00]
            M1A0 (Local0, C010, Ones, 0xC7)
            M1A0 (Local1, C010, Ones, 0xC8)
            Local0 = Local1 = P930 [0x00]
            M1A0 (Local0, C010, Ones, 0xC9)
            M1A0 (Local1, C010, Ones, 0xCA)
            Local0 = Local1 = P931 [0x00]
            M1A0 (Local0, C010, Ones, 0xCB)
            M1A0 (Local1, C010, Ones, 0xCC)
            Local0 = Local1 = P932 [0x00]
            M1A0 (Local0, C010, Ones, 0xCD)
            M1A0 (Local1, C010, Ones, 0xCE)
            Local0 = Local1 = P933 [0x00]
            M1A0 (Local0, C010, Ones, 0xCF)
            M1A0 (Local1, C010, Ones, 0xD0)
            Local0 = Local1 = P934 [0x00]
            M1A0 (Local0, C010, Ones, 0xD1)
            M1A0 (Local1, C010, Ones, 0xD2)
            If (Y103)
            {
                Local0 = Local1 = P935 [0x00]
                M1A0 (Local0, C010, Ones, 0xD3)
                M1A0 (Local1, C010, Ones, 0xD4)
            }

            Local0 = Local1 = P936 [0x00]
            M1A0 (Local0, C010, Ones, 0xD5)
            M1A0 (Local1, C010, Ones, 0xD6)
            Local0 = Local1 = P937 [0x00]
            M1A0 (Local0, C010, Ones, 0xD7)
            M1A0 (Local1, C010, Ones, 0xD8)
            Local0 = Local1 = P938 [0x00]
            M1A0 (Local0, C010, Ones, 0xD9)
            M1A0 (Local1, C010, Ones, 0xDA)
            Local0 = Local1 = P939 [0x00]
            M1A0 (Local0, C010, Ones, 0xDB)
            M1A0 (Local1, C010, Ones, 0xDC)
            Local0 = Local1 = P93A [0x00]
            M1A0 (Local0, C010, Ones, 0xDD)
            M1A0 (Local1, C010, Ones, 0xDE)
            Local0 = Local1 = P93B [0x00]
            M1A0 (Local0, C010, Ones, 0xDF)
            M1A0 (Local1, C010, Ones, 0xE0)
            Local0 = Local1 = P93C [0x00]
            M1A0 (Local0, C010, Ones, 0xE1)
            M1A0 (Local1, C010, Ones, 0xE2)
            Local0 = Local1 = P93D [0x00]
            M1A0 (Local0, C010, Ones, 0xE3)
            M1A0 (Local1, C010, Ones, 0xE4)
            Local0 = Local1 = P93E [0x00]
            M1A0 (Local0, C010, Ones, 0xE5)
            M1A0 (Local1, C010, Ones, 0xE6)
            Local0 = Local1 = P93F [0x00]
            M1A0 (Local0, C010, Ones, 0xE7)
            M1A0 (Local1, C010, Ones, 0xE8)
            Local0 = Local1 = P940 [0x00]
            M1A0 (Local0, C010, Ones, 0xE9)
            M1A0 (Local1, C010, Ones, 0xEA)
            Local0 = Local1 = P941 [0x00]
            M1A0 (Local0, C010, Ones, 0xEB)
            M1A0 (Local1, C010, Ones, 0xEC)
            Local0 = Local1 = P942 [0x00]
            M1A0 (Local0, C010, Ones, 0xED)
            M1A0 (Local1, C010, Ones, 0xEE)
            Local0 = Local1 = P943 [0x00]
            M1A0 (Local0, C010, Ones, 0xEF)
            M1A0 (Local1, C010, Ones, 0xF0)
            Local0 = Local1 = P944 [0x00]
            M1A0 (Local0, C010, Ones, 0xF1)
            M1A0 (Local1, C010, Ones, 0xF2)
            Local0 = Local1 = P945 [0x00]
            M1A0 (Local0, C010, Ones, 0xF3)
            M1A0 (Local1, C010, Ones, 0xF4)
            Local0 = Local1 = P946 [0x00]
            M1A0 (Local0, C010, Ones, 0xF5)
            M1A0 (Local1, C010, Ones, 0xF6)
            Local0 = Local1 = P947 [0x00]
            M1A0 (Local0, C010, Ones, 0xF7)
            M1A0 (Local1, C010, Ones, 0xF8)
            Local0 = Local1 = P948 [0x00]
            M1A0 (Local0, C010, Ones, 0xF9)
            M1A0 (Local1, C010, Ones, 0xFA)
            Local0 = Local1 = P949 [0x00]
            M1A0 (Local0, C010, Ones, 0xFB)
            M1A0 (Local1, C010, Ones, 0xFC)
            Local0 = Local1 = P94A [0x00]
            M1A0 (Local0, C010, Ones, 0xFD)
            M1A0 (Local1, C010, Ones, 0xFE)
            Local0 = Local1 = P94B [0x00]
            M1A0 (Local0, C010, Ones, 0xFF)
            M1A0 (Local1, C010, Ones, 0x0100)
            Local0 = Local1 = P94C [0x00]
            M1A0 (Local0, C010, Ones, 0x0101)
            M1A0 (Local1, C010, Ones, 0x0102)
            Local0 = Local1 = P94D [0x00]
            M1A0 (Local0, C010, Ones, 0x0103)
            M1A0 (Local1, C010, Ones, 0x0104)
            Local0 = Local1 = P94E [0x00]
            M1A0 (Local0, C010, Ones, 0x0105)
            M1A0 (Local1, C010, Ones, 0x0106)
            Local0 = Local1 = P94F [0x00]
            M1A0 (Local0, C010, Ones, 0x0107)
            M1A0 (Local1, C010, Ones, 0x0108)
            Local0 = Local1 = P950 [0x00]
            M1A0 (Local0, C010, Ones, 0x0109)
            M1A0 (Local1, C010, Ones, 0x010A)
            Local0 = Local1 = P951 [0x00]
            M1A0 (Local0, C010, Ones, 0x010B)
            M1A0 (Local1, C010, Ones, 0x010C)
            Local0 = Local1 = P952 [0x00]
            M1A0 (Local0, C010, Ones, 0x010D)
            M1A0 (Local1, C010, Ones, 0x010E)
        }

        M1A6 ()
    }

    /* m16a but with global data */
    /* arg0 - writing mode */
    Method (M191, 1, NotSerialized)
    {
        If (Y100)
        {
            TS00 ("m191")
        }
        Else
        {
            Debug = "m191"
        }

        /* T2:R1-R14 */
        /* Computational Data */
        Local0 = RefOf (I900)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xFE7CB391D65A0000, __LINE__)
        Local0 = RefOf (I901)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xC1790001, __LINE__)
        Local0 = RefOf (S900)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "12340002", __LINE__)
        Local0 = RefOf (S901)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "qwrtyu0003", __LINE__)
        Local0 = RefOf (B900)
        M1A2 (Local0, C00B, 0x00, 0x00, C00B, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            }, 0x0113)
        /* Not Computational Data */

        Local0 = RefOf (E900)
        M1A0 (Local0, C00F, Ones, 0x0118)
        Local0 = RefOf (MX90)
        M1A0 (Local0, C011, Ones, 0x0119)
        Local0 = RefOf (D900)
        M1A0 (Local0, C00E, Ones, 0x011A)
        If (Arg0)
        {
            If (Y508)
            {
                Local0 = RefOf (TZ90)
                M1A0 (Local0, C015, Ones, 0x011B)
            }
        }
        Else
        {
            Local0 = RefOf (TZ90)
            M1A0 (Local0, C015, Ones, 0x011B)
        }

        Local0 = RefOf (PR90)
        M1A0 (Local0, C014, Ones, 0x011C)
        If (Arg0)
        {
            If (Y510)
            {
                Local0 = RefOf (R900)
                M1A0 (Local0, C012, Ones, 0x011D)
            }
        }
        Else
        {
            Local0 = RefOf (R900)
            M1A0 (Local0, C012, Ones, 0x03EA)
        }

        Local0 = RefOf (PW90)
        M1A0 (Local0, C013, Ones, 0x011E)
        /* Package */

        Local0 = RefOf (P953)
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xABCD0018, __LINE__)
        If (Arg0)
        {
            M1AB ()
            Return (Zero)
        }

        /* Computational Data (Field Unit and Buffer Field) */

        Local0 = RefOf (F900)
        M1A2 (Local0, C00D, 0x00, 0x00, C009, 0x00, __LINE__)
        Local0 = RefOf (BN90)
        M1A2 (Local0, C00D, 0x00, 0x00, C009, 0x00, __LINE__)
        Local0 = RefOf (IF90)
        M1A2 (Local0, C00D, 0x00, 0x00, C009, 0x00, __LINE__)
        Local0 = RefOf (BF90)
        M1A2 (Local0, C016, 0x00, 0x00, C00B, Buffer(){0xB0}, __LINE__)
        /* Elements of Package are Uninitialized */

        Local0 = RefOf (P900)
        M1A0 (Local0, C00C, Ones, 0x011F)
        /* Elements of Package are Computational Data */

        Local0 = RefOf (P901)
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xABCD0004, __LINE__)
        M1A2 (Local0, C00C, 0x01, 0x01, C009, 0x1122334455660005, __LINE__)
        Local0 = RefOf (P902)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "12340006", __LINE__)
        M1A2 (Local0, C00C, 0x01, 0x01, C00A, "q1w2e3r4t5y6u7i80007", __LINE__)
        Local0 = RefOf (P903)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "qwrtyuiop0008", __LINE__)
        M1A2 (Local0, C00C, 0x01, 0x01, C00A, "1234567890abdef0250009", __LINE__)
        Local0 = RefOf (P904)
        M1A2 (Local0, C00C, 0x01, 0x00, C00B, Buffer (0x03)
            {
                 0xB5, 0xB6, 0xB7                                 // ...
            }, 0x0126)
        Local0 = RefOf (P905)
        M1A2 (Local0, C00C, 0x02, 0x00, C009, 0x0ABC000A, __LINE__)
        M1A2 (Local0, C00C, 0x02, 0x01, C00A, "0xabc000b", __LINE__)
        Local0 = RefOf (P906)
        M1A2 (Local0, C00C, 0x02, 0x00, C00A, "abc000d", __LINE__)
        Local0 = RefOf (P907)
        M1A2 (Local0, C00C, 0x02, 0x00, C00A, "aqwevbgnm000e", __LINE__)
        Local0 = RefOf (P908)
        M1A2 (Local0, C00C, 0x02, 0x00, C00B, Buffer (0x05)
            {
                 0xBA, 0xBB, 0xBC, 0xBD, 0xBE                     // .....
            }, 0x012B)
        Local0 = RefOf (P909)
        M1A2 (Local0, C00C, 0x03, 0x00, C009, 0x0ABC000F, __LINE__)
        Local0 = RefOf (P90A)
        M1A2 (Local0, C00C, 0x03, 0x00, C00A, "12340010", __LINE__)
        Local0 = RefOf (P90B)
        M1A2 (Local0, C00C, 0x03, 0x00, C00A, "zxswefas0011", __LINE__)
        Local0 = RefOf (P90C)
        M1A2 (Local0, C00C, 0x03, 0x00, C00B, Buffer (0x03)
            {
                 0xBF, 0xC0, 0xC1                                 // ...
            }, 0x012F)
        Local0 = RefOf (P90D)
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xFE7CB391D65A0000, __LINE__)
        Local0 = RefOf (P90E)
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xC1790001, __LINE__)
        Local0 = RefOf (P90F)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "12340002", __LINE__)
        Local0 = RefOf (P910)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "qwrtyu0003", __LINE__)
        Local0 = RefOf (P911)
        M1A2 (Local0, C00C, 0x01, 0x00, C00B, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            }, 0x0134)
        If (Y118)
        {
            Local0 = RefOf (P912)
            M1A2 (Local0, C00C, 0x01, 0x00, C00D, 0x00, __LINE__)
            Local0 = RefOf (P913)
            M1A2 (Local0, C00C, 0x01, 0x00, C00D, 0x00, __LINE__)
            Local0 = RefOf (P914)
            M1A2 (Local0, C00C, 0x01, 0x00, C00D, 0x00, __LINE__)
            Local0 = RefOf (P915)
            M1A2 (Local0, C00C, 0x01, 0x00, C016, 0xB0, __LINE__)
        }

        /* Elements of Package are NOT Computational Data */

        Local0 = RefOf (P916)
        M1A0 (Local0, C00C, Ones, 0x0139)
        Local0 = RefOf (P917)
        M1A0 (Local0, C00C, Ones, 0x013A)
        Local0 = RefOf (P918)
        M1A0 (Local0, C00C, Ones, 0x013B)
        Local0 = RefOf (P919)
        M1A0 (Local0, C00C, Ones, 0x013C)
        Local0 = RefOf (P91A)
        M1A0 (Local0, C00C, Ones, 0x013D)
        Local0 = RefOf (P91B)
        M1A0 (Local0, C00C, Ones, 0x013E)
        Local0 = RefOf (P91C)
        M1A0 (Local0, C00C, Ones, 0x013F)
        /* Elements of Package are Methods */

        Local0 = RefOf (P91D)
        M1A0 (Local0, C00C, Ones, 0x0140)
        Local0 = RefOf (P91E)
        M1A0 (Local0, C00C, Ones, 0x0141)
        Local0 = RefOf (P91F)
        M1A0 (Local0, C00C, Ones, 0x0142)
        Local0 = RefOf (P920)
        M1A0 (Local0, C00C, Ones, 0x0143)
        Local0 = RefOf (P921)
        M1A0 (Local0, C00C, Ones, 0x0144)
        Local0 = RefOf (P922)
        M1A0 (Local0, C00C, Ones, 0x0145)
        Local0 = RefOf (P923)
        M1A0 (Local0, C00C, Ones, 0x0146)
        Local0 = RefOf (P924)
        M1A0 (Local0, C00C, Ones, 0x0147)
        Local0 = RefOf (P925)
        M1A0 (Local0, C00C, Ones, 0x0148)
        Local0 = RefOf (P926)
        M1A0 (Local0, C00C, Ones, 0x0149)
        Local0 = RefOf (P927)
        M1A0 (Local0, C00C, Ones, 0x014A)
        Local0 = RefOf (P928)
        M1A0 (Local0, C00C, Ones, 0x014B)
        Local0 = RefOf (P929)
        M1A0 (Local0, C00C, Ones, 0x014C)
        Local0 = RefOf (P92A)
        M1A0 (Local0, C00C, Ones, 0x014D)
        Local0 = RefOf (P92B)
        M1A0 (Local0, C00C, Ones, 0x014E)
        Local0 = RefOf (P92C)
        M1A0 (Local0, C00C, Ones, 0x014F)
        Local0 = RefOf (P92D)
        M1A0 (Local0, C00C, Ones, 0x0150)
        Local0 = RefOf (P92E)
        M1A0 (Local0, C00C, Ones, 0x0151)
        Local0 = RefOf (P92F)
        M1A0 (Local0, C00C, Ones, 0x0152)
        Local0 = RefOf (P930)
        M1A0 (Local0, C00C, Ones, 0x0153)
        Local0 = RefOf (P931)
        M1A0 (Local0, C00C, Ones, 0x0154)
        Local0 = RefOf (P932)
        M1A0 (Local0, C00C, Ones, 0x0155)
        Local0 = RefOf (P933)
        M1A0 (Local0, C00C, Ones, 0x0156)
        Local0 = RefOf (P934)
        M1A0 (Local0, C00C, Ones, 0x0157)
        Local0 = RefOf (P935)
        M1A0 (Local0, C00C, Ones, 0x0158)
        Local0 = RefOf (P936)
        M1A0 (Local0, C00C, Ones, 0x0159)
        Local0 = RefOf (P937)
        M1A0 (Local0, C00C, Ones, 0x015A)
        Local0 = RefOf (P938)
        M1A0 (Local0, C00C, Ones, 0x015B)
        Local0 = RefOf (P939)
        M1A0 (Local0, C00C, Ones, 0x015C)
        Local0 = RefOf (P93A)
        M1A0 (Local0, C00C, Ones, 0x015D)
        Local0 = RefOf (P93B)
        M1A0 (Local0, C00C, Ones, 0x015E)
        Local0 = RefOf (P93C)
        M1A0 (Local0, C00C, Ones, 0x015F)
        Local0 = RefOf (P93D)
        M1A0 (Local0, C00C, Ones, 0x0160)
        Local0 = RefOf (P93E)
        M1A0 (Local0, C00C, Ones, 0x0161)
        Local0 = RefOf (P93F)
        M1A0 (Local0, C00C, Ones, 0x0162)
        Local0 = RefOf (P940)
        M1A0 (Local0, C00C, Ones, 0x0163)
        Local0 = RefOf (P941)
        M1A0 (Local0, C00C, Ones, 0x0164)
        Local0 = RefOf (P942)
        M1A0 (Local0, C00C, Ones, 0x0165)
        Local0 = RefOf (P943)
        M1A0 (Local0, C00C, Ones, 0x0166)
        Local0 = RefOf (P944)
        M1A0 (Local0, C00C, Ones, 0x0167)
        Local0 = RefOf (P945)
        M1A0 (Local0, C00C, Ones, 0x0168)
        Local0 = RefOf (P946)
        M1A0 (Local0, C00C, Ones, 0x0169)
        Local0 = RefOf (P947)
        M1A0 (Local0, C00C, Ones, 0x016A)
        Local0 = RefOf (P948)
        M1A0 (Local0, C00C, Ones, 0x016B)
        Local0 = RefOf (P949)
        M1A0 (Local0, C00C, Ones, 0x016C)
        Local0 = RefOf (P94A)
        M1A0 (Local0, C00C, Ones, 0x016D)
        Local0 = RefOf (P94B)
        M1A0 (Local0, C00C, Ones, 0x016E)
        Local0 = RefOf (P94C)
        M1A0 (Local0, C00C, Ones, 0x016F)
        Local0 = RefOf (P94D)
        M1A0 (Local0, C00C, Ones, 0x0170)
        Local0 = RefOf (P94E)
        M1A0 (Local0, C00C, Ones, 0x0171)
        Local0 = RefOf (P94F)
        M1A0 (Local0, C00C, Ones, 0x0172)
        Local0 = RefOf (P950)
        M1A0 (Local0, C00C, Ones, 0x0173)
        Local0 = RefOf (P951)
        M1A0 (Local0, C00C, Ones, 0x0174)
        Local0 = RefOf (P952)
        M1A0 (Local0, C00C, Ones, 0x0175)
        /* Methods */

        Local0 = RefOf (M900)
        M1A0 (Local0, C010, Ones, 0x0176)
        Local0 = RefOf (M901)
        M1A0 (Local0, C010, Ones, 0x0177)
        Local0 = RefOf (M902)
        M1A0 (Local0, C010, Ones, 0x0178)
        Local0 = RefOf (M903)
        M1A0 (Local0, C010, Ones, 0x0179)
        Local0 = RefOf (M904)
        M1A0 (Local0, C010, Ones, 0x017A)
        Local0 = RefOf (M905)
        M1A0 (Local0, C010, Ones, 0x017B)
        Local0 = RefOf (M906)
        M1A0 (Local0, C010, Ones, 0x017C)
        Local0 = RefOf (M907)
        M1A0 (Local0, C010, Ones, 0x017D)
        Local0 = RefOf (M908)
        M1A0 (Local0, C010, Ones, 0x017E)
        Local0 = RefOf (M909)
        M1A0 (Local0, C010, Ones, 0x017F)
        Local0 = RefOf (M90A)
        M1A0 (Local0, C010, Ones, 0x0180)
        Local0 = RefOf (M90B)
        M1A0 (Local0, C010, Ones, 0x0181)
        Local0 = RefOf (M90C)
        M1A0 (Local0, C010, Ones, 0x0182)
        Local0 = RefOf (M90D)
        M1A0 (Local0, C010, Ones, 0x0183)
        Local0 = RefOf (M90E)
        M1A0 (Local0, C010, Ones, 0x0184)
        Local0 = RefOf (M90F)
        M1A0 (Local0, C010, Ones, 0x0185)
        Local0 = RefOf (M910)
        M1A0 (Local0, C010, Ones, 0x0186)
        Local0 = RefOf (M911)
        M1A0 (Local0, C010, Ones, 0x0187)
        Local0 = RefOf (M912)
        M1A0 (Local0, C010, Ones, 0x0188)
        Local0 = RefOf (M913)
        M1A0 (Local0, C010, Ones, 0x0189)
        Local0 = RefOf (M914)
        M1A0 (Local0, C010, Ones, 0x018A)
        Local0 = RefOf (M915)
        M1A0 (Local0, C010, Ones, 0x018B)
        Local0 = RefOf (M916)
        M1A0 (Local0, C010, Ones, 0x018C)
        Local0 = RefOf (M917)
        M1A0 (Local0, C010, Ones, 0x018D)
        Local0 = RefOf (M918)
        M1A0 (Local0, C010, Ones, 0x018E)
        Local0 = RefOf (M919)
        M1A0 (Local0, C010, Ones, 0x018F)
        Local0 = RefOf (M91A)
        M1A0 (Local0, C010, Ones, 0x0190)
        Local0 = RefOf (M91B)
        M1A0 (Local0, C010, Ones, 0x0191)
        Local0 = RefOf (M91C)
        M1A0 (Local0, C010, Ones, 0x0192)
        Local0 = RefOf (M91D)
        M1A0 (Local0, C010, Ones, 0x0193)
        Local0 = RefOf (M91E)
        M1A0 (Local0, C010, Ones, 0x0194)
        Local0 = RefOf (M91F)
        M1A0 (Local0, C010, Ones, 0x0195)
        Local0 = RefOf (M920)
        M1A0 (Local0, C010, Ones, 0x0196)
        Local0 = RefOf (M921)
        M1A0 (Local0, C010, Ones, 0x0197)
        Local0 = RefOf (M922)
        M1A0 (Local0, C010, Ones, 0x0198)
        Local0 = RefOf (M923)
        M1A0 (Local0, C010, Ones, 0x0199)
        Local0 = RefOf (M924)
        M1A0 (Local0, C010, Ones, 0x019A)
        Local0 = RefOf (M925)
        M1A0 (Local0, C010, Ones, 0x019B)
        Local0 = RefOf (M926)
        M1A0 (Local0, C010, Ones, 0x019C)
        Local0 = RefOf (M927)
        M1A0 (Local0, C010, Ones, 0x019D)
        Local0 = RefOf (M928)
        M1A0 (Local0, C010, Ones, 0x019E)
        Local0 = RefOf (M929)
        M1A0 (Local0, C010, Ones, 0x019F)
        Local0 = RefOf (M92A)
        M1A0 (Local0, C010, Ones, 0x01A0)
        Local0 = RefOf (M92B)
        M1A0 (Local0, C010, Ones, 0x01A1)
        Local0 = RefOf (M92C)
        M1A0 (Local0, C010, Ones, 0x01A2)
        Local0 = RefOf (M92D)
        M1A0 (Local0, C010, Ones, 0x01A3)
        Local0 = RefOf (M92E)
        M1A0 (Local0, C010, Ones, 0x01A4)
        Local0 = RefOf (M92F)
        M1A0 (Local0, C010, Ones, 0x01A5)
        Local0 = RefOf (M930)
        M1A0 (Local0, C010, Ones, 0x01A6)
        Local0 = RefOf (M931)
        M1A0 (Local0, C010, Ones, 0x01A7)
        Local0 = RefOf (M932)
        M1A0 (Local0, C010, Ones, 0x01A8)
        Local0 = RefOf (M933)
        M1A0 (Local0, C010, Ones, 0x01A9)
        Local0 = RefOf (M934)
        M1A0 (Local0, C010, Ones, 0x01AA)
        Local0 = RefOf (M935)
        M1A0 (Local0, C010, Ones, 0x01AB)
        M1A6 ()
        Return (Zero)
    }

    /* m16b but with global data */

    Method (M192, 0, NotSerialized)
    {
        If (Y100)
        {
            TS00 ("m192")
        }
        Else
        {
            Debug = "m192"
        }

        /* T2:C1-C14 */
        /* Computational Data */
        Local0 = CondRefOf (I900)
        M1A4 (Local0, 0x01AC)
        Local0 = CondRefOf (I901)
        M1A4 (Local0, 0x01AD)
        Local0 = CondRefOf (S900)
        M1A4 (Local0, 0x01AE)
        Local0 = CondRefOf (S901)
        M1A4 (Local0, 0x01AF)
        Local0 = CondRefOf (B900)
        M1A4 (Local0, 0x01B0)
        Local0 = CondRefOf (F900)
        M1A4 (Local0, 0x01B1)
        Local0 = CondRefOf (BN90)
        M1A4 (Local0, 0x01B2)
        Local0 = CondRefOf (IF90)
        M1A4 (Local0, 0x01B3)
        Local0 = CondRefOf (BF90)
        M1A4 (Local0, 0x01B4)
        /* Not Computational Data */

        Local0 = CondRefOf (E900)
        M1A4 (Local0, 0x01B5)
        Local0 = CondRefOf (MX90)
        M1A4 (Local0, 0x01B6)
        Local0 = CondRefOf (D900)
        M1A4 (Local0, 0x01B7)
        Local0 = CondRefOf (TZ90)
        M1A4 (Local0, 0x01C2)
        Local0 = CondRefOf (PR90)
        M1A4 (Local0, 0x01C3)
        Local0 = CondRefOf (R900)
        M1A4 (Local0, 0x01C4)
        Local0 = CondRefOf (PW90)
        M1A4 (Local0, 0x01C5)
        /* Elements of Package are Uninitialized */

        Local0 = CondRefOf (P900)
        M1A4 (Local0, 0x01C6)
        /* Elements of Package are Computational Data */

        Local0 = CondRefOf (P901)
        M1A4 (Local0, 0x01C7)
        Local0 = CondRefOf (P902)
        M1A4 (Local0, 0x01C8)
        Local0 = CondRefOf (P903)
        M1A4 (Local0, 0x01C9)
        Local0 = CondRefOf (P904)
        M1A4 (Local0, 0x01CA)
        Local0 = CondRefOf (P905)
        M1A4 (Local0, 0x01CB)
        Local0 = CondRefOf (P906)
        M1A4 (Local0, 0x01CC)
        Local0 = CondRefOf (P907)
        M1A4 (Local0, 0x01CD)
        Local0 = CondRefOf (P908)
        M1A4 (Local0, 0x01CE)
        Local0 = CondRefOf (P909)
        M1A4 (Local0, 0x01CF)
        Local0 = CondRefOf (P90A)
        M1A4 (Local0, 0x01D0)
        Local0 = CondRefOf (P90B)
        M1A4 (Local0, 0x01D1)
        Local0 = CondRefOf (P90C)
        M1A4 (Local0, 0x01D2)
        Local0 = CondRefOf (P90D)
        M1A4 (Local0, 0x01D3)
        Local0 = CondRefOf (P90E)
        M1A4 (Local0, 0x01D4)
        Local0 = CondRefOf (P90F)
        M1A4 (Local0, 0x01D5)
        Local0 = CondRefOf (P910)
        M1A4 (Local0, 0x01D6)
        Local0 = CondRefOf (P911)
        M1A4 (Local0, 0x01D7)
        Local0 = CondRefOf (P912)
        M1A4 (Local0, 0x01D8)
        Local0 = CondRefOf (P913)
        M1A4 (Local0, 0x01D9)
        Local0 = CondRefOf (P914)
        M1A4 (Local0, 0x01DA)
        Local0 = CondRefOf (P915)
        M1A4 (Local0, 0x01DB)
        /* Elements of Package are NOT Computational Data */

        Local0 = CondRefOf (P916)
        M1A4 (Local0, 0x01DC)
        Local0 = CondRefOf (P917)
        M1A4 (Local0, 0x01DD)
        Local0 = CondRefOf (P918)
        M1A4 (Local0, 0x01DE)
        Local0 = CondRefOf (P919)
        M1A4 (Local0, 0x01DF)
        Local0 = CondRefOf (P91A)
        M1A4 (Local0, 0x01E0)
        Local0 = CondRefOf (P91B)
        M1A4 (Local0, 0x01E1)
        Local0 = CondRefOf (P91C)
        M1A4 (Local0, 0x01E2)
        /* Elements of Package are Methods */

        Local0 = CondRefOf (P91D)
        M1A4 (Local0, 0x01E3)
        Local0 = CondRefOf (P91E)
        M1A4 (Local0, 0x01E4)
        Local0 = CondRefOf (P91F)
        M1A4 (Local0, 0x01E5)
        Local0 = CondRefOf (P920)
        M1A4 (Local0, 0x01E6)
        Local0 = CondRefOf (P921)
        M1A4 (Local0, 0x01E7)
        Local0 = CondRefOf (P922)
        M1A4 (Local0, 0x01E8)
        Local0 = CondRefOf (P923)
        M1A4 (Local0, 0x01E9)
        Local0 = CondRefOf (P924)
        M1A4 (Local0, 0x01EA)
        Local0 = CondRefOf (P925)
        M1A4 (Local0, 0x01EB)
        Local0 = CondRefOf (P926)
        M1A4 (Local0, 0x01EC)
        Local0 = CondRefOf (P927)
        M1A4 (Local0, 0x01ED)
        Local0 = CondRefOf (P928)
        M1A4 (Local0, 0x01EE)
        Local0 = CondRefOf (P929)
        M1A4 (Local0, 0x01EF)
        Local0 = CondRefOf (P92A)
        M1A4 (Local0, 0x01F0)
        Local0 = CondRefOf (P92B)
        M1A4 (Local0, 0x01F1)
        Local0 = CondRefOf (P92C)
        M1A4 (Local0, 0x01F2)
        Local0 = CondRefOf (P92D)
        M1A4 (Local0, 0x01F3)
        Local0 = CondRefOf (P92E)
        M1A4 (Local0, 0x01F4)
        Local0 = CondRefOf (P92F)
        M1A4 (Local0, 0x01F5)
        Local0 = CondRefOf (P930)
        M1A4 (Local0, 0x01F6)
        Local0 = CondRefOf (P931)
        M1A4 (Local0, 0x01F7)
        Local0 = CondRefOf (P932)
        M1A4 (Local0, 0x01F8)
        Local0 = CondRefOf (P933)
        M1A4 (Local0, 0x01F9)
        Local0 = CondRefOf (P934)
        M1A4 (Local0, 0x01FA)
        Local0 = CondRefOf (P935)
        M1A4 (Local0, 0x01FB)
        Local0 = CondRefOf (P936)
        M1A4 (Local0, 0x01FC)
        Local0 = CondRefOf (P937)
        M1A4 (Local0, 0x01FD)
        Local0 = CondRefOf (P938)
        M1A4 (Local0, 0x01FE)
        Local0 = CondRefOf (P939)
        M1A4 (Local0, 0x01FF)
        Local0 = CondRefOf (P93A)
        M1A4 (Local0, 0x0200)
        Local0 = CondRefOf (P93B)
        M1A4 (Local0, 0x0201)
        Local0 = CondRefOf (P93C)
        M1A4 (Local0, 0x0202)
        Local0 = CondRefOf (P93D)
        M1A4 (Local0, 0x0203)
        Local0 = CondRefOf (P93E)
        M1A4 (Local0, 0x0204)
        Local0 = CondRefOf (P93F)
        M1A4 (Local0, 0x0205)
        Local0 = CondRefOf (P940)
        M1A4 (Local0, 0x0206)
        Local0 = CondRefOf (P941)
        M1A4 (Local0, 0x0207)
        Local0 = CondRefOf (P942)
        M1A4 (Local0, 0x0208)
        Local0 = CondRefOf (P943)
        M1A4 (Local0, 0x0209)
        Local0 = CondRefOf (P944)
        M1A4 (Local0, 0x020A)
        Local0 = CondRefOf (P945)
        M1A4 (Local0, 0x020B)
        Local0 = CondRefOf (P946)
        M1A4 (Local0, 0x020C)
        Local0 = CondRefOf (P947)
        M1A4 (Local0, 0x020D)
        Local0 = CondRefOf (P948)
        M1A4 (Local0, 0x020E)
        Local0 = CondRefOf (P949)
        M1A4 (Local0, 0x020F)
        Local0 = CondRefOf (P94A)
        M1A4 (Local0, 0x0210)
        Local0 = CondRefOf (P94B)
        M1A4 (Local0, 0x0211)
        Local0 = CondRefOf (P94C)
        M1A4 (Local0, 0x0212)
        Local0 = CondRefOf (P94D)
        M1A4 (Local0, 0x0213)
        Local0 = CondRefOf (P94E)
        M1A4 (Local0, 0x0214)
        Local0 = CondRefOf (P94F)
        M1A4 (Local0, 0x0215)
        Local0 = CondRefOf (P950)
        M1A4 (Local0, 0x0216)
        Local0 = CondRefOf (P951)
        M1A4 (Local0, 0x0217)
        Local0 = CondRefOf (P952)
        M1A4 (Local0, 0x0218)
        /* Methods */

        Local0 = CondRefOf (M900)
        M1A4 (Local0, 0x0219)
        Local0 = CondRefOf (M901)
        M1A4 (Local0, 0x021A)
        Local0 = CondRefOf (M902)
        M1A4 (Local0, 0x021B)
        Local0 = CondRefOf (M903)
        M1A4 (Local0, 0x021C)
        Local0 = CondRefOf (M904)
        M1A4 (Local0, 0x021D)
        Local0 = CondRefOf (M905)
        M1A4 (Local0, 0x021E)
        Local0 = CondRefOf (M906)
        M1A4 (Local0, 0x021F)
        Local0 = CondRefOf (M907)
        M1A4 (Local0, 0x0220)
        Local0 = CondRefOf (M908)
        M1A4 (Local0, 0x0221)
        Local0 = CondRefOf (M909)
        M1A4 (Local0, 0x0222)
        Local0 = CondRefOf (M90A)
        M1A4 (Local0, 0x0223)
        Local0 = CondRefOf (M90B)
        M1A4 (Local0, 0x0224)
        Local0 = CondRefOf (M90C)
        M1A4 (Local0, 0x0225)
        Local0 = CondRefOf (M90D)
        M1A4 (Local0, 0x0226)
        Local0 = CondRefOf (M90E)
        M1A4 (Local0, 0x0227)
        Local0 = CondRefOf (M90F)
        M1A4 (Local0, 0x0228)
        Local0 = CondRefOf (M910)
        M1A4 (Local0, 0x0229)
        Local0 = CondRefOf (M911)
        M1A4 (Local0, 0x022A)
        Local0 = CondRefOf (M912)
        M1A4 (Local0, 0x022B)
        Local0 = CondRefOf (M913)
        M1A4 (Local0, 0x022C)
        Local0 = CondRefOf (M914)
        M1A4 (Local0, 0x022D)
        Local0 = CondRefOf (M915)
        M1A4 (Local0, 0x022E)
        Local0 = CondRefOf (M916)
        M1A4 (Local0, 0x022F)
        Local0 = CondRefOf (M917)
        M1A4 (Local0, 0x0230)
        Local0 = CondRefOf (M918)
        M1A4 (Local0, 0x0231)
        Local0 = CondRefOf (M919)
        M1A4 (Local0, 0x0232)
        Local0 = CondRefOf (M91A)
        M1A4 (Local0, 0x0233)
        Local0 = CondRefOf (M91B)
        M1A4 (Local0, 0x0234)
        Local0 = CondRefOf (M91C)
        M1A4 (Local0, 0x0235)
        Local0 = CondRefOf (M91D)
        M1A4 (Local0, 0x0236)
        Local0 = CondRefOf (M91E)
        M1A4 (Local0, 0x0237)
        Local0 = CondRefOf (M91F)
        M1A4 (Local0, 0x0238)
        Local0 = CondRefOf (M920)
        M1A4 (Local0, 0x0239)
        Local0 = CondRefOf (M921)
        M1A4 (Local0, 0x023A)
        Local0 = CondRefOf (M922)
        M1A4 (Local0, 0x023B)
        Local0 = CondRefOf (M923)
        M1A4 (Local0, 0x023C)
        Local0 = CondRefOf (M924)
        M1A4 (Local0, 0x023D)
        Local0 = CondRefOf (M925)
        M1A4 (Local0, 0x023E)
        Local0 = CondRefOf (M926)
        M1A4 (Local0, 0x023F)
        Local0 = CondRefOf (M927)
        M1A4 (Local0, 0x0240)
        Local0 = CondRefOf (M928)
        M1A4 (Local0, 0x0241)
        Local0 = CondRefOf (M929)
        M1A4 (Local0, 0x0242)
        Local0 = CondRefOf (M92A)
        M1A4 (Local0, 0x0243)
        Local0 = CondRefOf (M92B)
        M1A4 (Local0, 0x0244)
        Local0 = CondRefOf (M92C)
        M1A4 (Local0, 0x0245)
        Local0 = CondRefOf (M92D)
        M1A4 (Local0, 0x0246)
        Local0 = CondRefOf (M92E)
        M1A4 (Local0, 0x0247)
        Local0 = CondRefOf (M92F)
        M1A4 (Local0, 0x0248)
        Local0 = CondRefOf (M930)
        M1A4 (Local0, 0x0249)
        Local0 = CondRefOf (M931)
        M1A4 (Local0, 0x024A)
        Local0 = CondRefOf (M932)
        M1A4 (Local0, 0x024B)
        Local0 = CondRefOf (M933)
        M1A4 (Local0, 0x024C)
        Local0 = CondRefOf (M934)
        M1A4 (Local0, 0x024D)
        Local0 = CondRefOf (M935)
        M1A4 (Local0, 0x024E)
        M1A6 ()
    }

    /* m16c but with global data */
    /* arg0 - writing mode */
    Method (M193, 1, NotSerialized)
    {
        If (Y100)
        {
            TS00 ("m193")
        }
        Else
        {
            Debug = "m193"
        }

        /* T2:CR1-CR14 */
        /* Computational Data */
        Local1 = CondRefOf (I900, Local0)
        If (M1A4 (Local1, 0x024F))
        {
            M1A2 (Local0, C009, 0x00, 0x00, C009, 0xFE7CB391D65A0000, __LINE__)
        }

        Local1 = CondRefOf (I901, Local0)
        If (M1A4 (Local1, 0x0251))
        {
            M1A2 (Local0, C009, 0x00, 0x00, C009, 0xC1790001, __LINE__)
        }

        Local1 = CondRefOf (S900, Local0)
        If (M1A4 (Local1, 0x0253))
        {
            M1A2 (Local0, C00A, 0x00, 0x00, C00A, "12340002", __LINE__)
        }

        Local1 = CondRefOf (S901, Local0)
        If (M1A4 (Local1, 0x0255))
        {
            M1A2 (Local0, C00A, 0x00, 0x00, C00A, "qwrtyu0003", __LINE__)
        }

        Local1 = CondRefOf (B900, Local0)
        If (M1A4 (Local1, 0x0257))
        {
            M1A2 (Local0, C00B, 0x00, 0x00, C00B, Buffer (0x05)
                {
                     0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
                }, 0x0258)
        }

        /* Not Computational Data */

        Local1 = CondRefOf (E900, Local0)
        M1A0 (Local0, C00F, Local1, 0x0261)
        Local1 = CondRefOf (MX90, Local0)
        M1A0 (Local0, C011, Local1, 0x0262)
        Local1 = CondRefOf (D900, Local0)
        M1A0 (Local0, C00E, Local1, 0x0263)
        If (Arg0)
        {
            If (Y508)
            {
                Local1 = CondRefOf (TZ90, Local0)
                M1A0 (Local0, C015, Local1, 0x0264)
            }
        }
        Else
        {
            Local1 = CondRefOf (TZ90, Local0)
            M1A0 (Local0, C015, Local1, 0x03EC)
        }

        Local1 = CondRefOf (PR90, Local0)
        M1A0 (Local0, C014, Local1, 0x0265)
        If (Arg0)
        {
            If (Y510)
            {
                Local1 = CondRefOf (R900, Local0)
                M1A0 (Local0, C012, Local1, 0x0266)
            }
        }
        Else
        {
            Local1 = CondRefOf (R900, Local0)
            M1A0 (Local0, C012, Local1, 0x0266)
        }

        Local1 = CondRefOf (PW90, Local0)
        M1A0 (Local0, C013, Local1, 0x0267)
        /* Package */

        Local1 = CondRefOf (P953, Local0)
        If (M1A4 (Local1, 0x03ED))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xABCD0018, __LINE__)
        }

        If (Arg0)
        {
            M1AB ()
            Return (Zero)
        }

        /* Computational Data (Field Unit and Buffer Field) */

        Local1 = CondRefOf (F900, Local0)
        If (M1A4 (Local1, 0x0259))
        {
            M1A2 (Local0, C00D, 0x00, 0x00, C009, 0x00, __LINE__)
        }

        Local1 = CondRefOf (BN90, Local0)
        If (M1A4 (Local1, 0x025B))
        {
            M1A2 (Local0, C00D, 0x00, 0x00, C009, 0x00, __LINE__)
        }

        Local1 = CondRefOf (IF90, Local0)
        If (M1A4 (Local1, 0x025D))
        {
            M1A2 (Local0, C00D, 0x00, 0x00, C009, 0x00, __LINE__)
        }

        Local1 = CondRefOf (BF90, Local0)
        If (M1A4 (Local1, 0x025F))
        {
            M1A2 (Local0, C016, 0x00, 0x00, C00B, Buffer(){0xB0}, __LINE__)
        }

        /* Elements of Package are Uninitialized */

        Local1 = CondRefOf (P900, Local0)
        M1A0 (Local0, C00C, Local1, 0x0268)
        /* Elements of Package are Computational Data */

        Local1 = CondRefOf (P901, Local0)
        If (M1A4 (Local1, 0x0269))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xABCD0004, __LINE__)
            M1A2 (Local0, C00C, 0x01, 0x01, C009, 0x1122334455660005, __LINE__)
        }

        Local1 = CondRefOf (P902, Local0)
        If (M1A4 (Local1, 0x026C))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C00A, "12340006", __LINE__)
            M1A2 (Local0, C00C, 0x01, 0x01, C00A, "q1w2e3r4t5y6u7i80007", __LINE__)
        }

        Local1 = CondRefOf (P903, Local0)
        If (M1A4 (Local1, 0x026F))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C00A, "qwrtyuiop0008", __LINE__)
            M1A2 (Local0, C00C, 0x01, 0x01, C00A, "1234567890abdef0250009", __LINE__)
        }

        Local1 = CondRefOf (P904, Local0)
        If (M1A4 (Local1, 0x0272))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C00B, Buffer (0x03)
                {
                     0xB5, 0xB6, 0xB7                                 // ...
                }, 0x0273)
        }

        Local1 = CondRefOf (P905, Local0)
        If (M1A4 (Local1, 0x0274))
        {
            M1A2 (Local0, C00C, 0x02, 0x00, C009, 0x0ABC000A, __LINE__)
            M1A2 (Local0, C00C, 0x02, 0x01, C00A, "0xabc000b", __LINE__)
        }

        Local1 = CondRefOf (P906, Local0)
        If (M1A4 (Local1, 0x0277))
        {
            M1A2 (Local0, C00C, 0x02, 0x00, C00A, "abc000d", __LINE__)
        }

        Local1 = CondRefOf (P907, Local0)
        If (M1A4 (Local1, 0x0279))
        {
            M1A2 (Local0, C00C, 0x02, 0x00, C00A, "aqwevbgnm000e", __LINE__)
        }

        Local1 = CondRefOf (P908, Local0)
        If (M1A4 (Local1, 0x027B))
        {
            M1A2 (Local0, C00C, 0x02, 0x00, C00B, Buffer (0x05)
                {
                     0xBA, 0xBB, 0xBC, 0xBD, 0xBE                     // .....
                }, 0x027C)
        }

        Local1 = CondRefOf (P909, Local0)
        If (M1A4 (Local1, 0x027D))
        {
            M1A2 (Local0, C00C, 0x03, 0x00, C009, 0x0ABC000F, __LINE__)
        }

        Local1 = CondRefOf (P90A, Local0)
        If (M1A4 (Local1, 0x027F))
        {
            M1A2 (Local0, C00C, 0x03, 0x00, C00A, "12340010", __LINE__)
        }

        Local1 = CondRefOf (P90B, Local0)
        If (M1A4 (Local1, 0x0281))
        {
            M1A2 (Local0, C00C, 0x03, 0x00, C00A, "zxswefas0011", __LINE__)
        }

        Local1 = CondRefOf (P90C, Local0)
        If (M1A4 (Local1, 0x0283))
        {
            M1A2 (Local0, C00C, 0x03, 0x00, C00B, Buffer (0x03)
                {
                     0xBF, 0xC0, 0xC1                                 // ...
                }, 0x0284)
        }

        Local1 = CondRefOf (P90D, Local0)
        If (M1A4 (Local1, 0x0285))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xFE7CB391D65A0000, __LINE__)
        }

        Local1 = CondRefOf (P90E, Local0)
        If (M1A4 (Local1, 0x0287))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xC1790001, __LINE__)
        }

        Local1 = CondRefOf (P90F, Local0)
        If (M1A4 (Local1, 0x0289))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C00A, "12340002", __LINE__)
        }

        Local1 = CondRefOf (P910, Local0)
        If (M1A4 (Local1, 0x028B))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C00A, "qwrtyu0003", __LINE__)
        }

        Local1 = CondRefOf (P911, Local0)
        If (M1A4 (Local1, 0x028D))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C00B, Buffer (0x05)
                {
                     0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
                }, 0x028E)
        }

        If (Y118)
        {
            Local1 = CondRefOf (P912, Local0)
            If (M1A4 (Local1, 0x028F))
            {
                M1A2 (Local0, C00C, 0x01, 0x00, C00D, 0x00, __LINE__)
            }

            Local1 = CondRefOf (P913, Local0)
            If (M1A4 (Local1, 0x0291))
            {
                M1A2 (Local0, C00C, 0x01, 0x00, C00D, 0x00, __LINE__)
            }

            Local1 = CondRefOf (P914, Local0)
            If (M1A4 (Local1, 0x0293))
            {
                M1A2 (Local0, C00C, 0x01, 0x00, C00D, 0x00, __LINE__)
            }

            Local1 = CondRefOf (P915, Local0)
            If (M1A4 (Local1, 0x0295))
            {
                M1A2 (Local0, C00C, 0x01, 0x00, C016, 0xB0, __LINE__)
            }
        }

        /* Elements of Package are NOT Computational Data */

        Local1 = CondRefOf (P916, Local0)
        M1A0 (Local0, C00C, Local1, 0x0297)
        Local1 = CondRefOf (P917, Local0)
        M1A0 (Local0, C00C, Local1, 0x0298)
        Local1 = CondRefOf (P918, Local0)
        M1A0 (Local0, C00C, Local1, 0x19FF)
        Local1 = CondRefOf (P919, Local0)
        M1A0 (Local0, C00C, Local1, 0x029A)
        Local1 = CondRefOf (P91A, Local0)
        M1A0 (Local0, C00C, Local1, 0x029B)
        Local1 = CondRefOf (P91B, Local0)
        M1A0 (Local0, C00C, Local1, 0x029C)
        Local1 = CondRefOf (P91C, Local0)
        M1A0 (Local0, C00C, Local1, 0x029D)
        /* Elements of Package are Methods */

        Local1 = CondRefOf (P91D, Local0)
        M1A0 (Local0, C00C, Local1, 0x029E)
        Local1 = CondRefOf (P91E, Local0)
        M1A0 (Local0, C00C, Local1, 0x029F)
        Local1 = CondRefOf (P91F, Local0)
        M1A0 (Local0, C00C, Local1, 0x02A0)
        Local1 = CondRefOf (P920, Local0)
        M1A0 (Local0, C00C, Local1, 0x02A1)
        Local1 = CondRefOf (P921, Local0)
        M1A0 (Local0, C00C, Local1, 0x02A2)
        Local1 = CondRefOf (P922, Local0)
        M1A0 (Local0, C00C, Local1, 0x02A3)
        Local1 = CondRefOf (P923, Local0)
        M1A0 (Local0, C00C, Local1, 0x02A4)
        Local1 = CondRefOf (P924, Local0)
        M1A0 (Local0, C00C, Local1, 0x02A5)
        Local1 = CondRefOf (P925, Local0)
        M1A0 (Local0, C00C, Local1, 0x02A6)
        Local1 = CondRefOf (P926, Local0)
        M1A0 (Local0, C00C, Local1, 0x02A7)
        Local1 = CondRefOf (P927, Local0)
        M1A0 (Local0, C00C, Local1, 0x02A8)
        Local1 = CondRefOf (P928, Local0)
        M1A0 (Local0, C00C, Local1, 0x02A9)
        Local1 = CondRefOf (P929, Local0)
        M1A0 (Local0, C00C, Local1, 0x02AA)
        Local1 = CondRefOf (P92A, Local0)
        M1A0 (Local0, C00C, Local1, 0x02AB)
        Local1 = CondRefOf (P92B, Local0)
        M1A0 (Local0, C00C, Local1, 0x02AC)
        Local1 = CondRefOf (P92C, Local0)
        M1A0 (Local0, C00C, Local1, 0x02AD)
        Local1 = CondRefOf (P92D, Local0)
        M1A0 (Local0, C00C, Local1, 0x02AE)
        Local1 = CondRefOf (P92E, Local0)
        M1A0 (Local0, C00C, Local1, 0x02AF)
        Local1 = CondRefOf (P92F, Local0)
        M1A0 (Local0, C00C, Local1, 0x02B0)
        Local1 = CondRefOf (P930, Local0)
        M1A0 (Local0, C00C, Local1, 0x02B1)
        Local1 = CondRefOf (P931, Local0)
        M1A0 (Local0, C00C, Local1, 0x02B2)
        Local1 = CondRefOf (P932, Local0)
        M1A0 (Local0, C00C, Local1, 0x02B3)
        Local1 = CondRefOf (P933, Local0)
        M1A0 (Local0, C00C, Local1, 0x02B4)
        Local1 = CondRefOf (P934, Local0)
        M1A0 (Local0, C00C, Local1, 0x02B5)
        Local1 = CondRefOf (P935, Local0)
        M1A0 (Local0, C00C, Local1, 0x02B6)
        Local1 = CondRefOf (P936, Local0)
        M1A0 (Local0, C00C, Local1, 0x02B7)
        Local1 = CondRefOf (P937, Local0)
        M1A0 (Local0, C00C, Local1, 0x02B8)
        Local1 = CondRefOf (P938, Local0)
        M1A0 (Local0, C00C, Local1, 0x02B9)
        Local1 = CondRefOf (P939, Local0)
        M1A0 (Local0, C00C, Local1, 0x02BA)
        Local1 = CondRefOf (P93A, Local0)
        M1A0 (Local0, C00C, Local1, 0x02BB)
        Local1 = CondRefOf (P93B, Local0)
        M1A0 (Local0, C00C, Local1, 0x02BC)
        Local1 = CondRefOf (P93C, Local0)
        M1A0 (Local0, C00C, Local1, 0x02BD)
        Local1 = CondRefOf (P93D, Local0)
        M1A0 (Local0, C00C, Local1, 0x02BE)
        Local1 = CondRefOf (P93E, Local0)
        M1A0 (Local0, C00C, Local1, 0x02BF)
        Local1 = CondRefOf (P93F, Local0)
        M1A0 (Local0, C00C, Local1, 0x02C0)
        Local1 = CondRefOf (P940, Local0)
        M1A0 (Local0, C00C, Local1, 0x02C1)
        Local1 = CondRefOf (P941, Local0)
        M1A0 (Local0, C00C, Local1, 0x02C2)
        Local1 = CondRefOf (P942, Local0)
        M1A0 (Local0, C00C, Local1, 0x02C3)
        Local1 = CondRefOf (P943, Local0)
        M1A0 (Local0, C00C, Local1, 0x02C4)
        Local1 = CondRefOf (P944, Local0)
        M1A0 (Local0, C00C, Local1, 0x02C5)
        Local1 = CondRefOf (P945, Local0)
        M1A0 (Local0, C00C, Local1, 0x02C6)
        Local1 = CondRefOf (P946, Local0)
        M1A0 (Local0, C00C, Local1, 0x02C7)
        Local1 = CondRefOf (P947, Local0)
        M1A0 (Local0, C00C, Local1, 0x02C8)
        Local1 = CondRefOf (P948, Local0)
        M1A0 (Local0, C00C, Local1, 0x02C9)
        Local1 = CondRefOf (P949, Local0)
        M1A0 (Local0, C00C, Local1, 0x02CA)
        Local1 = CondRefOf (P94A, Local0)
        M1A0 (Local0, C00C, Local1, 0x02CB)
        Local1 = CondRefOf (P94B, Local0)
        M1A0 (Local0, C00C, Local1, 0x02CC)
        Local1 = CondRefOf (P94C, Local0)
        M1A0 (Local0, C00C, Local1, 0x02CD)
        Local1 = CondRefOf (P94D, Local0)
        M1A0 (Local0, C00C, Local1, 0x02CE)
        Local1 = CondRefOf (P94E, Local0)
        M1A0 (Local0, C00C, Local1, 0x02CF)
        Local1 = CondRefOf (P94F, Local0)
        M1A0 (Local0, C00C, Local1, 0x02D0)
        Local1 = CondRefOf (P950, Local0)
        M1A0 (Local0, C00C, Local1, 0x02D1)
        Local1 = CondRefOf (P951, Local0)
        M1A0 (Local0, C00C, Local1, 0x02D2)
        Local1 = CondRefOf (P952, Local0)
        M1A0 (Local0, C00C, Local1, 0x02D3)
        /* Methods */

        Local1 = CondRefOf (M900, Local0)
        M1A0 (Local0, C010, Local1, 0x02D4)
        Local1 = CondRefOf (M901, Local0)
        M1A0 (Local0, C010, Local1, 0x02D5)
        Local1 = CondRefOf (M902, Local0)
        M1A0 (Local0, C010, Local1, 0x02D6)
        Local1 = CondRefOf (M903, Local0)
        M1A0 (Local0, C010, Local1, 0x02D7)
        Local1 = CondRefOf (M904, Local0)
        M1A0 (Local0, C010, Local1, 0x02D8)
        Local1 = CondRefOf (M905, Local0)
        M1A0 (Local0, C010, Local1, 0x02D9)
        Local1 = CondRefOf (M906, Local0)
        M1A0 (Local0, C010, Local1, 0x02DA)
        Local1 = CondRefOf (M907, Local0)
        M1A0 (Local0, C010, Local1, 0x02DB)
        Local1 = CondRefOf (M908, Local0)
        M1A0 (Local0, C010, Local1, 0x02DC)
        Local1 = CondRefOf (M909, Local0)
        M1A0 (Local0, C010, Local1, 0x02DD)
        Local1 = CondRefOf (M90A, Local0)
        M1A0 (Local0, C010, Local1, 0x02DE)
        Local1 = CondRefOf (M90B, Local0)
        M1A0 (Local0, C010, Local1, 0x02DF)
        Local1 = CondRefOf (M90C, Local0)
        M1A0 (Local0, C010, Local1, 0x02E0)
        Local1 = CondRefOf (M90D, Local0)
        M1A0 (Local0, C010, Local1, 0x02E1)
        Local1 = CondRefOf (M90E, Local0)
        M1A0 (Local0, C010, Local1, 0x02E2)
        Local1 = CondRefOf (M90F, Local0)
        M1A0 (Local0, C010, Local1, 0x02E3)
        Local1 = CondRefOf (M910, Local0)
        M1A0 (Local0, C010, Local1, 0x02E4)
        Local1 = CondRefOf (M911, Local0)
        M1A0 (Local0, C010, Local1, 0x02E5)
        Local1 = CondRefOf (M912, Local0)
        M1A0 (Local0, C010, Local1, 0x02E6)
        Local1 = CondRefOf (M913, Local0)
        M1A0 (Local0, C010, Local1, 0x02E7)
        Local1 = CondRefOf (M914, Local0)
        M1A0 (Local0, C010, Local1, 0x02E8)
        Local1 = CondRefOf (M915, Local0)
        M1A0 (Local0, C010, Local1, 0x02E9)
        Local1 = CondRefOf (M916, Local0)
        M1A0 (Local0, C010, Local1, 0x02EA)
        Local1 = CondRefOf (M917, Local0)
        M1A0 (Local0, C010, Local1, 0x02EB)
        Local1 = CondRefOf (M918, Local0)
        M1A0 (Local0, C010, Local1, 0x02EC)
        Local1 = CondRefOf (M919, Local0)
        M1A0 (Local0, C010, Local1, 0x02ED)
        Local1 = CondRefOf (M91A, Local0)
        M1A0 (Local0, C010, Local1, 0x02EE)
        Local1 = CondRefOf (M91B, Local0)
        M1A0 (Local0, C010, Local1, 0x02EF)
        Local1 = CondRefOf (M91C, Local0)
        M1A0 (Local0, C010, Local1, 0x02F0)
        Local1 = CondRefOf (M91D, Local0)
        M1A0 (Local0, C010, Local1, 0x02F1)
        Local1 = CondRefOf (M91E, Local0)
        M1A0 (Local0, C010, Local1, 0x02F2)
        Local1 = CondRefOf (M91F, Local0)
        M1A0 (Local0, C010, Local1, 0x02F3)
        Local1 = CondRefOf (M920, Local0)
        M1A0 (Local0, C010, Local1, 0x02F4)
        Local1 = CondRefOf (M921, Local0)
        M1A0 (Local0, C010, Local1, 0x02F5)
        Local1 = CondRefOf (M922, Local0)
        M1A0 (Local0, C010, Local1, 0x02F6)
        Local1 = CondRefOf (M923, Local0)
        M1A0 (Local0, C010, Local1, 0x02F7)
        Local1 = CondRefOf (M924, Local0)
        M1A0 (Local0, C010, Local1, 0x02F8)
        Local1 = CondRefOf (M925, Local0)
        M1A0 (Local0, C010, Local1, 0x02F9)
        Local1 = CondRefOf (M926, Local0)
        M1A0 (Local0, C010, Local1, 0x02FA)
        Local1 = CondRefOf (M927, Local0)
        M1A0 (Local0, C010, Local1, 0x02FB)
        Local1 = CondRefOf (M928, Local0)
        M1A0 (Local0, C010, Local1, 0x02FC)
        Local1 = CondRefOf (M929, Local0)
        M1A0 (Local0, C010, Local1, 0x02FD)
        Local1 = CondRefOf (M92A, Local0)
        M1A0 (Local0, C010, Local1, 0x02FE)
        Local1 = CondRefOf (M92B, Local0)
        M1A0 (Local0, C010, Local1, 0x02FF)
        Local1 = CondRefOf (M92C, Local0)
        M1A0 (Local0, C010, Local1, 0x0300)
        Local1 = CondRefOf (M92D, Local0)
        M1A0 (Local0, C010, Local1, 0x0301)
        Local1 = CondRefOf (M92E, Local0)
        M1A0 (Local0, C010, Local1, 0x030C)
        Local1 = CondRefOf (M92F, Local0)
        M1A0 (Local0, C010, Local1, 0x030D)
        Local1 = CondRefOf (M930, Local0)
        M1A0 (Local0, C010, Local1, 0x030E)
        Local1 = CondRefOf (M931, Local0)
        M1A0 (Local0, C010, Local1, 0x030F)
        Local1 = CondRefOf (M932, Local0)
        M1A0 (Local0, C010, Local1, 0x0310)
        Local1 = CondRefOf (M933, Local0)
        M1A0 (Local0, C010, Local1, 0x0311)
        Local1 = CondRefOf (M934, Local0)
        M1A0 (Local0, C010, Local1, 0x0312)
        Local1 = CondRefOf (M935, Local0)
        M1A0 (Local0, C010, Local1, 0x0313)
        M1A6 ()
        Return (Zero)
    }

    /* /////////////////////////////////////////////////////////////////////////// */
    /* */
    /* TABLE 4: all the legal ways to generate references to the named objects */
    /*          being elements of Package */
    /* */
    /* /////////////////////////////////////////////////////////////////////////// */
    /* m16e but with global data */
    Method (M194, 0, NotSerialized)
    {
        If (Y100)
        {
            TS00 ("m194")
        }
        Else
        {
            Debug = "m194"
        }

        If (!Y900)
        {
            Debug = "Test m194 skipped!"
            Return (Zero)
        }

        /* T4:x,I1-I14,x,x */
        /* Computational Data */
        Store (Index (Package (0x01)
                {
                    I900
                }, 0x00), Local0)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xFE7CB391D65A0000, __LINE__)
        Store (Index (Package (0x01)
                {
                    I901
                }, 0x00), Local0)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xC1790001, __LINE__)
        Store (Index (Package (0x01)
                {
                    S900
                }, 0x00), Local0)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "12340002", __LINE__)
        Store (Index (Package (0x01)
                {
                    S901
                }, 0x00), Local0)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "qwrtyu0003", __LINE__)
        Store (Index (Package (0x01)
                {
                    B900
                }, 0x00), Local0)
        M1A2 (Local0, C00B, 0x00, 0x00, C00B, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            }, 0x0318)
        If (Y118)
        {
            Store (Index (Package (0x01)
                    {
                        F900
                    }, 0x00), Local0)
            M1A2 (Local0, C00D, 0x00, 0x00, C00D, 0x00, __LINE__)
            Store (Index (Package (0x01)
                    {
                        BN90
                    }, 0x00), Local0)
            M1A2 (Local0, C00D, 0x00, 0x00, C00D, 0x00, __LINE__)
            Store (Index (Package (0x01)
                    {
                        IF90
                    }, 0x00), Local0)
            M1A2 (Local0, C00D, 0x00, 0x00, C00D, 0x00, __LINE__)
            Store (Index (Package (0x01)
                    {
                        BF90
                    }, 0x00), Local0)
            M1A2 (Local0, C016, 0x00, 0x00, C016, 0xB0, __LINE__)
        }

        /* Not Computational Data */

        Store (Index (Package (0x01)
                {
                    E900
                }, 0x00), Local0)
        M1A0 (Local0, C00F, Ones, 0x031D)
        Store (Index (Package (0x01)
                {
                    MX90
                }, 0x00), Local0)
        M1A0 (Local0, C011, Ones, 0x031E)
        Store (Index (Package (0x01)
                {
                    D900
                }, 0x00), Local0)
        M1A0 (Local0, C00E, Ones, 0x031F)
        Store (Index (Package (0x01)
                {
                    TZ90
                }, 0x00), Local0)
        M1A0 (Local0, C015, Ones, 0x0320)
        Store (Index (Package (0x01)
                {
                    PR90
                }, 0x00), Local0)
        M1A0 (Local0, C014, Ones, 0x0321)
        Store (Index (Package (0x01)
                {
                    R900
                }, 0x00), Local0)
        M1A0 (Local0, C012, Ones, 0x0322)
        Store (Index (Package (0x01)
                {
                    PW90
                }, 0x00), Local0)
        M1A0 (Local0, C013, Ones, 0x0323)
        /* Elements of Package are Uninitialized */

        Store (Index (Package (0x01)
                {
                    P900
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0324)
        /* Elements of Package are Computational Data */

        Store (Index (Package (0x01)
                {
                    P901
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xABCD0004, __LINE__)
        M1A2 (Local0, C00C, 0x01, 0x01, C009, 0x1122334455660005, __LINE__)
        Store (Index (Package (0x01)
                {
                    P902
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "12340006", __LINE__)
        M1A2 (Local0, C00C, 0x01, 0x01, C00A, "q1w2e3r4t5y6u7i80007", __LINE__)
        Store (Index (Package (0x01)
                {
                    P903
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "qwrtyuiop0008", __LINE__)
        M1A2 (Local0, C00C, 0x01, 0x01, C00A, "1234567890abdef0250009", __LINE__)
        Store (Index (Package (0x01)
                {
                    P904
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C00B, Buffer (0x03)
            {
                 0xB5, 0xB6, 0xB7                                 // ...
            }, 0x032B)
        Store (Index (Package (0x01)
                {
                    P905
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x02, 0x00, C009, 0x0ABC000A, __LINE__)
        M1A2 (Local0, C00C, 0x02, 0x01, C00A, "0xabc000b", __LINE__)
        Store (Index (Package (0x01)
                {
                    P906
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x02, 0x00, C00A, "abc000d", __LINE__)
        Store (Index (Package (0x01)
                {
                    P907
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x02, 0x00, C00A, "aqwevbgnm000e", __LINE__)
        Store (Index (Package (0x01)
                {
                    P908
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x02, 0x00, C00B, Buffer (0x05)
            {
                 0xBA, 0xBB, 0xBC, 0xBD, 0xBE                     // .....
            }, 0x0330)
        Store (Index (Package (0x01)
                {
                    P909
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x03, 0x00, C009, 0x0ABC000F, __LINE__)
        Store (Index (Package (0x01)
                {
                    P90A
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x03, 0x00, C00A, "12340010", __LINE__)
        Store (Index (Package (0x01)
                {
                    P90B
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x03, 0x00, C00A, "zxswefas0011", __LINE__)
        Store (Index (Package (0x01)
                {
                    P90C
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x03, 0x00, C00B, Buffer (0x03)
            {
                 0xBF, 0xC0, 0xC1                                 // ...
            }, 0x0334)
        Store (Index (Package (0x01)
                {
                    P90D
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xFE7CB391D65A0000, __LINE__)
        Store (Index (Package (0x01)
                {
                    P90E
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xC1790001, __LINE__)
        Store (Index (Package (0x01)
                {
                    P90F
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "12340002", __LINE__)
        Store (Index (Package (0x01)
                {
                    P910
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "qwrtyu0003", __LINE__)
        Store (Index (Package (0x01)
                {
                    P911
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C00B, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            }, 0x0339)
        If (Y118)
        {
            Store (Index (Package (0x01)
                    {
                        P912
                    }, 0x00), Local0)
            M1A2 (Local0, C00C, 0x01, 0x00, C00D, 0x00, __LINE__)
            Store (Index (Package (0x01)
                    {
                        P913
                    }, 0x00), Local0)
            M1A2 (Local0, C00C, 0x01, 0x00, C00D, 0x00, __LINE__)
            Store (Index (Package (0x01)
                    {
                        P914
                    }, 0x00), Local0)
            M1A2 (Local0, C00C, 0x01, 0x00, C00D, 0x00, __LINE__)
            Store (Index (Package (0x01)
                    {
                        P915
                    }, 0x00), Local0)
            M1A2 (Local0, C00C, 0x01, 0x00, C016, 0xB0, __LINE__)
        }

        /* Elements of Package are NOT Computational Data */

        Store (Index (Package (0x01)
                {
                    P916
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x033E)
        Store (Index (Package (0x01)
                {
                    P917
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x033F)
        Store (Index (Package (0x01)
                {
                    P918
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0340)
        Store (Index (Package (0x01)
                {
                    P919
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0341)
        Store (Index (Package (0x01)
                {
                    P91A
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0342)
        Store (Index (Package (0x01)
                {
                    P91B
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0343)
        Store (Index (Package (0x01)
                {
                    P91C
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0344)
        /* Elements of Package are Methods */

        Store (Index (Package (0x01)
                {
                    P91D
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0345)
        Store (Index (Package (0x01)
                {
                    P91E
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0346)
        Store (Index (Package (0x01)
                {
                    P91F
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0347)
        Store (Index (Package (0x01)
                {
                    P920
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0348)
        Store (Index (Package (0x01)
                {
                    P921
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0349)
        Store (Index (Package (0x01)
                {
                    P922
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x034A)
        Store (Index (Package (0x01)
                {
                    P923
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x034B)
        Store (Index (Package (0x01)
                {
                    P924
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x034C)
        Store (Index (Package (0x01)
                {
                    P925
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x034D)
        Store (Index (Package (0x01)
                {
                    P926
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x034E)
        Store (Index (Package (0x01)
                {
                    P927
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x034F)
        Store (Index (Package (0x01)
                {
                    P928
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0350)
        Store (Index (Package (0x01)
                {
                    P929
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0351)
        Store (Index (Package (0x01)
                {
                    P92A
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0352)
        Store (Index (Package (0x01)
                {
                    P92B
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0353)
        Store (Index (Package (0x01)
                {
                    P92C
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0354)
        Store (Index (Package (0x01)
                {
                    P92D
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0355)
        Store (Index (Package (0x01)
                {
                    P92E
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0356)
        Store (Index (Package (0x01)
                {
                    P92F
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0357)
        Store (Index (Package (0x01)
                {
                    P930
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0358)
        Store (Index (Package (0x01)
                {
                    P931
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0359)
        Store (Index (Package (0x01)
                {
                    P932
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x035A)
        Store (Index (Package (0x01)
                {
                    P933
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x035B)
        Store (Index (Package (0x01)
                {
                    P934
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x035C)
        Store (Index (Package (0x01)
                {
                    P935
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x035D)
        Store (Index (Package (0x01)
                {
                    P936
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x035E)
        Store (Index (Package (0x01)
                {
                    P937
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x035F)
        Store (Index (Package (0x01)
                {
                    P938
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0360)
        Store (Index (Package (0x01)
                {
                    P939
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0361)
        Store (Index (Package (0x01)
                {
                    P93A
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0362)
        Store (Index (Package (0x01)
                {
                    P93B
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0363)
        Store (Index (Package (0x01)
                {
                    P93C
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0364)
        Store (Index (Package (0x01)
                {
                    P93D
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0365)
        Store (Index (Package (0x01)
                {
                    P93E
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0366)
        Store (Index (Package (0x01)
                {
                    P93F
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0367)
        Store (Index (Package (0x01)
                {
                    P940
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0368)
        Store (Index (Package (0x01)
                {
                    P941
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0369)
        Store (Index (Package (0x01)
                {
                    P942
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x036A)
        Store (Index (Package (0x01)
                {
                    P943
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x036B)
        Store (Index (Package (0x01)
                {
                    P944
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x036C)
        Store (Index (Package (0x01)
                {
                    P945
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x036D)
        Store (Index (Package (0x01)
                {
                    P946
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x036E)
        Store (Index (Package (0x01)
                {
                    P947
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x036F)
        Store (Index (Package (0x01)
                {
                    P948
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0370)
        Store (Index (Package (0x01)
                {
                    P949
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0371)
        Store (Index (Package (0x01)
                {
                    P94A
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0372)
        Store (Index (Package (0x01)
                {
                    P94B
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0373)
        Store (Index (Package (0x01)
                {
                    P94C
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0374)
        Store (Index (Package (0x01)
                {
                    P94D
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0375)
        Store (Index (Package (0x01)
                {
                    P94E
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0376)
        Store (Index (Package (0x01)
                {
                    P94F
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0377)
        Store (Index (Package (0x01)
                {
                    P950
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0378)
        Store (Index (Package (0x01)
                {
                    P951
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x0379)
        Store (Index (Package (0x01)
                {
                    P952
                }, 0x00), Local0)
        M1A0 (Local0, C00C, Ones, 0x037A)
        /* Methods */

        Store (Index (Package (0x01)
                {
                    M900
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x037B)
        Store (Index (Package (0x01)
                {
                    M901
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x037C)
        Store (Index (Package (0x01)
                {
                    M902
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x037D)
        Store (Index (Package (0x01)
                {
                    M903
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x037E)
        Store (Index (Package (0x01)
                {
                    M904
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x037F)
        Store (Index (Package (0x01)
                {
                    M905
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x0380)
        Store (Index (Package (0x01)
                {
                    M906
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x0381)
        Store (Index (Package (0x01)
                {
                    M907
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x0382)
        Store (Index (Package (0x01)
                {
                    M908
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x0383)
        Store (Index (Package (0x01)
                {
                    M909
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x0384)
        Store (Index (Package (0x01)
                {
                    M90A
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x0385)
        Store (Index (Package (0x01)
                {
                    M90B
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x0386)
        Store (Index (Package (0x01)
                {
                    M90C
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x0387)
        Store (Index (Package (0x01)
                {
                    M90D
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x0388)
        Store (Index (Package (0x01)
                {
                    M90E
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x0389)
        Store (Index (Package (0x01)
                {
                    M90F
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x038A)
        Store (Index (Package (0x01)
                {
                    M910
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x038B)
        Store (Index (Package (0x01)
                {
                    M911
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x038C)
        Store (Index (Package (0x01)
                {
                    M912
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x038D)
        Store (Index (Package (0x01)
                {
                    M913
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x038E)
        Store (Index (Package (0x01)
                {
                    M914
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x038F)
        Store (Index (Package (0x01)
                {
                    M915
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x0390)
        Store (Index (Package (0x01)
                {
                    M916
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x0391)
        Store (Index (Package (0x01)
                {
                    M917
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x0392)
        Store (Index (Package (0x01)
                {
                    M918
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x0393)
        Store (Index (Package (0x01)
                {
                    M919
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x0394)
        Store (Index (Package (0x01)
                {
                    M91A
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x0395)
        Store (Index (Package (0x01)
                {
                    M91B
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x0396)
        Store (Index (Package (0x01)
                {
                    M91C
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x0397)
        Store (Index (Package (0x01)
                {
                    M91D
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x0398)
        Store (Index (Package (0x01)
                {
                    M91E
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x0399)
        Store (Index (Package (0x01)
                {
                    M91F
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x039A)
        Store (Index (Package (0x01)
                {
                    M920
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x039B)
        Store (Index (Package (0x01)
                {
                    M921
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x039C)
        Store (Index (Package (0x01)
                {
                    M922
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x039D)
        Store (Index (Package (0x01)
                {
                    M923
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x039E)
        Store (Index (Package (0x01)
                {
                    M924
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x039F)
        Store (Index (Package (0x01)
                {
                    M925
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x03A0)
        Store (Index (Package (0x01)
                {
                    M926
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x03A1)
        Store (Index (Package (0x01)
                {
                    M927
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x03A2)
        Store (Index (Package (0x01)
                {
                    M928
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x03A3)
        Store (Index (Package (0x01)
                {
                    M929
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x03A4)
        Store (Index (Package (0x01)
                {
                    M92A
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x03A5)
        Store (Index (Package (0x01)
                {
                    M92B
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x03A6)
        Store (Index (Package (0x01)
                {
                    M92C
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x03A7)
        Store (Index (Package (0x01)
                {
                    M92D
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x03A8)
        Store (Index (Package (0x01)
                {
                    M92E
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x03A9)
        Store (Index (Package (0x01)
                {
                    M92F
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x03AA)
        Store (Index (Package (0x01)
                {
                    M930
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x03AB)
        Store (Index (Package (0x01)
                {
                    M931
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x03AC)
        Store (Index (Package (0x01)
                {
                    M932
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x03AD)
        Store (Index (Package (0x01)
                {
                    M933
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x03AE)
        Store (Index (Package (0x01)
                {
                    M934
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x03AF)
        Store (Index (Package (0x01)
                {
                    M935
                }, 0x00), Local0)
        M1A0 (Local0, C010, Ones, 0x03B0)
        /* T4:x,IR1-IR14,x,x */
        /* Computational Data */
        Local0 = Index (Package (0x01)
                {
                    I900
                }, 0x00, Local1)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xFE7CB391D65A0000, __LINE__)
        M1A2 (Local1, C009, 0x00, 0x00, C009, 0xFE7CB391D65A0000, __LINE__)
        Local0 = Index (Package (0x01)
                {
                    I901
                }, 0x00, Local1)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xC1790001, __LINE__)
        M1A2 (Local1, C009, 0x00, 0x00, C009, 0xC1790001, __LINE__)
        Local0 = Index (Package (0x01)
                {
                    S900
                }, 0x00, Local1)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "12340002", __LINE__)
        M1A2 (Local1, C00A, 0x00, 0x00, C00A, "12340002", __LINE__)
        Local0 = Index (Package (0x01)
                {
                    S901
                }, 0x00, Local1)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "qwrtyu0003", __LINE__)
        M1A2 (Local1, C00A, 0x00, 0x00, C00A, "qwrtyu0003", __LINE__)
        Local0 = Index (Package (0x01)
                {
                    B900
                }, 0x00, Local1)
        M1A2 (Local0, C00B, 0x00, 0x00, C00B, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            }, 0x03B9)
        M1A2 (Local1, C00B, 0x00, 0x00, C00B, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            }, 0x03BA)
        If (Y118)
        {
            Local0 = Index (Package (0x01)
                    {
                        F900
                    }, 0x00, Local1)
            M1A2 (Local0, C00D, 0x00, 0x00, C00D, 0x00, __LINE__)
            M1A2 (Local1, C00D, 0x00, 0x00, C00D, 0x00, __LINE__)
            Local0 = Index (Package (0x01)
                    {
                        BN90
                    }, 0x00, Local1)
            M1A2 (Local0, C00D, 0x00, 0x00, C00D, 0x00, __LINE__)
            M1A2 (Local1, C00D, 0x00, 0x00, C00D, 0x00, __LINE__)
            Local0 = Index (Package (0x01)
                    {
                        IF90
                    }, 0x00, Local1)
            M1A2 (Local0, C00D, 0x00, 0x00, C00D, 0x00, __LINE__)
            M1A2 (Local1, C00D, 0x00, 0x00, C00D, 0x00, __LINE__)
            Local0 = Index (Package (0x01)
                    {
                        BF90
                    }, 0x00, Local1)
            M1A2 (Local0, C016, 0x00, 0x00, C016, 0xB0, __LINE__)
            M1A2 (Local1, C016, 0x00, 0x00, C016, 0xB0, __LINE__)
        }

        /* Not Computational Data */

        Local0 = Index (Package (0x01)
                {
                    E900
                }, 0x00, Local1)
        M1A0 (Local0, C00F, Ones, 0x03C3)
        M1A0 (Local1, C00F, Ones, 0x03C4)
        Local0 = Index (Package (0x01)
                {
                    MX90
                }, 0x00, Local1)
        M1A0 (Local0, C011, Ones, 0x03C5)
        M1A0 (Local1, C011, Ones, 0x03C6)
        Local0 = Index (Package (0x01)
                {
                    D900
                }, 0x00, Local1)
        M1A0 (Local0, C00E, Ones, 0x03C7)
        M1A0 (Local1, C00E, Ones, 0x03C8)
        Local0 = Index (Package (0x01)
                {
                    TZ90
                }, 0x00, Local1)
        M1A0 (Local0, C015, Ones, 0x03C9)
        M1A0 (Local1, C015, Ones, 0x03CA)
        Local0 = Index (Package (0x01)
                {
                    PR90
                }, 0x00, Local1)
        M1A0 (Local0, C014, Ones, 0x03CB)
        M1A0 (Local1, C014, Ones, 0x03CC)
        Local0 = Index (Package (0x01)
                {
                    R900
                }, 0x00, Local1)
        M1A0 (Local0, C012, Ones, 0x03CD)
        M1A0 (Local1, C012, Ones, 0x03CE)
        Local0 = Index (Package (0x01)
                {
                    PW90
                }, 0x00, Local1)
        M1A0 (Local0, C013, Ones, 0x03CF)
        M1A0 (Local1, C013, Ones, 0x03D0)
        /* Elements of Package are Uninitialized */

        Local0 = Index (Package (0x01)
                {
                    P900
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x03D1)
        M1A0 (Local1, C00C, Ones, 0x03D2)
        /* Elements of Package are Computational Data */

        Local0 = Index (Package (0x01)
                {
                    P901
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xABCD0004, __LINE__)
        M1A2 (Local0, C00C, 0x01, 0x01, C009, 0x1122334455660005, __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x00, C009, 0xABCD0004, __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x01, C009, 0x1122334455660005, __LINE__)
        Local0 = Index (Package (0x01)
                {
                    P902
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "12340006", __LINE__)
        M1A2 (Local0, C00C, 0x01, 0x01, C00A, "q1w2e3r4t5y6u7i80007", __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x00, C00A, "12340006", __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x01, C00A, "q1w2e3r4t5y6u7i80007", __LINE__)
        Local0 = Index (Package (0x01)
                {
                    P903
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "qwrtyuiop0008", __LINE__)
        M1A2 (Local0, C00C, 0x01, 0x01, C00A, "1234567890abdef0250009", __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x00, C00A, "qwrtyuiop0008", __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x01, C00A, "1234567890abdef0250009", __LINE__)
        Local0 = Index (Package (0x01)
                {
                    P904
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x01, 0x00, C00B, Buffer (0x03)
            {
                 0xB5, 0xB6, 0xB7                                 // ...
            }, 0x03DF)
        M1A2 (Local1, C00C, 0x01, 0x00, C00B, Buffer (0x03)
            {
                 0xB5, 0xB6, 0xB7                                 // ...
            }, 0x03E0)
        Local0 = Index (Package (0x01)
                {
                    P905
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x02, 0x00, C009, 0x0ABC000A, __LINE__)
        M1A2 (Local0, C00C, 0x02, 0x01, C00A, "0xabc000b", __LINE__)
        M1A2 (Local1, C00C, 0x02, 0x00, C009, 0x0ABC000A, __LINE__)
        M1A2 (Local1, C00C, 0x02, 0x01, C00A, "0xabc000b", __LINE__)
        Local0 = Index (Package (0x01)
                {
                    P906
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x02, 0x00, C00A, "abc000d", __LINE__)
        M1A2 (Local1, C00C, 0x02, 0x00, C00A, "abc000d", __LINE__)
        Local0 = Index (Package (0x01)
                {
                    P907
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x02, 0x00, C00A, "aqwevbgnm000e", __LINE__)
        M1A2 (Local1, C00C, 0x02, 0x00, C00A, "aqwevbgnm000e", __LINE__)
        Local0 = Index (Package (0x01)
                {
                    P908
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x02, 0x00, C00B, Buffer (0x05)
            {
                 0xBA, 0xBB, 0xBC, 0xBD, 0xBE                     // .....
            }, 0x03E9)
        M1A2 (Local1, C00C, 0x02, 0x00, C00B, Buffer (0x05)
            {
                 0xBA, 0xBB, 0xBC, 0xBD, 0xBE                     // .....
            }, 0x03EA)
        Local0 = Index (Package (0x01)
                {
                    P909
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x03, 0x00, C009, 0x0ABC000F, __LINE__)
        M1A2 (Local1, C00C, 0x03, 0x00, C009, 0x0ABC000F, __LINE__)
        Local0 = Index (Package (0x01)
                {
                    P90A
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x03, 0x00, C00A, "12340010", __LINE__)
        M1A2 (Local1, C00C, 0x03, 0x00, C00A, "12340010", __LINE__)
        Local0 = Index (Package (0x01)
                {
                    P90B
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x03, 0x00, C00A, "zxswefas0011", __LINE__)
        M1A2 (Local1, C00C, 0x03, 0x00, C00A, "zxswefas0011", __LINE__)
        Local0 = Index (Package (0x01)
                {
                    P90C
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x03, 0x00, C00B, Buffer (0x03)
            {
                 0xBF, 0xC0, 0xC1                                 // ...
            }, 0x03F1)
        M1A2 (Local1, C00C, 0x03, 0x00, C00B, Buffer (0x03)
            {
                 0xBF, 0xC0, 0xC1                                 // ...
            }, 0x03F2)
        Local0 = Index (Package (0x01)
                {
                    P90D
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xFE7CB391D65A0000, __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x00, C009, 0xFE7CB391D65A0000, __LINE__)
        Local0 = Index (Package (0x01)
                {
                    P90E
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xC1790001, __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x00, C009, 0xC1790001, __LINE__)
        Local0 = Index (Package (0x01)
                {
                    P90F
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "12340002", __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x00, C00A, "12340002", __LINE__)
        Local0 = Index (Package (0x01)
                {
                    P910
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "qwrtyu0003", __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x00, C00A, "qwrtyu0003", __LINE__)
        Local0 = Index (Package (0x01)
                {
                    P911
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x01, 0x00, C00B, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            }, 0x03FB)
        M1A2 (Local1, C00C, 0x01, 0x00, C00B, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            }, 0x03FC)
        If (Y118)
        {
            Local0 = Index (Package (0x01)
                    {
                        P912
                    }, 0x00, Local1)
            M1A2 (Local0, C00C, 0x01, 0x00, C00D, 0x00, __LINE__)
            M1A2 (Local1, C00C, 0x01, 0x00, C00D, 0x00, __LINE__)
            Local0 = Index (Package (0x01)
                    {
                        P913
                    }, 0x00, Local1)
            M1A2 (Local0, C00C, 0x01, 0x00, C00D, 0x00, __LINE__)
            M1A2 (Local1, C00C, 0x01, 0x00, C00D, 0x00, __LINE__)
            Local0 = Index (Package (0x01)
                    {
                        P914
                    }, 0x00, Local1)
            M1A2 (Local0, C00C, 0x01, 0x00, C00D, 0x00, __LINE__)
            M1A2 (Local1, C00C, 0x01, 0x00, C00D, 0x00, __LINE__)
            Local0 = Index (Package (0x01)
                    {
                        P915
                    }, 0x00, Local1)
            M1A2 (Local0, C00C, 0x01, 0x00, C016, 0xB0, __LINE__)
            M1A2 (Local1, C00C, 0x01, 0x00, C016, 0xB0, __LINE__)
        }

        /* Elements of Package are NOT Computational Data */

        Local0 = Index (Package (0x01)
                {
                    P916
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x0405)
        M1A0 (Local1, C00C, Ones, 0x0406)
        Local0 = Index (Package (0x01)
                {
                    P917
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x0407)
        M1A0 (Local1, C00C, Ones, 0x0408)
        Local0 = Index (Package (0x01)
                {
                    P918
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x0409)
        M1A0 (Local1, C00C, Ones, 0x040A)
        Local0 = Index (Package (0x01)
                {
                    P919
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x040B)
        M1A0 (Local1, C00C, Ones, 0x040C)
        Local0 = Index (Package (0x01)
                {
                    P91A
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x040D)
        M1A0 (Local1, C00C, Ones, 0x040E)
        Local0 = Index (Package (0x01)
                {
                    P91B
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x040F)
        M1A0 (Local1, C00C, Ones, 0x0410)
        Local0 = Index (Package (0x01)
                {
                    P91C
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x0411)
        M1A0 (Local1, C00C, Ones, 0x0412)
        /* Elements of Package are Methods */

        Local0 = Index (Package (0x01)
                {
                    P91D
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x0413)
        M1A0 (Local1, C00C, Ones, 0x0414)
        Local0 = Index (Package (0x01)
                {
                    P91E
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x0415)
        M1A0 (Local1, C00C, Ones, 0x0416)
        Local0 = Index (Package (0x01)
                {
                    P91F
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x0417)
        M1A0 (Local1, C00C, Ones, 0x0418)
        Local0 = Index (Package (0x01)
                {
                    P920
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x0419)
        M1A0 (Local1, C00C, Ones, 0x041A)
        Local0 = Index (Package (0x01)
                {
                    P921
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x041B)
        M1A0 (Local1, C00C, Ones, 0x041C)
        Local0 = Index (Package (0x01)
                {
                    P922
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x041D)
        M1A0 (Local1, C00C, Ones, 0x041E)
        Local0 = Index (Package (0x01)
                {
                    P923
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x041F)
        M1A0 (Local1, C00C, Ones, 0x0420)
        Local0 = Index (Package (0x01)
                {
                    P924
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x0421)
        M1A0 (Local1, C00C, Ones, 0x0422)
        Local0 = Index (Package (0x01)
                {
                    P925
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x0423)
        M1A0 (Local1, C00C, Ones, 0x0424)
        Local0 = Index (Package (0x01)
                {
                    P926
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x0425)
        M1A0 (Local1, C00C, Ones, 0x0426)
        Local0 = Index (Package (0x01)
                {
                    P927
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x0427)
        M1A0 (Local1, C00C, Ones, 0x0428)
        Local0 = Index (Package (0x01)
                {
                    P928
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x0429)
        M1A0 (Local1, C00C, Ones, 0x042A)
        Local0 = Index (Package (0x01)
                {
                    P929
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x042B)
        M1A0 (Local1, C00C, Ones, 0x042C)
        Local0 = Index (Package (0x01)
                {
                    P92A
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x042D)
        M1A0 (Local1, C00C, Ones, 0x042E)
        Local0 = Index (Package (0x01)
                {
                    P92B
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x042F)
        M1A0 (Local1, C00C, Ones, 0x0430)
        Local0 = Index (Package (0x01)
                {
                    P92C
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x0431)
        M1A0 (Local1, C00C, Ones, 0x0432)
        Local0 = Index (Package (0x01)
                {
                    P92D
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x0433)
        M1A0 (Local1, C00C, Ones, 0x0434)
        Local0 = Index (Package (0x01)
                {
                    P92E
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x0435)
        M1A0 (Local1, C00C, Ones, 0x0436)
        Local0 = Index (Package (0x01)
                {
                    P92F
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x0437)
        M1A0 (Local1, C00C, Ones, 0x0438)
        Local0 = Index (Package (0x01)
                {
                    P930
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x0439)
        M1A0 (Local1, C00C, Ones, 0x043A)
        Local0 = Index (Package (0x01)
                {
                    P931
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x043B)
        M1A0 (Local1, C00C, Ones, 0x043C)
        Local0 = Index (Package (0x01)
                {
                    P932
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x043D)
        M1A0 (Local1, C00C, Ones, 0x043E)
        Local0 = Index (Package (0x01)
                {
                    P933
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x043F)
        M1A0 (Local1, C00C, Ones, 0x0440)
        Local0 = Index (Package (0x01)
                {
                    P934
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x0441)
        M1A0 (Local1, C00C, Ones, 0x0442)
        Local0 = Index (Package (0x01)
                {
                    P935
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x0443)
        M1A0 (Local1, C00C, Ones, 0x0444)
        Local0 = Index (Package (0x01)
                {
                    P936
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x0445)
        M1A0 (Local1, C00C, Ones, 0x0446)
        Local0 = Index (Package (0x01)
                {
                    P937
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x0447)
        M1A0 (Local1, C00C, Ones, 0x0448)
        Local0 = Index (Package (0x01)
                {
                    P938
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x0449)
        M1A0 (Local1, C00C, Ones, 0x044A)
        Local0 = Index (Package (0x01)
                {
                    P939
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x044B)
        M1A0 (Local1, C00C, Ones, 0x044C)
        Local0 = Index (Package (0x01)
                {
                    P93A
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x044D)
        M1A0 (Local1, C00C, Ones, 0x044E)
        Local0 = Index (Package (0x01)
                {
                    P93B
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x044F)
        M1A0 (Local1, C00C, Ones, 0x0450)
        Local0 = Index (Package (0x01)
                {
                    P93C
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x0451)
        M1A0 (Local1, C00C, Ones, 0x0452)
        Local0 = Index (Package (0x01)
                {
                    P93D
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x0453)
        M1A0 (Local1, C00C, Ones, 0x0454)
        Local0 = Index (Package (0x01)
                {
                    P93E
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x0455)
        M1A0 (Local1, C00C, Ones, 0x0456)
        Local0 = Index (Package (0x01)
                {
                    P93F
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x0457)
        M1A0 (Local1, C00C, Ones, 0x0458)
        Local0 = Index (Package (0x01)
                {
                    P940
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x0459)
        M1A0 (Local1, C00C, Ones, 0x045A)
        Local0 = Index (Package (0x01)
                {
                    P941
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x045B)
        M1A0 (Local1, C00C, Ones, 0x045C)
        Local0 = Index (Package (0x01)
                {
                    P942
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x045D)
        M1A0 (Local1, C00C, Ones, 0x045E)
        Local0 = Index (Package (0x01)
                {
                    P943
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x045F)
        M1A0 (Local1, C00C, Ones, 0x0460)
        Local0 = Index (Package (0x01)
                {
                    P944
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x0461)
        M1A0 (Local1, C00C, Ones, 0x0462)
        Local0 = Index (Package (0x01)
                {
                    P945
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x0463)
        M1A0 (Local1, C00C, Ones, 0x0464)
        Local0 = Index (Package (0x01)
                {
                    P946
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x0465)
        M1A0 (Local1, C00C, Ones, 0x0466)
        Local0 = Index (Package (0x01)
                {
                    P947
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x0467)
        M1A0 (Local1, C00C, Ones, 0x0468)
        Local0 = Index (Package (0x01)
                {
                    P948
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x0469)
        M1A0 (Local1, C00C, Ones, 0x046A)
        Local0 = Index (Package (0x01)
                {
                    P949
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x046B)
        M1A0 (Local1, C00C, Ones, 0x046C)
        Local0 = Index (Package (0x01)
                {
                    P94A
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x046D)
        M1A0 (Local1, C00C, Ones, 0x046E)
        Local0 = Index (Package (0x01)
                {
                    P94B
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x046F)
        M1A0 (Local1, C00C, Ones, 0x0470)
        Local0 = Index (Package (0x01)
                {
                    P94C
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x0471)
        M1A0 (Local1, C00C, Ones, 0x0472)
        Local0 = Index (Package (0x01)
                {
                    P94D
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x0473)
        M1A0 (Local1, C00C, Ones, 0x0474)
        Local0 = Index (Package (0x01)
                {
                    P94E
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x0475)
        M1A0 (Local1, C00C, Ones, 0x0476)
        Local0 = Index (Package (0x01)
                {
                    P94F
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x0477)
        M1A0 (Local1, C00C, Ones, 0x0478)
        Local0 = Index (Package (0x01)
                {
                    P950
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x0479)
        M1A0 (Local1, C00C, Ones, 0x047A)
        Local0 = Index (Package (0x01)
                {
                    P951
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x047B)
        M1A0 (Local1, C00C, Ones, 0x047C)
        Local0 = Index (Package (0x01)
                {
                    P952
                }, 0x00, Local1)
        M1A0 (Local0, C00C, Ones, 0x047D)
        M1A0 (Local1, C00C, Ones, 0x047E)
        /* Methods */

        Local0 = Index (Package (0x01)
                {
                    M900
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x047F)
        M1A0 (Local1, C010, Ones, 0x0480)
        Local0 = Index (Package (0x01)
                {
                    M901
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x0481)
        M1A0 (Local1, C010, Ones, 0x0482)
        Local0 = Index (Package (0x01)
                {
                    M902
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x0483)
        M1A0 (Local1, C010, Ones, 0x0484)
        Local0 = Index (Package (0x01)
                {
                    M903
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x0485)
        M1A0 (Local1, C010, Ones, 0x0486)
        Local0 = Index (Package (0x01)
                {
                    M904
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x0487)
        M1A0 (Local1, C010, Ones, 0x0488)
        Local0 = Index (Package (0x01)
                {
                    M905
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x0489)
        M1A0 (Local1, C010, Ones, 0x048A)
        Local0 = Index (Package (0x01)
                {
                    M906
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x048B)
        M1A0 (Local1, C010, Ones, 0x048C)
        Local0 = Index (Package (0x01)
                {
                    M907
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x048D)
        M1A0 (Local1, C010, Ones, 0x048E)
        Local0 = Index (Package (0x01)
                {
                    M908
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x048F)
        M1A0 (Local1, C010, Ones, 0x0490)
        Local0 = Index (Package (0x01)
                {
                    M909
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x0491)
        M1A0 (Local1, C010, Ones, 0x0492)
        Local0 = Index (Package (0x01)
                {
                    M90A
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x0493)
        M1A0 (Local1, C010, Ones, 0x0494)
        Local0 = Index (Package (0x01)
                {
                    M90B
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x0495)
        M1A0 (Local1, C010, Ones, 0x0496)
        Local0 = Index (Package (0x01)
                {
                    M90C
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x0497)
        M1A0 (Local1, C010, Ones, 0x0498)
        Local0 = Index (Package (0x01)
                {
                    M90D
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x0499)
        M1A0 (Local1, C010, Ones, 0x049A)
        Local0 = Index (Package (0x01)
                {
                    M90E
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x049B)
        M1A0 (Local1, C010, Ones, 0x049C)
        Local0 = Index (Package (0x01)
                {
                    M90F
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x049D)
        M1A0 (Local1, C010, Ones, 0x049E)
        Local0 = Index (Package (0x01)
                {
                    M910
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x049F)
        M1A0 (Local1, C010, Ones, 0x04A0)
        Local0 = Index (Package (0x01)
                {
                    M911
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x04A1)
        M1A0 (Local1, C010, Ones, 0x04A2)
        Local0 = Index (Package (0x01)
                {
                    M912
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x04A3)
        M1A0 (Local1, C010, Ones, 0x04A4)
        Local0 = Index (Package (0x01)
                {
                    M913
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x04A5)
        M1A0 (Local1, C010, Ones, 0x04A6)
        Local0 = Index (Package (0x01)
                {
                    M914
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x04A7)
        M1A0 (Local1, C010, Ones, 0x04A8)
        Local0 = Index (Package (0x01)
                {
                    M915
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x04A9)
        M1A0 (Local1, C010, Ones, 0x04AA)
        Local0 = Index (Package (0x01)
                {
                    M916
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x04AB)
        M1A0 (Local1, C010, Ones, 0x04AC)
        Local0 = Index (Package (0x01)
                {
                    M917
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x04AD)
        M1A0 (Local1, C010, Ones, 0x04AE)
        Local0 = Index (Package (0x01)
                {
                    M918
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x04AF)
        M1A0 (Local1, C010, Ones, 0x04B0)
        Local0 = Index (Package (0x01)
                {
                    M919
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x04B1)
        M1A0 (Local1, C010, Ones, 0x04B2)
        Local0 = Index (Package (0x01)
                {
                    M91A
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x04B3)
        M1A0 (Local1, C010, Ones, 0x04B4)
        Local0 = Index (Package (0x01)
                {
                    M91B
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x04B5)
        M1A0 (Local1, C010, Ones, 0x04B6)
        Local0 = Index (Package (0x01)
                {
                    M91C
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x04B7)
        M1A0 (Local1, C010, Ones, 0x04B8)
        Local0 = Index (Package (0x01)
                {
                    M91D
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x04B9)
        M1A0 (Local1, C010, Ones, 0x04BA)
        Local0 = Index (Package (0x01)
                {
                    M91E
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x04BB)
        M1A0 (Local1, C010, Ones, 0x04BC)
        Local0 = Index (Package (0x01)
                {
                    M91F
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x04BD)
        M1A0 (Local1, C010, Ones, 0x04BE)
        Local0 = Index (Package (0x01)
                {
                    M920
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x04BF)
        M1A0 (Local1, C010, Ones, 0x04C0)
        Local0 = Index (Package (0x01)
                {
                    M921
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x04C1)
        M1A0 (Local1, C010, Ones, 0x04C2)
        Local0 = Index (Package (0x01)
                {
                    M922
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x04C3)
        M1A0 (Local1, C010, Ones, 0x04C4)
        Local0 = Index (Package (0x01)
                {
                    M923
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x04C5)
        M1A0 (Local1, C010, Ones, 0x04C6)
        Local0 = Index (Package (0x01)
                {
                    M924
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x04C7)
        M1A0 (Local1, C010, Ones, 0x04C8)
        Local0 = Index (Package (0x01)
                {
                    M925
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x04C9)
        M1A0 (Local1, C010, Ones, 0x04CA)
        Local0 = Index (Package (0x01)
                {
                    M926
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x04CB)
        M1A0 (Local1, C010, Ones, 0x04CC)
        Local0 = Index (Package (0x01)
                {
                    M927
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x04CD)
        M1A0 (Local1, C010, Ones, 0x04CE)
        Local0 = Index (Package (0x01)
                {
                    M928
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x04CF)
        M1A0 (Local1, C010, Ones, 0x04D0)
        Local0 = Index (Package (0x01)
                {
                    M929
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x04D1)
        M1A0 (Local1, C010, Ones, 0x04D2)
        Local0 = Index (Package (0x01)
                {
                    M92A
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x04D3)
        M1A0 (Local1, C010, Ones, 0x04D4)
        Local0 = Index (Package (0x01)
                {
                    M92B
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x04D5)
        M1A0 (Local1, C010, Ones, 0x04D6)
        Local0 = Index (Package (0x01)
                {
                    M92C
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x04D7)
        M1A0 (Local1, C010, Ones, 0x04D8)
        Local0 = Index (Package (0x01)
                {
                    M92D
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x04D9)
        M1A0 (Local1, C010, Ones, 0x04DA)
        Local0 = Index (Package (0x01)
                {
                    M92E
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x04DB)
        M1A0 (Local1, C010, Ones, 0x04DC)
        Local0 = Index (Package (0x01)
                {
                    M92F
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x04DD)
        M1A0 (Local1, C010, Ones, 0x04DE)
        Local0 = Index (Package (0x01)
                {
                    M930
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x04DF)
        M1A0 (Local1, C010, Ones, 0x04E0)
        Local0 = Index (Package (0x01)
                {
                    M931
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x04E1)
        M1A0 (Local1, C010, Ones, 0x04E2)
        Local0 = Index (Package (0x01)
                {
                    M932
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x04E3)
        M1A0 (Local1, C010, Ones, 0x04E4)
        Local0 = Index (Package (0x01)
                {
                    M933
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x04E5)
        M1A0 (Local1, C010, Ones, 0x04E6)
        Local0 = Index (Package (0x01)
                {
                    M934
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x04E7)
        M1A0 (Local1, C010, Ones, 0x04E8)
        Local0 = Index (Package (0x01)
                {
                    M935
                }, 0x00, Local1)
        M1A0 (Local0, C010, Ones, 0x04E9)
        M1A0 (Local1, C010, Ones, 0x04EA)
        M1A6 ()
    }

    Method (M195, 5, NotSerialized)
    {
        C081 = Z080       /* absolute index of file initiating the checking */ /* \Z080 */
        C089 = 0x01      /* flag of Reference, object otherwise */
        /*
         *	Store(0xd7, f900)
         *	Store(0xd8, if90)
         */
        If (Arg0)
        {
            M190 ()
        }

        If (Arg1)
        {
            M191 (C083)
        }

        If (Arg2)
        {
            M192 ()
        }

        If (Arg3)
        {
            M193 (C083)
        }

        If (Arg4)
        {
            M194 ()
        }
    }

    /* Usual mode */

    Method (M196, 0, NotSerialized)
    {
        C084 = 0x01  /* run verification of references (reading) */
        C085 = 0x00  /* create the chain of references to LocalX, then dereference them */
        Debug = "Usual mode:"
        M195 (0x01, 0x01, 0x01, 0x01, 0x01)
    }

    /* The mode with the chain of references to LocalX */

    Method (M197, 0, NotSerialized)
    {
        C084 = 0x01  /* run verification of references (reading) */
        C085 = 0x01  /* create the chain of references to LocalX, then dereference them */
        Debug = "The mode with the chain of references to LocalX:"
        M195 (0x01, 0x01, 0x01, 0x01, 0x01)
    }

    /* Run-method */

    Method (REF4, 0, NotSerialized)
    {
        Debug = "TEST: REF4, References"
        C080 = "REF4" /* name of test */
        C082 = 0x00      /* flag of test of exceptions */
        C083 = 0x00      /* run verification of references (write/read) */
        C086 = 0x00      /* flag, run test till the first error */
        C087 = 0x01      /* apply DeRefOf to ArgX-ObjectReference */
        M196 ()
        M197 ()
    }
