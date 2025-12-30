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
     * TABLE 6: all the legal ways to generate references to ArgX
     *
     * Producing Reference operators:
     *
     *    Index, RefOf, CondRefOf
     */
    Name (Z079, 0x4F)
    /* /////////////////////////////////////////////////////////////////////////// */
    /* */
    /* TABLE 6: all the legal ways to generate references to ArgX */
    /* */
    /* /////////////////////////////////////////////////////////////////////////// */
    /* m169,m190,m170 */
    Method (M180, 2, NotSerialized)
    {
        If (Y100)
        {
            TS00 ("m180")
        }
        Else
        {
            Debug = "m180"
        }

        /* T6:I2-I4 */
        /* Computational Data */
        Arg1 = S900 /* \S900 */
        Store (Arg1 [0x00], Local0)
        M1A2 (Local0, C016, 0x00, 0x00, C009, 0x31, __LINE__)
        Arg1 = S901 /* \S901 */
        Store (Arg1 [0x02], Local0)
        M1A2 (Local0, C016, 0x00, 0x00, C009, 0x72, __LINE__)
        Arg1 = B900 /* \B900 */
        Store (Arg1 [0x03], Local0)
        M1A2 (Local0, C016, 0x00, 0x00, C009, 0xB3, __LINE__)
        /* Elements of Package are Uninitialized */

        If (Y104)
        {
            Arg1 = P900 /* \P900 */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C008, Ones, 0x04)
        }

        /* Elements of Package are Computational Data */

        Arg1 = P901 /* \P901 */
        Store (Arg1 [0x00], Local0)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xABCD0004, __LINE__)
        Arg1 = P901 /* \P901 */
        Store (Arg1 [0x01], Local0)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0x1122334455660005, __LINE__)
        Arg1 = P902 /* \P902 */
        Store (Arg1 [0x00], Local0)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "12340006", __LINE__)
        Arg1 = P902 /* \P902 */
        Store (Arg1 [0x01], Local0)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "q1w2e3r4t5y6u7i80007", __LINE__)
        Arg1 = P903 /* \P903 */
        Store (Arg1 [0x00], Local0)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "qwrtyuiop0008", __LINE__)
        Arg1 = P903 /* \P903 */
        Store (Arg1 [0x01], Local0)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "1234567890abdef0250009", __LINE__)
        Arg1 = P904 /* \P904 */
        Store (Arg1 [0x00], Local0)
        M1A2 (Local0, C00B, 0x00, 0x00, C00B, Buffer (0x03)
            {
                 0xB5, 0xB6, 0xB7                                 // ...
            }, 0x0B)
        Arg1 = P905 /* \P905 */
        Store (Arg1 [0x00], Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0x0ABC000A, __LINE__)
        Arg1 = P905 /* \P905 */
        Store (Arg1 [0x00], Local0)
        M1A2 (Local0, C00C, 0x01, 0x01, C00A, "0xabc000b", __LINE__)
        Arg1 = P906 /* \P906 */
        Store (Arg1 [0x00], Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "abc000d", __LINE__)
        Arg1 = P907 /* \P907 */
        Store (Arg1 [0x00], Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "aqwevbgnm000e", __LINE__)
        Arg1 = P908 /* \P908 */
        Store (Arg1 [0x00], Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C00B, Buffer (0x05)
            {
                 0xBA, 0xBB, 0xBC, 0xBD, 0xBE                     // .....
            }, 0x10)
        Arg1 = P909 /* \P909 */
        Store (Arg1 [0x00], Local0)
        M1A2 (Local0, C00C, 0x02, 0x00, C009, 0x0ABC000F, __LINE__)
        Arg1 = P90A /* \P90A */
        Store (Arg1 [0x00], Local0)
        M1A2 (Local0, C00C, 0x02, 0x00, C00A, "12340010", __LINE__)
        Arg1 = P90B /* \P90B */
        Store (Arg1 [0x00], Local0)
        M1A2 (Local0, C00C, 0x02, 0x00, C00A, "zxswefas0011", __LINE__)
        Arg1 = P90C /* \P90C */
        Store (Arg1 [0x00], Local0)
        M1A2 (Local0, C00C, 0x02, 0x00, C00B, Buffer (0x03)
            {
                 0xBF, 0xC0, 0xC1                                 // ...
            }, 0x14)
        Arg1 = P90D /* \P90D */
        Store (Arg1 [0x00], Local0)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xFE7CB391D65A0000, __LINE__)
        Arg1 = P90E /* \P90E */
        Store (Arg1 [0x00], Local0)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xC1790001, __LINE__)
        Arg1 = P90F /* \P90F */
        Store (Arg1 [0x00], Local0)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "12340002", __LINE__)
        Arg1 = P910 /* \P910 */
        Store (Arg1 [0x00], Local0)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "qwrtyu0003", __LINE__)
        Arg1 = P911 /* \P911 */
        Store (Arg1 [0x00], Local0)
        M1A2 (Local0, C00B, 0x00, 0x00, C00B, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            }, 0x19)
        If (Y118)
        {
            Arg1 = P912 /* \P912 */
            Store (Arg1 [0x00], Local0)
            M1A2 (Local0, C00D, 0x00, 0x00, C00D, 0x00, __LINE__)
            Arg1 = P913 /* \P913 */
            Store (Arg1 [0x00], Local0)
            M1A2 (Local0, C00D, 0x00, 0x00, C00D, 0x00, __LINE__)
            Arg1 = P914 /* \P914 */
            Store (Arg1 [0x00], Local0)
            M1A2 (Local0, C00D, 0x00, 0x00, C00D, 0x00, __LINE__)
            Arg1 = P915 /* \P915 */
            Store (Arg1 [0x00], Local0)
            M1A2 (Local0, C016, 0x00, 0x00, C016, 0xB0, __LINE__)
        }

        /* Elements of Package are NOT Computational Data */

        Arg1 = P916 /* \P916 */
        Store (Arg1 [0x00], Local0)
        M1A0 (Local0, C00E, Ones, 0x1E)
        Arg1 = P917 /* \P917 */
        Store (Arg1 [0x00], Local0)
        M1A0 (Local0, C00F, Ones, 0x1F)
        Arg1 = P918 /* \P918 */
        Store (Arg1 [0x00], Local0)
        M1A0 (Local0, C011, Ones, 0x20)
        Arg1 = P919 /* \P919 */
        Store (Arg1 [0x00], Local0)
        M1A0 (Local0, C012, Ones, 0x21)
        Arg1 = P91A /* \P91A */
        Store (Arg1 [0x00], Local0)
        M1A0 (Local0, C013, Ones, 0x22)
        Arg1 = P91B /* \P91B */
        Store (Arg1 [0x00], Local0)
        M1A0 (Local0, C014, Ones, 0x23)
        Arg1 = P91C /* \P91C */
        Store (Arg1 [0x00], Local0)
        M1A0 (Local0, C015, Ones, 0x24)
        /* Elements of Package are Methods */

        If (Y105)
        {
            Arg1 = P91D /* \P91D */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x25)
            Arg1 = P91E /* \P91E */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x26)
            Arg1 = P91F /* \P91F */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x27)
            Arg1 = P920 /* \P920 */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x28)
            Arg1 = P921 /* \P921 */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x29)
            Arg1 = P922 /* \P922 */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x2A)
            Arg1 = P923 /* \P923 */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x2B)
            Arg1 = P924 /* \P924 */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x2C)
            Arg1 = P925 /* \P925 */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x2D)
            Arg1 = P926 /* \P926 */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x2E)
            Arg1 = P927 /* \P927 */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x2F)
            Arg1 = P928 /* \P928 */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x30)
            Arg1 = P929 /* \P929 */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x31)
            Arg1 = P92A /* \P92A */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x32)
            Arg1 = P92B /* \P92B */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x33)
            Arg1 = P92C /* \P92C */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x34)
            Arg1 = P92D /* \P92D */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x35)
            Arg1 = P92E /* \P92E */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x36)
            Arg1 = P92F /* \P92F */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x37)
            Arg1 = P930 /* \P930 */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x38)
            Arg1 = P931 /* \P931 */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x39)
            Arg1 = P932 /* \P932 */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x3A)
            Arg1 = P933 /* \P933 */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x3B)
            Arg1 = P934 /* \P934 */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x3C)
            If (Y103)
            {
                Arg1 = P935 /* \P935 */
                Store (Arg1 [0x00], Local0)
                M1A0 (Local0, C010, Ones, 0x3D)
            }

            Arg1 = P936 /* \P936 */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x3E)
            Arg1 = P937 /* \P937 */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x3F)
            Arg1 = P938 /* \P938 */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x40)
            Arg1 = P939 /* \P939 */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x41)
            Arg1 = P93A /* \P93A */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x42)
            Arg1 = P93B /* \P93B */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x43)
            Arg1 = P93C /* \P93C */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x44)
            Arg1 = P93D /* \P93D */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x45)
            Arg1 = P93E /* \P93E */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x46)
            Arg1 = P93F /* \P93F */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x47)
            Arg1 = P940 /* \P940 */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x48)
            Arg1 = P941 /* \P941 */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x49)
            Arg1 = P942 /* \P942 */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x4A)
            Arg1 = P943 /* \P943 */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x4B)
            Arg1 = P944 /* \P944 */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x4C)
            Arg1 = P945 /* \P945 */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x4D)
            Arg1 = P946 /* \P946 */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x4E)
            Arg1 = P947 /* \P947 */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x4F)
            Arg1 = P948 /* \P948 */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x50)
            Arg1 = P949 /* \P949 */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x51)
            Arg1 = P94A /* \P94A */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x52)
            Arg1 = P94B /* \P94B */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x53)
            Arg1 = P94C /* \P94C */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x54)
            Arg1 = P94D /* \P94D */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x55)
            Arg1 = P94E /* \P94E */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x56)
            Arg1 = P94F /* \P94F */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x57)
            Arg1 = P950 /* \P950 */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x58)
            Arg1 = P951 /* \P951 */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x59)
            Arg1 = P952 /* \P952 */
            Store (Arg1 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x5A)
        }

        /* T6:IR2-IR4 */
        /* Computational Data */
        Arg1 = S900 /* \S900 */
        Local0 = Local1 = Arg1 [0x00]
        M1A2 (Local0, C016, 0x00, 0x00, C009, 0x31, __LINE__)
        M1A2 (Local1, C016, 0x00, 0x00, C009, 0x31, __LINE__)
        Arg1 = S901 /* \S901 */
        Local0 = Local1 = Arg1 [0x02]
        M1A2 (Local0, C016, 0x00, 0x00, C009, 0x72, __LINE__)
        M1A2 (Local1, C016, 0x00, 0x00, C009, 0x72, __LINE__)
        Arg1 = B900 /* \B900 */
        Local0 = Local1 = Arg1 [0x04]
        M1A2 (Local0, C016, 0x00, 0x00, C009, 0xB4, __LINE__)
        M1A2 (Local1, C016, 0x00, 0x00, C009, 0xB4, __LINE__)
        /* Elements of Package are Uninitialized */

        If (Y104)
        {
            Arg1 = P900 /* \P900 */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C008, Ones, 0x61)
            M1A0 (Local1, C008, Ones, 0x62)
        }

        /* Elements of Package are Computational Data */

        Arg1 = P901 /* \P901 */
        Local0 = Local1 = Arg1 [0x00]
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xABCD0004, __LINE__)
        M1A2 (Local1, C009, 0x00, 0x00, C009, 0xABCD0004, __LINE__)
        Arg1 = P901 /* \P901 */
        Local0 = Local1 = Arg1 [0x01]
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0x1122334455660005, __LINE__)
        M1A2 (Local1, C009, 0x00, 0x00, C009, 0x1122334455660005, __LINE__)
        Arg1 = P902 /* \P902 */
        Local0 = Local1 = Arg1 [0x00]
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "12340006", __LINE__)
        M1A2 (Local1, C00A, 0x00, 0x00, C00A, "12340006", __LINE__)
        Arg1 = P902 /* \P902 */
        Local0 = Local1 = Arg1 [0x01]
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "q1w2e3r4t5y6u7i80007", __LINE__)
        M1A2 (Local1, C00A, 0x00, 0x00, C00A, "q1w2e3r4t5y6u7i80007", __LINE__)
        Arg1 = P903 /* \P903 */
        Local0 = Local1 = Arg1 [0x00]
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "qwrtyuiop0008", __LINE__)
        M1A2 (Local1, C00A, 0x00, 0x00, C00A, "qwrtyuiop0008", __LINE__)
        Arg1 = P903 /* \P903 */
        Local0 = Local1 = Arg1 [0x01]
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "1234567890abdef0250009", __LINE__)
        M1A2 (Local1, C00A, 0x00, 0x00, C00A, "1234567890abdef0250009", __LINE__)
        Arg1 = P904 /* \P904 */
        Local0 = Local1 = Arg1 [0x00]
        M1A2 (Local0, C00B, 0x00, 0x00, C00B, Buffer (0x03)
            {
                 0xB5, 0xB6, 0xB7                                 // ...
            }, 0x6F)
        M1A2 (Local1, C00B, 0x00, 0x00, C00B, Buffer (0x03)
            {
                 0xB5, 0xB6, 0xB7                                 // ...
            }, 0x70)
        Arg1 = P905 /* \P905 */
        Local0 = Local1 = Arg1 [0x00]
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0x0ABC000A, __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x00, C009, 0x0ABC000A, __LINE__)
        Arg1 = P905 /* \P905 */
        Local0 = Local1 = Arg1 [0x00]
        M1A2 (Local0, C00C, 0x01, 0x01, C00A, "0xabc000b", __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x01, C00A, "0xabc000b", __LINE__)
        Arg1 = P906 /* \P906 */
        Local0 = Local1 = Arg1 [0x00]
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "abc000d", __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x00, C00A, "abc000d", __LINE__)
        Arg1 = P907 /* \P907 */
        Local0 = Local1 = Arg1 [0x00]
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "aqwevbgnm000e", __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x00, C00A, "aqwevbgnm000e", __LINE__)
        Arg1 = P908 /* \P908 */
        Local0 = Local1 = Arg1 [0x00]
        M1A2 (Local0, C00C, 0x01, 0x00, C00B, Buffer (0x05)
            {
                 0xBA, 0xBB, 0xBC, 0xBD, 0xBE                     // .....
            }, 0x79)
        M1A2 (Local1, C00C, 0x01, 0x00, C00B, Buffer (0x05)
            {
                 0xBA, 0xBB, 0xBC, 0xBD, 0xBE                     // .....
            }, 0x7A)
        Arg1 = P909 /* \P909 */
        Local0 = Local1 = Arg1 [0x00]
        M1A2 (Local0, C00C, 0x02, 0x00, C009, 0x0ABC000F, __LINE__)
        M1A2 (Local1, C00C, 0x02, 0x00, C009, 0x0ABC000F, __LINE__)
        Arg1 = P90A /* \P90A */
        Local0 = Local1 = Arg1 [0x00]
        M1A2 (Local0, C00C, 0x02, 0x00, C00A, "12340010", __LINE__)
        M1A2 (Local1, C00C, 0x02, 0x00, C00A, "12340010", __LINE__)
        Arg1 = P90B /* \P90B */
        Local0 = Local1 = Arg1 [0x00]
        M1A2 (Local0, C00C, 0x02, 0x00, C00A, "zxswefas0011", __LINE__)
        M1A2 (Local1, C00C, 0x02, 0x00, C00A, "zxswefas0011", __LINE__)
        Arg1 = P90C /* \P90C */
        Local0 = Local1 = Arg1 [0x00]
        M1A2 (Local0, C00C, 0x02, 0x00, C00B, Buffer (0x03)
            {
                 0xBF, 0xC0, 0xC1                                 // ...
            }, 0x81)
        M1A2 (Local1, C00C, 0x02, 0x00, C00B, Buffer (0x03)
            {
                 0xBF, 0xC0, 0xC1                                 // ...
            }, 0x82)
        Arg1 = P90D /* \P90D */
        Local0 = Local1 = Arg1 [0x00]
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xFE7CB391D65A0000, __LINE__)
        M1A2 (Local1, C009, 0x00, 0x00, C009, 0xFE7CB391D65A0000, __LINE__)
        Arg1 = P90E /* \P90E */
        Local0 = Local1 = Arg1 [0x00]
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xC1790001, __LINE__)
        M1A2 (Local1, C009, 0x00, 0x00, C009, 0xC1790001, __LINE__)
        Arg1 = P90F /* \P90F */
        Local0 = Local1 = Arg1 [0x00]
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "12340002", __LINE__)
        M1A2 (Local1, C00A, 0x00, 0x00, C00A, "12340002", __LINE__)
        Arg1 = P910 /* \P910 */
        Local0 = Local1 = Arg1 [0x00]
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "qwrtyu0003", __LINE__)
        M1A2 (Local1, C00A, 0x00, 0x00, C00A, "qwrtyu0003", __LINE__)
        Arg1 = P911 /* \P911 */
        Local0 = Local1 = Arg1 [0x00]
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
            Arg1 = P912 /* \P912 */
            Local0 = Local1 = Arg1 [0x00]
            M1A2 (Local0, C00D, 0x00, 0x00, C00D, 0x00, __LINE__)
            M1A2 (Local1, C00D, 0x00, 0x00, C00D, 0x00, __LINE__)
            Arg1 = P913 /* \P913 */
            Local0 = Local1 = Arg1 [0x00]
            M1A2 (Local0, C00D, 0x00, 0x00, C00D, 0x00, __LINE__)
            M1A2 (Local1, C00D, 0x00, 0x00, C00D, 0x00, __LINE__)
            Arg1 = P914 /* \P914 */
            Local0 = Local1 = Arg1 [0x00]
            M1A2 (Local0, C00D, 0x00, 0x00, C00D, 0x00, __LINE__)
            M1A2 (Local1, C00D, 0x00, 0x00, C00D, 0x00, __LINE__)
            Arg1 = P915 /* \P915 */
            Local0 = Local1 = Arg1 [0x00]
            M1A2 (Local0, C016, 0x00, 0x00, C016, 0xB0, __LINE__)
            M1A2 (Local1, C016, 0x00, 0x00, C016, 0xB0, __LINE__)
        }

        /* Elements of Package are NOT Computational Data */

        Arg1 = P916 /* \P916 */
        Local0 = Local1 = Arg1 [0x00]
        M1A0 (Local0, C00E, Ones, 0x95)
        M1A0 (Local1, C00E, Ones, 0x96)
        Arg1 = P917 /* \P917 */
        Local0 = Local1 = Arg1 [0x00]
        M1A0 (Local0, C00F, Ones, 0x97)
        M1A0 (Local1, C00F, Ones, 0x98)
        Arg1 = P918 /* \P918 */
        Local0 = Local1 = Arg1 [0x00]
        M1A0 (Local0, C011, Ones, 0x99)
        M1A0 (Local1, C011, Ones, 0x9A)
        Arg1 = P919 /* \P919 */
        Local0 = Local1 = Arg1 [0x00]
        M1A0 (Local0, C012, Ones, 0x9B)
        M1A0 (Local1, C012, Ones, 0x9C)
        Arg1 = P91A /* \P91A */
        Local0 = Local1 = Arg1 [0x00]
        M1A0 (Local0, C013, Ones, 0x9D)
        M1A0 (Local1, C013, Ones, 0x9E)
        Arg1 = P91B /* \P91B */
        Local0 = Local1 = Arg1 [0x00]
        M1A0 (Local0, C014, Ones, 0x9F)
        M1A0 (Local1, C014, Ones, 0xA0)
        Arg1 = P91C /* \P91C */
        Local0 = Local1 = Arg1 [0x00]
        M1A0 (Local0, C015, Ones, 0xA1)
        M1A0 (Local1, C015, Ones, 0xA2)
        /* Elements of Package are Methods */

        If (Y105)
        {
            Arg1 = P91D /* \P91D */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xA3)
            M1A0 (Local1, C010, Ones, 0xA4)
            Arg1 = P91E /* \P91E */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xA5)
            M1A0 (Local1, C010, Ones, 0xA6)
            Arg1 = P91F /* \P91F */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xA7)
            M1A0 (Local1, C010, Ones, 0xA8)
            Arg1 = P920 /* \P920 */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xA9)
            M1A0 (Local1, C010, Ones, 0xAA)
            Arg1 = P921 /* \P921 */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xAB)
            M1A0 (Local1, C010, Ones, 0xAC)
            Arg1 = P922 /* \P922 */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xAD)
            M1A0 (Local1, C010, Ones, 0xAE)
            Arg1 = P923 /* \P923 */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xAF)
            M1A0 (Local1, C010, Ones, 0xB0)
            Arg1 = P924 /* \P924 */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xB1)
            M1A0 (Local1, C010, Ones, 0xB2)
            Arg1 = P925 /* \P925 */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xB3)
            M1A0 (Local1, C010, Ones, 0xB4)
            Arg1 = P926 /* \P926 */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xB5)
            M1A0 (Local1, C010, Ones, 0xB6)
            Arg1 = P927 /* \P927 */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xB7)
            M1A0 (Local1, C010, Ones, 0xB8)
            Arg1 = P928 /* \P928 */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xB9)
            M1A0 (Local1, C010, Ones, 0xBA)
            Arg1 = P929 /* \P929 */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xBB)
            M1A0 (Local1, C010, Ones, 0xBC)
            Arg1 = P92A /* \P92A */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xBD)
            M1A0 (Local1, C010, Ones, 0xBE)
            Arg1 = P92B /* \P92B */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xBF)
            M1A0 (Local1, C010, Ones, 0xC0)
            Arg1 = P92C /* \P92C */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xC1)
            M1A0 (Local1, C010, Ones, 0xC2)
            Arg1 = P92D /* \P92D */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xC3)
            M1A0 (Local1, C010, Ones, 0xC4)
            Arg1 = P92E /* \P92E */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xC5)
            M1A0 (Local1, C010, Ones, 0xC6)
            Arg1 = P92F /* \P92F */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xC7)
            M1A0 (Local1, C010, Ones, 0xC8)
            Arg1 = P930 /* \P930 */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xC9)
            M1A0 (Local1, C010, Ones, 0xCA)
            Arg1 = P931 /* \P931 */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xCB)
            M1A0 (Local1, C010, Ones, 0xCC)
            Arg1 = P932 /* \P932 */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xCD)
            M1A0 (Local1, C010, Ones, 0xCE)
            Arg1 = P933 /* \P933 */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xCF)
            M1A0 (Local1, C010, Ones, 0xD0)
            Arg1 = P934 /* \P934 */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xD1)
            M1A0 (Local1, C010, Ones, 0xD2)
            If (Y103)
            {
                Arg1 = P935 /* \P935 */
                Local0 = Local1 = Arg1 [0x00]
                M1A0 (Local0, C010, Ones, 0xD3)
                M1A0 (Local1, C010, Ones, 0xD4)
            }

            Arg1 = P936 /* \P936 */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xD5)
            M1A0 (Local1, C010, Ones, 0xD6)
            Arg1 = P937 /* \P937 */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xD7)
            M1A0 (Local1, C010, Ones, 0xD8)
            Arg1 = P938 /* \P938 */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xD9)
            M1A0 (Local1, C010, Ones, 0xDA)
            Arg1 = P939 /* \P939 */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xDB)
            M1A0 (Local1, C010, Ones, 0xDC)
            Arg1 = P93A /* \P93A */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xDD)
            M1A0 (Local1, C010, Ones, 0xDE)
            Arg1 = P93B /* \P93B */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xDF)
            M1A0 (Local1, C010, Ones, 0xE0)
            Arg1 = P93C /* \P93C */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xE1)
            M1A0 (Local1, C010, Ones, 0xE2)
            Arg1 = P93D /* \P93D */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xE3)
            M1A0 (Local1, C010, Ones, 0xE4)
            Arg1 = P93E /* \P93E */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xE5)
            M1A0 (Local1, C010, Ones, 0xE6)
            Arg1 = P93F /* \P93F */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xE7)
            M1A0 (Local1, C010, Ones, 0xE8)
            Arg1 = P940 /* \P940 */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xE9)
            M1A0 (Local1, C010, Ones, 0xEA)
            Arg1 = P941 /* \P941 */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xEB)
            M1A0 (Local1, C010, Ones, 0xEC)
            Arg1 = P942 /* \P942 */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xED)
            M1A0 (Local1, C010, Ones, 0xEE)
            Arg1 = P943 /* \P943 */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xEF)
            M1A0 (Local1, C010, Ones, 0xF0)
            Arg1 = P944 /* \P944 */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xF1)
            M1A0 (Local1, C010, Ones, 0xF2)
            Arg1 = P945 /* \P945 */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xF3)
            M1A0 (Local1, C010, Ones, 0xF4)
            Arg1 = P946 /* \P946 */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xF5)
            M1A0 (Local1, C010, Ones, 0xF6)
            Arg1 = P947 /* \P947 */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xF7)
            M1A0 (Local1, C010, Ones, 0xF8)
            Arg1 = P948 /* \P948 */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xF9)
            M1A0 (Local1, C010, Ones, 0xFA)
            Arg1 = P949 /* \P949 */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xFB)
            M1A0 (Local1, C010, Ones, 0xFC)
            Arg1 = P94A /* \P94A */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xFD)
            M1A0 (Local1, C010, Ones, 0xFE)
            Arg1 = P94B /* \P94B */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0xFF)
            M1A0 (Local1, C010, Ones, 0x0100)
            Arg1 = P94C /* \P94C */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0x0101)
            M1A0 (Local1, C010, Ones, 0x0102)
            Arg1 = P94D /* \P94D */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0x0103)
            M1A0 (Local1, C010, Ones, 0x0104)
            Arg1 = P94E /* \P94E */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0x0105)
            M1A0 (Local1, C010, Ones, 0x0106)
            Arg1 = P94F /* \P94F */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0x0107)
            M1A0 (Local1, C010, Ones, 0x0108)
            Arg1 = P950 /* \P950 */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0x0109)
            M1A0 (Local1, C010, Ones, 0x010A)
            Arg1 = P951 /* \P951 */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0x010B)
            M1A0 (Local1, C010, Ones, 0x010C)
            Arg1 = P952 /* \P952 */
            Local0 = Local1 = Arg1 [0x00]
            M1A0 (Local0, C010, Ones, 0x010D)
            M1A0 (Local1, C010, Ones, 0x010E)
        }

        M1A6 ()
    }

    /* m16a,m191,m171 */
    /* arg2 - writing mode */
    Method (M181, 3, NotSerialized)
    {
        If (Y100)
        {
            TS00 ("m181")
        }
        Else
        {
            Debug = "m181"
        }

        /* T6:R0-R5,R14 */
        /* Uninitialized Local */
        If (Arg0)
        {
            Arg6 = 0x00
        }

        Local0 = RefOf (Arg6)
        M1A0 (Local0, C008, Ones, 0x03E8)
        /* Computational Data */

        Arg1 = I900 /* \I900 */
        Local0 = RefOf (Arg1)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xFE7CB391D65A0000, __LINE__)
        Arg1 = I901 /* \I901 */
        Local0 = RefOf (Arg1)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xC1790001, __LINE__)
        Arg1 = S900 /* \S900 */
        Local0 = RefOf (Arg1)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "12340002", __LINE__)
        Arg1 = S901 /* \S901 */
        Local0 = RefOf (Arg1)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "qwrtyu0003", __LINE__)
        Arg1 = B900 /* \B900 */
        Local0 = RefOf (Arg1)
        M1A2 (Local0, C00B, 0x00, 0x00, C00B, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            }, 0x0113)
        /* Not Computational Data */
        /* Package */
        Arg1 = P953 /* \P953 */
        Local0 = RefOf (Arg1)
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xABCD0018, __LINE__)
        If (Arg2)
        {
            /* Data are unchanged, because writings were made */
            /* into the new objects associated with arg1. */
            M1A6 ()
            Return (Zero)
        }

        /* Computational Data (Field Unit and Buffer Field) */

        Arg1 = F900 /* \F900 */
        Local0 = RefOf (Arg1)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0x00, __LINE__)
        Arg1 = BN90 /* \BN90 */
        Local0 = RefOf (Arg1)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0x00, __LINE__)
        Arg1 = IF90 /* \IF90 */
        Local0 = RefOf (Arg1)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0x00, __LINE__)
        Arg1 = BF90 /* \BF90 */
        Local0 = RefOf (Arg1)
        M1A2 (Local0, C00B, 0x00, 0x00, C00B, Buffer(){0xB0}, __LINE__)
        /* Elements of Package are Uninitialized */

        Arg1 = P900 /* \P900 */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x011F)
        /* Elements of Package are Computational Data */

        Arg1 = P901 /* \P901 */
        Local0 = RefOf (Arg1)
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xABCD0004, __LINE__)
        M1A2 (Local0, C00C, 0x01, 0x01, C009, 0x1122334455660005, __LINE__)
        Arg1 = P902 /* \P902 */
        Local0 = RefOf (Arg1)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "12340006", __LINE__)
        M1A2 (Local0, C00C, 0x01, 0x01, C00A, "q1w2e3r4t5y6u7i80007", __LINE__)
        Arg1 = P903 /* \P903 */
        Local0 = RefOf (Arg1)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "qwrtyuiop0008", __LINE__)
        M1A2 (Local0, C00C, 0x01, 0x01, C00A, "1234567890abdef0250009", __LINE__)
        Arg1 = P904 /* \P904 */
        Local0 = RefOf (Arg1)
        M1A2 (Local0, C00C, 0x01, 0x00, C00B, Buffer (0x03)
            {
                 0xB5, 0xB6, 0xB7                                 // ...
            }, 0x0126)
        Arg1 = P905 /* \P905 */
        Local0 = RefOf (Arg1)
        M1A2 (Local0, C00C, 0x02, 0x00, C009, 0x0ABC000A, __LINE__)
        M1A2 (Local0, C00C, 0x02, 0x01, C00A, "0xabc000b", __LINE__)
        Arg1 = P906 /* \P906 */
        Local0 = RefOf (Arg1)
        M1A2 (Local0, C00C, 0x02, 0x00, C00A, "abc000d", __LINE__)
        Arg1 = P907 /* \P907 */
        Local0 = RefOf (Arg1)
        M1A2 (Local0, C00C, 0x02, 0x00, C00A, "aqwevbgnm000e", __LINE__)
        Arg1 = P908 /* \P908 */
        Local0 = RefOf (Arg1)
        M1A2 (Local0, C00C, 0x02, 0x00, C00B, Buffer (0x05)
            {
                 0xBA, 0xBB, 0xBC, 0xBD, 0xBE                     // .....
            }, 0x012B)
        Arg1 = P909 /* \P909 */
        Local0 = RefOf (Arg1)
        M1A2 (Local0, C00C, 0x03, 0x00, C009, 0x0ABC000F, __LINE__)
        Arg1 = P90A /* \P90A */
        Local0 = RefOf (Arg1)
        M1A2 (Local0, C00C, 0x03, 0x00, C00A, "12340010", __LINE__)
        Arg1 = P90B /* \P90B */
        Local0 = RefOf (Arg1)
        M1A2 (Local0, C00C, 0x03, 0x00, C00A, "zxswefas0011", __LINE__)
        Arg1 = P90C /* \P90C */
        Local0 = RefOf (Arg1)
        M1A2 (Local0, C00C, 0x03, 0x00, C00B, Buffer (0x03)
            {
                 0xBF, 0xC0, 0xC1                                 // ...
            }, 0x012F)
        Arg1 = P90D /* \P90D */
        Local0 = RefOf (Arg1)
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xFE7CB391D65A0000, __LINE__)
        Arg1 = P90E /* \P90E */
        Local0 = RefOf (Arg1)
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xC1790001, __LINE__)
        Arg1 = P90F /* \P90F */
        Local0 = RefOf (Arg1)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "12340002", __LINE__)
        Arg1 = P910 /* \P910 */
        Local0 = RefOf (Arg1)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "qwrtyu0003", __LINE__)
        Arg1 = P911 /* \P911 */
        Local0 = RefOf (Arg1)
        M1A2 (Local0, C00C, 0x01, 0x00, C00B, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            }, 0x0134)
        If (Y118)
        {
            Arg1 = P912 /* \P912 */
            Local0 = RefOf (Arg1)
            M1A2 (Local0, C00C, 0x01, 0x00, C00D, 0x00, __LINE__)
            Arg1 = P913 /* \P913 */
            Local0 = RefOf (Arg1)
            M1A2 (Local0, C00C, 0x01, 0x00, C00D, 0x00, __LINE__)
            Arg1 = P914 /* \P914 */
            Local0 = RefOf (Arg1)
            M1A2 (Local0, C00C, 0x01, 0x00, C00D, 0x00, __LINE__)
            Arg1 = P915 /* \P915 */
            Local0 = RefOf (Arg1)
            M1A2 (Local0, C00C, 0x01, 0x00, C016, 0xB0, __LINE__)
        }

        /* Elements of Package are NOT Computational Data */

        Arg1 = P916 /* \P916 */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x0139)
        Arg1 = P917 /* \P917 */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x013A)
        Arg1 = P918 /* \P918 */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x013B)
        Arg1 = P919 /* \P919 */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x013C)
        Arg1 = P91A /* \P91A */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x013D)
        Arg1 = P91B /* \P91B */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x013E)
        Arg1 = P91C /* \P91C */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x013F)
        /* Elements of Package are Methods */

        Arg1 = P91D /* \P91D */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x0140)
        Arg1 = P91E /* \P91E */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x0141)
        Arg1 = P91F /* \P91F */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x0142)
        Arg1 = P920 /* \P920 */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x0143)
        Arg1 = P921 /* \P921 */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x0144)
        Arg1 = P922 /* \P922 */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x0145)
        Arg1 = P923 /* \P923 */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x0146)
        Arg1 = P924 /* \P924 */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x0147)
        Arg1 = P925 /* \P925 */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x0148)
        Arg1 = P926 /* \P926 */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x0149)
        Arg1 = P927 /* \P927 */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x014A)
        Arg1 = P928 /* \P928 */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x014B)
        Arg1 = P929 /* \P929 */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x014C)
        Arg1 = P92A /* \P92A */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x014D)
        Arg1 = P92B /* \P92B */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x014E)
        Arg1 = P92C /* \P92C */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x014F)
        Arg1 = P92D /* \P92D */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x0150)
        Arg1 = P92E /* \P92E */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x0151)
        Arg1 = P92F /* \P92F */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x0152)
        Arg1 = P930 /* \P930 */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x0153)
        Arg1 = P931 /* \P931 */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x0154)
        Arg1 = P932 /* \P932 */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x0155)
        Arg1 = P933 /* \P933 */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x0156)
        Arg1 = P934 /* \P934 */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x0157)
        Arg1 = P935 /* \P935 */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x0158)
        Arg1 = P936 /* \P936 */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x0159)
        Arg1 = P937 /* \P937 */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x015A)
        Arg1 = P938 /* \P938 */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x015B)
        Arg1 = P939 /* \P939 */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x015C)
        Arg1 = P93A /* \P93A */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x015D)
        Arg1 = P93B /* \P93B */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x015E)
        Arg1 = P93C /* \P93C */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x015F)
        Arg1 = P93D /* \P93D */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x0160)
        Arg1 = P93E /* \P93E */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x0161)
        Arg1 = P93F /* \P93F */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x0162)
        Arg1 = P940 /* \P940 */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x0163)
        Arg1 = P941 /* \P941 */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x0164)
        Arg1 = P942 /* \P942 */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x0165)
        Arg1 = P943 /* \P943 */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x0166)
        Arg1 = P944 /* \P944 */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x0167)
        Arg1 = P945 /* \P945 */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x0168)
        Arg1 = P946 /* \P946 */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x0169)
        Arg1 = P947 /* \P947 */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x016A)
        Arg1 = P948 /* \P948 */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x016B)
        Arg1 = P949 /* \P949 */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x016C)
        Arg1 = P94A /* \P94A */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x016D)
        Arg1 = P94B /* \P94B */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x016E)
        Arg1 = P94C /* \P94C */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x016F)
        Arg1 = P94D /* \P94D */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x0170)
        Arg1 = P94E /* \P94E */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x0171)
        Arg1 = P94F /* \P94F */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x0172)
        Arg1 = P950 /* \P950 */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x0173)
        Arg1 = P951 /* \P951 */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x0174)
        Arg1 = P952 /* \P952 */
        Local0 = RefOf (Arg1)
        M1A0 (Local0, C00C, Ones, 0x0175)
        M1A6 ()
        Return (Zero)
    }

    /* m16c,m193,m172 */
    /* arg2 - writing mode */
    Method (M182, 3, NotSerialized)
    {
        If (Y100)
        {
            TS00 ("m182")
        }
        Else
        {
            Debug = "m182"
        }

        /* T6:CR0-CR5,CR14 */
        /* Uninitialized Local */
        If (Arg0)
        {
            Arg6 = 0x00
        }

        Local1 = CondRefOf (Arg6, Local0)
        If (M1A4 (Local1, 0x024D))
        {
            M1A0 (Local0, C008, Ones, 0x024E)
        }

        /* Computational Data */

        Arg1 = I900 /* \I900 */
        Local1 = CondRefOf (Arg1, Local0)
        If (M1A4 (Local1, 0x024F))
        {
            M1A2 (Local0, C009, 0x00, 0x00, C009, 0xFE7CB391D65A0000, __LINE__)
        }

        Arg1 = I901 /* \I901 */
        Local1 = CondRefOf (Arg1, Local0)
        If (M1A4 (Local1, 0x0251))
        {
            M1A2 (Local0, C009, 0x00, 0x00, C009, 0xC1790001, __LINE__)
        }

        Arg1 = S900 /* \S900 */
        Local1 = CondRefOf (Arg1, Local0)
        If (M1A4 (Local1, 0x0253))
        {
            M1A2 (Local0, C00A, 0x00, 0x00, C00A, "12340002", __LINE__)
        }

        Arg1 = S901 /* \S901 */
        Local1 = CondRefOf (Arg1, Local0)
        If (M1A4 (Local1, 0x0255))
        {
            M1A2 (Local0, C00A, 0x00, 0x00, C00A, "qwrtyu0003", __LINE__)
        }

        Arg1 = B900 /* \B900 */
        Local1 = CondRefOf (Arg1, Local0)
        If (M1A4 (Local1, 0x0257))
        {
            M1A2 (Local0, C00B, 0x00, 0x00, C00B, Buffer (0x05)
                {
                     0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
                }, 0x0258)
        }

        /* Not Computational Data */
        /* Package */
        Arg1 = P953 /* \P953 */
        Local1 = CondRefOf (Arg1, Local0)
        If (M1A4 (Local1, 0x03F0))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xABCD0018, __LINE__)
        }

        If (Arg2)
        {
            /* Data are unchanged, because writings were made */
            /* into the new objects associated with arg1. */
            M1A6 ()
            Return (Zero)
        }

        /* Computational Data (Field Unit and Buffer Field) */

        Arg1 = F900 /* \F900 */
        Local1 = CondRefOf (Arg1, Local0)
        If (M1A4 (Local1, 0x0259))
        {
            M1A2 (Local0, C009, 0x00, 0x00, C009, 0x00, __LINE__)
        }

        Arg1 = BN90 /* \BN90 */
        Local1 = CondRefOf (Arg1, Local0)
        If (M1A4 (Local1, 0x025B))
        {
            M1A2 (Local0, C009, 0x00, 0x00, C009, 0x00, __LINE__)
        }

        Arg1 = IF90 /* \IF90 */
        Local1 = CondRefOf (Arg1, Local0)
        If (M1A4 (Local1, 0x025D))
        {
            M1A2 (Local0, C009, 0x00, 0x00, C009, 0x00, __LINE__)
        }

        Arg1 = BF90 /* \BF90 */
        Local1 = CondRefOf (Arg1, Local0)
        If (M1A4 (Local1, 0x025F))
        {
            M1A2 (Local0, C00B, 0x00, 0x00, C00B, Buffer(){0xB0}, __LINE__)
        }

        /* Elements of Package are Uninitialized */

        Arg1 = P900 /* \P900 */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x0268)
        /* Elements of Package are Computational Data */

        Arg1 = P901 /* \P901 */
        Local1 = CondRefOf (Arg1, Local0)
        If (M1A4 (Local1, 0x0269))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xABCD0004, __LINE__)
            M1A2 (Local0, C00C, 0x01, 0x01, C009, 0x1122334455660005, __LINE__)
        }

        Arg1 = P902 /* \P902 */
        Local1 = CondRefOf (Arg1, Local0)
        If (M1A4 (Local1, 0x026C))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C00A, "12340006", __LINE__)
            M1A2 (Local0, C00C, 0x01, 0x01, C00A, "q1w2e3r4t5y6u7i80007", __LINE__)
        }

        Arg1 = P903 /* \P903 */
        Local1 = CondRefOf (Arg1, Local0)
        If (M1A4 (Local1, 0x026F))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C00A, "qwrtyuiop0008", __LINE__)
            M1A2 (Local0, C00C, 0x01, 0x01, C00A, "1234567890abdef0250009", __LINE__)
        }

        Arg1 = P904 /* \P904 */
        Local1 = CondRefOf (Arg1, Local0)
        If (M1A4 (Local1, 0x0272))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C00B, Buffer (0x03)
                {
                     0xB5, 0xB6, 0xB7                                 // ...
                }, 0x0273)
        }

        Arg1 = P905 /* \P905 */
        Local1 = CondRefOf (Arg1, Local0)
        If (M1A4 (Local1, 0x0274))
        {
            M1A2 (Local0, C00C, 0x02, 0x00, C009, 0x0ABC000A, __LINE__)
            M1A2 (Local0, C00C, 0x02, 0x01, C00A, "0xabc000b", __LINE__)
        }

        Arg1 = P906 /* \P906 */
        Local1 = CondRefOf (Arg1, Local0)
        If (M1A4 (Local1, 0x0277))
        {
            M1A2 (Local0, C00C, 0x02, 0x00, C00A, "abc000d", __LINE__)
        }

        Arg1 = P907 /* \P907 */
        Local1 = CondRefOf (Arg1, Local0)
        If (M1A4 (Local1, 0x0279))
        {
            M1A2 (Local0, C00C, 0x02, 0x00, C00A, "aqwevbgnm000e", __LINE__)
        }

        Arg1 = P908 /* \P908 */
        Local1 = CondRefOf (Arg1, Local0)
        If (M1A4 (Local1, 0x027B))
        {
            M1A2 (Local0, C00C, 0x02, 0x00, C00B, Buffer (0x05)
                {
                     0xBA, 0xBB, 0xBC, 0xBD, 0xBE                     // .....
                }, 0x027C)
        }

        Arg1 = P909 /* \P909 */
        Local1 = CondRefOf (Arg1, Local0)
        If (M1A4 (Local1, 0x027D))
        {
            M1A2 (Local0, C00C, 0x03, 0x00, C009, 0x0ABC000F, __LINE__)
        }

        Arg1 = P90A /* \P90A */
        Local1 = CondRefOf (Arg1, Local0)
        If (M1A4 (Local1, 0x027F))
        {
            M1A2 (Local0, C00C, 0x03, 0x00, C00A, "12340010", __LINE__)
        }

        Arg1 = P90B /* \P90B */
        Local1 = CondRefOf (Arg1, Local0)
        If (M1A4 (Local1, 0x0281))
        {
            M1A2 (Local0, C00C, 0x03, 0x00, C00A, "zxswefas0011", __LINE__)
        }

        Arg1 = P90C /* \P90C */
        Local1 = CondRefOf (Arg1, Local0)
        If (M1A4 (Local1, 0x0283))
        {
            M1A2 (Local0, C00C, 0x03, 0x00, C00B, Buffer (0x03)
                {
                     0xBF, 0xC0, 0xC1                                 // ...
                }, 0x0284)
        }

        Arg1 = P90D /* \P90D */
        Local1 = CondRefOf (Arg1, Local0)
        If (M1A4 (Local1, 0x0285))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xFE7CB391D65A0000, __LINE__)
        }

        Arg1 = P90E /* \P90E */
        Local1 = CondRefOf (Arg1, Local0)
        If (M1A4 (Local1, 0x0287))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xC1790001, __LINE__)
        }

        Arg1 = P90F /* \P90F */
        Local1 = CondRefOf (Arg1, Local0)
        If (M1A4 (Local1, 0x0289))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C00A, "12340002", __LINE__)
        }

        Arg1 = P910 /* \P910 */
        Local1 = CondRefOf (Arg1, Local0)
        If (M1A4 (Local1, 0x028B))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C00A, "qwrtyu0003", __LINE__)
        }

        Arg1 = P911 /* \P911 */
        Local1 = CondRefOf (Arg1, Local0)
        If (M1A4 (Local1, 0x028D))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C00B, Buffer (0x05)
                {
                     0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
                }, 0x028E)
        }

        If (Y118)
        {
            Arg1 = P912 /* \P912 */
            Local1 = CondRefOf (Arg1, Local0)
            If (M1A4 (Local1, 0x028F))
            {
                M1A2 (Local0, C00C, 0x01, 0x00, C00D, 0x00, __LINE__)
            }

            Arg1 = P913 /* \P913 */
            Local1 = CondRefOf (Arg1, Local0)
            If (M1A4 (Local1, 0x0291))
            {
                M1A2 (Local0, C00C, 0x01, 0x00, C00D, 0x00, __LINE__)
            }

            Arg1 = P914 /* \P914 */
            Local1 = CondRefOf (Arg1, Local0)
            If (M1A4 (Local1, 0x0293))
            {
                M1A2 (Local0, C00C, 0x01, 0x00, C00D, 0x00, __LINE__)
            }

            Arg1 = P915 /* \P915 */
            Local1 = CondRefOf (Arg1, Local0)
            If (M1A4 (Local1, 0x0295))
            {
                M1A2 (Local0, C00C, 0x01, 0x00, C016, 0xB0, __LINE__)
            }
        }

        /* Elements of Package are NOT Computational Data */

        Arg1 = P916 /* \P916 */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x0297)
        Arg1 = P917 /* \P917 */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x0298)
        Arg1 = P918 /* \P918 */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x19FF)
        Arg1 = P919 /* \P919 */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x029A)
        Arg1 = P91A /* \P91A */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x029B)
        Arg1 = P91B /* \P91B */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x029C)
        Arg1 = P91C /* \P91C */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x029D)
        /* Elements of Package are Methods */

        Arg1 = P91D /* \P91D */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x029E)
        Arg1 = P91E /* \P91E */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x029F)
        Arg1 = P91F /* \P91F */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02A0)
        Arg1 = P920 /* \P920 */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02A1)
        Arg1 = P921 /* \P921 */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02A2)
        Arg1 = P922 /* \P922 */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02A3)
        Arg1 = P923 /* \P923 */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02A4)
        Arg1 = P924 /* \P924 */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02A5)
        Arg1 = P925 /* \P925 */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02A6)
        Arg1 = P926 /* \P926 */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02A7)
        Arg1 = P927 /* \P927 */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02A8)
        Arg1 = P928 /* \P928 */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02A9)
        Arg1 = P929 /* \P929 */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02AA)
        Arg1 = P92A /* \P92A */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02AB)
        Arg1 = P92B /* \P92B */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02AC)
        Arg1 = P92C /* \P92C */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02AD)
        Arg1 = P92D /* \P92D */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02AE)
        Arg1 = P92E /* \P92E */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02AF)
        Arg1 = P92F /* \P92F */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02B0)
        Arg1 = P930 /* \P930 */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02B1)
        Arg1 = P931 /* \P931 */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02B2)
        Arg1 = P932 /* \P932 */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02B3)
        Arg1 = P933 /* \P933 */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02B4)
        Arg1 = P934 /* \P934 */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02B5)
        Arg1 = P935 /* \P935 */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02B6)
        Arg1 = P936 /* \P936 */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02B7)
        Arg1 = P937 /* \P937 */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02B8)
        Arg1 = P938 /* \P938 */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02B9)
        Arg1 = P939 /* \P939 */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02BA)
        Arg1 = P93A /* \P93A */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02BB)
        Arg1 = P93B /* \P93B */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02BC)
        Arg1 = P93C /* \P93C */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02BD)
        Arg1 = P93D /* \P93D */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02BE)
        Arg1 = P93E /* \P93E */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02BF)
        Arg1 = P93F /* \P93F */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02C0)
        Arg1 = P940 /* \P940 */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02C1)
        Arg1 = P941 /* \P941 */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02C2)
        Arg1 = P942 /* \P942 */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02C3)
        Arg1 = P943 /* \P943 */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02C4)
        Arg1 = P944 /* \P944 */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02C5)
        Arg1 = P945 /* \P945 */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02C6)
        Arg1 = P946 /* \P946 */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02C7)
        Arg1 = P947 /* \P947 */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02C8)
        Arg1 = P948 /* \P948 */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02C9)
        Arg1 = P949 /* \P949 */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02CA)
        Arg1 = P94A /* \P94A */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02CB)
        Arg1 = P94B /* \P94B */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02CC)
        Arg1 = P94C /* \P94C */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02CD)
        Arg1 = P94D /* \P94D */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02CE)
        Arg1 = P94E /* \P94E */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02CF)
        Arg1 = P94F /* \P94F */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02D0)
        Arg1 = P950 /* \P950 */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02D1)
        Arg1 = P951 /* \P951 */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02D2)
        Arg1 = P952 /* \P952 */
        Local1 = CondRefOf (Arg1, Local0)
        M1A0 (Local0, C00C, Local1, 0x02D3)
        M1A6 ()
        Return (Zero)
    }

    Method (M185, 3, NotSerialized)
    {
        C081 = Z079       /* absolute index of file initiating the checking */ /* \Z079 */
        C089 = 0x01      /* flag of Reference, object otherwise */
        If (Arg0)
        {
            M180 (0x00, 0x00)
        }

        If (Arg1)
        {
            M181 (0x00, 0x00, C083)
        }

        If (Arg2)
        {
            M182 (0x00, 0x00, C083)
        }
    }

    /* The mode with the chain of references to LocalX */

    Method (M186, 0, NotSerialized)
    {
        C084 = 0x01  /* run verification of references (reading) */
        C085 = 0x01  /* create the chain of references to LocalX, then dereference them */
        Debug = "The mode with the chain of references to LocalX:"
        M185 (0x01, 0x01, 0x01)
    }

    /* Run-method */

    Method (REF3, 0, NotSerialized)
    {
        Debug = "TEST: REF3, References"
        C080 = "REF3" /* name of test */
        C082 = 0x00      /* flag of test of exceptions */
        C083 = 0x00      /* run verification of references (write/read) */
        C086 = 0x00      /* flag, run test till the first error */
        C087 = 0x01      /* apply DeRefOf to ArgX-ObjectReference */
        M186 ()
    }
