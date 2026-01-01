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
     * TABLE 5: all the legal ways to generate references to LocalX
     *
     * Producing Reference operators:
     *
     *    Index, RefOf, CondRefOf
     */
    Name (Z078, 0x4E)
    /* /////////////////////////////////////////////////////////////////////////// */
    /* */
    /* TABLE 5: all the legal ways to generate references to LocalX */
    /* */
    /* /////////////////////////////////////////////////////////////////////////// */
    /* m169,m190 */
    Method (M170, 0, NotSerialized)
    {
        If (Y100)
        {
            TS00 ("m170")
        }
        Else
        {
            Debug = "m170"
        }

        /* T5:I2-I4 */
        /* Computational Data */
        Local7 = S900 /* \S900 */
        Store (Local7 [0x00], Local0)
        M1A2 (Local0, C016, 0x00, 0x00, C009, 0x31, __LINE__)
        Local7 = S901 /* \S901 */
        Store (Local7 [0x02], Local0)
        M1A2 (Local0, C016, 0x00, 0x00, C009, 0x72, __LINE__)
        Local7 = B900 /* \B900 */
        Store (Local7 [0x03], Local0)
        M1A2 (Local0, C016, 0x00, 0x00, C009, 0xB3, __LINE__)
        /* Elements of Package are Uninitialized */

        If (Y104)
        {
            Local7 = P900 /* \P900 */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C008, Ones, 0x04)
        }

        /* Elements of Package are Computational Data */

        Local7 = P901 /* \P901 */
        Store (Local7 [0x00], Local0)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xABCD0004, __LINE__)
        Local7 = P901 /* \P901 */
        Store (Local7 [0x01], Local0)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0x1122334455660005, __LINE__)
        Local7 = P902 /* \P902 */
        Store (Local7 [0x00], Local0)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "12340006", __LINE__)
        Local7 = P902 /* \P902 */
        Store (Local7 [0x01], Local0)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "q1w2e3r4t5y6u7i80007", __LINE__)
        Local7 = P903 /* \P903 */
        Store (Local7 [0x00], Local0)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "qwrtyuiop0008", __LINE__)
        Local7 = P903 /* \P903 */
        Store (Local7 [0x01], Local0)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "1234567890abdef0250009", __LINE__)
        Local7 = P904 /* \P904 */
        Store (Local7 [0x00], Local0)
        M1A2 (Local0, C00B, 0x00, 0x00, C00B, Buffer (0x03)
            {
                 0xB5, 0xB6, 0xB7                                 // ...
            }, 0x0B)
        Local7 = P905 /* \P905 */
        Store (Local7 [0x00], Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0x0ABC000A, __LINE__)
        Local7 = P905 /* \P905 */
        Store (Local7 [0x00], Local0)
        M1A2 (Local0, C00C, 0x01, 0x01, C00A, "0xabc000b", __LINE__)
        Local7 = P906 /* \P906 */
        Store (Local7 [0x00], Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "abc000d", __LINE__)
        Local7 = P907 /* \P907 */
        Store (Local7 [0x00], Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "aqwevbgnm000e", __LINE__)
        Local7 = P908 /* \P908 */
        Store (Local7 [0x00], Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C00B, Buffer (0x05)
            {
                 0xBA, 0xBB, 0xBC, 0xBD, 0xBE                     // .....
            }, 0x10)
        Local7 = P909 /* \P909 */
        Store (Local7 [0x00], Local0)
        M1A2 (Local0, C00C, 0x02, 0x00, C009, 0x0ABC000F, __LINE__)
        Local7 = P90A /* \P90A */
        Store (Local7 [0x00], Local0)
        M1A2 (Local0, C00C, 0x02, 0x00, C00A, "12340010", __LINE__)
        Local7 = P90B /* \P90B */
        Store (Local7 [0x00], Local0)
        M1A2 (Local0, C00C, 0x02, 0x00, C00A, "zxswefas0011", __LINE__)
        Local7 = P90C /* \P90C */
        Store (Local7 [0x00], Local0)
        M1A2 (Local0, C00C, 0x02, 0x00, C00B, Buffer (0x03)
            {
                 0xBF, 0xC0, 0xC1                                 // ...
            }, 0x14)
        Local7 = P90D /* \P90D */
        Store (Local7 [0x00], Local0)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xFE7CB391D65A0000, __LINE__)
        Local7 = P90E /* \P90E */
        Store (Local7 [0x00], Local0)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xC1790001, __LINE__)
        Local7 = P90F /* \P90F */
        Store (Local7 [0x00], Local0)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "12340002", __LINE__)
        Local7 = P910 /* \P910 */
        Store (Local7 [0x00], Local0)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "qwrtyu0003", __LINE__)
        Local7 = P911 /* \P911 */
        Store (Local7 [0x00], Local0)
        M1A2 (Local0, C00B, 0x00, 0x00, C00B, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            }, 0x19)
        If (Y118)
        {
            Local7 = P912 /* \P912 */
            Store (Local7 [0x00], Local0)
            M1A2 (Local0, C00D, 0x00, 0x00, C00D, 0x00, __LINE__)
            Local7 = P913 /* \P913 */
            Store (Local7 [0x00], Local0)
            M1A2 (Local0, C00D, 0x00, 0x00, C00D, 0x00, __LINE__)
            Local7 = P914 /* \P914 */
            Store (Local7 [0x00], Local0)
            M1A2 (Local0, C00D, 0x00, 0x00, C00D, 0x00, __LINE__)
            Local7 = P915 /* \P915 */
            Store (Local7 [0x00], Local0)
            M1A2 (Local0, C016, 0x00, 0x00, C016, 0xB0, __LINE__)
        }

        /* Elements of Package are NOT Computational Data */

        Local7 = P916 /* \P916 */
        Store (Local7 [0x00], Local0)
        M1A0 (Local0, C00E, Ones, 0x1E)
        Local7 = P917 /* \P917 */
        Store (Local7 [0x00], Local0)
        M1A0 (Local0, C00F, Ones, 0x1F)
        Local7 = P918 /* \P918 */
        Store (Local7 [0x00], Local0)
        M1A0 (Local0, C011, Ones, 0x20)
        Local7 = P919 /* \P919 */
        Store (Local7 [0x00], Local0)
        M1A0 (Local0, C012, Ones, 0x21)
        Local7 = P91A /* \P91A */
        Store (Local7 [0x00], Local0)
        M1A0 (Local0, C013, Ones, 0x22)
        Local7 = P91B /* \P91B */
        Store (Local7 [0x00], Local0)
        M1A0 (Local0, C014, Ones, 0x23)
        Local7 = P91C /* \P91C */
        Store (Local7 [0x00], Local0)
        M1A0 (Local0, C015, Ones, 0x24)
        /* Elements of Package are Methods */

        If (Y105)
        {
            Local7 = P91D /* \P91D */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x25)
            Local7 = P91E /* \P91E */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x26)
            Local7 = P91F /* \P91F */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x27)
            Local7 = P920 /* \P920 */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x28)
            Local7 = P921 /* \P921 */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x29)
            Local7 = P922 /* \P922 */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x2A)
            Local7 = P923 /* \P923 */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x2B)
            Local7 = P924 /* \P924 */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x2C)
            Local7 = P925 /* \P925 */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x2D)
            Local7 = P926 /* \P926 */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x2E)
            Local7 = P927 /* \P927 */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x2F)
            Local7 = P928 /* \P928 */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x30)
            Local7 = P929 /* \P929 */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x31)
            Local7 = P92A /* \P92A */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x32)
            Local7 = P92B /* \P92B */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x33)
            Local7 = P92C /* \P92C */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x34)
            Local7 = P92D /* \P92D */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x35)
            Local7 = P92E /* \P92E */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x36)
            Local7 = P92F /* \P92F */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x37)
            Local7 = P930 /* \P930 */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x38)
            Local7 = P931 /* \P931 */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x39)
            Local7 = P932 /* \P932 */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x3A)
            Local7 = P933 /* \P933 */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x3B)
            Local7 = P934 /* \P934 */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x3C)
            If (Y103)
            {
                Local7 = P935 /* \P935 */
                Store (Local7 [0x00], Local0)
                M1A0 (Local0, C010, Ones, 0x3D)
            }

            Local7 = P936 /* \P936 */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x3E)
            Local7 = P937 /* \P937 */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x3F)
            Local7 = P938 /* \P938 */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x40)
            Local7 = P939 /* \P939 */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x41)
            Local7 = P93A /* \P93A */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x42)
            Local7 = P93B /* \P93B */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x43)
            Local7 = P93C /* \P93C */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x44)
            Local7 = P93D /* \P93D */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x45)
            Local7 = P93E /* \P93E */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x46)
            Local7 = P93F /* \P93F */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x47)
            Local7 = P940 /* \P940 */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x48)
            Local7 = P941 /* \P941 */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x49)
            Local7 = P942 /* \P942 */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x4A)
            Local7 = P943 /* \P943 */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x4B)
            Local7 = P944 /* \P944 */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x4C)
            Local7 = P945 /* \P945 */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x4D)
            Local7 = P946 /* \P946 */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x4E)
            Local7 = P947 /* \P947 */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x4F)
            Local7 = P948 /* \P948 */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x50)
            Local7 = P949 /* \P949 */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x51)
            Local7 = P94A /* \P94A */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x52)
            Local7 = P94B /* \P94B */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x53)
            Local7 = P94C /* \P94C */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x54)
            Local7 = P94D /* \P94D */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x55)
            Local7 = P94E /* \P94E */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x56)
            Local7 = P94F /* \P94F */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x57)
            Local7 = P950 /* \P950 */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x58)
            Local7 = P951 /* \P951 */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x59)
            Local7 = P952 /* \P952 */
            Store (Local7 [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x5A)
        }

        /* T5:IR2-IR4 */
        /* Computational Data */
        Local7 = S900 /* \S900 */
        Local0 = Local1 = Local7 [0x00]
        M1A2 (Local0, C016, 0x00, 0x00, C009, 0x31, __LINE__)
        M1A2 (Local1, C016, 0x00, 0x00, C009, 0x31, __LINE__)
        Local7 = S901 /* \S901 */
        Local0 = Local1 = Local7 [0x02]
        M1A2 (Local0, C016, 0x00, 0x00, C009, 0x72, __LINE__)
        M1A2 (Local1, C016, 0x00, 0x00, C009, 0x72, __LINE__)
        Local7 = B900 /* \B900 */
        Local0 = Local1 = Local7 [0x04]
        M1A2 (Local0, C016, 0x00, 0x00, C009, 0xB4, __LINE__)
        M1A2 (Local1, C016, 0x00, 0x00, C009, 0xB4, __LINE__)
        /* Elements of Package are Uninitialized */

        If (Y104)
        {
            Local7 = P900 /* \P900 */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C008, Ones, 0x61)
            M1A0 (Local1, C008, Ones, 0x62)
        }

        /* Elements of Package are Computational Data */

        Local7 = P901 /* \P901 */
        Local0 = Local1 = Local7 [0x00]
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xABCD0004, __LINE__)
        M1A2 (Local1, C009, 0x00, 0x00, C009, 0xABCD0004, __LINE__)
        Local7 = P901 /* \P901 */
        Local0 = Local1 = Local7 [0x01]
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0x1122334455660005, __LINE__)
        M1A2 (Local1, C009, 0x00, 0x00, C009, 0x1122334455660005, __LINE__)
        Local7 = P902 /* \P902 */
        Local0 = Local1 = Local7 [0x00]
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "12340006", __LINE__)
        M1A2 (Local1, C00A, 0x00, 0x00, C00A, "12340006", __LINE__)
        Local7 = P902 /* \P902 */
        Local0 = Local1 = Local7 [0x01]
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "q1w2e3r4t5y6u7i80007", __LINE__)
        M1A2 (Local1, C00A, 0x00, 0x00, C00A, "q1w2e3r4t5y6u7i80007", __LINE__)
        Local7 = P903 /* \P903 */
        Local0 = Local1 = Local7 [0x00]
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "qwrtyuiop0008", __LINE__)
        M1A2 (Local1, C00A, 0x00, 0x00, C00A, "qwrtyuiop0008", __LINE__)
        Local7 = P903 /* \P903 */
        Local0 = Local1 = Local7 [0x01]
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "1234567890abdef0250009", __LINE__)
        M1A2 (Local1, C00A, 0x00, 0x00, C00A, "1234567890abdef0250009", __LINE__)
        Local7 = P904 /* \P904 */
        Local0 = Local1 = Local7 [0x00]
        M1A2 (Local0, C00B, 0x00, 0x00, C00B, Buffer (0x03)
            {
                 0xB5, 0xB6, 0xB7                                 // ...
            }, 0x6F)
        M1A2 (Local1, C00B, 0x00, 0x00, C00B, Buffer (0x03)
            {
                 0xB5, 0xB6, 0xB7                                 // ...
            }, 0x70)
        Local7 = P905 /* \P905 */
        Local0 = Local1 = Local7 [0x00]
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0x0ABC000A, __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x00, C009, 0x0ABC000A, __LINE__)
        Local7 = P905 /* \P905 */
        Local0 = Local1 = Local7 [0x00]
        M1A2 (Local0, C00C, 0x01, 0x01, C00A, "0xabc000b", __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x01, C00A, "0xabc000b", __LINE__)
        Local7 = P906 /* \P906 */
        Local0 = Local1 = Local7 [0x00]
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "abc000d", __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x00, C00A, "abc000d", __LINE__)
        Local7 = P907 /* \P907 */
        Local0 = Local1 = Local7 [0x00]
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "aqwevbgnm000e", __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x00, C00A, "aqwevbgnm000e", __LINE__)
        Local7 = P908 /* \P908 */
        Local0 = Local1 = Local7 [0x00]
        M1A2 (Local0, C00C, 0x01, 0x00, C00B, Buffer (0x05)
            {
                 0xBA, 0xBB, 0xBC, 0xBD, 0xBE                     // .....
            }, 0x79)
        M1A2 (Local1, C00C, 0x01, 0x00, C00B, Buffer (0x05)
            {
                 0xBA, 0xBB, 0xBC, 0xBD, 0xBE                     // .....
            }, 0x7A)
        Local7 = P909 /* \P909 */
        Local0 = Local1 = Local7 [0x00]
        M1A2 (Local0, C00C, 0x02, 0x00, C009, 0x0ABC000F, __LINE__)
        M1A2 (Local1, C00C, 0x02, 0x00, C009, 0x0ABC000F, __LINE__)
        Local7 = P90A /* \P90A */
        Local0 = Local1 = Local7 [0x00]
        M1A2 (Local0, C00C, 0x02, 0x00, C00A, "12340010", __LINE__)
        M1A2 (Local1, C00C, 0x02, 0x00, C00A, "12340010", __LINE__)
        Local7 = P90B /* \P90B */
        Local0 = Local1 = Local7 [0x00]
        M1A2 (Local0, C00C, 0x02, 0x00, C00A, "zxswefas0011", __LINE__)
        M1A2 (Local1, C00C, 0x02, 0x00, C00A, "zxswefas0011", __LINE__)
        Local7 = P90C /* \P90C */
        Local0 = Local1 = Local7 [0x00]
        M1A2 (Local0, C00C, 0x02, 0x00, C00B, Buffer (0x03)
            {
                 0xBF, 0xC0, 0xC1                                 // ...
            }, 0x81)
        M1A2 (Local1, C00C, 0x02, 0x00, C00B, Buffer (0x03)
            {
                 0xBF, 0xC0, 0xC1                                 // ...
            }, 0x82)
        Local7 = P90D /* \P90D */
        Local0 = Local1 = Local7 [0x00]
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xFE7CB391D65A0000, __LINE__)
        M1A2 (Local1, C009, 0x00, 0x00, C009, 0xFE7CB391D65A0000, __LINE__)
        Local7 = P90E /* \P90E */
        Local0 = Local1 = Local7 [0x00]
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xC1790001, __LINE__)
        M1A2 (Local1, C009, 0x00, 0x00, C009, 0xC1790001, __LINE__)
        Local7 = P90F /* \P90F */
        Local0 = Local1 = Local7 [0x00]
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "12340002", __LINE__)
        M1A2 (Local1, C00A, 0x00, 0x00, C00A, "12340002", __LINE__)
        Local7 = P910 /* \P910 */
        Local0 = Local1 = Local7 [0x00]
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "qwrtyu0003", __LINE__)
        M1A2 (Local1, C00A, 0x00, 0x00, C00A, "qwrtyu0003", __LINE__)
        Local7 = P911 /* \P911 */
        Local0 = Local1 = Local7 [0x00]
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
            Local7 = P912 /* \P912 */
            Local0 = Local1 = Local7 [0x00]
            M1A2 (Local0, C00D, 0x00, 0x00, C00D, 0x00, __LINE__)
            M1A2 (Local1, C00D, 0x00, 0x00, C00D, 0x00, __LINE__)
            Local7 = P913 /* \P913 */
            Local0 = Local1 = Local7 [0x00]
            M1A2 (Local0, C00D, 0x00, 0x00, C00D, 0x00, __LINE__)
            M1A2 (Local1, C00D, 0x00, 0x00, C00D, 0x00, __LINE__)
            Local7 = P914 /* \P914 */
            Local0 = Local1 = Local7 [0x00]
            M1A2 (Local0, C00D, 0x00, 0x00, C00D, 0x00, __LINE__)
            M1A2 (Local1, C00D, 0x00, 0x00, C00D, 0x00, __LINE__)
            Local7 = P915 /* \P915 */
            Local0 = Local1 = Local7 [0x00]
            M1A2 (Local0, C016, 0x00, 0x00, C016, 0xB0, __LINE__)
            M1A2 (Local1, C016, 0x00, 0x00, C016, 0xB0, __LINE__)
        }

        /* Elements of Package are NOT Computational Data */

        Local7 = P916 /* \P916 */
        Local0 = Local1 = Local7 [0x00]
        M1A0 (Local0, C00E, Ones, 0x95)
        M1A0 (Local1, C00E, Ones, 0x96)
        Local7 = P917 /* \P917 */
        Local0 = Local1 = Local7 [0x00]
        M1A0 (Local0, C00F, Ones, 0x97)
        M1A0 (Local1, C00F, Ones, 0x98)
        Local7 = P918 /* \P918 */
        Local0 = Local1 = Local7 [0x00]
        M1A0 (Local0, C011, Ones, 0x99)
        M1A0 (Local1, C011, Ones, 0x9A)
        Local7 = P919 /* \P919 */
        Local0 = Local1 = Local7 [0x00]
        M1A0 (Local0, C012, Ones, 0x9B)
        M1A0 (Local1, C012, Ones, 0x9C)
        Local7 = P91A /* \P91A */
        Local0 = Local1 = Local7 [0x00]
        M1A0 (Local0, C013, Ones, 0x9D)
        M1A0 (Local1, C013, Ones, 0x9E)
        Local7 = P91B /* \P91B */
        Local0 = Local1 = Local7 [0x00]
        M1A0 (Local0, C014, Ones, 0x9F)
        M1A0 (Local1, C014, Ones, 0xA0)
        Local7 = P91C /* \P91C */
        Local0 = Local1 = Local7 [0x00]
        M1A0 (Local0, C015, Ones, 0xA1)
        M1A0 (Local1, C015, Ones, 0xA2)
        /* Elements of Package are Methods */

        If (Y105)
        {
            Local7 = P91D /* \P91D */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xA3)
            M1A0 (Local1, C010, Ones, 0xA4)
            Local7 = P91E /* \P91E */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xA5)
            M1A0 (Local1, C010, Ones, 0xA6)
            Local7 = P91F /* \P91F */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xA7)
            M1A0 (Local1, C010, Ones, 0xA8)
            Local7 = P920 /* \P920 */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xA9)
            M1A0 (Local1, C010, Ones, 0xAA)
            Local7 = P921 /* \P921 */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xAB)
            M1A0 (Local1, C010, Ones, 0xAC)
            Local7 = P922 /* \P922 */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xAD)
            M1A0 (Local1, C010, Ones, 0xAE)
            Local7 = P923 /* \P923 */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xAF)
            M1A0 (Local1, C010, Ones, 0xB0)
            Local7 = P924 /* \P924 */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xB1)
            M1A0 (Local1, C010, Ones, 0xB2)
            Local7 = P925 /* \P925 */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xB3)
            M1A0 (Local1, C010, Ones, 0xB4)
            Local7 = P926 /* \P926 */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xB5)
            M1A0 (Local1, C010, Ones, 0xB6)
            Local7 = P927 /* \P927 */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xB7)
            M1A0 (Local1, C010, Ones, 0xB8)
            Local7 = P928 /* \P928 */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xB9)
            M1A0 (Local1, C010, Ones, 0xBA)
            Local7 = P929 /* \P929 */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xBB)
            M1A0 (Local1, C010, Ones, 0xBC)
            Local7 = P92A /* \P92A */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xBD)
            M1A0 (Local1, C010, Ones, 0xBE)
            Local7 = P92B /* \P92B */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xBF)
            M1A0 (Local1, C010, Ones, 0xC0)
            Local7 = P92C /* \P92C */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xC1)
            M1A0 (Local1, C010, Ones, 0xC2)
            Local7 = P92D /* \P92D */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xC3)
            M1A0 (Local1, C010, Ones, 0xC4)
            Local7 = P92E /* \P92E */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xC5)
            M1A0 (Local1, C010, Ones, 0xC6)
            Local7 = P92F /* \P92F */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xC7)
            M1A0 (Local1, C010, Ones, 0xC8)
            Local7 = P930 /* \P930 */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xC9)
            M1A0 (Local1, C010, Ones, 0xCA)
            Local7 = P931 /* \P931 */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xCB)
            M1A0 (Local1, C010, Ones, 0xCC)
            Local7 = P932 /* \P932 */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xCD)
            M1A0 (Local1, C010, Ones, 0xCE)
            Local7 = P933 /* \P933 */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xCF)
            M1A0 (Local1, C010, Ones, 0xD0)
            Local7 = P934 /* \P934 */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xD1)
            M1A0 (Local1, C010, Ones, 0xD2)
            If (Y103)
            {
                Local7 = P935 /* \P935 */
                Local0 = Local1 = Local7 [0x00]
                M1A0 (Local0, C010, Ones, 0xD3)
                M1A0 (Local1, C010, Ones, 0xD4)
            }

            Local7 = P936 /* \P936 */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xD5)
            M1A0 (Local1, C010, Ones, 0xD6)
            Local7 = P937 /* \P937 */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xD7)
            M1A0 (Local1, C010, Ones, 0xD8)
            Local7 = P938 /* \P938 */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xD9)
            M1A0 (Local1, C010, Ones, 0xDA)
            Local7 = P939 /* \P939 */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xDB)
            M1A0 (Local1, C010, Ones, 0xDC)
            Local7 = P93A /* \P93A */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xDD)
            M1A0 (Local1, C010, Ones, 0xDE)
            Local7 = P93B /* \P93B */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xDF)
            M1A0 (Local1, C010, Ones, 0xE0)
            Local7 = P93C /* \P93C */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xE1)
            M1A0 (Local1, C010, Ones, 0xE2)
            Local7 = P93D /* \P93D */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xE3)
            M1A0 (Local1, C010, Ones, 0xE4)
            Local7 = P93E /* \P93E */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xE5)
            M1A0 (Local1, C010, Ones, 0xE6)
            Local7 = P93F /* \P93F */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xE7)
            M1A0 (Local1, C010, Ones, 0xE8)
            Local7 = P940 /* \P940 */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xE9)
            M1A0 (Local1, C010, Ones, 0xEA)
            Local7 = P941 /* \P941 */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xEB)
            M1A0 (Local1, C010, Ones, 0xEC)
            Local7 = P942 /* \P942 */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xED)
            M1A0 (Local1, C010, Ones, 0xEE)
            Local7 = P943 /* \P943 */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xEF)
            M1A0 (Local1, C010, Ones, 0xF0)
            Local7 = P944 /* \P944 */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xF1)
            M1A0 (Local1, C010, Ones, 0xF2)
            Local7 = P945 /* \P945 */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xF3)
            M1A0 (Local1, C010, Ones, 0xF4)
            Local7 = P946 /* \P946 */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xF5)
            M1A0 (Local1, C010, Ones, 0xF6)
            Local7 = P947 /* \P947 */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xF7)
            M1A0 (Local1, C010, Ones, 0xF8)
            Local7 = P948 /* \P948 */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xF9)
            M1A0 (Local1, C010, Ones, 0xFA)
            Local7 = P949 /* \P949 */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xFB)
            M1A0 (Local1, C010, Ones, 0xFC)
            Local7 = P94A /* \P94A */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xFD)
            M1A0 (Local1, C010, Ones, 0xFE)
            Local7 = P94B /* \P94B */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0xFF)
            M1A0 (Local1, C010, Ones, 0x0100)
            Local7 = P94C /* \P94C */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0x0101)
            M1A0 (Local1, C010, Ones, 0x0102)
            Local7 = P94D /* \P94D */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0x0103)
            M1A0 (Local1, C010, Ones, 0x0104)
            Local7 = P94E /* \P94E */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0x0105)
            M1A0 (Local1, C010, Ones, 0x0106)
            Local7 = P94F /* \P94F */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0x0107)
            M1A0 (Local1, C010, Ones, 0x0108)
            Local7 = P950 /* \P950 */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0x0109)
            M1A0 (Local1, C010, Ones, 0x010A)
            Local7 = P951 /* \P951 */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0x010B)
            M1A0 (Local1, C010, Ones, 0x010C)
            Local7 = P952 /* \P952 */
            Local0 = Local1 = Local7 [0x00]
            M1A0 (Local0, C010, Ones, 0x010D)
            M1A0 (Local1, C010, Ones, 0x010E)
        }

        M1A6 ()
    }

    /* m16a,m191 */
    /* arg1 - writing mode */
    Method (M171, 2, NotSerialized)
    {
        If (Y100)
        {
            TS00 ("m171")
        }
        Else
        {
            Debug = "m171"
        }

        /* T5:R0-R5,R14 */
        /* Uninitialized Local */
        If (Arg0)
        {
            Local7 = 0x00
        }

        Local0 = RefOf (Local7)
        M1A0 (Local0, C008, Ones, 0x03E8)
        /* Computational Data */

        Local7 = I900 /* \I900 */
        Local0 = RefOf (Local7)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xFE7CB391D65A0000, __LINE__)
        Local7 = I901 /* \I901 */
        Local0 = RefOf (Local7)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xC1790001, __LINE__)
        Local7 = S900 /* \S900 */
        Local0 = RefOf (Local7)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "12340002", __LINE__)
        Local7 = S901 /* \S901 */
        Local0 = RefOf (Local7)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "qwrtyu0003", __LINE__)
        Local7 = B900 /* \B900 */
        Local0 = RefOf (Local7)
        M1A2 (Local0, C00B, 0x00, 0x00, C00B, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            }, 0x0113)
        /* Not Computational Data */
        /* Package */
        Local7 = P953 /* \P953 */
        Local0 = RefOf (Local7)
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xABCD0018, __LINE__)
        If (Arg1)
        {
            /* Data are unchanged, because writings were made */
            /* into the new objects associated with Local7. */
            M1A6 ()
            Return (Zero)
        }

        /* Computational Data (Field Unit and Buffer Field) */

        Local7 = F900 /* \F900 */
        Local0 = RefOf (Local7)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0x00, __LINE__)
        Local7 = BN90 /* \BN90 */
        Local0 = RefOf (Local7)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0x00, __LINE__)
        Local7 = IF90 /* \IF90 */
        Local0 = RefOf (Local7)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0x00, __LINE__)
        Local7 = BF90 /* \BF90 */
        Local0 = RefOf (Local7)
        M1A2 (Local0, C00B, 0x00, 0x00, C00B, Buffer(){0xB0}, __LINE__)
        /* Elements of Package are Uninitialized */

        Local7 = P900 /* \P900 */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x011F)
        /* Elements of Package are Computational Data */

        Local7 = P901 /* \P901 */
        Local0 = RefOf (Local7)
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xABCD0004, __LINE__)
        M1A2 (Local0, C00C, 0x01, 0x01, C009, 0x1122334455660005, __LINE__)
        Local7 = P902 /* \P902 */
        Local0 = RefOf (Local7)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "12340006", __LINE__)
        M1A2 (Local0, C00C, 0x01, 0x01, C00A, "q1w2e3r4t5y6u7i80007", __LINE__)
        Local7 = P903 /* \P903 */
        Local0 = RefOf (Local7)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "qwrtyuiop0008", __LINE__)
        M1A2 (Local0, C00C, 0x01, 0x01, C00A, "1234567890abdef0250009", __LINE__)
        Local7 = P904 /* \P904 */
        Local0 = RefOf (Local7)
        M1A2 (Local0, C00C, 0x01, 0x00, C00B, Buffer (0x03)
            {
                 0xB5, 0xB6, 0xB7                                 // ...
            }, 0x0126)
        Local7 = P905 /* \P905 */
        Local0 = RefOf (Local7)
        M1A2 (Local0, C00C, 0x02, 0x00, C009, 0x0ABC000A, __LINE__)
        M1A2 (Local0, C00C, 0x02, 0x01, C00A, "0xabc000b", __LINE__)
        Local7 = P906 /* \P906 */
        Local0 = RefOf (Local7)
        M1A2 (Local0, C00C, 0x02, 0x00, C00A, "abc000d", __LINE__)
        Local7 = P907 /* \P907 */
        Local0 = RefOf (Local7)
        M1A2 (Local0, C00C, 0x02, 0x00, C00A, "aqwevbgnm000e", __LINE__)
        Local7 = P908 /* \P908 */
        Local0 = RefOf (Local7)
        M1A2 (Local0, C00C, 0x02, 0x00, C00B, Buffer (0x05)
            {
                 0xBA, 0xBB, 0xBC, 0xBD, 0xBE                     // .....
            }, 0x012B)
        Local7 = P909 /* \P909 */
        Local0 = RefOf (Local7)
        M1A2 (Local0, C00C, 0x03, 0x00, C009, 0x0ABC000F, __LINE__)
        Local7 = P90A /* \P90A */
        Local0 = RefOf (Local7)
        M1A2 (Local0, C00C, 0x03, 0x00, C00A, "12340010", __LINE__)
        Local7 = P90B /* \P90B */
        Local0 = RefOf (Local7)
        M1A2 (Local0, C00C, 0x03, 0x00, C00A, "zxswefas0011", __LINE__)
        Local7 = P90C /* \P90C */
        Local0 = RefOf (Local7)
        M1A2 (Local0, C00C, 0x03, 0x00, C00B, Buffer (0x03)
            {
                 0xBF, 0xC0, 0xC1                                 // ...
            }, 0x012F)
        Local7 = P90D /* \P90D */
        Local0 = RefOf (Local7)
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xFE7CB391D65A0000, __LINE__)
        Local7 = P90E /* \P90E */
        Local0 = RefOf (Local7)
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xC1790001, __LINE__)
        Local7 = P90F /* \P90F */
        Local0 = RefOf (Local7)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "12340002", __LINE__)
        Local7 = P910 /* \P910 */
        Local0 = RefOf (Local7)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "qwrtyu0003", __LINE__)
        Local7 = P911 /* \P911 */
        Local0 = RefOf (Local7)
        M1A2 (Local0, C00C, 0x01, 0x00, C00B, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            }, 0x0134)
        If (Y118)
        {
            Local7 = P912 /* \P912 */
            Local0 = RefOf (Local7)
            M1A2 (Local0, C00C, 0x01, 0x00, C00D, 0x00, __LINE__)
            Local7 = P913 /* \P913 */
            Local0 = RefOf (Local7)
            M1A2 (Local0, C00C, 0x01, 0x00, C00D, 0x00, __LINE__)
            Local7 = P914 /* \P914 */
            Local0 = RefOf (Local7)
            M1A2 (Local0, C00C, 0x01, 0x00, C00D, 0x00, __LINE__)
            Local7 = P915 /* \P915 */
            Local0 = RefOf (Local7)
            M1A2 (Local0, C00C, 0x01, 0x00, C016, 0xB0, __LINE__)
        }

        /* Elements of Package are NOT Computational Data */

        Local7 = P916 /* \P916 */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x0139)
        Local7 = P917 /* \P917 */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x013A)
        Local7 = P918 /* \P918 */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x013B)
        Local7 = P919 /* \P919 */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x013C)
        Local7 = P91A /* \P91A */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x013D)
        Local7 = P91B /* \P91B */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x013E)
        Local7 = P91C /* \P91C */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x013F)
        /* Elements of Package are Methods */

        Local7 = P91D /* \P91D */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x0140)
        Local7 = P91E /* \P91E */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x0141)
        Local7 = P91F /* \P91F */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x0142)
        Local7 = P920 /* \P920 */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x0143)
        Local7 = P921 /* \P921 */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x0144)
        Local7 = P922 /* \P922 */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x0145)
        Local7 = P923 /* \P923 */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x0146)
        Local7 = P924 /* \P924 */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x0147)
        Local7 = P925 /* \P925 */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x0148)
        Local7 = P926 /* \P926 */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x0149)
        Local7 = P927 /* \P927 */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x014A)
        Local7 = P928 /* \P928 */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x014B)
        Local7 = P929 /* \P929 */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x014C)
        Local7 = P92A /* \P92A */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x014D)
        Local7 = P92B /* \P92B */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x014E)
        Local7 = P92C /* \P92C */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x014F)
        Local7 = P92D /* \P92D */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x0150)
        Local7 = P92E /* \P92E */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x0151)
        Local7 = P92F /* \P92F */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x0152)
        Local7 = P930 /* \P930 */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x0153)
        Local7 = P931 /* \P931 */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x0154)
        Local7 = P932 /* \P932 */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x0155)
        Local7 = P933 /* \P933 */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x0156)
        Local7 = P934 /* \P934 */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x0157)
        Local7 = P935 /* \P935 */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x0158)
        Local7 = P936 /* \P936 */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x0159)
        Local7 = P937 /* \P937 */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x015A)
        Local7 = P938 /* \P938 */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x015B)
        Local7 = P939 /* \P939 */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x015C)
        Local7 = P93A /* \P93A */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x015D)
        Local7 = P93B /* \P93B */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x015E)
        Local7 = P93C /* \P93C */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x015F)
        Local7 = P93D /* \P93D */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x0160)
        Local7 = P93E /* \P93E */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x0161)
        Local7 = P93F /* \P93F */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x0162)
        Local7 = P940 /* \P940 */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x0163)
        Local7 = P941 /* \P941 */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x0164)
        Local7 = P942 /* \P942 */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x0165)
        Local7 = P943 /* \P943 */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x0166)
        Local7 = P944 /* \P944 */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x0167)
        Local7 = P945 /* \P945 */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x0168)
        Local7 = P946 /* \P946 */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x0169)
        Local7 = P947 /* \P947 */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x016A)
        Local7 = P948 /* \P948 */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x016B)
        Local7 = P949 /* \P949 */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x016C)
        Local7 = P94A /* \P94A */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x016D)
        Local7 = P94B /* \P94B */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x016E)
        Local7 = P94C /* \P94C */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x016F)
        Local7 = P94D /* \P94D */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x0170)
        Local7 = P94E /* \P94E */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x0171)
        Local7 = P94F /* \P94F */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x0172)
        Local7 = P950 /* \P950 */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x0173)
        Local7 = P951 /* \P951 */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x0174)
        Local7 = P952 /* \P952 */
        Local0 = RefOf (Local7)
        M1A0 (Local0, C00C, Ones, 0x0175)
        M1A6 ()
        Return (Zero)
    }

    /* m16c,m193 */
    /* arg1 - writing mode */
    Method (M172, 2, NotSerialized)
    {
        If (Y100)
        {
            TS00 ("m172")
        }
        Else
        {
            Debug = "m172"
        }

        /* T5:CR0-CR5,CR14 */
        /* Uninitialized Local */
        If (Arg0)
        {
            Local7 = 0x00
        }

        Local1 = CondRefOf (Local7, Local0)
        If (M1A4 (Local1, 0x024D))
        {
            M1A0 (Local0, C008, Ones, 0x024E)
        }

        /* Computational Data */

        Local7 = I900 /* \I900 */
        Local1 = CondRefOf (Local7, Local0)
        If (M1A4 (Local1, 0x024F))
        {
            M1A2 (Local0, C009, 0x00, 0x00, C009, 0xFE7CB391D65A0000, __LINE__)
        }

        Local7 = I901 /* \I901 */
        Local1 = CondRefOf (Local7, Local0)
        If (M1A4 (Local1, 0x0251))
        {
            M1A2 (Local0, C009, 0x00, 0x00, C009, 0xC1790001, __LINE__)
        }

        Local7 = S900 /* \S900 */
        Local1 = CondRefOf (Local7, Local0)
        If (M1A4 (Local1, 0x0253))
        {
            M1A2 (Local0, C00A, 0x00, 0x00, C00A, "12340002", __LINE__)
        }

        Local7 = S901 /* \S901 */
        Local1 = CondRefOf (Local7, Local0)
        If (M1A4 (Local1, 0x0255))
        {
            M1A2 (Local0, C00A, 0x00, 0x00, C00A, "qwrtyu0003", __LINE__)
        }

        Local7 = B900 /* \B900 */
        Local1 = CondRefOf (Local7, Local0)
        If (M1A4 (Local1, 0x0257))
        {
            M1A2 (Local0, C00B, 0x00, 0x00, C00B, Buffer (0x05)
                {
                     0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
                }, 0x0258)
        }

        /* Not Computational Data */
        /* Package */
        Local7 = P953 /* \P953 */
        Local1 = CondRefOf (Local7, Local0)
        If (M1A4 (Local1, 0x03F2))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xABCD0018, __LINE__)
        }

        If (Arg1)
        {
            /* Data are unchanged, because writings were made */
            /* into the new objects associated with Local7. */
            M1A6 ()
            Return (Zero)
        }

        /* Computational Data (Field Unit and Buffer Field) */

        Local7 = F900 /* \F900 */
        Local1 = CondRefOf (Local7, Local0)
        If (M1A4 (Local1, 0x0259))
        {
            M1A2 (Local0, C009, 0x00, 0x00, C009, 0x00, __LINE__)
        }

        Local7 = BN90 /* \BN90 */
        Local1 = CondRefOf (Local7, Local0)
        If (M1A4 (Local1, 0x025B))
        {
            M1A2 (Local0, C009, 0x00, 0x00, C009, 0x00, __LINE__)
        }

        Local7 = IF90 /* \IF90 */
        Local1 = CondRefOf (Local7, Local0)
        If (M1A4 (Local1, 0x025D))
        {
            M1A2 (Local0, C009, 0x00, 0x00, C009, 0x00, __LINE__)
        }

        Local7 = BF90 /* \BF90 */
        Local1 = CondRefOf (Local7, Local0)
        If (M1A4 (Local1, 0x025F))
        {
            M1A2 (Local0, C00B, 0x00, 0x00, C00B, Buffer(){0xB0}, __LINE__)
        }

        /* Elements of Package are Uninitialized */

        Local7 = P900 /* \P900 */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x0268)
        /* Elements of Package are Computational Data */

        Local7 = P901 /* \P901 */
        Local1 = CondRefOf (Local7, Local0)
        If (M1A4 (Local1, 0x0269))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xABCD0004, __LINE__)
            M1A2 (Local0, C00C, 0x01, 0x01, C009, 0x1122334455660005, __LINE__)
        }

        Local7 = P902 /* \P902 */
        Local1 = CondRefOf (Local7, Local0)
        If (M1A4 (Local1, 0x026C))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C00A, "12340006", __LINE__)
            M1A2 (Local0, C00C, 0x01, 0x01, C00A, "q1w2e3r4t5y6u7i80007", __LINE__)
        }

        Local7 = P903 /* \P903 */
        Local1 = CondRefOf (Local7, Local0)
        If (M1A4 (Local1, 0x026F))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C00A, "qwrtyuiop0008", __LINE__)
            M1A2 (Local0, C00C, 0x01, 0x01, C00A, "1234567890abdef0250009", __LINE__)
        }

        Local7 = P904 /* \P904 */
        Local1 = CondRefOf (Local7, Local0)
        If (M1A4 (Local1, 0x0272))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C00B, Buffer (0x03)
                {
                     0xB5, 0xB6, 0xB7                                 // ...
                }, 0x0273)
        }

        Local7 = P905 /* \P905 */
        Local1 = CondRefOf (Local7, Local0)
        If (M1A4 (Local1, 0x0274))
        {
            M1A2 (Local0, C00C, 0x02, 0x00, C009, 0x0ABC000A, __LINE__)
            M1A2 (Local0, C00C, 0x02, 0x01, C00A, "0xabc000b", __LINE__)
        }

        Local7 = P906 /* \P906 */
        Local1 = CondRefOf (Local7, Local0)
        If (M1A4 (Local1, 0x0277))
        {
            M1A2 (Local0, C00C, 0x02, 0x00, C00A, "abc000d", __LINE__)
        }

        Local7 = P907 /* \P907 */
        Local1 = CondRefOf (Local7, Local0)
        If (M1A4 (Local1, 0x0279))
        {
            M1A2 (Local0, C00C, 0x02, 0x00, C00A, "aqwevbgnm000e", __LINE__)
        }

        Local7 = P908 /* \P908 */
        Local1 = CondRefOf (Local7, Local0)
        If (M1A4 (Local1, 0x027B))
        {
            M1A2 (Local0, C00C, 0x02, 0x00, C00B, Buffer (0x05)
                {
                     0xBA, 0xBB, 0xBC, 0xBD, 0xBE                     // .....
                }, 0x027C)
        }

        Local7 = P909 /* \P909 */
        Local1 = CondRefOf (Local7, Local0)
        If (M1A4 (Local1, 0x027D))
        {
            M1A2 (Local0, C00C, 0x03, 0x00, C009, 0x0ABC000F, __LINE__)
        }

        Local7 = P90A /* \P90A */
        Local1 = CondRefOf (Local7, Local0)
        If (M1A4 (Local1, 0x027F))
        {
            M1A2 (Local0, C00C, 0x03, 0x00, C00A, "12340010", __LINE__)
        }

        Local7 = P90B /* \P90B */
        Local1 = CondRefOf (Local7, Local0)
        If (M1A4 (Local1, 0x0281))
        {
            M1A2 (Local0, C00C, 0x03, 0x00, C00A, "zxswefas0011", __LINE__)
        }

        Local7 = P90C /* \P90C */
        Local1 = CondRefOf (Local7, Local0)
        If (M1A4 (Local1, 0x0283))
        {
            M1A2 (Local0, C00C, 0x03, 0x00, C00B, Buffer (0x03)
                {
                     0xBF, 0xC0, 0xC1                                 // ...
                }, 0x0284)
        }

        Local7 = P90D /* \P90D */
        Local1 = CondRefOf (Local7, Local0)
        If (M1A4 (Local1, 0x0285))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xFE7CB391D65A0000, __LINE__)
        }

        Local7 = P90E /* \P90E */
        Local1 = CondRefOf (Local7, Local0)
        If (M1A4 (Local1, 0x0287))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xC1790001, __LINE__)
        }

        Local7 = P90F /* \P90F */
        Local1 = CondRefOf (Local7, Local0)
        If (M1A4 (Local1, 0x0289))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C00A, "12340002", __LINE__)
        }

        Local7 = P910 /* \P910 */
        Local1 = CondRefOf (Local7, Local0)
        If (M1A4 (Local1, 0x028B))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C00A, "qwrtyu0003", __LINE__)
        }

        Local7 = P911 /* \P911 */
        Local1 = CondRefOf (Local7, Local0)
        If (M1A4 (Local1, 0x028D))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C00B, Buffer (0x05)
                {
                     0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
                }, 0x028E)
        }

        If (Y118)
        {
            Local7 = P912 /* \P912 */
            Local1 = CondRefOf (Local7, Local0)
            If (M1A4 (Local1, 0x028F))
            {
                M1A2 (Local0, C00C, 0x01, 0x00, C00D, 0x00, __LINE__)
            }

            Local7 = P913 /* \P913 */
            Local1 = CondRefOf (Local7, Local0)
            If (M1A4 (Local1, 0x0291))
            {
                M1A2 (Local0, C00C, 0x01, 0x00, C00D, 0x00, __LINE__)
            }

            Local7 = P914 /* \P914 */
            Local1 = CondRefOf (Local7, Local0)
            If (M1A4 (Local1, 0x0293))
            {
                M1A2 (Local0, C00C, 0x01, 0x00, C00D, 0x00, __LINE__)
            }

            Local7 = P915 /* \P915 */
            Local1 = CondRefOf (Local7, Local0)
            If (M1A4 (Local1, 0x0295))
            {
                M1A2 (Local0, C00C, 0x01, 0x00, C016, 0xB0, __LINE__)
            }
        }

        /* Elements of Package are NOT Computational Data */

        Local7 = P916 /* \P916 */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x0297)
        Local7 = P917 /* \P917 */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x0298)
        Local7 = P918 /* \P918 */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x19FF)
        Local7 = P919 /* \P919 */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x029A)
        Local7 = P91A /* \P91A */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x029B)
        Local7 = P91B /* \P91B */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x029C)
        Local7 = P91C /* \P91C */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x029D)
        /* Elements of Package are Methods */

        Local7 = P91D /* \P91D */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x029E)
        Local7 = P91E /* \P91E */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x029F)
        Local7 = P91F /* \P91F */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02A0)
        Local7 = P920 /* \P920 */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02A1)
        Local7 = P921 /* \P921 */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02A2)
        Local7 = P922 /* \P922 */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02A3)
        Local7 = P923 /* \P923 */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02A4)
        Local7 = P924 /* \P924 */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02A5)
        Local7 = P925 /* \P925 */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02A6)
        Local7 = P926 /* \P926 */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02A7)
        Local7 = P927 /* \P927 */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02A8)
        Local7 = P928 /* \P928 */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02A9)
        Local7 = P929 /* \P929 */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02AA)
        Local7 = P92A /* \P92A */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02AB)
        Local7 = P92B /* \P92B */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02AC)
        Local7 = P92C /* \P92C */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02AD)
        Local7 = P92D /* \P92D */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02AE)
        Local7 = P92E /* \P92E */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02AF)
        Local7 = P92F /* \P92F */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02B0)
        Local7 = P930 /* \P930 */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02B1)
        Local7 = P931 /* \P931 */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02B2)
        Local7 = P932 /* \P932 */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02B3)
        Local7 = P933 /* \P933 */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02B4)
        Local7 = P934 /* \P934 */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02B5)
        Local7 = P935 /* \P935 */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02B6)
        Local7 = P936 /* \P936 */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02B7)
        Local7 = P937 /* \P937 */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02B8)
        Local7 = P938 /* \P938 */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02B9)
        Local7 = P939 /* \P939 */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02BA)
        Local7 = P93A /* \P93A */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02BB)
        Local7 = P93B /* \P93B */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02BC)
        Local7 = P93C /* \P93C */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02BD)
        Local7 = P93D /* \P93D */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02BE)
        Local7 = P93E /* \P93E */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02BF)
        Local7 = P93F /* \P93F */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02C0)
        Local7 = P940 /* \P940 */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02C1)
        Local7 = P941 /* \P941 */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02C2)
        Local7 = P942 /* \P942 */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02C3)
        Local7 = P943 /* \P943 */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02C4)
        Local7 = P944 /* \P944 */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02C5)
        Local7 = P945 /* \P945 */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02C6)
        Local7 = P946 /* \P946 */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02C7)
        Local7 = P947 /* \P947 */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02C8)
        Local7 = P948 /* \P948 */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02C9)
        Local7 = P949 /* \P949 */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02CA)
        Local7 = P94A /* \P94A */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02CB)
        Local7 = P94B /* \P94B */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02CC)
        Local7 = P94C /* \P94C */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02CD)
        Local7 = P94D /* \P94D */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02CE)
        Local7 = P94E /* \P94E */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02CF)
        Local7 = P94F /* \P94F */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02D0)
        Local7 = P950 /* \P950 */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02D1)
        Local7 = P951 /* \P951 */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02D2)
        Local7 = P952 /* \P952 */
        Local1 = CondRefOf (Local7, Local0)
        M1A0 (Local0, C00C, Local1, 0x02D3)
        M1A6 ()
        Return (Zero)
    }

    Method (M175, 3, NotSerialized)
    {
        C081 = Z078       /* absolute index of file initiating the checking */ /* \Z078 */
        C089 = 0x01      /* flag of Reference, object otherwise */
        If (Arg0)
        {
            M170 ()
        }

        If (Arg1)
        {
            M171 (0x00, C083)
        }

        If (Arg2)
        {
            M172 (0x00, C083)
        }
    }

    /* The mode with the chain of references to LocalX */

    Method (M176, 0, NotSerialized)
    {
        C084 = 0x01  /* run verification of references (reading) */
        C085 = 0x01  /* create the chain of references to LocalX, then dereference them */
        Debug = "The mode with the chain of references to LocalX:"
        M175 (0x01, 0x01, 0x01)
    }

    /* Run-method */

    Method (REF2, 0, NotSerialized)
    {
        Debug = "TEST: REF2, References"
        C080 = "REF2" /* name of test */
        C082 = 0x00      /* flag of test of exceptions */
        C083 = 0x00      /* run verification of references (write/read) */
        C086 = 0x00      /* flag, run test till the first error */
        C087 = 0x01      /* apply DeRefOf to ArgX-ObjectReference */
        M176 ()
    }
