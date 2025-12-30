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
     */
    Name (Z108, 0x6C)
    /* m16a */

    Method (M1B0, 0, NotSerialized)
    {
        If (Y100)
        {
            TS00 ("m1b0")
        }
        Else
        {
            Debug = "m1b0"
        }

        /* T2:R1-R14 */
        /* Computational Data */
        M1A2 (I900, C009, 0x00, 0x00, C009, 0xFE7CB391D65A0000, __LINE__)
        M1A2 (I901, C009, 0x00, 0x00, C009, 0xC1790001, __LINE__)
        M1A2 (S900, C00A, 0x00, 0x00, C00A, "12340002", __LINE__)
        M1A2 (S901, C00A, 0x00, 0x00, C00A, "qwrtyu0003", __LINE__)
        M1A2 (B900, C00B, 0x00, 0x00, C00B, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            }, 0x04)
        M1A2 (F900, C009, 0x00, 0x00, C009, 0x00, __LINE__)
        M1A2 (BN90, C009, 0x00, 0x00, C009, 0x00, __LINE__)
        M1A2 (IF90, C009, 0x00, 0x00, C009, 0x00, __LINE__)
        M1A2 (BF90, C00B, 0x00, 0x00, C00B, Buffer() {0xB0}, __LINE__)
        /* Not Computational Data */

        M1A0 (E900, C00F, Ones, 0x09)
        M1A0 (MX90, C011, Ones, 0x0A)
        If (Y511)
        {
            M1A0 (D900, C00E, Ones, 0x0B)
        }

        If (Y508)
        {
            M1A0 (TZ90, C015, Ones, 0x0C)
        }

        M1A0 (PR90, C014, Ones, 0x0D)
        M1A0 (R900, C012, Ones, 0x0E)
        M1A0 (PW90, C013, Ones, 0x0F)
        /* Elements of Package are Uninitialized */

        M1A0 (P900, C00C, Ones, 0x10)
        /* Elements of Package are Computational Data */

        M1A2 (P901, C00C, 0x01, 0x00, C009, 0xABCD0004, __LINE__)
        M1A2 (P901, C00C, 0x01, 0x01, C009, 0x1122334455660005, __LINE__)
        M1A2 (P902, C00C, 0x01, 0x00, C00A, "12340006", __LINE__)
        M1A2 (P902, C00C, 0x01, 0x01, C00A, "q1w2e3r4t5y6u7i80007", __LINE__)
        M1A2 (P903, C00C, 0x01, 0x00, C00A, "qwrtyuiop0008", __LINE__)
        M1A2 (P903, C00C, 0x01, 0x01, C00A, "1234567890abdef0250009", __LINE__)
        M1A2 (P904, C00C, 0x01, 0x00, C00B, Buffer (0x03)
            {
                 0xB5, 0xB6, 0xB7                                 // ...
            }, 0x17)
        M1A2 (P905, C00C, 0x02, 0x00, C009, 0x0ABC000A, __LINE__)
        M1A2 (P905, C00C, 0x02, 0x01, C00A, "0xabc000b", __LINE__)
        M1A2 (P906, C00C, 0x02, 0x00, C00A, "abc000d", __LINE__)
        M1A2 (P907, C00C, 0x02, 0x00, C00A, "aqwevbgnm000e", __LINE__)
        M1A2 (P908, C00C, 0x02, 0x00, C00B, Buffer (0x05)
            {
                 0xBA, 0xBB, 0xBC, 0xBD, 0xBE                     // .....
            }, 0x1C)
        M1A2 (P909, C00C, 0x03, 0x00, C009, 0x0ABC000F, __LINE__)
        M1A2 (P90A, C00C, 0x03, 0x00, C00A, "12340010", __LINE__)
        M1A2 (P90B, C00C, 0x03, 0x00, C00A, "zxswefas0011", __LINE__)
        M1A2 (P90C, C00C, 0x03, 0x00, C00B, Buffer (0x03)
            {
                 0xBF, 0xC0, 0xC1                                 // ...
            }, 0x20)
        M1A2 (P90D, C00C, 0x01, 0x00, C009, 0xFE7CB391D65A0000, __LINE__)
        M1A2 (P90E, C00C, 0x01, 0x00, C009, 0xC1790001, __LINE__)
        M1A2 (P90F, C00C, 0x01, 0x00, C00A, "12340002", __LINE__)
        M1A2 (P910, C00C, 0x01, 0x00, C00A, "qwrtyu0003", __LINE__)
        M1A2 (P911, C00C, 0x01, 0x00, C00B, Buffer (0x05)
            {
                 0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
            }, 0x25)
        If (Y118)
        {
            M1A2 (P912, C00C, 0x01, 0x00, C00D, 0x00, __LINE__)
            M1A2 (P913, C00C, 0x01, 0x00, C00D, 0x00, __LINE__)
            M1A2 (P914, C00C, 0x01, 0x00, C00D, 0x00, __LINE__)
            M1A2 (P915, C00C, 0x01, 0x00, C016, 0xB0, __LINE__)
        }

        /* Elements of Package are NOT Computational Data */

        M1A0 (P916, C00C, Ones, 0x2A)
        M1A0 (P917, C00C, Ones, 0x2B)
        M1A0 (P918, C00C, Ones, 0x2C)
        M1A0 (P919, C00C, Ones, 0x2D)
        M1A0 (P91A, C00C, Ones, 0x2E)
        M1A0 (P91B, C00C, Ones, 0x2F)
        M1A0 (P91C, C00C, Ones, 0x30)
        /* Elements of Package are Methods */

        M1A0 (P91D, C00C, Ones, 0x31)
        M1A0 (P91E, C00C, Ones, 0x32)
        M1A0 (P91F, C00C, Ones, 0x33)
        M1A0 (P920, C00C, Ones, 0x34)
        M1A0 (P921, C00C, Ones, 0x35)
        M1A0 (P922, C00C, Ones, 0x36)
        M1A0 (P923, C00C, Ones, 0x37)
        M1A0 (P924, C00C, Ones, 0x38)
        M1A0 (P925, C00C, Ones, 0x39)
        M1A0 (P926, C00C, Ones, 0x3A)
        M1A0 (P927, C00C, Ones, 0x3B)
        M1A0 (P928, C00C, Ones, 0x3C)
        M1A0 (P929, C00C, Ones, 0x3D)
        M1A0 (P92A, C00C, Ones, 0x3E)
        M1A0 (P92B, C00C, Ones, 0x3F)
        M1A0 (P92C, C00C, Ones, 0x40)
        M1A0 (P92D, C00C, Ones, 0x41)
        M1A0 (P92E, C00C, Ones, 0x42)
        M1A0 (P92F, C00C, Ones, 0x43)
        M1A0 (P930, C00C, Ones, 0x44)
        M1A0 (P931, C00C, Ones, 0x45)
        M1A0 (P932, C00C, Ones, 0x46)
        M1A0 (P933, C00C, Ones, 0x47)
        M1A0 (P934, C00C, Ones, 0x48)
        M1A0 (P935, C00C, Ones, 0x49)
        M1A0 (P936, C00C, Ones, 0x4A)
        M1A0 (P937, C00C, Ones, 0x4B)
        M1A0 (P938, C00C, Ones, 0x4C)
        M1A0 (P939, C00C, Ones, 0x4D)
        M1A0 (P93A, C00C, Ones, 0x4E)
        M1A0 (P93B, C00C, Ones, 0x4F)
        M1A0 (P93C, C00C, Ones, 0x50)
        M1A0 (P93D, C00C, Ones, 0x51)
        M1A0 (P93E, C00C, Ones, 0x52)
        M1A0 (P93F, C00C, Ones, 0x53)
        M1A0 (P940, C00C, Ones, 0x54)
        M1A0 (P941, C00C, Ones, 0x55)
        M1A0 (P942, C00C, Ones, 0x56)
        M1A0 (P943, C00C, Ones, 0x57)
        M1A0 (P944, C00C, Ones, 0x58)
        M1A0 (P945, C00C, Ones, 0x59)
        M1A0 (P946, C00C, Ones, 0x5A)
        M1A0 (P947, C00C, Ones, 0x5B)
        M1A0 (P948, C00C, Ones, 0x5C)
        M1A0 (P949, C00C, Ones, 0x5D)
        M1A0 (P94A, C00C, Ones, 0x5E)
        M1A0 (P94B, C00C, Ones, 0x5F)
        M1A0 (P94C, C00C, Ones, 0x60)
        M1A0 (P94D, C00C, Ones, 0x61)
        M1A0 (P94E, C00C, Ones, 0x62)
        M1A0 (P94F, C00C, Ones, 0x63)
        M1A0 (P950, C00C, Ones, 0x64)
        M1A0 (P951, C00C, Ones, 0x65)
        M1A0 (P952, C00C, Ones, 0x66)
        M1A0 (P953, C00C, Ones, 0x67)
        /* Methods */

        If (Y509)
        {
            M1A0 (M900 (), C010, Ones, 0x68)
            M1A0 (M901 (), C010, Ones, 0x69)
            M1A0 (M902 (), C010, Ones, 0x6A)
            M1A0 (M903 (), C010, Ones, 0x6B)
            M1A0 (M904 (), C010, Ones, 0x6C)
            M1A0 (M905 (), C010, Ones, 0x6D)
            M1A0 (M906 (), C010, Ones, 0x6E)
            M1A0 (M907 (), C010, Ones, 0x6F)
            M1A0 (M908 (), C010, Ones, 0x70)
            M1A0 (M909 (), C010, Ones, 0x71)
            M1A0 (M90A (), C010, Ones, 0x72)
            M1A0 (M90B (), C010, Ones, 0x73)
            M1A0 (M90C (), C010, Ones, 0x74)
            M1A0 (M90D (), C010, Ones, 0x75)
            M1A0 (M90E (), C010, Ones, 0x76)
            M1A0 (M90F (), C010, Ones, 0x77)
            M1A0 (M910 (), C010, Ones, 0x78)
            M1A0 (M911 (), C010, Ones, 0x79)
            M1A0 (M912 (), C010, Ones, 0x7A)
            M1A0 (M913 (), C010, Ones, 0x7B)
            M1A0 (M914 (), C010, Ones, 0x7C)
            M1A0 (M915 (), C010, Ones, 0x7D)
            M1A0 (M916 (), C010, Ones, 0x7E)
            M1A0 (M917 (), C010, Ones, 0x7F)
            M1A0 (M918 (), C010, Ones, 0x80)
            M1A0 (M919 (), C010, Ones, 0x81)
            M1A0 (M91A (), C010, Ones, 0x82)
            M1A0 (M91B (), C010, Ones, 0x83)
            M1A0 (M91C (), C010, Ones, 0x84)
            M1A0 (M91D (), C010, Ones, 0x85)
            M1A0 (M91E (), C010, Ones, 0x86)
            M1A0 (M91F (), C010, Ones, 0x87)
            M1A0 (M920 (), C010, Ones, 0x88)
            M1A0 (M921 (), C010, Ones, 0x89)
            M1A0 (M922 (), C010, Ones, 0x8A)
            M1A0 (M923 (), C010, Ones, 0x8B)
            M1A0 (M924 (), C010, Ones, 0x8C)
            M1A0 (M925 (), C010, Ones, 0x8D)
            M1A0 (M926 (), C010, Ones, 0x8E)
            M1A0 (M927 (), C010, Ones, 0x8F)
            M1A0 (M928 (), C010, Ones, 0x90)
            M1A0 (M929 (), C010, Ones, 0x91)
            M1A0 (M92A (), C010, Ones, 0x92)
            M1A0 (M92B (), C010, Ones, 0x93)
            M1A0 (M92C (), C010, Ones, 0x94)
            M1A0 (M92D (), C010, Ones, 0x95)
            M1A0 (M92E (), C010, Ones, 0x96)
            M1A0 (M92F (), C010, Ones, 0x97)
            M1A0 (M930 (), C010, Ones, 0x98)
            M1A0 (M931 (), C010, Ones, 0x99)
            M1A0 (M932 (), C010, Ones, 0x9A)
            M1A0 (M933 (), C010, Ones, 0x9B)
            M1A0 (M934 (), C010, Ones, 0x9C)
            M1A0 (M935 (), C010, Ones, 0x9D)
        }

        M1A6 ()
    }

    /*
     * CopyObject of Object to LocalX:
     *
     * Local0-Local7 can be written with any
     * type object without any conversion.
     *
     * Check each type after each one.
     */
    Method (M1B1, 0, Serialized)
    {
        C081 = Z108 /* absolute index of file initiating the checking */ /* \Z108 */
        /* All types */

        CopyObject (I900, Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (S900, Local0)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        CopyObject (B900, Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (P900, Local0)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        CopyObject (F900, Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (D900, Local0)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        CopyObject (E900, Local0)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        If (RN06)
        {
            CopyObject (M901 (), Local0)
        }
        Else
        {
            CopyObject (DerefOf (RefOf (M901)), Local0)
        }

        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        CopyObject (MX90, Local0)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        If (Y510)
        {
            CopyObject (R900, Local0)
            M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        }

        CopyObject (PW90, Local0)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        CopyObject (PR90, Local0)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        If (Y508)
        {
            CopyObject (TZ90, Local0)
            M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        }

        CopyObject (BF90, Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        /*///////////////////// All after Integer */

        CopyObject (I900, Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (I900, Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (S900, Local0)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        CopyObject (I900, Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (B900, Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (I900, Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (P900, Local0)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        CopyObject (I900, Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (F900, Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (I900, Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (D900, Local0)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        CopyObject (I900, Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (E900, Local0)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        CopyObject (I900, Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        If (RN06)
        {
            CopyObject (M901 (), Local0)
        }
        Else
        {
            CopyObject (DerefOf (RefOf (M901)), Local0)
        }

        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        CopyObject (I900, Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (MX90, Local0)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        CopyObject (I900, Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        If (Y510)
        {
            CopyObject (R900, Local0)
            M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        }

        CopyObject (I900, Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (PW90, Local0)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        CopyObject (I900, Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (PR90, Local0)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        CopyObject (I900, Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        If (Y508)
        {
            CopyObject (TZ90, Local0)
            M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        }

        CopyObject (I900, Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (BF90, Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (I900, Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-Integer after String */

        CopyObject (S900, Local0)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        CopyObject (S900, Local0)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        CopyObject (B900, Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (S900, Local0)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        CopyObject (P900, Local0)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        CopyObject (S900, Local0)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        CopyObject (F900, Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (S900, Local0)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        CopyObject (D900, Local0)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        CopyObject (S900, Local0)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        CopyObject (E900, Local0)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        CopyObject (S900, Local0)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        If (RN06)
        {
            CopyObject (M901 (), Local0)
        }
        Else
        {
            CopyObject (DerefOf (RefOf (M901)), Local0)
        }

        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        CopyObject (S900, Local0)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        CopyObject (MX90, Local0)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        CopyObject (S900, Local0)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        If (Y510)
        {
            CopyObject (R900, Local0)
            M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        }

        CopyObject (S900, Local0)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        CopyObject (PW90, Local0)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        CopyObject (S900, Local0)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        CopyObject (PR90, Local0)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        CopyObject (S900, Local0)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        If (Y508)
        {
            CopyObject (TZ90, Local0)
            M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        }

        CopyObject (S900, Local0)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        CopyObject (BF90, Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (S900, Local0)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-(Integer+String) after Buffer */

        CopyObject (B900, Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (B900, Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (P900, Local0)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        CopyObject (B900, Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (F900, Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (B900, Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (D900, Local0)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        CopyObject (B900, Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (E900, Local0)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        CopyObject (B900, Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        If (RN06)
        {
            CopyObject (M901 (), Local0)
        }
        Else
        {
            CopyObject (DerefOf (RefOf (M901)), Local0)
        }

        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        CopyObject (B900, Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (MX90, Local0)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        CopyObject (B900, Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        If (Y510)
        {
            CopyObject (R900, Local0)
            M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        }

        CopyObject (B900, Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (PW90, Local0)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        CopyObject (B900, Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (PR90, Local0)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        CopyObject (B900, Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        If (Y508)
        {
            CopyObject (TZ90, Local0)
            M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        }

        CopyObject (B900, Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (BF90, Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (B900, Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-(...) after Package */

        CopyObject (P900, Local0)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        CopyObject (P900, Local0)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        CopyObject (F900, Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (P900, Local0)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        CopyObject (D900, Local0)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        CopyObject (P900, Local0)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        CopyObject (E900, Local0)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        CopyObject (P900, Local0)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        If (RN06)
        {
            CopyObject (M901 (), Local0)
        }
        Else
        {
            CopyObject (DerefOf (RefOf (M901)), Local0)
        }

        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        CopyObject (P900, Local0)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        CopyObject (MX90, Local0)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        CopyObject (P900, Local0)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        If (Y510)
        {
            CopyObject (R900, Local0)
            M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        }

        CopyObject (P900, Local0)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        CopyObject (PW90, Local0)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        CopyObject (P900, Local0)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        CopyObject (PR90, Local0)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        CopyObject (P900, Local0)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        If (Y508)
        {
            CopyObject (TZ90, Local0)
            M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        }

        CopyObject (P900, Local0)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        CopyObject (BF90, Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (P900, Local0)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-(...) after Field Unit */

        CopyObject (F900, Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (F900, Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (D900, Local0)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        CopyObject (F900, Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (E900, Local0)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        CopyObject (F900, Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        If (RN06)
        {
            CopyObject (M901 (), Local0)
        }
        Else
        {
            CopyObject (DerefOf (RefOf (M901)), Local0)
        }

        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        CopyObject (F900, Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (MX90, Local0)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        CopyObject (F900, Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        If (Y510)
        {
            CopyObject (R900, Local0)
            M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        }

        CopyObject (F900, Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (PW90, Local0)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        CopyObject (F900, Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (PR90, Local0)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        CopyObject (F900, Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        If (Y508)
        {
            CopyObject (TZ90, Local0)
            M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        }

        CopyObject (F900, Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (BF90, Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (F900, Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-(...) after Device */

        CopyObject (D900, Local0)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        CopyObject (D900, Local0)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        CopyObject (E900, Local0)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        CopyObject (D900, Local0)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        If (RN06)
        {
            CopyObject (M901 (), Local0)
        }
        Else
        {
            CopyObject (DerefOf (RefOf (M901)), Local0)
        }

        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        CopyObject (D900, Local0)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        CopyObject (MX90, Local0)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        CopyObject (D900, Local0)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        If (Y510)
        {
            CopyObject (R900, Local0)
            M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        }

        CopyObject (D900, Local0)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        CopyObject (PW90, Local0)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        CopyObject (D900, Local0)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        CopyObject (PR90, Local0)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        CopyObject (D900, Local0)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        If (Y508)
        {
            CopyObject (TZ90, Local0)
            M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        }

        CopyObject (D900, Local0)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        CopyObject (BF90, Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (D900, Local0)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-(...) after Event */

        CopyObject (E900, Local0)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        CopyObject (E900, Local0)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        If (RN06)
        {
            CopyObject (M901 (), Local0)
        }
        Else
        {
            CopyObject (DerefOf (RefOf (M901)), Local0)
        }

        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        CopyObject (E900, Local0)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        CopyObject (MX90, Local0)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        CopyObject (E900, Local0)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        If (Y510)
        {
            CopyObject (R900, Local0)
            M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        }

        CopyObject (E900, Local0)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        CopyObject (PW90, Local0)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        CopyObject (E900, Local0)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        CopyObject (PR90, Local0)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        CopyObject (E900, Local0)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        If (Y508)
        {
            CopyObject (TZ90, Local0)
            M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        }

        CopyObject (E900, Local0)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        CopyObject (BF90, Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (E900, Local0)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-(...) after Method */

        If (RN06)
        {
            CopyObject (M901 (), Local0)
        }
        Else
        {
            CopyObject (DerefOf (RefOf (M901)), Local0)
        }

        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        If (RN06)
        {
            CopyObject (M901 (), Local0)
        }
        Else
        {
            CopyObject (DerefOf (RefOf (M901)), Local0)
        }

        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        CopyObject (MX90, Local0)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        If (RN06)
        {
            CopyObject (M901 (), Local0)
        }
        Else
        {
            CopyObject (DerefOf (RefOf (M901)), Local0)
        }

        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        If (Y510)
        {
            CopyObject (R900, Local0)
            M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        }

        If (RN06)
        {
            CopyObject (M901 (), Local0)
        }
        Else
        {
            CopyObject (DerefOf (RefOf (M901)), Local0)
        }

        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        CopyObject (PW90, Local0)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        If (RN06)
        {
            CopyObject (M901 (), Local0)
        }
        Else
        {
            CopyObject (DerefOf (RefOf (M901)), Local0)
        }

        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        CopyObject (PR90, Local0)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        If (RN06)
        {
            CopyObject (M901 (), Local0)
        }
        Else
        {
            CopyObject (DerefOf (RefOf (M901)), Local0)
        }

        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        If (Y508)
        {
            CopyObject (TZ90, Local0)
            M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        }

        If (RN06)
        {
            CopyObject (M901 (), Local0)
        }
        Else
        {
            CopyObject (DerefOf (RefOf (M901)), Local0)
        }

        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        CopyObject (BF90, Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        If (RN06)
        {
            CopyObject (M901 (), Local0)
        }
        Else
        {
            CopyObject (DerefOf (RefOf (M901)), Local0)
        }

        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-(...) after Mutex */

        CopyObject (MX90, Local0)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        CopyObject (MX90, Local0)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        If (Y510)
        {
            CopyObject (R900, Local0)
            M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        }

        CopyObject (MX90, Local0)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        CopyObject (PW90, Local0)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        CopyObject (MX90, Local0)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        CopyObject (PR90, Local0)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        CopyObject (MX90, Local0)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        If (Y508)
        {
            CopyObject (TZ90, Local0)
            M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        }

        CopyObject (MX90, Local0)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        CopyObject (BF90, Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (MX90, Local0)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-(...) after Operation Region */

        If (Y510)
        {
            CopyObject (R900, Local0)
            M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        }

        If (Y510)
        {
            CopyObject (R900, Local0)
            M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        }

        CopyObject (PW90, Local0)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        If (Y510)
        {
            CopyObject (R900, Local0)
            M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        }

        CopyObject (PR90, Local0)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        If (Y510)
        {
            CopyObject (R900, Local0)
            M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        }

        If (Y508)
        {
            CopyObject (TZ90, Local0)
            M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        }

        If (Y510)
        {
            CopyObject (R900, Local0)
            M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        }

        CopyObject (BF90, Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        If (Y510)
        {
            CopyObject (R900, Local0)
            M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        }

        /*///////////////////// All-(...) after Power Resource */

        CopyObject (PW90, Local0)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        CopyObject (PW90, Local0)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        CopyObject (PR90, Local0)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        CopyObject (PW90, Local0)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        If (Y508)
        {
            CopyObject (TZ90, Local0)
            M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        }

        CopyObject (PW90, Local0)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        CopyObject (BF90, Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (PW90, Local0)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-(...) after Processor */

        CopyObject (PR90, Local0)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        CopyObject (PR90, Local0)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        If (Y508)
        {
            CopyObject (TZ90, Local0)
            M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        }

        CopyObject (PR90, Local0)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        CopyObject (BF90, Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (PR90, Local0)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-(...) after Thermal Zone */

        If (Y508)
        {
            CopyObject (TZ90, Local0)
            M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        }

        CopyObject (BF90, Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        If (Y508)
        {
            CopyObject (TZ90, Local0)
            M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        }

        /*///////////////////// All-(...) after Buffer Field */

        CopyObject (BF90, Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (BF90, Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
    }

    /*
     * Store of Object to LocalX:
     *
     * Local0-Local7 can be written without any conversion
     *
     * A set of available for Store types is restricted
     *
     * Check each available type after each one
     */
    Method (M1B2, 0, Serialized)
    {
        C081 = Z108 /* absolute index of file initiating the checking */ /* \Z108 */
        /* All available for Store types */

        Local0 = I900 /* \I900 */
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        Local0 = S900 /* \S900 */
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        Local0 = B900 /* \B900 */
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        Local0 = P900 /* \P900 */
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        Local0 = F900 /* \F900 */
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        Local0 = BF90 /* \BF90 */
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        /*///////////////////// All after Integer */

        Local0 = I900 /* \I900 */
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        Local0 = I900 /* \I900 */
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        Local0 = S900 /* \S900 */
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        Local0 = I900 /* \I900 */
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        Local0 = B900 /* \B900 */
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        Local0 = I900 /* \I900 */
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        Local0 = P900 /* \P900 */
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        Local0 = I900 /* \I900 */
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        Local0 = F900 /* \F900 */
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        Local0 = I900 /* \I900 */
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        Local0 = BF90 /* \BF90 */
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        Local0 = I900 /* \I900 */
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-Integer after String */

        Local0 = S900 /* \S900 */
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        Local0 = S900 /* \S900 */
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        Local0 = B900 /* \B900 */
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        Local0 = S900 /* \S900 */
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        Local0 = P900 /* \P900 */
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        Local0 = S900 /* \S900 */
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        Local0 = F900 /* \F900 */
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        Local0 = S900 /* \S900 */
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        Local0 = BF90 /* \BF90 */
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        Local0 = S900 /* \S900 */
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-(Integer+String) after Buffer */

        Local0 = B900 /* \B900 */
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        Local0 = B900 /* \B900 */
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        Local0 = P900 /* \P900 */
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        Local0 = B900 /* \B900 */
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        Local0 = F900 /* \F900 */
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        Local0 = B900 /* \B900 */
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        Local0 = BF90 /* \BF90 */
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        Local0 = B900 /* \B900 */
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-(...) after Package */

        Local0 = P900 /* \P900 */
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        Local0 = P900 /* \P900 */
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        Local0 = F900 /* \F900 */
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        Local0 = P900 /* \P900 */
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        Local0 = BF90 /* \BF90 */
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        Local0 = P900 /* \P900 */
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-(...) after Field Unit */

        Local0 = F900 /* \F900 */
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        Local0 = F900 /* \F900 */
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        Local0 = BF90 /* \BF90 */
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        Local0 = F900 /* \F900 */
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-(...) after Buffer Field */

        Local0 = BF90 /* \BF90 */
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        Local0 = BF90 /* \BF90 */
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
    }

    /*
     * CopyObject the result of RefOf/CondRefOf to LocalX
     *
     * Local0-Local7 can be written with RefOf_References
     * to any type object without any conversion.
     *
     * Check each type after each one.
     *
     * The same as m1b1 but RefOf() added.
     */
    Method (M1B4, 0, Serialized)
    {
        C081 = Z108 /* absolute index of file initiating the checking */ /* \Z108 */
        /* All types */

        CopyObject (RefOf (I900), Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (S900), Local0)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (B900), Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (P900), Local0)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (F900), Local0)
        M1A3 (Local0, C00D, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (D900), Local0)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (E900), Local0)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (M901), Local0)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (MX90), Local0)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (R900), Local0)
        M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (PW90), Local0)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (PR90), Local0)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (TZ90), Local0)
        M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (BF90), Local0)
        M1A3 (Local0, C016, Z108, __METHOD__, __LINE__)
        /*///////////////////// All after Integer */

        CopyObject (RefOf (I900), Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (I900), Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (S900), Local0)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (I900), Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (B900), Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (I900), Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (P900), Local0)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (I900), Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (F900), Local0)
        M1A3 (Local0, C00D, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (I900), Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (D900), Local0)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (I900), Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (E900), Local0)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (I900), Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (M901), Local0)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (I900), Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (MX90), Local0)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (I900), Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (R900), Local0)
        M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (I900), Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (PW90), Local0)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (I900), Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (PR90), Local0)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (I900), Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (TZ90), Local0)
        M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (I900), Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (BF90), Local0)
        M1A3 (Local0, C016, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (I900), Local0)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-Integer after String */

        CopyObject (RefOf (S900), Local0)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (S900), Local0)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (B900), Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (S900), Local0)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (P900), Local0)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (S900), Local0)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (F900), Local0)
        M1A3 (Local0, C00D, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (S900), Local0)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (D900), Local0)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (S900), Local0)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (E900), Local0)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (S900), Local0)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (M901), Local0)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (S900), Local0)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (MX90), Local0)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (S900), Local0)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (R900), Local0)
        M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (S900), Local0)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (PW90), Local0)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (S900), Local0)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (PR90), Local0)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (S900), Local0)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (TZ90), Local0)
        M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (S900), Local0)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (BF90), Local0)
        M1A3 (Local0, C016, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (S900), Local0)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-(Integer+String) after Buffer */

        CopyObject (RefOf (B900), Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (B900), Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (P900), Local0)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (B900), Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (F900), Local0)
        M1A3 (Local0, C00D, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (B900), Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (D900), Local0)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (B900), Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (E900), Local0)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (B900), Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (M901), Local0)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (B900), Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (MX90), Local0)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (B900), Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (R900), Local0)
        M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (B900), Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (PW90), Local0)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (B900), Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (PR90), Local0)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (B900), Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (TZ90), Local0)
        M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (B900), Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (BF90), Local0)
        M1A3 (Local0, C016, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (B900), Local0)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-(...) after Package */

        CopyObject (RefOf (P900), Local0)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (P900), Local0)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (F900), Local0)
        M1A3 (Local0, C00D, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (P900), Local0)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (D900), Local0)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (P900), Local0)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (E900), Local0)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (P900), Local0)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (M901), Local0)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (P900), Local0)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (MX90), Local0)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (P900), Local0)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (R900), Local0)
        M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (P900), Local0)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (PW90), Local0)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (P900), Local0)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (PR90), Local0)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (P900), Local0)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (TZ90), Local0)
        M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (P900), Local0)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (BF90), Local0)
        M1A3 (Local0, C016, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (P900), Local0)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-(...) after Field Unit */

        CopyObject (RefOf (F900), Local0)
        M1A3 (Local0, C00D, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (F900), Local0)
        M1A3 (Local0, C00D, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (D900), Local0)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (F900), Local0)
        M1A3 (Local0, C00D, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (E900), Local0)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (F900), Local0)
        M1A3 (Local0, C00D, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (M901), Local0)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (F900), Local0)
        M1A3 (Local0, C00D, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (MX90), Local0)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (F900), Local0)
        M1A3 (Local0, C00D, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (R900), Local0)
        M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (F900), Local0)
        M1A3 (Local0, C00D, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (PW90), Local0)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (F900), Local0)
        M1A3 (Local0, C00D, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (PR90), Local0)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (F900), Local0)
        M1A3 (Local0, C00D, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (TZ90), Local0)
        M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (F900), Local0)
        M1A3 (Local0, C00D, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (BF90), Local0)
        M1A3 (Local0, C016, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (F900), Local0)
        M1A3 (Local0, C00D, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-(...) after Device */

        CopyObject (RefOf (D900), Local0)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (D900), Local0)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (E900), Local0)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (D900), Local0)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (M901), Local0)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (D900), Local0)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (MX90), Local0)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (D900), Local0)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (R900), Local0)
        M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (D900), Local0)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (PW90), Local0)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (D900), Local0)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (PR90), Local0)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (D900), Local0)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (TZ90), Local0)
        M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (D900), Local0)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (BF90), Local0)
        M1A3 (Local0, C016, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (D900), Local0)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-(...) after Event */

        CopyObject (RefOf (E900), Local0)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (E900), Local0)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (M901), Local0)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (E900), Local0)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (MX90), Local0)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (E900), Local0)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (R900), Local0)
        M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (E900), Local0)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (PW90), Local0)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (E900), Local0)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (PR90), Local0)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (E900), Local0)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (TZ90), Local0)
        M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (E900), Local0)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (BF90), Local0)
        M1A3 (Local0, C016, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (E900), Local0)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-(...) after Method */

        CopyObject (RefOf (M901), Local0)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (M901), Local0)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (MX90), Local0)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (M901), Local0)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (R900), Local0)
        M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (M901), Local0)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (PW90), Local0)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (M901), Local0)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (PR90), Local0)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (M901), Local0)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (TZ90), Local0)
        M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (M901), Local0)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (BF90), Local0)
        M1A3 (Local0, C016, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (M901), Local0)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-(...) after Mutex */

        CopyObject (RefOf (MX90), Local0)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (MX90), Local0)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (R900), Local0)
        M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (MX90), Local0)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (PW90), Local0)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (MX90), Local0)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (PR90), Local0)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (MX90), Local0)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (TZ90), Local0)
        M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (MX90), Local0)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (BF90), Local0)
        M1A3 (Local0, C016, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (MX90), Local0)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-(...) after Operation Region */

        CopyObject (RefOf (R900), Local0)
        M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (R900), Local0)
        M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (PW90), Local0)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (R900), Local0)
        M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (PR90), Local0)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (R900), Local0)
        M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (TZ90), Local0)
        M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (R900), Local0)
        M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (BF90), Local0)
        M1A3 (Local0, C016, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (R900), Local0)
        M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-(...) after Power Resource */

        CopyObject (RefOf (PW90), Local0)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (PW90), Local0)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (PR90), Local0)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (PW90), Local0)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (TZ90), Local0)
        M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (PW90), Local0)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (BF90), Local0)
        M1A3 (Local0, C016, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (PW90), Local0)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-(...) after Processor */

        CopyObject (RefOf (PR90), Local0)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (PR90), Local0)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (TZ90), Local0)
        M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (PR90), Local0)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (BF90), Local0)
        M1A3 (Local0, C016, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (PR90), Local0)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-(...) after Thermal Zone */

        CopyObject (RefOf (TZ90), Local0)
        M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (BF90), Local0)
        M1A3 (Local0, C016, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (TZ90), Local0)
        M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-(...) after Buffer Field */

        CopyObject (RefOf (BF90), Local0)
        M1A3 (Local0, C016, Z108, __METHOD__, __LINE__)
        CopyObject (RefOf (BF90), Local0)
        M1A3 (Local0, C016, Z108, __METHOD__, __LINE__)
    }

    /*
     * Store the result of RefOf/CondRefOf to LocalX
     *
     * The same as m1b4 but Store instead of CopyObject.
     */
    Method (M1B5, 0, Serialized)
    {
        C081 = Z108 /* absolute index of file initiating the checking */ /* \Z108 */
        /* All types */

        Local0 = RefOf (I900)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (S900)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (B900)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (P900)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (F900)
        M1A3 (Local0, C00D, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (D900)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (E900)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (M901)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (MX90)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (R900)
        M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (PW90)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (PR90)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (TZ90)
        M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (BF90)
        M1A3 (Local0, C016, Z108, __METHOD__, __LINE__)
        /*///////////////////// All after Integer */

        Local0 = RefOf (I900)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (I900)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (S900)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (I900)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (B900)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (I900)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (P900)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (I900)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (F900)
        M1A3 (Local0, C00D, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (I900)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (D900)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (I900)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (E900)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (I900)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (M901)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (I900)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (MX90)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (I900)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (R900)
        M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (I900)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (PW90)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (I900)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (PR90)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (I900)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (TZ90)
        M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (I900)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (BF90)
        M1A3 (Local0, C016, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (I900)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-Integer after String */

        Local0 = RefOf (S900)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (S900)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (B900)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (S900)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (P900)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (S900)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (F900)
        M1A3 (Local0, C00D, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (S900)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (D900)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (S900)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (E900)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (S900)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (M901)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (S900)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (MX90)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (S900)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (R900)
        M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (S900)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (PW90)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (S900)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (PR90)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (S900)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (TZ90)
        M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (S900)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (BF90)
        M1A3 (Local0, C016, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (S900)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-(Integer+String) after Buffer */

        Local0 = RefOf (B900)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (B900)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (P900)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (B900)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (F900)
        M1A3 (Local0, C00D, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (B900)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (D900)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (B900)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (E900)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (B900)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (M901)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (B900)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (MX90)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (B900)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (R900)
        M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (B900)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (PW90)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (B900)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (PR90)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (B900)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (TZ90)
        M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (B900)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (BF90)
        M1A3 (Local0, C016, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (B900)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-(...) after Package */

        Local0 = RefOf (P900)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (P900)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (F900)
        M1A3 (Local0, C00D, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (P900)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (D900)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (P900)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (E900)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (P900)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (M901)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (P900)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (MX90)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (P900)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (R900)
        M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (P900)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (PW90)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (P900)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (PR90)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (P900)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (TZ90)
        M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (P900)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (BF90)
        M1A3 (Local0, C016, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (P900)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-(...) after Field Unit */

        Local0 = RefOf (F900)
        M1A3 (Local0, C00D, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (F900)
        M1A3 (Local0, C00D, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (D900)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (F900)
        M1A3 (Local0, C00D, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (E900)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (F900)
        M1A3 (Local0, C00D, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (M901)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (F900)
        M1A3 (Local0, C00D, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (MX90)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (F900)
        M1A3 (Local0, C00D, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (R900)
        M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (F900)
        M1A3 (Local0, C00D, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (PW90)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (F900)
        M1A3 (Local0, C00D, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (PR90)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (F900)
        M1A3 (Local0, C00D, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (TZ90)
        M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (F900)
        M1A3 (Local0, C00D, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (BF90)
        M1A3 (Local0, C016, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (F900)
        M1A3 (Local0, C00D, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-(...) after Device */

        Local0 = RefOf (D900)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (D900)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (E900)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (D900)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (M901)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (D900)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (MX90)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (D900)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (R900)
        M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (D900)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (PW90)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (D900)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (PR90)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (D900)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (TZ90)
        M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (D900)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (BF90)
        M1A3 (Local0, C016, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (D900)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-(...) after Event */

        Local0 = RefOf (E900)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (E900)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (M901)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (E900)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (MX90)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (E900)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (R900)
        M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (E900)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (PW90)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (E900)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (PR90)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (E900)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (TZ90)
        M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (E900)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (BF90)
        M1A3 (Local0, C016, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (E900)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-(...) after Method */

        Local0 = RefOf (M901)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (M901)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (MX90)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (M901)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (R900)
        M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (M901)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (PW90)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (M901)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (PR90)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (M901)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (TZ90)
        M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (M901)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (BF90)
        M1A3 (Local0, C016, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (M901)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-(...) after Mutex */

        Local0 = RefOf (MX90)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (MX90)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (R900)
        M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (MX90)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (PW90)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (MX90)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (PR90)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (MX90)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (TZ90)
        M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (MX90)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (BF90)
        M1A3 (Local0, C016, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (MX90)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-(...) after Operation Region */

        Local0 = RefOf (R900)
        M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (R900)
        M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (PW90)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (R900)
        M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (PR90)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (R900)
        M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (TZ90)
        M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (R900)
        M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (BF90)
        M1A3 (Local0, C016, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (R900)
        M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-(...) after Power Resource */

        Local0 = RefOf (PW90)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (PW90)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (PR90)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (PW90)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (TZ90)
        M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (PW90)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (BF90)
        M1A3 (Local0, C016, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (PW90)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-(...) after Processor */

        Local0 = RefOf (PR90)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (PR90)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (TZ90)
        M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (PR90)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (BF90)
        M1A3 (Local0, C016, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (PR90)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-(...) after Thermal Zone */

        Local0 = RefOf (TZ90)
        M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (BF90)
        M1A3 (Local0, C016, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (TZ90)
        M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        /*///////////////////// All-(...) after Buffer Field */

        Local0 = RefOf (BF90)
        M1A3 (Local0, C016, Z108, __METHOD__, __LINE__)
        Local0 = RefOf (BF90)
        M1A3 (Local0, C016, Z108, __METHOD__, __LINE__)
    }

    /* CopyObject the result of Index to LocalX */

    Method (M1B6, 0, Serialized)
    {
        C081 = Z108 /* absolute index of file initiating the checking */ /* \Z108 */
        /* Computational Data */

        CopyObject (Local0 = S900 [0x01], Local1)
        M1A3 (Local0, C016, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C016, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = B900 [0x01], Local1)
        M1A3 (Local0, C016, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C016, Z108, __METHOD__, __LINE__)
        /* Elements of Package are Uninitialized */

        If (Y127)
        {
            CopyObject (Local0 = P900 [0x00], Local1)
            M1A3 (Local0, C008, Z108, __METHOD__, __LINE__)
            M1A3 (Local1, C008, Z108, __METHOD__, __LINE__)
        }

        /* Elements of Package are Computational Data */

        CopyObject (Local0 = P901 [0x01], Local1)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C009, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P904 [0x01], Local1)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C00B, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P905 [0x00], Local1)
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C00C, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P90D [0x00], Local1)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C009, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P90E [0x00], Local1)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C009, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P90F [0x00], Local1)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C00A, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P910 [0x00], Local1)
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C00A, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P911 [0x00], Local1)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C00B, Z108, __METHOD__, __LINE__)
        /* These objects become an integer in a package */

        CopyObject (Local0 = P912 [0x00], Local1)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C009, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P913 [0x00], Local1)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C009, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P914 [0x00], Local1)
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C009, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P915 [0x00], Local1)
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C00B, Z108, __METHOD__, __LINE__)
        /* Elements of Package are NOT Computational Data */

        CopyObject (Local0 = P916 [0x00], Local1)
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C00E, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P917 [0x00], Local1)
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C00F, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P918 [0x00], Local1)
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C011, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P919 [0x00], Local1)
        M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C012, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P91A [0x00], Local1)
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C013, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P91B [0x00], Local1)
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C014, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P91C [0x00], Local1)
        M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C015, Z108, __METHOD__, __LINE__)
        /* Elements of Package are Methods */

        CopyObject (Local0 = P91D [0x00], Local1)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P91E [0x00], Local1)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P91F [0x00], Local1)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P920 [0x00], Local1)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P921 [0x00], Local1)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P922 [0x00], Local1)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P923 [0x00], Local1)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P924 [0x00], Local1)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P925 [0x00], Local1)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P926 [0x00], Local1)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P927 [0x00], Local1)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P928 [0x00], Local1)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P929 [0x00], Local1)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P92A [0x00], Local1)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P92B [0x00], Local1)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P92C [0x00], Local1)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P92D [0x00], Local1)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P92E [0x00], Local1)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P92F [0x00], Local1)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P930 [0x00], Local1)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P931 [0x00], Local1)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P932 [0x00], Local1)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P933 [0x00], Local1)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P934 [0x00], Local1)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P935 [0x00], Local1)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P936 [0x00], Local1)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P937 [0x00], Local1)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P938 [0x00], Local1)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P939 [0x00], Local1)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P93A [0x00], Local1)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        CopyObject (Local0 = P93B [0x00], Local1)
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        M1A6 ()
    }

    /* Store the result of Index to LocalX. */
    /* */
    /* The same as m1b6 but Store instead of CopyObject. */
    Method (M1B7, 0, Serialized)
    {
        C081 = Z108 /* absolute index of file initiating the checking */ /* \Z108 */
        /* Computational Data */

        Local1 = Local0 = S900 [0x01]
        M1A3 (Local0, C016, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C016, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = B900 [0x01]
        M1A3 (Local0, C016, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C016, Z108, __METHOD__, __LINE__)
        /* Elements of Package are Uninitialized */

        Local1 = Local0 = P900 [0x00]
        M1A3 (Local0, C008, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C008, Z108, __METHOD__, __LINE__)
        /* Elements of Package are Computational Data */

        Local1 = Local0 = P901 [0x01]
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C009, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P904 [0x01]
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C00B, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P905 [0x00]
        M1A3 (Local0, C00C, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C00C, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P90D [0x00]
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C009, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P90E [0x00]
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C009, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P90F [0x00]
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C00A, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P910 [0x00]
        M1A3 (Local0, C00A, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C00A, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P911 [0x00]
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C00B, Z108, __METHOD__, __LINE__)
        /* These objects become an integer in a package */

        Local1 = Local0 = P912 [0x00]
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C009, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P913 [0x00]
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C009, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P914 [0x00]
        M1A3 (Local0, C009, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C009, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P915 [0x00]
        M1A3 (Local0, C00B, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C00B, Z108, __METHOD__, __LINE__)
        /* Elements of Package are NOT Computational Data */

        Local1 = Local0 = P916 [0x00]
        M1A3 (Local0, C00E, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C00E, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P917 [0x00]
        M1A3 (Local0, C00F, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C00F, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P918 [0x00]
        M1A3 (Local0, C011, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C011, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P919 [0x00]
        M1A3 (Local0, C012, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C012, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P91A [0x00]
        M1A3 (Local0, C013, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C013, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P91B [0x00]
        M1A3 (Local0, C014, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C014, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P91C [0x00]
        M1A3 (Local0, C015, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C015, Z108, __METHOD__, __LINE__)
        /* Elements of Package are Methods */

        Local1 = Local0 = P91D [0x00]
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P91E [0x00]
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P91F [0x00]
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P920 [0x00]
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P921 [0x00]
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P922 [0x00]
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P923 [0x00]
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P924 [0x00]
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P925 [0x00]
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P926 [0x00]
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P927 [0x00]
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P928 [0x00]
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P929 [0x00]
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P92A [0x00]
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P92B [0x00]
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P92C [0x00]
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P92D [0x00]
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P92E [0x00]
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P92F [0x00]
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P930 [0x00]
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P931 [0x00]
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P932 [0x00]
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P933 [0x00]
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P934 [0x00]
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P935 [0x00]
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P936 [0x00]
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P937 [0x00]
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P938 [0x00]
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P939 [0x00]
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P93A [0x00]
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        Local1 = Local0 = P93B [0x00]
        M1A3 (Local0, C010, Z108, __METHOD__, __LINE__)
        M1A3 (Local1, C010, Z108, __METHOD__, __LINE__)
        M1A6 ()
    }

    Method (M1C0, 0, NotSerialized)
    {
        C081 = Z108       /* absolute index of file initiating the checking */ /* \Z108 */
        C089 = 0x00      /* flag of Reference, object otherwise */
        M1B0 ()
    }
