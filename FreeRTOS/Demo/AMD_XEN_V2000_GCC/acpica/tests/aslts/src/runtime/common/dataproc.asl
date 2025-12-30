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
    Name (Z114, 0x72)
    /* Check the type of Object */
    /* arg0 - Object */
    /* arg1 - expected type */
    /* arg2 - absolute index of file initiating the checking */
    /* arg3 - the name of Method initiating the checking */
    /* arg4 - index of checking (inside the file) */
    Method (M1A3, 5, NotSerialized)
    {
        Local7 = 0x01
        Local0 = ObjectType (Arg0)
        If ((Local0 != Arg1))
        {
            ERR ("m1a3", Z114, __LINE__, Arg2, Arg4, Local0, Arg1)
            Local7 = 0x00
        }

        Return (Local7)
    }

    /* Check that all the data (global) are not corrupted */

    Method (M1A6, 0, Serialized)
    {
        Name (TS, "m1a6")
        /* Computational Data */
        /* Integer */
        Local0 = ObjectType (I900)
        If ((Local0 != C009))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local0, C009)
        }

        If ((I900 != 0xFE7CB391D65A0000))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, I900, 0xFE7CB391D65A0000)
        }

        Local0 = ObjectType (I901)
        If ((Local0 != C009))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local0, C009)
        }

        If ((I901 != 0xC1790001))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, I901, 0xC1790001)
        }

        Local0 = ObjectType (I902)
        If ((Local0 != C009))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local0, C009)
        }

        If ((I902 != 0x00))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, I902, 0x00)
        }

        Local0 = ObjectType (I903)
        If ((Local0 != C009))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local0, C009)
        }

        If ((I903 != 0xFFFFFFFFFFFFFFFF))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, I903, 0xFFFFFFFFFFFFFFFF)
        }

        Local0 = ObjectType (I904)
        If ((Local0 != C009))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local0, C009)
        }

        If ((I904 != 0xFFFFFFFF))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, I904, 0xFFFFFFFF)
        }

        /* String */

        Local0 = ObjectType (S900)
        If ((Local0 != C00A))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local0, C00A)
        }

        If ((S900 != "12340002"))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, S900, "12340002")
        }

        Local0 = ObjectType (S901)
        If ((Local0 != C00A))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local0, C00A)
        }

        If ((S901 != "qwrtyu0003"))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, S901, "qwrtyu0003")
        }

        /* Buffer */

        Local0 = ObjectType (B900)
        If ((Local0 != C00B))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local0, C00B)
        }

        If ((B900 != Buffer (0x05)
                    {
                         0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
                    }))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, B900, Buffer (0x05)
                {
                     0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
                })
        }

        /* Buffer Field */

        Local0 = ObjectType (BF90)
        If ((Local0 != C016))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local0, C016)
        }

        Local1 = Buffer (0x1) { 0xB0}
        If (BF90 != Local1)
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, BF90, Local1)
        }

        /* One level Package */

        Store (P900 [0x00], Local0)
        Local1 = ObjectType (Local0)
        If ((Local1 != C008))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local1, C008)
        }

        Store (P901 [0x00], Local0)
        Local1 = DerefOf (Local0)
        Local2 = ObjectType (Local1)
        If ((Local2 != C009))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local2, C009)
        }

        If ((Local1 != 0xABCD0004))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local1, 0xABCD0004)
        }

        Store (P901 [0x01], Local0)
        Local1 = DerefOf (Local0)
        Local2 = ObjectType (Local1)
        If ((Local2 != C009))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local2, C009)
        }

        If ((Local1 != 0x1122334455660005))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local1, 0x1122334455660005)
        }

        Store (P902 [0x00], Local0)
        Local1 = DerefOf (Local0)
        Local2 = ObjectType (Local1)
        If ((Local2 != C00A))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local2, C00A)
        }

        If ((Local1 != "12340006"))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local1, "12340006")
        }

        Store (P902 [0x01], Local0)
        Local1 = DerefOf (Local0)
        Local2 = ObjectType (Local1)
        If ((Local2 != C00A))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local2, C00A)
        }

        If ((Local1 != "q1w2e3r4t5y6u7i80007"))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local1, "q1w2e3r4t5y6u7i80007")
        }

        Store (P903 [0x00], Local0)
        Local1 = DerefOf (Local0)
        Local2 = ObjectType (Local1)
        If ((Local2 != C00A))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local2, C00A)
        }

        If ((Local1 != "qwrtyuiop0008"))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local1, "qwrtyuiop0008")
        }

        Store (P903 [0x01], Local0)
        Local1 = DerefOf (Local0)
        Local2 = ObjectType (Local1)
        If ((Local2 != C00A))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local2, C00A)
        }

        If ((Local1 != "1234567890abdef0250009"))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local1, "1234567890abdef0250009")
        }

        Store (P904 [0x00], Local0)
        Local1 = DerefOf (Local0)
        Local2 = ObjectType (Local1)
        If ((Local2 != C00B))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local2, C00B)
        }

        If ((Local1 != Buffer (0x03)
                    {
                         0xB5, 0xB6, 0xB7                                 // ...
                    }))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local1, Buffer (0x03)
                {
                     0xB5, 0xB6, 0xB7                                 // ...
                })
        }

        Store (P904 [0x01], Local0)
        Local1 = DerefOf (Local0)
        Local2 = ObjectType (Local1)
        If ((Local2 != C00B))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local2, C00B)
        }

        If ((Local1 != Buffer (0x02)
                    {
                         0xB8, 0xB9                                       // ..
                    }))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local1, Buffer (0x02)
                {
                     0xB8, 0xB9                                       // ..
                })
        }

        /* Two level Package */

        Store (P905 [0x00], Local0)
        Local1 = DerefOf (Local0)
        Store (Local1 [0x00], Local2)
        Local3 = DerefOf (Local2)
        Local4 = ObjectType (Local3)
        If ((Local4 != C009))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local4, C009)
        }

        If ((Local3 != 0x0ABC000A))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local3, 0x0ABC000A)
        }

        Store (P905 [0x00], Local0)
        Local1 = DerefOf (Local0)
        Store (Local1 [0x01], Local2)
        Local3 = DerefOf (Local2)
        Local4 = ObjectType (Local3)
        If ((Local4 != C00A))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local4, C00A)
        }

        If ((Local3 != "0xabc000b"))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local3, "0xabc000b")
        }

        Store (P905 [0x00], Local0)
        Local1 = DerefOf (Local0)
        Store (Local1 [0x02], Local2)
        Local3 = DerefOf (Local2)
        Local4 = ObjectType (Local3)
        If ((Local4 != C00A))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local4, C00A)
        }

        If ((Local3 != "abc000c"))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local3, "abc000c")
        }

        Store (P906 [0x00], Local0)
        Local1 = DerefOf (Local0)
        Store (Local1 [0x00], Local2)
        Local3 = DerefOf (Local2)
        Local4 = ObjectType (Local3)
        If ((Local4 != C00A))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local4, C00A)
        }

        If ((Local3 != "abc000d"))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local3, "abc000d")
        }

        Store (P907 [0x00], Local0)
        Local1 = DerefOf (Local0)
        Store (Local1 [0x00], Local2)
        Local3 = DerefOf (Local2)
        Local4 = ObjectType (Local3)
        If ((Local4 != C00A))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local4, C00A)
        }

        If ((Local3 != "aqwevbgnm000e"))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local3, "aqwevbgnm000e")
        }

        Store (P908 [0x00], Local0)
        Local1 = DerefOf (Local0)
        Store (Local1 [0x00], Local2)
        Local3 = DerefOf (Local2)
        Local4 = ObjectType (Local3)
        If ((Local4 != C00B))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local4, C00B)
        }

        If ((Local3 != Buffer (0x05)
                    {
                         0xBA, 0xBB, 0xBC, 0xBD, 0xBE                     // .....
                    }))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local3, Buffer (0x05)
                {
                     0xBA, 0xBB, 0xBC, 0xBD, 0xBE                     // .....
                })
        }

        /* Three level Package */

        Store (P909 [0x00], Local0)
        Local1 = DerefOf (Local0)
        Store (Local1 [0x00], Local2)
        Local3 = DerefOf (Local2)
        Store (Local3 [0x00], Local4)
        Local5 = DerefOf (Local4)
        Local6 = ObjectType (Local5)
        If ((Local6 != C009))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local6, C009)
        }

        If ((Local5 != 0x0ABC000F))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local5, 0x0ABC000F)
        }

        Store (P90A [0x00], Local0)
        Local1 = DerefOf (Local0)
        Store (Local1 [0x00], Local2)
        Local3 = DerefOf (Local2)
        Store (Local3 [0x00], Local4)
        Local5 = DerefOf (Local4)
        Local6 = ObjectType (Local5)
        If ((Local6 != C00A))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local6, C00A)
        }

        If ((Local5 != "12340010"))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local5, "12340010")
        }

        Store (P90B [0x00], Local0)
        Local1 = DerefOf (Local0)
        Store (Local1 [0x00], Local2)
        Local3 = DerefOf (Local2)
        Store (Local3 [0x00], Local4)
        Local5 = DerefOf (Local4)
        Local6 = ObjectType (Local5)
        If ((Local6 != C00A))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local6, C00A)
        }

        If ((Local5 != "zxswefas0011"))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local5, "zxswefas0011")
        }

        Store (P90C [0x00], Local0)
        Local1 = DerefOf (Local0)
        Store (Local1 [0x00], Local2)
        Local3 = DerefOf (Local2)
        Store (Local3 [0x00], Local4)
        Local5 = DerefOf (Local4)
        Local6 = ObjectType (Local5)
        If ((Local6 != C00B))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local6, C00B)
        }

        If ((Local5 != Buffer (0x03)
                    {
                         0xBF, 0xC0, 0xC1                                 // ...
                    }))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local5, Buffer (0x03)
                {
                     0xBF, 0xC0, 0xC1                                 // ...
                })
        }

        /* Additional Packages */
        /* p953 */
        Store (P953 [0x00], Local0)
        Local1 = DerefOf (Local0)
        Local2 = ObjectType (Local1)
        If ((Local2 != C009))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local2, C009)
        }

        If ((Local1 != 0xABCD0018))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local1, 0xABCD0018)
        }

        Store (P953 [0x01], Local0)
        Local1 = DerefOf (Local0)
        Local2 = ObjectType (Local1)
        If ((Local2 != C009))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local2, C009)
        }

        If ((Local1 != 0xABCD0019))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local1, 0xABCD0019)
        }

        /* p955 */

        M1AF (P955, 0x01, 0x01, 0x00)
        /* Not Computational Data */

        M1AA (TS, E900, C00F, 0x00, 0x013B)
        M1AA (TS, MX90, C011, 0x00, 0x013C)
        M1AA (TS, D900, C00E, 0x00, 0x013D)
        If (Y508)
        {
            M1AA (TS, TZ90, C015, 0x00, 0x013E)
        }

        M1AA (TS, PR90, C014, 0x00, 0x013F)
        M1AA (TS, R900, C012, 0x00, 0x0140)
        M1AA (TS, PW90, C013, 0x00, 0x0141)
        /* Field Unit (Field) */

        Local0 = ObjectType (F900)
        If ((Local0 != C00D))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local0, C00D)
        }

        Local0 = ObjectType (F901)
        If ((Local0 != C00D))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local0, C00D)
        }

        Local0 = ObjectType (F902)
        If ((Local0 != C00D))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local0, C00D)
        }

        Local0 = ObjectType (F903)
        If ((Local0 != C00D))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local0, C00D)
        }

        /* Field Unit (IndexField) */

        Local0 = ObjectType (IF90)
        If ((Local0 != C00D))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local0, C00D)
        }

        Local0 = ObjectType (IF91)
        If ((Local0 != C00D))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local0, C00D)
        }

        /* Field Unit (BankField) */

        Local0 = ObjectType (BN90)
        If ((Local0 != C00D))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local0, C00D)
        }
        /*
     *	if (LNotEqual(f900, 0xd7)) {
     *		err(ts, z114, __LINE__, 0, 0, f900, 0xd7)
     *	}
     *
     *	if (LNotEqual(if90, 0xd7)) {
     *		err(ts, z114, __LINE__, 0, 0, if90, 0xd7)
     *	}
     */
    }

    /* Verifying result */
    /* arg0 - test name */
    /* arg1 - object */
    /* arg2 - expected type of object */
    /* arg3 - expected value of object */
    /* arg4 - index of checking (inside the file) */
    Method (M1AA, 5, NotSerialized)
    {
        Local7 = 0x00
        Local0 = ObjectType (Arg1)
        If ((Local0 != Arg2))
        {
            ERR (Arg0, Z114, __LINE__, 0x00, Arg4, Local0, Arg2)
            Local7 = 0x01
        }
        ElseIf ((Arg2 < C00C))
        {
            If ((Arg1 != Arg3))
            {
                ERR (Arg0, Z114, __LINE__, 0x00, Arg4, Arg1, Arg3)
                Local7 = 0x01
            }
        }

        Return (Local7)
    }

    /* Check and restore the global data after writing into them */

    Method (M1AB, 0, Serialized)
    {
        Name (TS, "m1ab")
        /* Computational Data */

        M1AA (TS, I900, C009, C08A, 0x0144)
        M1AA (TS, I901, C009, C08A, 0x0145)
        M1AA (TS, S900, C009, C08A, 0x0146)
        M1AA (TS, S901, C009, C08A, 0x0147)
        M1AA (TS, B900, C009, C08A, 0x0148)
        /* Package */

        M1AA (TS, P953, C009, C08A, 0x0149)
        /* Not Computational Data */

        M1AA (TS, E900, C009, C08A, 0x014A)
        M1AA (TS, MX90, C009, C08A, 0x014B)
        M1AA (TS, D900, C009, C08A, 0x014C)
        If (Y508)
        {
            M1AA (TS, TZ90, C009, C08A, 0x014D)
        }

        M1AA (TS, PR90, C009, C08A, 0x014E)
        If (Y510)
        {
            M1AA (TS, R900, C009, C08A, 0x014F)
        }

        M1AA (TS, PW90, C009, C08A, 0x0150)
        M1AC ()
        M1A6 ()
    }

    /* Restore the global data after writing into them */

    Method (M1AC, 0, NotSerialized)
    {
        /* Computational Data */

        CopyObject (I9Z0, I900) /* \I900 */
        CopyObject (I9Z1, I901) /* \I901 */
        CopyObject (S9Z0, S900) /* \S900 */
        CopyObject (S9Z1, S901) /* \S901 */
        CopyObject (B9Z0, B900) /* \B900 */
        /* Package */

        CopyObject (P954, P953) /* \P953 */
        /* Restore p955 Package */

        M1C6 ()
        /* Not Computational Data */

        CopyObject (E9Z0, E900) /* \E900 */
        CopyObject (MX91, MX90) /* \MX90 */
        CopyObject (D9Z0, D900) /* \D900 */
        If (Y508)
        {
            CopyObject (TZ91, TZ90) /* \TZ90 */
        }

        CopyObject (PR91, PR90) /* \PR90 */
        If (Y510)
        {
            CopyObject (R9Z0, R900) /* \R900 */
        }

        CopyObject (PW91, PW90) /* \PW90 */
    }

    /* Verify p955-like Package */
    /* arg0 - Package */
    /* arg1 - check for non-computational data */
    /* arg2 - check Field Unit and Buffer Field */
    /* arg3 - elements of Package are RefOf_References */
    Method (M1AF, 4, Serialized)
    {
        Name (TS, "m1af")
        Store (Arg0 [0x00], Local0)
        Local1 = ObjectType (Local0)
        If ((Local1 != C009))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local1, C009)
        }
        Else
        {
            Local1 = DerefOf (Local0)
            If ((Local1 != 0x00))
            {
                ERR (TS, Z113, __LINE__, 0x00, 0x00, Local1, 0x00)
            }
        }

        Store (Arg0 [0x01], Local0)
        Local1 = ObjectType (Local0)
        If ((Local1 != C009))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local1, C009)
        }
        Else
        {
            Local1 = DerefOf (Local0)
            If (Arg3)
            {
                Local2 = DerefOf (Local1)
                Local1 = Local2
            }

            If ((Local1 != 0xFE7CB391D65A0000))
            {
                ERR (TS, Z114, __LINE__, 0x00, 0x00, Local1, 0xFE7CB391D65A0000)
            }
        }

        Store (Arg0 [0x02], Local0)
        Local1 = ObjectType (Local0)
        If ((Local1 != C00A))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local1, C00A)
        }
        Else
        {
            Local1 = DerefOf (Local0)
            If (Arg3)
            {
                Local2 = DerefOf (Local1)
                Local1 = Local2
            }

            If ((Local1 != "12340002"))
            {
                ERR (TS, Z114, __LINE__, 0x00, 0x00, Local1, "12340002")
            }
        }

        Store (Arg0 [0x03], Local0)
        Local1 = ObjectType (Local0)
        If ((Local1 != C00B))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local1, C00A)
        }
        Else
        {
            Local1 = DerefOf (Local0)
            If (Arg3)
            {
                Local2 = DerefOf (Local1)
                Local1 = Local2
            }

            If ((Local1 != Buffer (0x05)
                        {
                             0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
                        }))
            {
                ERR (TS, Z114, __LINE__, 0x00, 0x00, Local1, Buffer (0x05)
                    {
                         0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
                    })
            }
        }

        Store (Arg0 [0x04], Local0)
        M1AA (TS, Local0, C00C, 0x00, 0x013F)
        /* 5th element is a region field, which will be resolved to an integer */

        If (Arg2)
        {
            Store (Arg0 [0x05], Local0)
            Local1 = ObjectType (Local0)
            Local7 = DerefOf (Local0)
            If (Arg3)
            {
                If ((Local1 != C00D))
                {
                    ERR (TS, Z114, __LINE__, 0x00, 0x00, Local1, C00D)
                }
                Else
                {
                    Local6 = DerefOf (Local7)
                    Local7 = Local6
                }
            }

            Local5 = ObjectType (Local7)
            If ((Local5 != C009))
            {
                ERR (TS, Z114, __LINE__, 0x00, 0x00, Local5, C009)
            }
            ElseIf ((Local7 != 0x00))
            {
                ERR (TS, Z114, __LINE__, 0x00, 0x00, Local7, 0x00)
            }
        }

        If (Arg1)
        {
            Store (Arg0 [0x06], Local0)
            M1AA (TS, Local0, C00E, 0x00, 0x013F)
            Store (Arg0 [0x07], Local0)
            M1AA (TS, Local0, C00F, 0x00, 0x013F)
            Store (Arg0 [0x08], Local0)
            M1AA (TS, Local0, C010, 0x00, 0x013F)
            Store (Arg0 [0x09], Local0)
            M1AA (TS, Local0, C011, 0x00, 0x013F)
            Store (Arg0 [0x0A], Local0)
            M1AA (TS, Local0, C012, 0x00, 0x013F)
            Store (Arg0 [0x0B], Local0)
            M1AA (TS, Local0, C013, 0x00, 0x013F)
            Store (Arg0 [0x0C], Local0)
            M1AA (TS, Local0, C014, 0x00, 0x013F)
            Store (Arg0 [0x0D], Local0)
            M1AA (TS, Local0, C015, 0x00, 0x013F)
        }

        /* 14th element is a buffer field created by CreateField, which will be resolved to a buffer */

        If (Arg2)
        {
            Store (Arg0 [0x0E], Local0)
            Local1 = ObjectType (Local0)
            Local7 = DerefOf (Local0)
            If (Arg3)
            {
                If ((Local1 != C016))
                {
                    ERR (TS, Z114, __LINE__, 0x00, 0x00, Local1, C016)
                }
                Else
                {
                    Local6 = DerefOf (Local7)
                    Local7 = Local6
                }
            }

            Local5 = ObjectType (Local7)
            If ((Local5 != C00B))
            {
                ERR (TS, Z114, __LINE__, 0x00, 0x00, Local5, C00B)
            }
            ElseIf ((Local7 != Buffer(){0xB0}))
            {
                ERR (TS, Z114, __LINE__, 0x00, 0x00, Local7, Buffer(){0xB0})
            }
        }

        Store (Arg0 [0x0F], Local0)
        Local1 = ObjectType (Local0)
        If ((Local1 != C009))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local1, C009)
        }
        Else
        {
            Local1 = DerefOf (Local0)
            If ((Local1 != 0x0F))
            {
                ERR (TS, Z114, __LINE__, 0x00, 0x00, Local1, 0x0F)
            }
        }

        Store (Arg0 [0x10], Local0)
        Local1 = ObjectType (Local0)
        If ((Local1 != C009))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local1, C009)
        }
        Else
        {
            Local1 = DerefOf (Local0)
            If ((Local1 != 0x10))
            {
                ERR (TS, Z114, __LINE__, 0x00, 0x00, Local1, 0x10)
            }
        }

        Store (Arg0 [0x11], Local0)
        Local1 = ObjectType (Local0)
        If ((Local1 != C008))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, Local1, C008)
        }

        /* Evaluation of Method m936 takes place */

        If ((I905 != 0xABCD001A))
        {
            ERR (TS, Z114, __LINE__, 0x00, 0x00, I905, 0xABCD001A)
        }
    }

    /* Restore p955 Package */

    Method (M1C6, 0, NotSerialized)
    {
        CopyObject (P956, P955) /* \P955 */
        I905 = I9Z5 /* \I9Z5 */
    }
