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
     *
     * Different type data for different needs
     *
     */
    /*
     SEE: uncomment m918 after fixing bug (?) of ACPICA
     SEE: uncomment below:
     //	Method(m918) { return (tz90) }
     */
    Name (Z113, 0x71)
    /* Not Computational Data */

    Event (E900)
    Event (E9Z0)
    Mutex (MX90, 0x00)
    Mutex (MX91, 0x00)
    Device (D900)
    {
        Name (I900, 0xABCD0017)
    }

    Device (D9Z0)
    {
        Name (I900, 0xABCD0017)
    }

    ThermalZone (TZ90)
    {
    }

    ThermalZone (TZ91)
    {
    }

    Processor (PR90, 0x00, 0xFFFFFFFF, 0x00){}
    Processor (PR91, 0x00, 0xFFFFFFFF, 0x00){}
    OperationRegion (R900, SystemMemory, 0x0100, 0x0100)
    OperationRegion (R9Z0, SystemMemory, 0x0100, 0x0100)
    PowerResource (PW90, 0x01, 0x0000)
    {
        Method (MMMM, 0, NotSerialized)
        {
            Return (0x00)
        }
    }

    PowerResource (PW91, 0x01, 0x0000)
    {
        Method (MMMM, 0, NotSerialized)
        {
            Return (0x00)
        }
    }

    /* Computational Data */

    Name (I900, 0xFE7CB391D65A0000)
    Name (I9Z0, 0xFE7CB391D65A0000)
    Name (I901, 0xC1790001)
    Name (I9Z1, 0xC1790001)
    Name (I902, 0x00)
    Name (I903, 0xFFFFFFFFFFFFFFFF)
    Name (I904, 0xFFFFFFFF)
    Name (S900, "12340002")
    Name (S9Z0, "12340002")
    Name (S901, "qwrtyu0003")
    Name (S9Z1, "qwrtyu0003")
    Name (B900, Buffer (0x05)
    {
         0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
    })
    Name (B9Z0, Buffer (0x05)
    {
         0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
    })
    CreateField (B9Z0, 0x00, 0x08, BF90)
    Field (R9Z0, ByteAcc, NoLock, Preserve)
    {
        F900,   8,
        F901,   8,
        F902,   8,
        F903,   8
    }

    BankField (R9Z0, F901, 0x00, ByteAcc, NoLock, Preserve)
    {
        BN90,   4
    }

    IndexField (F902, F903, ByteAcc, NoLock, Preserve)
    {
        IF90,   8,
        IF91,   8
    }

    /* Elements of Package are Uninitialized */

    Name (P900, Package (0x01){})
    /* Elements of Package are Computational Data */

    Name (P901, Package (0x02)
    {
        0xABCD0004,
        0x1122334455660005
    })
    Name (P902, Package (0x02)
    {
        "12340006",
        "q1w2e3r4t5y6u7i80007"
    })
    Name (P903, Package (0x02)
    {
        "qwrtyuiop0008",
        "1234567890abdef0250009"
    })
    Name (P904, Package (0x02)
    {
        Buffer (0x03)
        {
             0xB5, 0xB6, 0xB7                                 // ...
        },

        Buffer (0x02)
        {
             0xB8, 0xB9                                       // ..
        }
    })
    Name (P905, Package (0x01)
    {
        Package (0x03)
        {
            0x0ABC000A,
            "0xabc000b",
            "abc000c"
        }
    })
    Name (P906, Package (0x01)
    {
        Package (0x01)
        {
            "abc000d"
        }
    })
    Name (P907, Package (0x01)
    {
        Package (0x01)
        {
            "aqwevbgnm000e"
        }
    })
    Name (P908, Package (0x01)
    {
        Package (0x01)
        {
            Buffer (0x05)
            {
                 0xBA, 0xBB, 0xBC, 0xBD, 0xBE                     // .....
            }
        }
    })
    Name (P909, Package (0x01)
    {
        Package (0x01)
        {
            Package (0x01)
            {
                0x0ABC000F
            }
        }
    })
    Name (P90A, Package (0x01)
    {
        Package (0x01)
        {
            Package (0x01)
            {
                "12340010"
            }
        }
    })
    Name (P90B, Package (0x01)
    {
        Package (0x01)
        {
            Package (0x01)
            {
                "zxswefas0011"
            }
        }
    })
    Name (P90C, Package (0x01)
    {
        Package (0x01)
        {
            Package (0x01)
            {
                Buffer (0x03)
                {
                     0xBF, 0xC0, 0xC1                                 // ...
                }
            }
        }
    })
    Name (P90D, Package (0x01)
    {
        I900
    })
    Name (P90E, Package (0x01)
    {
        I901
    })
    Name (P90F, Package (0x01)
    {
        S900
    })
    Name (P910, Package (0x01)
    {
        S901
    })
    Name (P911, Package (0x01)
    {
        B9Z0
    })
    Name (P912, Package (0x01)
    {
        F900
    })
    Name (P913, Package (0x01)
    {
        BN90
    })
    Name (P914, Package (0x01)
    {
        IF90
    })
    Name (P915, Package (0x01)
    {
        BF90
    })
    /* Elements of Package are NOT Computational Data */

    Name (P916, Package (0x01)
    {
        D900
    })
    Name (P917, Package (0x01)
    {
        E900
    })
    Name (P918, Package (0x01)
    {
        MX90
    })
    Name (P919, Package (0x01)
    {
        R9Z0
    })
    Name (P91A, Package (0x01)
    {
        PW90
    })
    Name (P91B, Package (0x01)
    {
        PR90
    })
    Name (P91C, Package (0x01)
    {
        TZ90
    })
    /* Methods */

    Method (M900, 0, NotSerialized)
    {
    }

    Method (M901, 0, NotSerialized)
    {
        Return (0x0ABC0012)
    }

    Method (M902, 0, NotSerialized)
    {
        Return ("zxvgswquiy0013")
    }

    Method (M903, 0, NotSerialized)
    {
        Return (Buffer (0x01)
        {
             0xC2                                             // .
        })
    }

    Method (M904, 0, NotSerialized)
    {
        Return (Package (0x01)
        {
            0x0ABC0014
        })
    }

    Method (M905, 0, NotSerialized)
    {
        Return (Package (0x01)
        {
            "lkjhgtre0015"
        })
    }

    Method (M906, 0, NotSerialized)
    {
        Return (Package (0x01)
        {
            Buffer (0x01)
            {
                 0xC3                                             // .
            }
        })
    }

    Method (M907, 0, NotSerialized)
    {
        Return (Package (0x01)
        {
            Package (0x01)
            {
                0x0ABC0016
            }
        })
    }

    Method (M908, 0, NotSerialized)
    {
        Return (I900) /* \I900 */
    }

    Method (M909, 0, NotSerialized)
    {
        Return (I901) /* \I901 */
    }

    Method (M90A, 0, NotSerialized)
    {
        Return (S900) /* \S900 */
    }

    Method (M90B, 0, NotSerialized)
    {
        Return (S901) /* \S901 */
    }

    Method (M90C, 0, NotSerialized)
    {
        Return (B9Z0) /* \B9Z0 */
    }

    Method (M90D, 0, NotSerialized)
    {
        Return (F900) /* \F900 */
    }

    Method (M90E, 0, NotSerialized)
    {
        Return (BN90) /* \BN90 */
    }

    Method (M90F, 0, NotSerialized)
    {
        Return (IF90) /* \IF90 */
    }

    Method (M910, 0, NotSerialized)
    {
        Return (BF90) /* \BF90 */
    }

    Method (M911, 0, NotSerialized)
    {
        Return (D900) /* \D900 */
    }

    Method (M912, 0, NotSerialized)
    {
        Return (E900) /* \E900 */
    }

    Method (M913, 0, NotSerialized)
    {
        Return (M901 ())
    }

    Method (M914, 0, NotSerialized)
    {
        Return (MX90) /* \MX90 */
    }

    Method (M915, 0, NotSerialized)
    {
        Return (R9Z0) /* \R9Z0 */
    }

    Method (M916, 0, NotSerialized)
    {
        Return (PW90) /* \PW90 */
    }

    Method (M917, 0, NotSerialized)
    {
        Return (PR90) /* \PR90 */
    }

    /*	Method(m918) { return (tz90) } */

    Method (M918, 0, NotSerialized)
    {
        Return (0x00)
    }

    Method (M919, 0, NotSerialized)
    {
        Return (P900) /* \P900 */
    }

    Method (M91A, 0, NotSerialized)
    {
        Return (P901) /* \P901 */
    }

    Method (M91B, 0, NotSerialized)
    {
        Return (P902) /* \P902 */
    }

    Method (M91C, 0, NotSerialized)
    {
        Return (P903) /* \P903 */
    }

    Method (M91D, 0, NotSerialized)
    {
        Return (P904) /* \P904 */
    }

    Method (M91E, 0, NotSerialized)
    {
        Return (P905) /* \P905 */
    }

    Method (M91F, 0, NotSerialized)
    {
        Return (P906) /* \P906 */
    }

    Method (M920, 0, NotSerialized)
    {
        Return (P907) /* \P907 */
    }

    Method (M921, 0, NotSerialized)
    {
        Return (P908) /* \P908 */
    }

    Method (M922, 0, NotSerialized)
    {
        Return (P909) /* \P909 */
    }

    Method (M923, 0, NotSerialized)
    {
        Return (P90A) /* \P90A */
    }

    Method (M924, 0, NotSerialized)
    {
        Return (P90B) /* \P90B */
    }

    Method (M925, 0, NotSerialized)
    {
        Return (P90C) /* \P90C */
    }

    Method (M926, 0, NotSerialized)
    {
        Return (P90D) /* \P90D */
    }

    Method (M927, 0, NotSerialized)
    {
        Return (P90E) /* \P90E */
    }

    Method (M928, 0, NotSerialized)
    {
        Return (P90F) /* \P90F */
    }

    Method (M929, 0, NotSerialized)
    {
        Return (P910) /* \P910 */
    }

    Method (M92A, 0, NotSerialized)
    {
        Return (P911) /* \P911 */
    }

    Method (M92B, 0, NotSerialized)
    {
        Return (P912) /* \P912 */
    }

    Method (M92C, 0, NotSerialized)
    {
        Return (P913) /* \P913 */
    }

    Method (M92D, 0, NotSerialized)
    {
        Return (P914) /* \P914 */
    }

    Method (M92E, 0, NotSerialized)
    {
        Return (P915) /* \P915 */
    }

    Method (M92F, 0, NotSerialized)
    {
        Return (P916) /* \P916 */
    }

    Method (M930, 0, NotSerialized)
    {
        Return (P917) /* \P917 */
    }

    Method (M931, 0, NotSerialized)
    {
        Return (P918) /* \P918 */
    }

    Method (M932, 0, NotSerialized)
    {
        Return (P919) /* \P919 */
    }

    Method (M933, 0, NotSerialized)
    {
        Return (P91A) /* \P91A */
    }

    Method (M934, 0, NotSerialized)
    {
        Return (P91B) /* \P91B */
    }

    Method (M935, 0, NotSerialized)
    {
        Return (P91C) /* \P91C */
    }

    /* Elements of Package are Methods */

    Name (P91D, Package (0x01)
    {
        M900
    })
    Name (P91E, Package (0x01)
    {
        M901
    })
    Name (P91F, Package (0x01)
    {
        M902
    })
    Name (P920, Package (0x01)
    {
        M903
    })
    Name (P921, Package (0x01)
    {
        M904
    })
    Name (P922, Package (0x01)
    {
        M905
    })
    Name (P923, Package (0x01)
    {
        M906
    })
    Name (P924, Package (0x01)
    {
        M907
    })
    Name (P925, Package (0x01)
    {
        M908
    })
    Name (P926, Package (0x01)
    {
        M909
    })
    Name (P927, Package (0x01)
    {
        M90A
    })
    Name (P928, Package (0x01)
    {
        M90B
    })
    Name (P929, Package (0x01)
    {
        M90C
    })
    Name (P92A, Package (0x01)
    {
        M90D
    })
    Name (P92B, Package (0x01)
    {
        M90E
    })
    Name (P92C, Package (0x01)
    {
        M90F
    })
    Name (P92D, Package (0x01)
    {
        M910
    })
    Name (P92E, Package (0x01)
    {
        M911
    })
    Name (P92F, Package (0x01)
    {
        M912
    })
    Name (P930, Package (0x01)
    {
        M913
    })
    Name (P931, Package (0x01)
    {
        M914
    })
    Name (P932, Package (0x01)
    {
        M915
    })
    Name (P933, Package (0x01)
    {
        M916
    })
    Name (P934, Package (0x01)
    {
        M917
    })
    If (Y103)
    {
        Name (P935, Package (0x01)
        {
            M918
        })
    }

    Name (P936, Package (0x01)
    {
        M919
    })
    Name (P937, Package (0x01)
    {
        M91A
    })
    Name (P938, Package (0x01)
    {
        M91B
    })
    Name (P939, Package (0x01)
    {
        M91C
    })
    Name (P93A, Package (0x01)
    {
        M91D
    })
    Name (P93B, Package (0x01)
    {
        M91E
    })
    Name (P93C, Package (0x01)
    {
        M91F
    })
    Name (P93D, Package (0x01)
    {
        M920
    })
    Name (P93E, Package (0x01)
    {
        M921
    })
    Name (P93F, Package (0x01)
    {
        M922
    })
    Name (P940, Package (0x01)
    {
        M923
    })
    Name (P941, Package (0x01)
    {
        M924
    })
    Name (P942, Package (0x01)
    {
        M925
    })
    Name (P943, Package (0x01)
    {
        M926
    })
    Name (P944, Package (0x01)
    {
        M927
    })
    Name (P945, Package (0x01)
    {
        M928
    })
    Name (P946, Package (0x01)
    {
        M929
    })
    Name (P947, Package (0x01)
    {
        M92A
    })
    Name (P948, Package (0x01)
    {
        M92B
    })
    Name (P949, Package (0x01)
    {
        M92C
    })
    Name (P94A, Package (0x01)
    {
        M92D
    })
    Name (P94B, Package (0x01)
    {
        M92E
    })
    Name (P94C, Package (0x01)
    {
        M92F
    })
    Name (P94D, Package (0x01)
    {
        M930
    })
    Name (P94E, Package (0x01)
    {
        M931
    })
    Name (P94F, Package (0x01)
    {
        M932
    })
    Name (P950, Package (0x01)
    {
        M933
    })
    Name (P951, Package (0x01)
    {
        M934
    })
    Name (P952, Package (0x01)
    {
        M935
    })
    Name (P953, Package (0x02)
    {
        0xABCD0018,
        0xABCD0019
    })
    Name (P954, Package (0x02)
    {
        0xABCD0018,
        0xABCD0019
    })
    Name (I905, 0xABCD001A)
    Name (I9Z5, 0xABCD001A)
    Method (M936, 0, NotSerialized)
    {
        I905 = 0x00
        Return (MX90) /* \MX90 */
    }

    Name (P955, Package (0x12)
    {
        0x00,
        I900,
        S900,
        B900,
        P953,
        F900,
        D900,
        E900,
        M936,
        MX90,
        R900,
        PW90,
        PR90,
        TZ90,
        BF90,
        0x0F,
        0x10
    })
    Name (P956, Package (0x12)
    {
        0x00,
        I900,
        S900,
        B900,
        P953,
        F900,
        D900,
        E900,
        M936,
        MX90,
        R900,
        PW90,
        PR90,
        TZ90,
        BF90,
        0x0F,
        0x10
    })
    /* Global Standard Data */

    Name (IA00, 0x77)
    Name (SA00, "qwer0000")
    Name (BA00, Buffer (0x04)
    {
         0x01, 0x77, 0x03, 0x04                           // .w..
    })
    Name (PA00, Package (0x03)
    {
        0x05,
        0x77,
        0x07
    })
    Name (IA10, 0x77)
    Name (SA10, "qwer0000")
    Name (BA10, Buffer (0x04)
    {
         0x01, 0x77, 0x03, 0x04                           // .w..
    })
    Name (PA10, Package (0x03)
    {
        0x05,
        0x77,
        0x07
    })
    Name (IA01, 0x2B)
    Name (SA01, "qw+r0000")
    Name (BA01, Buffer (0x04)
    {
         0x01, 0x2B, 0x03, 0x04                           // .+..
    })
    Name (PA01, Package (0x03)
    {
        0x05,
        0x2B,
        0x07
    })
    Name (IA11, 0x2B)
    Name (SA11, "qw+r0000")
    Name (BA11, Buffer (0x04)
    {
         0x01, 0x2B, 0x03, 0x04                           // .+..
    })
    Name (PA11, Package (0x03)
    {
        0x05,
        0x2B,
        0x07
    })
