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
     *          (named objects, if present, are the local objects of Method)
     *
     * TABLE 1: all the legal ways to generate references to the
     *          immediate images (constants)
     * TABLE 2: all the legal ways to generate references to the
     *          named objects
     * TABLE 3: all the legal ways to generate references to the
     *          immediate images (constants) being elements of Package
     * TABLE 4: all the legal ways to generate references to the
     *          named objects being elements of Package
     *
     * Producing Reference operators:
     *
     *    Index, RefOf, CondRefOf
     */
    /*
     ???????????????????????????????????????
     SEE: after fixing bug 118 of ACPICA change all the local data
     so that they differ the relevant global ones.
     !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
     */
    Name (Z077, 0x4D)
    /* /////////////////////////////////////////////////////////////////////////// */
    /* */
    /* TABLE 1: all the legal ways to generate references */
    /*          to the immediate images (constants) */
    /* */
    /* /////////////////////////////////////////////////////////////////////////// */
    Method (M168, 0, NotSerialized)
    {
        If (Y100)
        {
            TS00 ("m168")
        }
        Else
        {
            Debug = "m168"
        }

        If (!Y900)
        {
            Debug = "Test m168 skipped!"
            Return (Zero)
        }

        /* T1:I2-I4 */

        Store (Index ("123456789", 0x05), Local0)
        M1A2 (Local0, C016, 0x00, 0x00, C009, 0x36, __LINE__)
        Store (Index ("qwrtyuiop", 0x05), Local0)
        M1A2 (Local0, C016, 0x00, 0x00, C009, 0x75, __LINE__)
        Store (Index (Buffer (0x08)
                {
                     0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08   // ........
                }, 0x05), Local0)
        M1A2 (Local0, C016, 0x00, 0x00, C009, 0x06, __LINE__)
        Store (Index (Package (0x01)
                {
                    0x00ABCDEF
                }, 0x00), Local0)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0x00ABCDEF, __LINE__)
        Store (Index (Package (0x01)
                {
                    "123456789"
                }, 0x00), Local0)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "123456789", __LINE__)
        Store (Index (Package (0x01)
                {
                    "qwrtyuiop"
                }, 0x00), Local0)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "qwrtyuiop", __LINE__)
        Store (Index (Package (0x01)
                {
                    Buffer (0x09)
                    {
                        /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
                        /* 0008 */  0x09                                             // .
                    }
                }, 0x00), Local0)
        M1A2 (Local0, C00B, 0x00, 0x00, C00B, Buffer (0x09)
            {
                /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
                /* 0008 */  0x09                                             // .
            }, 0x04F2)
        Store (Index (Package (0x01)
                {
                    Package (0x01)
                    {
                        0x00ABCDEF
                    }
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0x00ABCDEF, __LINE__)
        Store (Index (Package (0x01)
                {
                    Package (0x01)
                    {
                        "123456789"
                    }
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "123456789", __LINE__)
        Store (Index (Package (0x01)
                {
                    Package (0x01)
                    {
                        "qwrtyuiop"
                    }
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "qwrtyuiop", __LINE__)
        Store (Index (Package (0x01)
                {
                    Package (0x01)
                    {
                        Buffer (0x09)
                        {
                            /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
                            /* 0008 */  0x09                                             // .
                        }
                    }
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C00B, Buffer (0x09)
            {
                /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
                /* 0008 */  0x09                                             // .
            }, 0x04F6)
        Store (Index (Package (0x01)
                {
                    Package (0x01)
                    {
                        Package (0x01)
                        {
                            0x00ABCDEF
                        }
                    }
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x02, 0x00, C009, 0x00ABCDEF, __LINE__)
        Store (Index (Package (0x01)
                {
                    Package (0x01)
                    {
                        Package (0x01)
                        {
                            "123456789"
                        }
                    }
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x02, 0x00, C00A, "123456789", __LINE__)
        Store (Index (Package (0x01)
                {
                    Package (0x01)
                    {
                        Package (0x01)
                        {
                            "qwrtyuiop"
                        }
                    }
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x02, 0x00, C00A, "qwrtyuiop", __LINE__)
        Store (Index (Package (0x01)
                {
                    Package (0x01)
                    {
                        Package (0x01)
                        {
                            Buffer (0x09)
                            {
                                /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
                                /* 0008 */  0x09                                             // .
                            }
                        }
                    }
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x02, 0x00, C00B, Buffer (0x09)
            {
                /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
                /* 0008 */  0x09                                             // .
            }, 0x04FA)
        /* T1:IR2-IR4 */

        If (Y098)
        {
            Local0 = Index ("qwrtyuiop", 0x05, Local1)
            M1A2 (Local0, C016, 0x00, 0x00, C009, 0x75, __LINE__)
            M1A2 (Local1, C016, 0x00, 0x00, C009, 0x75, __LINE__)
            Local0 = Index (Buffer (0x08)
                    {
                         0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08   // ........
                    }, 0x05, Local1)
            M1A2 (Local0, C016, 0x00, 0x00, C009, 0x06, __LINE__)
            M1A2 (Local1, C016, 0x00, 0x00, C009, 0x06, __LINE__)
            Local0 = Index (Package (0x08)
                    {
                        0x01,
                        0x02,
                        0x03,
                        0x04,
                        0x05,
                        0x06,
                        0x07,
                        0x08
                    }, 0x05, Local1)
            M1A2 (Local0, C009, 0x00, 0x00, C009, 0x06, __LINE__)
            M1A2 (Local1, C009, 0x00, 0x00, C009, 0x06, __LINE__)
        }
    }

    /* /////////////////////////////////////////////////////////////////////////// */
    /* */
    /* TABLE 2: all the legal ways to generate references to the named objects */
    /* */
    /* /////////////////////////////////////////////////////////////////////////// */
    Method (M169, 0, Serialized)
    {
        If (Y100)
        {
            TS00 ("m169")
        }
        Else
        {
            Debug = "m169"
        }

        /* Not Computational Data */

        Event (E900)
        Event (E9Z0)
        Mutex (MX90, 0x00)
        Mutex (MX91, 0x00)
        Device (D900)
        {
            Name (I900, 0xABCD1017)
        }

        Device (D9Z0)
        {
            Name (I900, 0xABCD1017)
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

        Name (I900, 0xFE7CB391D65A1000)
        Name (I9Z0, 0xFE7CB391D65A1000)
        Name (I901, 0xC1791001)
        Name (I9Z1, 0xC1791001)
        Name (I902, 0x00)
        Name (I903, 0xFFFFFFFFFFFFFFFF)
        Name (I904, 0xFFFFFFFF)
        Name (S900, "12341002")
        Name (S9Z0, "12341002")
        Name (S901, "qwrtyu1003")
        Name (S9Z1, "qwrtyu1003")
        Name (B900, Buffer (0x05)
        {
             0x10, 0x11, 0x12, 0x13, 0x14                     // .....
        })
        Name (B9Z0, Buffer (0x05)
        {
             0x10, 0x11, 0x12, 0x13, 0x14                     // .....
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
            0xABCD1004,
            0x1122334455661005
        })
        Name (P902, Package (0x02)
        {
            "12341006",
            "q1w2e3r4t5y6u7i81007"
        })
        Name (P903, Package (0x02)
        {
            "qwrtyuiop1008",
            "1234567890abdef0251009"
        })
        Name (P904, Package (0x02)
        {
            Buffer (0x03)
            {
                 0xA0, 0xA1, 0xA2                                 // ...
            },

            Buffer (0x02)
            {
                 0xA3, 0xA4                                       // ..
            }
        })
        Name (P905, Package (0x01)
        {
            Package (0x03)
            {
                0x0ABC100A,
                "0xabc100b",
                "abc100c"
            }
        })
        Name (P906, Package (0x01)
        {
            Package (0x01)
            {
                "abc100d"
            }
        })
        Name (P907, Package (0x01)
        {
            Package (0x01)
            {
                "aqwevbgnm100e"
            }
        })
        Name (P908, Package (0x01)
        {
            Package (0x01)
            {
                Buffer (0x05)
                {
                     0xA5, 0xA6, 0xA7, 0xA8, 0xA9                     // .....
                }
            }
        })
        Name (P909, Package (0x01)
        {
            Package (0x01)
            {
                Package (0x01)
                {
                    0x0ABC100F
                }
            }
        })
        Name (P90A, Package (0x01)
        {
            Package (0x01)
            {
                Package (0x01)
                {
                    "12341010"
                }
            }
        })
        Name (P90B, Package (0x01)
        {
            Package (0x01)
            {
                Package (0x01)
                {
                    "zxswefas1011"
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
                         0xAA, 0xAB, 0xAC                                 // ...
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
            Return (0x0ABC1012)
        }

        Method (M902, 0, NotSerialized)
        {
            Return ("zxvgswquiy1013")
        }

        Method (M903, 0, NotSerialized)
        {
            Return (Buffer (0x01)
            {
                 0xAD                                             // .
            })
        }

        Method (M904, 0, NotSerialized)
        {
            Return (Package (0x01)
            {
                0x0ABC1014
            })
        }

        Method (M905, 0, NotSerialized)
        {
            Return (Package (0x01)
            {
                "lkjhgtre1015"
            })
        }

        Method (M906, 0, NotSerialized)
        {
            Return (Package (0x01)
            {
                Buffer (0x01)
                {
                     0xAE                                             // .
                }
            })
        }

        Method (M907, 0, NotSerialized)
        {
            Return (Package (0x01)
            {
                Package (0x01)
                {
                    0x0ABC1016
                }
            })
        }

        Method (M908, 0, NotSerialized)
        {
            Return (I900) /* \M169.I900 */
        }

        Method (M909, 0, NotSerialized)
        {
            Return (I901) /* \M169.I901 */
        }

        Method (M90A, 0, NotSerialized)
        {
            Return (S900) /* \M169.S900 */
        }

        Method (M90B, 0, NotSerialized)
        {
            Return (S901) /* \M169.S901 */
        }

        Method (M90C, 0, NotSerialized)
        {
            Return (B9Z0) /* \M169.B9Z0 */
        }

        Method (M90D, 0, NotSerialized)
        {
            Return (F900) /* \M169.F900 */
        }

        Method (M90E, 0, NotSerialized)
        {
            Return (BN90) /* \M169.BN90 */
        }

        Method (M90F, 0, NotSerialized)
        {
            Return (IF90) /* \M169.IF90 */
        }

        Method (M910, 0, NotSerialized)
        {
            Return (BF90) /* \M169.BF90 */
        }

        Method (M911, 0, NotSerialized)
        {
            Return (D900) /* \M169.D900 */
        }

        Method (M912, 0, NotSerialized)
        {
            Return (E900) /* \M169.E900 */
        }

        Method (M913, 0, NotSerialized)
        {
            Return (M901 ())
        }

        Method (M914, 0, NotSerialized)
        {
            Return (MX90) /* \M169.MX90 */
        }

        Method (M915, 0, NotSerialized)
        {
            Return (R9Z0) /* \M169.R9Z0 */
        }

        Method (M916, 0, NotSerialized)
        {
            Return (PW90) /* \M169.PW90 */
        }

        Method (M917, 0, NotSerialized)
        {
            Return (PR90) /* \M169.PR90 */
        }

        Method (M918, 0, NotSerialized)
        {
            Return (TZ90) /* \M169.TZ90 */
        }

        Method (M919, 0, NotSerialized)
        {
            Return (P900) /* \M169.P900 */
        }

        Method (M91A, 0, NotSerialized)
        {
            Return (P901) /* \M169.P901 */
        }

        Method (M91B, 0, NotSerialized)
        {
            Return (P902) /* \M169.P902 */
        }

        Method (M91C, 0, NotSerialized)
        {
            Return (P903) /* \M169.P903 */
        }

        Method (M91D, 0, NotSerialized)
        {
            Return (P904) /* \M169.P904 */
        }

        Method (M91E, 0, NotSerialized)
        {
            Return (P905) /* \M169.P905 */
        }

        Method (M91F, 0, NotSerialized)
        {
            Return (P906) /* \M169.P906 */
        }

        Method (M920, 0, NotSerialized)
        {
            Return (P907) /* \M169.P907 */
        }

        Method (M921, 0, NotSerialized)
        {
            Return (P908) /* \M169.P908 */
        }

        Method (M922, 0, NotSerialized)
        {
            Return (P909) /* \M169.P909 */
        }

        Method (M923, 0, NotSerialized)
        {
            Return (P90A) /* \M169.P90A */
        }

        Method (M924, 0, NotSerialized)
        {
            Return (P90B) /* \M169.P90B */
        }

        Method (M925, 0, NotSerialized)
        {
            Return (P90C) /* \M169.P90C */
        }

        Method (M926, 0, NotSerialized)
        {
            Return (P90D) /* \M169.P90D */
        }

        Method (M927, 0, NotSerialized)
        {
            Return (P90E) /* \M169.P90E */
        }

        Method (M928, 0, NotSerialized)
        {
            Return (P90F) /* \M169.P90F */
        }

        Method (M929, 0, NotSerialized)
        {
            Return (P910) /* \M169.P910 */
        }

        Method (M92A, 0, NotSerialized)
        {
            Return (P911) /* \M169.P911 */
        }

        Method (M92B, 0, NotSerialized)
        {
            Return (P912) /* \M169.P912 */
        }

        Method (M92C, 0, NotSerialized)
        {
            Return (P913) /* \M169.P913 */
        }

        Method (M92D, 0, NotSerialized)
        {
            Return (P914) /* \M169.P914 */
        }

        Method (M92E, 0, NotSerialized)
        {
            Return (P915) /* \M169.P915 */
        }

        Method (M92F, 0, NotSerialized)
        {
            Return (P916) /* \M169.P916 */
        }

        Method (M930, 0, NotSerialized)
        {
            Return (P917) /* \M169.P917 */
        }

        Method (M931, 0, NotSerialized)
        {
            Return (P918) /* \M169.P918 */
        }

        Method (M932, 0, NotSerialized)
        {
            Return (P919) /* \M169.P919 */
        }

        Method (M933, 0, NotSerialized)
        {
            Return (P91A) /* \M169.P91A */
        }

        Method (M934, 0, NotSerialized)
        {
            Return (P91B) /* \M169.P91B */
        }

        Method (M935, 0, NotSerialized)
        {
            Return (P91C) /* \M169.P91C */
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
            0xABCD1018,
            0xABCD1019
        })
        Name (P954, Package (0x02)
        {
            0xABCD1018,
            0xABCD1019
        })
        /* Check that all the data (local) are not corrupted */

        Method (M000, 0, NotSerialized)
        {
            /* Computational Data */
            /* Integer */
            Local0 = ObjectType (I900)
            If ((Local0 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C009)
            }

            If ((I900 != 0xFE7CB391D65A1000))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, I900, 0xFE7CB391D65A1000)
            }

            Local0 = ObjectType (I901)
            If ((Local0 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C009)
            }

            If ((I901 != 0xC1791001))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, I901, 0xC1791001)
            }

            Local0 = ObjectType (I902)
            If ((Local0 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C009)
            }

            If ((I902 != 0x00))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, I902, 0x00)
            }

            Local0 = ObjectType (I903)
            If ((Local0 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C009)
            }

            If ((I903 != 0xFFFFFFFFFFFFFFFF))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, I903, 0xFFFFFFFFFFFFFFFF)
            }

            Local0 = ObjectType (I904)
            If ((Local0 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C009)
            }

            If ((I904 != 0xFFFFFFFF))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, I904, 0xFFFFFFFF)
            }

            /* String */

            Local0 = ObjectType (S900)
            If ((Local0 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C00A)
            }

            If ((S900 != "12341002"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, S900, "12341002")
            }

            Local0 = ObjectType (S901)
            If ((Local0 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C00A)
            }

            If ((S901 != "qwrtyu1003"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, S901, "qwrtyu1003")
            }

            /* Buffer */

            Local0 = ObjectType (B900)
            If ((Local0 != C00B))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C00B)
            }

            If ((B900 != Buffer (0x05)
                        {
                             0x10, 0x11, 0x12, 0x13, 0x14                     // .....
                        }))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, B900, Buffer (0x05)
                    {
                         0x10, 0x11, 0x12, 0x13, 0x14                     // .....
                    })
            }

            /* Buffer Field */

            Local0 = ObjectType (BF90)
            If ((Local0 != C016))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C016)
            }

            If (BF90 != Buffer(){0x10})
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, BF90, Buffer(){0x10})
            }

            /* One level Package */

            Store (P900 [0x00], Local0)
            Local1 = ObjectType (Local0)
            If ((Local1 != C008))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, C008)
            }

            Store (P901 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C009)
            }

            If ((Local1 != 0xABCD1004))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, 0xABCD1004)
            }

            Store (P901 [0x01], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C009)
            }

            If ((Local1 != 0x1122334455661005))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, 0x1122334455661005)
            }

            Store (P902 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C00A)
            }

            If ((Local1 != "12341006"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, "12341006")
            }

            Store (P902 [0x01], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C00A)
            }

            If ((Local1 != "q1w2e3r4t5y6u7i81007"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, "q1w2e3r4t5y6u7i81007")
            }

            Store (P903 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C00A)
            }

            If ((Local1 != "qwrtyuiop1008"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, "qwrtyuiop1008")
            }

            Store (P903 [0x01], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C00A)
            }

            If ((Local1 != "1234567890abdef0251009"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, "1234567890abdef0251009")
            }

            Store (P904 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C00B))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C00B)
            }

            If ((Local1 != Buffer (0x03)
                        {
                             0xA0, 0xA1, 0xA2                                 // ...
                        }))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, Buffer (0x03)
                    {
                         0xA0, 0xA1, 0xA2                                 // ...
                    })
            }

            Store (P904 [0x01], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C00B))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C00B)
            }

            If ((Local1 != Buffer (0x02)
                        {
                             0xA3, 0xA4                                       // ..
                        }))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, Buffer (0x02)
                    {
                         0xA3, 0xA4                                       // ..
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
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local4, C009)
            }

            If ((Local3 != 0x0ABC100A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local3, 0x0ABC100A)
            }

            Store (P905 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Store (Local1 [0x01], Local2)
            Local3 = DerefOf (Local2)
            Local4 = ObjectType (Local3)
            If ((Local4 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local4, C00A)
            }

            If ((Local3 != "0xabc100b"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local3, "0xabc100b")
            }

            Store (P905 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Store (Local1 [0x02], Local2)
            Local3 = DerefOf (Local2)
            Local4 = ObjectType (Local3)
            If ((Local4 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local4, C00A)
            }

            If ((Local3 != "abc100c"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local3, "abc100c")
            }

            Store (P906 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Store (Local1 [0x00], Local2)
            Local3 = DerefOf (Local2)
            Local4 = ObjectType (Local3)
            If ((Local4 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local4, C00A)
            }

            If ((Local3 != "abc100d"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local3, "abc100d")
            }

            Store (P907 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Store (Local1 [0x00], Local2)
            Local3 = DerefOf (Local2)
            Local4 = ObjectType (Local3)
            If ((Local4 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local4, C00A)
            }

            If ((Local3 != "aqwevbgnm100e"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local3, "aqwevbgnm100e")
            }

            Store (P908 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Store (Local1 [0x00], Local2)
            Local3 = DerefOf (Local2)
            Local4 = ObjectType (Local3)
            If ((Local4 != C00B))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local4, C00B)
            }

            If ((Local3 != Buffer (0x05)
                        {
                             0xA5, 0xA6, 0xA7, 0xA8, 0xA9                     // .....
                        }))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local3, Buffer (0x05)
                    {
                         0xA5, 0xA6, 0xA7, 0xA8, 0xA9                     // .....
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
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local6, C009)
            }

            If ((Local5 != 0x0ABC100F))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local5, 0x0ABC100F)
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
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local6, C00A)
            }

            If ((Local5 != "12341010"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local5, "12341010")
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
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local6, C00A)
            }

            If ((Local5 != "zxswefas1011"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local5, "zxswefas1011")
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
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local6, C00B)
            }

            If ((Local5 != Buffer (0x03)
                        {
                             0xAA, 0xAB, 0xAC                                 // ...
                        }))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local5, Buffer (0x03)
                    {
                         0xAA, 0xAB, 0xAC                                 // ...
                    })
            }

            Store (P953 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C009)
            }

            If ((Local1 != 0xABCD1018))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, 0xABCD1018)
            }

            Store (P953 [0x01], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C009)
            }

            If ((Local1 != 0xABCD1019))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, 0xABCD1019)
            }

            /* Not Computational Data */

            M1AA (C080, E900, C00F, 0x00, 0x013B)
            M1AA (C080, MX90, C011, 0x00, 0x013C)
            M1AA (C080, D900, C00E, 0x00, 0x013D)
            If (Y508)
            {
                M1AA (C080, TZ90, C015, 0x00, 0x013E)
            }

            M1AA (C080, PR90, C014, 0x00, 0x013F)
            M1AA (C080, R900, C012, 0x00, 0x0140)
            M1AA (C080, PW90, C013, 0x00, 0x0141)
                /*
         *	// Field Unit (Field)
         *
         *	if (LNotEqual(f900, 0xd7)) {
         *		err(c080, z077, __LINE__, 0, 0, f900, 0xd7)
         *	}
         *
         *	// Field Unit (IndexField)
         *
         *	if (LNotEqual(if90, 0xd7)) {
         *		err(c080, z077, __LINE__, 0, 0, if90, 0xd7)
         *	}
         */
        }

        /* m000 */
        /* T2:I2-I4 */
        If (Y114)
        {
            Store (M902 () [0x00], Local0)
            M1A0 (Local0, C010, Ones, 0x00)
        }

        /* Computational Data */

        Store (S900 [0x00], Local0)
        M1A2 (Local0, C016, 0x00, 0x00, C009, 0x31, __LINE__)
        Store (S901 [0x02], Local0)
        M1A2 (Local0, C016, 0x00, 0x00, C009, 0x72, __LINE__)
        Store (B900 [0x03], Local0)
        M1A2 (Local0, C016, 0x00, 0x00, C009, 0x13, __LINE__)
        /* Package */

        Store (P953 [0x00], Local0)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xABCD1018, __LINE__)
        /* Elements of Package are Uninitialized */

        If (Y104)
        {
            Store (P900 [0x00], Local0)
            M1A0 (Local0, C008, Ones, 0x04)
        }

        /* Elements of Package are Computational Data */

        Store (P901 [0x00], Local0)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xABCD1004, __LINE__)
        Store (P901 [0x01], Local0)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0x1122334455661005, __LINE__)
        Store (P902 [0x00], Local0)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "12341006", __LINE__)
        Store (P902 [0x01], Local0)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "q1w2e3r4t5y6u7i81007", __LINE__)
        Store (P903 [0x00], Local0)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "qwrtyuiop1008", __LINE__)
        Store (P903 [0x01], Local0)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "1234567890abdef0251009", __LINE__)
        Store (P904 [0x00], Local0)
        M1A2 (Local0, C00B, 0x00, 0x00, C00B, Buffer (0x03)
            {
                 0xA0, 0xA1, 0xA2                                 // ...
            }, 0x0B)
        Store (P905 [0x00], Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0x0ABC100A, __LINE__)
        Store (P905 [0x00], Local0)
        M1A2 (Local0, C00C, 0x01, 0x01, C00A, "0xabc100b", __LINE__)
        Store (P906 [0x00], Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "abc100d", __LINE__)
        Store (P907 [0x00], Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "aqwevbgnm100e", __LINE__)
        Store (P908 [0x00], Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C00B, Buffer (0x05)
            {
                 0xA5, 0xA6, 0xA7, 0xA8, 0xA9                     // .....
            }, 0x10)
        Store (P909 [0x00], Local0)
        M1A2 (Local0, C00C, 0x02, 0x00, C009, 0x0ABC100F, __LINE__)
        Store (P90A [0x00], Local0)
        M1A2 (Local0, C00C, 0x02, 0x00, C00A, "12341010", __LINE__)
        Store (P90B [0x00], Local0)
        M1A2 (Local0, C00C, 0x02, 0x00, C00A, "zxswefas1011", __LINE__)
        Store (P90C [0x00], Local0)
        M1A2 (Local0, C00C, 0x02, 0x00, C00B, Buffer (0x03)
            {
                 0xAA, 0xAB, 0xAC                                 // ...
            }, 0x14)
        Store (P90D [0x00], Local0)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xFE7CB391D65A1000, __LINE__)
        Store (P90E [0x00], Local0)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xC1791001, __LINE__)
        Store (P90F [0x00], Local0)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "12341002", __LINE__)
        Store (P910 [0x00], Local0)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "qwrtyu1003", __LINE__)
        Store (P911 [0x00], Local0)
        M1A2 (Local0, C00B, 0x00, 0x00, C00B, Buffer (0x05)
            {
                 0x10, 0x11, 0x12, 0x13, 0x14                     // .....
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
            M1A2 (Local0, C016, 0x00, 0x00, C016, 0x10, __LINE__)
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
        M1A2 (Local0, C016, 0x00, 0x00, C009, 0x14, __LINE__)
        M1A2 (Local1, C016, 0x00, 0x00, C009, 0x14, __LINE__)
        /* Elements of Package are Uninitialized */

        If (Y104)
        {
            Local0 = Local1 = P900 [0x00]
            M1A0 (Local0, C008, Ones, 0x61)
            M1A0 (Local1, C008, Ones, 0x62)
        }

        /* Elements of Package are Computational Data */

        Local0 = Local1 = P901 [0x00]
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xABCD1004, __LINE__)
        M1A2 (Local1, C009, 0x00, 0x00, C009, 0xABCD1004, __LINE__)
        Local0 = Local1 = P901 [0x01]
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0x1122334455661005, __LINE__)
        M1A2 (Local1, C009, 0x00, 0x00, C009, 0x1122334455661005, __LINE__)
        Local0 = Local1 = P902 [0x00]
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "12341006", __LINE__)
        M1A2 (Local1, C00A, 0x00, 0x00, C00A, "12341006", __LINE__)
        Local0 = Local1 = P902 [0x01]
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "q1w2e3r4t5y6u7i81007", __LINE__)
        M1A2 (Local1, C00A, 0x00, 0x00, C00A, "q1w2e3r4t5y6u7i81007", __LINE__)
        Local0 = Local1 = P903 [0x00]
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "qwrtyuiop1008", __LINE__)
        M1A2 (Local1, C00A, 0x00, 0x00, C00A, "qwrtyuiop1008", __LINE__)
        Local0 = Local1 = P903 [0x01]
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "1234567890abdef0251009", __LINE__)
        M1A2 (Local1, C00A, 0x00, 0x00, C00A, "1234567890abdef0251009", __LINE__)
        Local0 = Local1 = P904 [0x00]
        M1A2 (Local0, C00B, 0x00, 0x00, C00B, Buffer (0x03)
            {
                 0xA0, 0xA1, 0xA2                                 // ...
            }, 0x6F)
        M1A2 (Local1, C00B, 0x00, 0x00, C00B, Buffer (0x03)
            {
                 0xA0, 0xA1, 0xA2                                 // ...
            }, 0x70)
        Local0 = Local1 = P905 [0x00]
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0x0ABC100A, __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x00, C009, 0x0ABC100A, __LINE__)
        Local0 = Local1 = P905 [0x00]
        M1A2 (Local0, C00C, 0x01, 0x01, C00A, "0xabc100b", __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x01, C00A, "0xabc100b", __LINE__)
        Local0 = Local1 = P906 [0x00]
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "abc100d", __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x00, C00A, "abc100d", __LINE__)
        Local0 = Local1 = P907 [0x00]
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "aqwevbgnm100e", __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x00, C00A, "aqwevbgnm100e", __LINE__)
        Local0 = Local1 = P908 [0x00]
        M1A2 (Local0, C00C, 0x01, 0x00, C00B, Buffer (0x05)
            {
                 0xA5, 0xA6, 0xA7, 0xA8, 0xA9                     // .....
            }, 0x79)
        M1A2 (Local1, C00C, 0x01, 0x00, C00B, Buffer (0x05)
            {
                 0xA5, 0xA6, 0xA7, 0xA8, 0xA9                     // .....
            }, 0x7A)
        Local0 = Local1 = P909 [0x00]
        M1A2 (Local0, C00C, 0x02, 0x00, C009, 0x0ABC100F, __LINE__)
        M1A2 (Local1, C00C, 0x02, 0x00, C009, 0x0ABC100F, __LINE__)
        Local0 = Local1 = P90A [0x00]
        M1A2 (Local0, C00C, 0x02, 0x00, C00A, "12341010", __LINE__)
        M1A2 (Local1, C00C, 0x02, 0x00, C00A, "12341010", __LINE__)
        Local0 = Local1 = P90B [0x00]
        M1A2 (Local0, C00C, 0x02, 0x00, C00A, "zxswefas1011", __LINE__)
        M1A2 (Local1, C00C, 0x02, 0x00, C00A, "zxswefas1011", __LINE__)
        Local0 = Local1 = P90C [0x00]
        M1A2 (Local0, C00C, 0x02, 0x00, C00B, Buffer (0x03)
            {
                 0xAA, 0xAB, 0xAC                                 // ...
            }, 0x81)
        M1A2 (Local1, C00C, 0x02, 0x00, C00B, Buffer (0x03)
            {
                 0xAA, 0xAB, 0xAC                                 // ...
            }, 0x82)
        Local0 = Local1 = P90D [0x00]
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xFE7CB391D65A1000, __LINE__)
        M1A2 (Local1, C009, 0x00, 0x00, C009, 0xFE7CB391D65A1000, __LINE__)
        Local0 = Local1 = P90E [0x00]
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xC1791001, __LINE__)
        M1A2 (Local1, C009, 0x00, 0x00, C009, 0xC1791001, __LINE__)
        Local0 = Local1 = P90F [0x00]
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "12341002", __LINE__)
        M1A2 (Local1, C00A, 0x00, 0x00, C00A, "12341002", __LINE__)
        Local0 = Local1 = P910 [0x00]
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "qwrtyu1003", __LINE__)
        M1A2 (Local1, C00A, 0x00, 0x00, C00A, "qwrtyu1003", __LINE__)
        Local0 = Local1 = P911 [0x00]
        M1A2 (Local0, C00B, 0x00, 0x00, C00B, Buffer (0x05)
            {
                 0x10, 0x11, 0x12, 0x13, 0x14                     // .....
            }, 0x8B)
        M1A2 (Local1, C00B, 0x00, 0x00, C00B, Buffer (0x05)
            {
                 0x10, 0x11, 0x12, 0x13, 0x14                     // .....
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
            M1A2 (Local0, C016, 0x00, 0x00, C016, 0x10, __LINE__)
            M1A2 (Local1, C016, 0x00, 0x00, C016, 0x10, __LINE__)
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

        M000 ()
        M1A6 ()
    }

    /* arg0 - writing mode */

    Method (M16A, 1, Serialized)
    {
        If (Y100)
        {
            TS00 ("m16a")
        }
        Else
        {
            Debug = "m16a"
        }

        /* Not Computational Data */

        Event (E900)
        Event (E9Z0)
        Mutex (MX90, 0x00)
        Mutex (MX91, 0x00)
        Device (D900)
        {
            Name (I900, 0xABCD2017)
        }

        Device (D9Z0)
        {
            Name (I900, 0xABCD2017)
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

        Name (I900, 0xFE7CB391D65A2000)
        Name (I9Z0, 0xFE7CB391D65A2000)
        Name (I901, 0xC1792001)
        Name (I9Z1, 0xC1792001)
        Name (I902, 0x00)
        Name (I903, 0xFFFFFFFFFFFFFFFF)
        Name (I904, 0xFFFFFFFF)
        Name (S900, "12342002")
        Name (S9Z0, "12342002")
        Name (S901, "qwrtyu2003")
        Name (S9Z1, "qwrtyu2003")
        Name (B900, Buffer (0x05)
        {
             0xC0, 0xC1, 0xC2, 0xC3, 0xC4                     // .....
        })
        Name (B9Z0, Buffer (0x05)
        {
             0xC0, 0xC1, 0xC2, 0xC3, 0xC4                     // .....
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
            0xABCD2004,
            0x1122334455662005
        })
        Name (P902, Package (0x02)
        {
            "12342006",
            "q1w2e3r4t5y6u7i82007"
        })
        Name (P903, Package (0x02)
        {
            "qwrtyuiop2008",
            "1234567890abdef0252009"
        })
        Name (P904, Package (0x02)
        {
            Buffer (0x03)
            {
                 0xC5, 0xC6, 0xC7                                 // ...
            },

            Buffer (0x02)
            {
                 0xC8, 0xC9                                       // ..
            }
        })
        Name (P905, Package (0x01)
        {
            Package (0x03)
            {
                0x0ABC200A,
                "0xabc200b",
                "abc200c"
            }
        })
        Name (P906, Package (0x01)
        {
            Package (0x01)
            {
                "abc200d"
            }
        })
        Name (P907, Package (0x01)
        {
            Package (0x01)
            {
                "aqwevbgnm200e"
            }
        })
        Name (P908, Package (0x01)
        {
            Package (0x01)
            {
                Buffer (0x05)
                {
                     0xCA, 0xCB, 0xCC, 0xCD, 0xCE                     // .....
                }
            }
        })
        Name (P909, Package (0x01)
        {
            Package (0x01)
            {
                Package (0x01)
                {
                    0x0ABC200F
                }
            }
        })
        Name (P90A, Package (0x01)
        {
            Package (0x01)
            {
                Package (0x01)
                {
                    "12342010"
                }
            }
        })
        Name (P90B, Package (0x01)
        {
            Package (0x01)
            {
                Package (0x01)
                {
                    "zxswefas2011"
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
                         0xCF, 0xD0, 0xD1                                 // ...
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
            Return (0x0ABC2012)
        }

        Method (M902, 0, NotSerialized)
        {
            Return ("zxvgswquiy2013")
        }

        Method (M903, 0, NotSerialized)
        {
            Return (Buffer (0x01)
            {
                 0xD2                                             // .
            })
        }

        Method (M904, 0, NotSerialized)
        {
            Return (Package (0x01)
            {
                0x0ABC2014
            })
        }

        Method (M905, 0, NotSerialized)
        {
            Return (Package (0x01)
            {
                "lkjhgtre2015"
            })
        }

        Method (M906, 0, NotSerialized)
        {
            Return (Package (0x01)
            {
                Buffer (0x01)
                {
                     0xD3                                             // .
                }
            })
        }

        Method (M907, 0, NotSerialized)
        {
            Return (Package (0x01)
            {
                Package (0x01)
                {
                    0x0ABC2016
                }
            })
        }

        Method (M908, 0, NotSerialized)
        {
            Return (I900) /* \M16A.I900 */
        }

        Method (M909, 0, NotSerialized)
        {
            Return (I901) /* \M16A.I901 */
        }

        Method (M90A, 0, NotSerialized)
        {
            Return (S900) /* \M16A.S900 */
        }

        Method (M90B, 0, NotSerialized)
        {
            Return (S901) /* \M16A.S901 */
        }

        Method (M90C, 0, NotSerialized)
        {
            Return (B9Z0) /* \M16A.B9Z0 */
        }

        Method (M90D, 0, NotSerialized)
        {
            Return (F900) /* \M16A.F900 */
        }

        Method (M90E, 0, NotSerialized)
        {
            Return (BN90) /* \M16A.BN90 */
        }

        Method (M90F, 0, NotSerialized)
        {
            Return (IF90) /* \M16A.IF90 */
        }

        Method (M910, 0, NotSerialized)
        {
            Return (BF90) /* \M16A.BF90 */
        }

        Method (M911, 0, NotSerialized)
        {
            Return (D900) /* \M16A.D900 */
        }

        Method (M912, 0, NotSerialized)
        {
            Return (E900) /* \M16A.E900 */
        }

        Method (M913, 0, NotSerialized)
        {
            Return (M901 ())
        }

        Method (M914, 0, NotSerialized)
        {
            Return (MX90) /* \M16A.MX90 */
        }

        Method (M915, 0, NotSerialized)
        {
            Return (R9Z0) /* \M16A.R9Z0 */
        }

        Method (M916, 0, NotSerialized)
        {
            Return (PW90) /* \M16A.PW90 */
        }

        Method (M917, 0, NotSerialized)
        {
            Return (PR90) /* \M16A.PR90 */
        }

        Method (M918, 0, NotSerialized)
        {
            Return (TZ90) /* \M16A.TZ90 */
        }

        Method (M919, 0, NotSerialized)
        {
            Return (P900) /* \M16A.P900 */
        }

        Method (M91A, 0, NotSerialized)
        {
            Return (P901) /* \M16A.P901 */
        }

        Method (M91B, 0, NotSerialized)
        {
            Return (P902) /* \M16A.P902 */
        }

        Method (M91C, 0, NotSerialized)
        {
            Return (P903) /* \M16A.P903 */
        }

        Method (M91D, 0, NotSerialized)
        {
            Return (P904) /* \M16A.P904 */
        }

        Method (M91E, 0, NotSerialized)
        {
            Return (P905) /* \M16A.P905 */
        }

        Method (M91F, 0, NotSerialized)
        {
            Return (P906) /* \M16A.P906 */
        }

        Method (M920, 0, NotSerialized)
        {
            Return (P907) /* \M16A.P907 */
        }

        Method (M921, 0, NotSerialized)
        {
            Return (P908) /* \M16A.P908 */
        }

        Method (M922, 0, NotSerialized)
        {
            Return (P909) /* \M16A.P909 */
        }

        Method (M923, 0, NotSerialized)
        {
            Return (P90A) /* \M16A.P90A */
        }

        Method (M924, 0, NotSerialized)
        {
            Return (P90B) /* \M16A.P90B */
        }

        Method (M925, 0, NotSerialized)
        {
            Return (P90C) /* \M16A.P90C */
        }

        Method (M926, 0, NotSerialized)
        {
            Return (P90D) /* \M16A.P90D */
        }

        Method (M927, 0, NotSerialized)
        {
            Return (P90E) /* \M16A.P90E */
        }

        Method (M928, 0, NotSerialized)
        {
            Return (P90F) /* \M16A.P90F */
        }

        Method (M929, 0, NotSerialized)
        {
            Return (P910) /* \M16A.P910 */
        }

        Method (M92A, 0, NotSerialized)
        {
            Return (P911) /* \M16A.P911 */
        }

        Method (M92B, 0, NotSerialized)
        {
            Return (P912) /* \M16A.P912 */
        }

        Method (M92C, 0, NotSerialized)
        {
            Return (P913) /* \M16A.P913 */
        }

        Method (M92D, 0, NotSerialized)
        {
            Return (P914) /* \M16A.P914 */
        }

        Method (M92E, 0, NotSerialized)
        {
            Return (P915) /* \M16A.P915 */
        }

        Method (M92F, 0, NotSerialized)
        {
            Return (P916) /* \M16A.P916 */
        }

        Method (M930, 0, NotSerialized)
        {
            Return (P917) /* \M16A.P917 */
        }

        Method (M931, 0, NotSerialized)
        {
            Return (P918) /* \M16A.P918 */
        }

        Method (M932, 0, NotSerialized)
        {
            Return (P919) /* \M16A.P919 */
        }

        Method (M933, 0, NotSerialized)
        {
            Return (P91A) /* \M16A.P91A */
        }

        Method (M934, 0, NotSerialized)
        {
            Return (P91B) /* \M16A.P91B */
        }

        Method (M935, 0, NotSerialized)
        {
            Return (P91C) /* \M16A.P91C */
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
            0xABCD2018,
            0xABCD2019
        })
        Name (P954, Package (0x02)
        {
            0xABCD2018,
            0xABCD2019
        })
        /* Check that all the data (local) are not corrupted */

        Method (M000, 0, NotSerialized)
        {
            /* Computational Data */
            /* Integer */
            Local0 = ObjectType (I900)
            If ((Local0 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C009)
            }

            If ((I900 != 0xFE7CB391D65A2000))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, I900, 0xFE7CB391D65A2000)
            }

            Local0 = ObjectType (I901)
            If ((Local0 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C009)
            }

            If ((I901 != 0xC1792001))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, I901, 0xC1792001)
            }

            Local0 = ObjectType (I902)
            If ((Local0 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C009)
            }

            If ((I902 != 0x00))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, I902, 0x00)
            }

            Local0 = ObjectType (I903)
            If ((Local0 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C009)
            }

            If ((I903 != 0xFFFFFFFFFFFFFFFF))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, I903, 0xFFFFFFFFFFFFFFFF)
            }

            Local0 = ObjectType (I904)
            If ((Local0 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C009)
            }

            If ((I904 != 0xFFFFFFFF))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, I904, 0xFFFFFFFF)
            }

            /* String */

            Local0 = ObjectType (S900)
            If ((Local0 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C00A)
            }

            If ((S900 != "12342002"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, S900, "12342002")
            }

            Local0 = ObjectType (S901)
            If ((Local0 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C00A)
            }

            If ((S901 != "qwrtyu2003"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, S901, "qwrtyu2003")
            }

            /* Buffer */

            Local0 = ObjectType (B900)
            If ((Local0 != C00B))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C00B)
            }

            If ((B900 != Buffer (0x05)
                        {
                             0xC0, 0xC1, 0xC2, 0xC3, 0xC4                     // .....
                        }))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, B900, Buffer (0x05)
                    {
                         0xC0, 0xC1, 0xC2, 0xC3, 0xC4                     // .....
                    })
            }

            /* Buffer Field */

            Local0 = ObjectType (BF90)
            If ((Local0 != C016))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C016)
            }

            If ((BF90 != Buffer(){0xC0}))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, BF90, Buffer() {0xC0})
            }

            /* One level Package */

            Store (P900 [0x00], Local0)
            Local1 = ObjectType (Local0)
            If ((Local1 != C008))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, C008)
            }

            Store (P901 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C009)
            }

            If ((Local1 != 0xABCD2004))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, 0xABCD2004)
            }

            Store (P901 [0x01], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C009)
            }

            If ((Local1 != 0x1122334455662005))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, 0x1122334455662005)
            }

            Store (P902 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C00A)
            }

            If ((Local1 != "12342006"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, "12342006")
            }

            Store (P902 [0x01], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C00A)
            }

            If ((Local1 != "q1w2e3r4t5y6u7i82007"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, "q1w2e3r4t5y6u7i82007")
            }

            Store (P903 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C00A)
            }

            If ((Local1 != "qwrtyuiop2008"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, "qwrtyuiop2008")
            }

            Store (P903 [0x01], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C00A)
            }

            If ((Local1 != "1234567890abdef0252009"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, "1234567890abdef0252009")
            }

            Store (P904 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C00B))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C00B)
            }

            If ((Local1 != Buffer (0x03)
                        {
                             0xC5, 0xC6, 0xC7                                 // ...
                        }))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, Buffer (0x03)
                    {
                         0xC5, 0xC6, 0xC7                                 // ...
                    })
            }

            Store (P904 [0x01], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C00B))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C00B)
            }

            If ((Local1 != Buffer (0x02)
                        {
                             0xC8, 0xC9                                       // ..
                        }))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, Buffer (0x02)
                    {
                         0xC8, 0xC9                                       // ..
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
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local4, C009)
            }

            If ((Local3 != 0x0ABC200A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local3, 0x0ABC200A)
            }

            Store (P905 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Store (Local1 [0x01], Local2)
            Local3 = DerefOf (Local2)
            Local4 = ObjectType (Local3)
            If ((Local4 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local4, C00A)
            }

            If ((Local3 != "0xabc200b"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local3, "0xabc200b")
            }

            Store (P905 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Store (Local1 [0x02], Local2)
            Local3 = DerefOf (Local2)
            Local4 = ObjectType (Local3)
            If ((Local4 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local4, C00A)
            }

            If ((Local3 != "abc200c"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local3, "abc200c")
            }

            Store (P906 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Store (Local1 [0x00], Local2)
            Local3 = DerefOf (Local2)
            Local4 = ObjectType (Local3)
            If ((Local4 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local4, C00A)
            }

            If ((Local3 != "abc200d"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local3, "abc200d")
            }

            Store (P907 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Store (Local1 [0x00], Local2)
            Local3 = DerefOf (Local2)
            Local4 = ObjectType (Local3)
            If ((Local4 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local4, C00A)
            }

            If ((Local3 != "aqwevbgnm200e"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local3, "aqwevbgnm200e")
            }

            Store (P908 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Store (Local1 [0x00], Local2)
            Local3 = DerefOf (Local2)
            Local4 = ObjectType (Local3)
            If ((Local4 != C00B))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local4, C00B)
            }

            If ((Local3 != Buffer (0x05)
                        {
                             0xCA, 0xCB, 0xCC, 0xCD, 0xCE                     // .....
                        }))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local3, Buffer (0x05)
                    {
                         0xCA, 0xCB, 0xCC, 0xCD, 0xCE                     // .....
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
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local6, C009)
            }

            If ((Local5 != 0x0ABC200F))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local5, 0x0ABC200F)
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
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local6, C00A)
            }

            If ((Local5 != "12342010"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local5, "12342010")
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
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local6, C00A)
            }

            If ((Local5 != "zxswefas2011"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local5, "zxswefas2011")
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
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local6, C00B)
            }

            If ((Local5 != Buffer (0x03)
                        {
                             0xCF, 0xD0, 0xD1                                 // ...
                        }))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local5, Buffer (0x03)
                    {
                         0xCF, 0xD0, 0xD1                                 // ...
                    })
            }

            Store (P953 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C009)
            }

            If ((Local1 != 0xABCD2018))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, 0xABCD2018)
            }

            Store (P953 [0x01], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C009)
            }

            If ((Local1 != 0xABCD2019))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, 0xABCD2019)
            }

            /* Not Computational Data */

            M1AA (C080, E900, C00F, 0x00, 0x013B)
            M1AA (C080, MX90, C011, 0x00, 0x013C)
            M1AA (C080, D900, C00E, 0x00, 0x013D)
            If (Y508)
            {
                M1AA (C080, TZ90, C015, 0x00, 0x013E)
            }

            M1AA (C080, PR90, C014, 0x00, 0x013F)
            M1AA (C080, R900, C012, 0x00, 0x0140)
            M1AA (C080, PW90, C013, 0x00, 0x0141)
                /*
         *	// Field Unit (Field)
         *
         *	if (LNotEqual(f900, 0xd7)) {
         *		err(c080, z077, __LINE__, 0, 0, f900, 0xd7)
         *	}
         *
         *	// Field Unit (IndexField)
         *
         *	if (LNotEqual(if90, 0xd7)) {
         *		err(c080, z077, __LINE__, 0, 0, if90, 0xd7)
         *	}
         */
        }

        /* m000 */
        /* Check and restore the global data after writing into them */
        Method (M001, 0, NotSerialized)
        {
            /* Computational Data */

            M1AA (C080, I900, C009, C08A, 0x0144)
            CopyObject (I9Z0, I900) /* \M16A.I900 */
            M1AA (C080, I901, C009, C08A, 0x0145)
            CopyObject (I9Z1, I901) /* \M16A.I901 */
            M1AA (C080, S900, C009, C08A, 0x0146)
            CopyObject (S9Z0, S900) /* \M16A.S900 */
            M1AA (C080, S901, C009, C08A, 0x0147)
            CopyObject (S9Z1, S901) /* \M16A.S901 */
            M1AA (C080, B900, C009, C08A, 0x0148)
            CopyObject (B9Z0, B900) /* \M16A.B900 */
            /* Package */

            M1AA (C080, P953, C009, C08A, 0x0149)
            CopyObject (P954, P953) /* \M16A.P953 */
            /* Not Computational Data */

            M1AA (C080, E900, C009, C08A, 0x014A)
            CopyObject (E9Z0, E900) /* \M16A.E900 */
            M1AA (C080, MX90, C009, C08A, 0x014B)
            CopyObject (MX91, MX90) /* \M16A.MX90 */
            M1AA (C080, D900, C009, C08A, 0x014C)
            CopyObject (D9Z0, D900) /* \M16A.D900 */
            If (Y508)
            {
                M1AA (C080, TZ90, C009, C08A, 0x014D)
                CopyObject (TZ91, TZ90) /* \M16A.TZ90 */
            }

            M1AA (C080, PR90, C009, C08A, 0x014E)
            CopyObject (PR91, PR90) /* \M16A.PR90 */
            If (Y510)
            {
                M1AA (C080, R900, C009, C08A, 0x014F)
                CopyObject (R9Z0, R900) /* \M16A.R900 */
            }

            M1AA (C080, PW90, C009, C08A, 0x0150)
            CopyObject (PW91, PW90) /* \M16A.PW90 */
            M000 ()
        }

        /* m001 */
        /* T2:R1-R14 */
        /* Computational Data */
        Local0 = RefOf (I900)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xFE7CB391D65A2000, __LINE__)
        Local0 = RefOf (I901)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xC1792001, __LINE__)
        Local0 = RefOf (S900)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "12342002", __LINE__)
        Local0 = RefOf (S901)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "qwrtyu2003", __LINE__)
        Local0 = RefOf (B900)
        M1A2 (Local0, C00B, 0x00, 0x00, C00B, Buffer (0x05)
            {
                 0xC0, 0xC1, 0xC2, 0xC3, 0xC4                     // .....
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
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xABCD2018, __LINE__)
        If (Arg0)
        {
            M001 ()
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
        M1A2 (Local0, C016, 0x00, 0x00, C00B, Buffer(){0xC0}, __LINE__)
        /* Elements of Package are Uninitialized */

        Local0 = RefOf (P900)
        M1A0 (Local0, C00C, Ones, 0x011F)
        /* Elements of Package are Computational Data */

        Local0 = RefOf (P901)
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xABCD2004, __LINE__)
        M1A2 (Local0, C00C, 0x01, 0x01, C009, 0x1122334455662005, __LINE__)
        Local0 = RefOf (P902)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "12342006", __LINE__)
        M1A2 (Local0, C00C, 0x01, 0x01, C00A, "q1w2e3r4t5y6u7i82007", __LINE__)
        Local0 = RefOf (P903)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "qwrtyuiop2008", __LINE__)
        M1A2 (Local0, C00C, 0x01, 0x01, C00A, "1234567890abdef0252009", __LINE__)
        Local0 = RefOf (P904)
        M1A2 (Local0, C00C, 0x01, 0x00, C00B, Buffer (0x03)
            {
                 0xC5, 0xC6, 0xC7                                 // ...
            }, 0x0126)
        Local0 = RefOf (P905)
        M1A2 (Local0, C00C, 0x02, 0x00, C009, 0x0ABC200A, __LINE__)
        M1A2 (Local0, C00C, 0x02, 0x01, C00A, "0xabc200b", __LINE__)
        Local0 = RefOf (P906)
        M1A2 (Local0, C00C, 0x02, 0x00, C00A, "abc200d", __LINE__)
        Local0 = RefOf (P907)
        M1A2 (Local0, C00C, 0x02, 0x00, C00A, "aqwevbgnm200e", __LINE__)
        Local0 = RefOf (P908)
        M1A2 (Local0, C00C, 0x02, 0x00, C00B, Buffer (0x05)
            {
                 0xCA, 0xCB, 0xCC, 0xCD, 0xCE                     // .....
            }, 0x012B)
        Local0 = RefOf (P909)
        M1A2 (Local0, C00C, 0x03, 0x00, C009, 0x0ABC200F, __LINE__)
        Local0 = RefOf (P90A)
        M1A2 (Local0, C00C, 0x03, 0x00, C00A, "12342010", __LINE__)
        Local0 = RefOf (P90B)
        M1A2 (Local0, C00C, 0x03, 0x00, C00A, "zxswefas2011", __LINE__)
        Local0 = RefOf (P90C)
        M1A2 (Local0, C00C, 0x03, 0x00, C00B, Buffer (0x03)
            {
                 0xCF, 0xD0, 0xD1                                 // ...
            }, 0x012F)
        Local0 = RefOf (P90D)
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xFE7CB391D65A2000, __LINE__)
        Local0 = RefOf (P90E)
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xC1792001, __LINE__)
        Local0 = RefOf (P90F)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "12342002", __LINE__)
        Local0 = RefOf (P910)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "qwrtyu2003", __LINE__)
        Local0 = RefOf (P911)
        M1A2 (Local0, C00C, 0x01, 0x00, C00B, Buffer (0x05)
            {
                 0xC0, 0xC1, 0xC2, 0xC3, 0xC4                     // .....
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
            M1A2 (Local0, C00C, 0x01, 0x00, C016, 0xC0, __LINE__)
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
        M000 ()
        M1A6 ()
        Return (Zero)
    }

    Method (M16B, 0, Serialized)
    {
        If (Y100)
        {
            TS00 ("m16b")
        }
        Else
        {
            Debug = "m16b"
        }

        /* Not Computational Data */

        Event (E900)
        Mutex (MX90, 0x00)
        Device (D900)
        {
        }

        ThermalZone (TZ90)
        {
        }

        Processor (PR90, 0x00, 0xFFFFFFFF, 0x00){}
        OperationRegion (R900, SystemMemory, 0x0100, 0x0100)
        OperationRegion (R9Z0, SystemMemory, 0x0100, 0x0100)
        PowerResource (PW90, 0x01, 0x0000)
        {
            Method (MMMM, 0, NotSerialized)
            {
                Return (0x00)
            }
        }

        /* Computational Data */

        Name (I900, 0xFE7CB391D65A3000)
        Name (I901, 0x21793001)
        Name (I902, 0x00)
        Name (I903, 0xFFFFFFFFFFFFFFFF)
        Name (I904, 0xFFFFFFFF)
        Name (S900, "12343002")
        Name (S901, "qwrtyu3003")
        Name (B900, Buffer (0x05)
        {
             0xD0, 0xD1, 0xD2, 0xD3, 0xD4                     // .....
        })
        Name (B9Z0, Buffer (0x05)
        {
             0xD0, 0xD1, 0xD2, 0xD3, 0xD4                     // .....
        })
        CreateField (B900, 0x00, 0x08, BF90)
        Field (R900, ByteAcc, NoLock, Preserve)
        {
            F900,   8,
            F901,   8,
            F902,   8,
            F903,   8
        }

        BankField (R900, F901, 0x00, ByteAcc, NoLock, Preserve)
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
            0xABCD3004,
            0x1122334455663005
        })
        Name (P902, Package (0x02)
        {
            "12343006",
            "q1w2e3r4t5y6u7i83007"
        })
        Name (P903, Package (0x02)
        {
            "qwrtyuiop3008",
            "1234567890abdef0253009"
        })
        Name (P904, Package (0x02)
        {
            Buffer (0x03)
            {
                 0xD5, 0xD6, 0xD7                                 // ...
            },

            Buffer (0x02)
            {
                 0xD8, 0xD9                                       // ..
            }
        })
        Name (P905, Package (0x01)
        {
            Package (0x03)
            {
                0x0ABC300A,
                "0xabc300b",
                "abc300c"
            }
        })
        Name (P906, Package (0x01)
        {
            Package (0x01)
            {
                "abc300d"
            }
        })
        Name (P907, Package (0x01)
        {
            Package (0x01)
            {
                "aqwevbgnm300e"
            }
        })
        Name (P908, Package (0x01)
        {
            Package (0x01)
            {
                Buffer (0x05)
                {
                     0xDA, 0xDB, 0xDC, 0xDD, 0xDE                     // .....
                }
            }
        })
        Name (P909, Package (0x01)
        {
            Package (0x01)
            {
                Package (0x01)
                {
                    0x0ABC300F
                }
            }
        })
        Name (P90A, Package (0x01)
        {
            Package (0x01)
            {
                Package (0x01)
                {
                    "12343010"
                }
            }
        })
        Name (P90B, Package (0x01)
        {
            Package (0x01)
            {
                Package (0x01)
                {
                    "zxswefas3011"
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
                         0xDF, 0x20, 0x21                                 // . !
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
            R900
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
            Return (0x0ABC3012)
        }

        Method (M902, 0, NotSerialized)
        {
            Return ("zxvgswquiy3013")
        }

        Method (M903, 0, NotSerialized)
        {
            Return (Buffer (0x01)
            {
                 0x22                                             // "
            })
        }

        Method (M904, 0, NotSerialized)
        {
            Return (Package (0x01)
            {
                0x0ABC3014
            })
        }

        Method (M905, 0, NotSerialized)
        {
            Return (Package (0x01)
            {
                "lkjhgtre3015"
            })
        }

        Method (M906, 0, NotSerialized)
        {
            Return (Package (0x01)
            {
                Buffer (0x01)
                {
                     0x23                                             // #
                }
            })
        }

        Method (M907, 0, NotSerialized)
        {
            Return (Package (0x01)
            {
                Package (0x01)
                {
                    0x0ABC3016
                }
            })
        }

        Method (M908, 0, NotSerialized)
        {
            Return (I900) /* \M16B.I900 */
        }

        Method (M909, 0, NotSerialized)
        {
            Return (I901) /* \M16B.I901 */
        }

        Method (M90A, 0, NotSerialized)
        {
            Return (S900) /* \M16B.S900 */
        }

        Method (M90B, 0, NotSerialized)
        {
            Return (S901) /* \M16B.S901 */
        }

        Method (M90C, 0, NotSerialized)
        {
            Return (B9Z0) /* \M16B.B9Z0 */
        }

        Method (M90D, 0, NotSerialized)
        {
            Return (F900) /* \M16B.F900 */
        }

        Method (M90E, 0, NotSerialized)
        {
            Return (BN90) /* \M16B.BN90 */
        }

        Method (M90F, 0, NotSerialized)
        {
            Return (IF90) /* \M16B.IF90 */
        }

        Method (M910, 0, NotSerialized)
        {
            Return (BF90) /* \M16B.BF90 */
        }

        Method (M911, 0, NotSerialized)
        {
            Return (D900) /* \M16B.D900 */
        }

        Method (M912, 0, NotSerialized)
        {
            Return (E900) /* \M16B.E900 */
        }

        Method (M913, 0, NotSerialized)
        {
            Return (M901 ())
        }

        Method (M914, 0, NotSerialized)
        {
            Return (MX90) /* \M16B.MX90 */
        }

        Method (M915, 0, NotSerialized)
        {
            Return (R900) /* \M16B.R900 */
        }

        Method (M916, 0, NotSerialized)
        {
            Return (PW90) /* \M16B.PW90 */
        }

        Method (M917, 0, NotSerialized)
        {
            Return (PR90) /* \M16B.PR90 */
        }

        Method (M918, 0, NotSerialized)
        {
            Return (TZ90) /* \M16B.TZ90 */
        }

        Method (M919, 0, NotSerialized)
        {
            Return (P900) /* \M16B.P900 */
        }

        Method (M91A, 0, NotSerialized)
        {
            Return (P901) /* \M16B.P901 */
        }

        Method (M91B, 0, NotSerialized)
        {
            Return (P902) /* \M16B.P902 */
        }

        Method (M91C, 0, NotSerialized)
        {
            Return (P903) /* \M16B.P903 */
        }

        Method (M91D, 0, NotSerialized)
        {
            Return (P904) /* \M16B.P904 */
        }

        Method (M91E, 0, NotSerialized)
        {
            Return (P905) /* \M16B.P905 */
        }

        Method (M91F, 0, NotSerialized)
        {
            Return (P906) /* \M16B.P906 */
        }

        Method (M920, 0, NotSerialized)
        {
            Return (P907) /* \M16B.P907 */
        }

        Method (M921, 0, NotSerialized)
        {
            Return (P908) /* \M16B.P908 */
        }

        Method (M922, 0, NotSerialized)
        {
            Return (P909) /* \M16B.P909 */
        }

        Method (M923, 0, NotSerialized)
        {
            Return (P90A) /* \M16B.P90A */
        }

        Method (M924, 0, NotSerialized)
        {
            Return (P90B) /* \M16B.P90B */
        }

        Method (M925, 0, NotSerialized)
        {
            Return (P90C) /* \M16B.P90C */
        }

        Method (M926, 0, NotSerialized)
        {
            Return (P90D) /* \M16B.P90D */
        }

        Method (M927, 0, NotSerialized)
        {
            Return (P90E) /* \M16B.P90E */
        }

        Method (M928, 0, NotSerialized)
        {
            Return (P90F) /* \M16B.P90F */
        }

        Method (M929, 0, NotSerialized)
        {
            Return (P910) /* \M16B.P910 */
        }

        Method (M92A, 0, NotSerialized)
        {
            Return (P911) /* \M16B.P911 */
        }

        Method (M92B, 0, NotSerialized)
        {
            Return (P912) /* \M16B.P912 */
        }

        Method (M92C, 0, NotSerialized)
        {
            Return (P913) /* \M16B.P913 */
        }

        Method (M92D, 0, NotSerialized)
        {
            Return (P914) /* \M16B.P914 */
        }

        Method (M92E, 0, NotSerialized)
        {
            Return (P915) /* \M16B.P915 */
        }

        Method (M92F, 0, NotSerialized)
        {
            Return (P916) /* \M16B.P916 */
        }

        Method (M930, 0, NotSerialized)
        {
            Return (P917) /* \M16B.P917 */
        }

        Method (M931, 0, NotSerialized)
        {
            Return (P918) /* \M16B.P918 */
        }

        Method (M932, 0, NotSerialized)
        {
            Return (P919) /* \M16B.P919 */
        }

        Method (M933, 0, NotSerialized)
        {
            Return (P91A) /* \M16B.P91A */
        }

        Method (M934, 0, NotSerialized)
        {
            Return (P91B) /* \M16B.P91B */
        }

        Method (M935, 0, NotSerialized)
        {
            Return (P91C) /* \M16B.P91C */
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
            0xABCD3018,
            0xABCD3019
        })
        Name (P954, Package (0x02)
        {
            0xABCD3018,
            0xABCD3019
        })
        /* Check that all the data (local) are not corrupted */

        Method (M000, 0, NotSerialized)
        {
            /* Computational Data */
            /* Integer */
            Local0 = ObjectType (I900)
            If ((Local0 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C009)
            }

            If ((I900 != 0xFE7CB391D65A3000))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, I900, 0xFE7CB391D65A3000)
            }

            Local0 = ObjectType (I901)
            If ((Local0 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C009)
            }

            If ((I901 != 0x21793001))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, I901, 0x21793001)
            }

            Local0 = ObjectType (I902)
            If ((Local0 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C009)
            }

            If ((I902 != 0x00))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, I902, 0x00)
            }

            Local0 = ObjectType (I903)
            If ((Local0 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C009)
            }

            If ((I903 != 0xFFFFFFFFFFFFFFFF))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, I903, 0xFFFFFFFFFFFFFFFF)
            }

            Local0 = ObjectType (I904)
            If ((Local0 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C009)
            }

            If ((I904 != 0xFFFFFFFF))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, I904, 0xFFFFFFFF)
            }

            /* String */

            Local0 = ObjectType (S900)
            If ((Local0 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C00A)
            }

            If ((S900 != "12343002"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, S900, "12343002")
            }

            Local0 = ObjectType (S901)
            If ((Local0 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C00A)
            }

            If ((S901 != "qwrtyu3003"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, S901, "qwrtyu3003")
            }

            /* Buffer */

            Local0 = ObjectType (B900)
            If ((Local0 != C00B))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C00B)
            }

            If ((B900 != Buffer (0x05)
                        {
                             0xD0, 0xD1, 0xD2, 0xD3, 0xD4                     // .....
                        }))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, B900, Buffer (0x05)
                    {
                         0xD0, 0xD1, 0xD2, 0xD3, 0xD4                     // .....
                    })
            }

            /* Buffer Field */

            Local0 = ObjectType (BF90)
            If ((Local0 != C016))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C016)
            }

            If (BF90 != Buffer(){0xD0})
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, BF90, Buffer(){0xD0})
            }

            /* One level Package */

            Store (P900 [0x00], Local0)
            Local1 = ObjectType (Local0)
            If ((Local1 != C008))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, C008)
            }

            Store (P901 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C009)
            }

            If ((Local1 != 0xABCD3004))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, 0xABCD3004)
            }

            Store (P901 [0x01], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C009)
            }

            If ((Local1 != 0x1122334455663005))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, 0x1122334455663005)
            }

            Store (P902 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C00A)
            }

            If ((Local1 != "12343006"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, "12343006")
            }

            Store (P902 [0x01], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C00A)
            }

            If ((Local1 != "q1w2e3r4t5y6u7i83007"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, "q1w2e3r4t5y6u7i83007")
            }

            Store (P903 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C00A)
            }

            If ((Local1 != "qwrtyuiop3008"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, "qwrtyuiop3008")
            }

            Store (P903 [0x01], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C00A)
            }

            If ((Local1 != "1234567890abdef0253009"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, "1234567890abdef0253009")
            }

            Store (P904 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C00B))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C00B)
            }

            If ((Local1 != Buffer (0x03)
                        {
                             0xD5, 0xD6, 0xD7                                 // ...
                        }))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, Buffer (0x03)
                    {
                         0xD5, 0xD6, 0xD7                                 // ...
                    })
            }

            Store (P904 [0x01], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C00B))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C00B)
            }

            If ((Local1 != Buffer (0x02)
                        {
                             0xD8, 0xD9                                       // ..
                        }))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, Buffer (0x02)
                    {
                         0xD8, 0xD9                                       // ..
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
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local4, C009)
            }

            If ((Local3 != 0x0ABC300A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local3, 0x0ABC300A)
            }

            Store (P905 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Store (Local1 [0x01], Local2)
            Local3 = DerefOf (Local2)
            Local4 = ObjectType (Local3)
            If ((Local4 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local4, C00A)
            }

            If ((Local3 != "0xabc300b"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local3, "0xabc300b")
            }

            Store (P905 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Store (Local1 [0x02], Local2)
            Local3 = DerefOf (Local2)
            Local4 = ObjectType (Local3)
            If ((Local4 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local4, C00A)
            }

            If ((Local3 != "abc300c"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local3, "abc300c")
            }

            Store (P906 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Store (Local1 [0x00], Local2)
            Local3 = DerefOf (Local2)
            Local4 = ObjectType (Local3)
            If ((Local4 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local4, C00A)
            }

            If ((Local3 != "abc300d"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local3, "abc300d")
            }

            Store (P907 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Store (Local1 [0x00], Local2)
            Local3 = DerefOf (Local2)
            Local4 = ObjectType (Local3)
            If ((Local4 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local4, C00A)
            }

            If ((Local3 != "aqwevbgnm300e"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local3, "aqwevbgnm300e")
            }

            Store (P908 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Store (Local1 [0x00], Local2)
            Local3 = DerefOf (Local2)
            Local4 = ObjectType (Local3)
            If ((Local4 != C00B))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local4, C00B)
            }

            If ((Local3 != Buffer (0x05)
                        {
                             0xDA, 0xDB, 0xDC, 0xDD, 0xDE                     // .....
                        }))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local3, Buffer (0x05)
                    {
                         0xDA, 0xDB, 0xDC, 0xDD, 0xDE                     // .....
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
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local6, C009)
            }

            If ((Local5 != 0x0ABC300F))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local5, 0x0ABC300F)
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
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local6, C00A)
            }

            If ((Local5 != "12343010"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local5, "12343010")
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
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local6, C00A)
            }

            If ((Local5 != "zxswefas3011"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local5, "zxswefas3011")
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
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local6, C00B)
            }

            If ((Local5 != Buffer (0x03)
                        {
                             0xDF, 0x20, 0x21                                 // . !
                        }))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local5, Buffer (0x03)
                    {
                         0xDF, 0x20, 0x21                                 // . !
                    })
            }

            Store (P953 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C009)
            }

            If ((Local1 != 0xABCD3018))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, 0xABCD3018)
            }

            Store (P953 [0x01], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C009)
            }

            If ((Local1 != 0xABCD3019))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, 0xABCD3019)
            }

            /* Not Computational Data */

            M1AA (C080, E900, C00F, 0x00, 0x013B)
            M1AA (C080, MX90, C011, 0x00, 0x013C)
            M1AA (C080, D900, C00E, 0x00, 0x013D)
            If (Y508)
            {
                M1AA (C080, TZ90, C015, 0x00, 0x013E)
            }

            M1AA (C080, PR90, C014, 0x00, 0x013F)
            M1AA (C080, R900, C012, 0x00, 0x0140)
            M1AA (C080, PW90, C013, 0x00, 0x0141)
                /*
         *	// Field Unit (Field)
         *
         *	if (LNotEqual(f900, 0xd7)) {
         *		err(c080, z077, __LINE__, 0, 0, f900, 0xd7)
         *	}
         *
         *	// Field Unit (IndexField)
         *
         *	if (LNotEqual(if90, 0xd7)) {
         *		err(c080, z077, __LINE__, 0, 0, if90, 0xd7)
         *	}
         */
        }

        /* m000 */
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
        M000 ()
        M1A6 ()
    }

    /* arg0 - writing mode */

    Method (M16C, 1, Serialized)
    {
        If (Y100)
        {
            TS00 ("m16c")
        }
        Else
        {
            Debug = "m16c"
        }

        /* Not Computational Data */

        Event (E900)
        Event (E9Z0)
        Mutex (MX90, 0x00)
        Mutex (MX91, 0x00)
        Device (D900)
        {
            Name (I900, 0xABCD4017)
        }

        Device (D9Z0)
        {
            Name (I900, 0xABCD4017)
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

        Name (I900, 0xFE7CB391D65A4000)
        Name (I9Z0, 0xFE7CB391D65A4000)
        Name (I901, 0xC1794001)
        Name (I9Z1, 0xC1794001)
        Name (I902, 0x00)
        Name (I903, 0xFFFFFFFFFFFFFFFF)
        Name (I904, 0xFFFFFFFF)
        Name (S900, "12344002")
        Name (S9Z0, "12344002")
        Name (S901, "qwrtyu4003")
        Name (S9Z1, "qwrtyu4003")
        Name (B900, Buffer (0x05)
        {
             0xE0, 0xE1, 0xE2, 0xE3, 0xE4                     // .....
        })
        Name (B9Z0, Buffer (0x05)
        {
             0xE0, 0xE1, 0xE2, 0xE3, 0xE4                     // .....
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
            0xABCD4004,
            0x1122334455664005
        })
        Name (P902, Package (0x02)
        {
            "12344006",
            "q1w2e3r4t5y6u7i84007"
        })
        Name (P903, Package (0x02)
        {
            "qwrtyuiop4008",
            "1234567890abdef0254009"
        })
        Name (P904, Package (0x02)
        {
            Buffer (0x03)
            {
                 0xE5, 0xE6, 0xE7                                 // ...
            },

            Buffer (0x02)
            {
                 0xE8, 0xE9                                       // ..
            }
        })
        Name (P905, Package (0x01)
        {
            Package (0x03)
            {
                0x0ABC400A,
                "0xabc400b",
                "abc400c"
            }
        })
        Name (P906, Package (0x01)
        {
            Package (0x01)
            {
                "abc400d"
            }
        })
        Name (P907, Package (0x01)
        {
            Package (0x01)
            {
                "aqwevbgnm400e"
            }
        })
        Name (P908, Package (0x01)
        {
            Package (0x01)
            {
                Buffer (0x05)
                {
                     0xEA, 0xEB, 0xEC, 0xED, 0xEE                     // .....
                }
            }
        })
        Name (P909, Package (0x01)
        {
            Package (0x01)
            {
                Package (0x01)
                {
                    0x0ABC400F
                }
            }
        })
        Name (P90A, Package (0x01)
        {
            Package (0x01)
            {
                Package (0x01)
                {
                    "12344010"
                }
            }
        })
        Name (P90B, Package (0x01)
        {
            Package (0x01)
            {
                Package (0x01)
                {
                    "zxswefas4011"
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
                         0xEF, 0x30, 0x31                                 // .01
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
            Return (0x0ABC4012)
        }

        Method (M902, 0, NotSerialized)
        {
            Return ("zxvgswquiy4013")
        }

        Method (M903, 0, NotSerialized)
        {
            Return (Buffer (0x01)
            {
                 0x32                                             // 2
            })
        }

        Method (M904, 0, NotSerialized)
        {
            Return (Package (0x01)
            {
                0x0ABC4014
            })
        }

        Method (M905, 0, NotSerialized)
        {
            Return (Package (0x01)
            {
                "lkjhgtre4015"
            })
        }

        Method (M906, 0, NotSerialized)
        {
            Return (Package (0x01)
            {
                Buffer (0x01)
                {
                     0x33                                             // 3
                }
            })
        }

        Method (M907, 0, NotSerialized)
        {
            Return (Package (0x01)
            {
                Package (0x01)
                {
                    0x0ABC4016
                }
            })
        }

        Method (M908, 0, NotSerialized)
        {
            Return (I900) /* \M16C.I900 */
        }

        Method (M909, 0, NotSerialized)
        {
            Return (I901) /* \M16C.I901 */
        }

        Method (M90A, 0, NotSerialized)
        {
            Return (S900) /* \M16C.S900 */
        }

        Method (M90B, 0, NotSerialized)
        {
            Return (S901) /* \M16C.S901 */
        }

        Method (M90C, 0, NotSerialized)
        {
            Return (B9Z0) /* \M16C.B9Z0 */
        }

        Method (M90D, 0, NotSerialized)
        {
            Return (F900) /* \M16C.F900 */
        }

        Method (M90E, 0, NotSerialized)
        {
            Return (BN90) /* \M16C.BN90 */
        }

        Method (M90F, 0, NotSerialized)
        {
            Return (IF90) /* \M16C.IF90 */
        }

        Method (M910, 0, NotSerialized)
        {
            Return (BF90) /* \M16C.BF90 */
        }

        Method (M911, 0, NotSerialized)
        {
            Return (D900) /* \M16C.D900 */
        }

        Method (M912, 0, NotSerialized)
        {
            Return (E900) /* \M16C.E900 */
        }

        Method (M913, 0, NotSerialized)
        {
            Return (M901 ())
        }

        Method (M914, 0, NotSerialized)
        {
            Return (MX90) /* \M16C.MX90 */
        }

        Method (M915, 0, NotSerialized)
        {
            Return (R9Z0) /* \M16C.R9Z0 */
        }

        Method (M916, 0, NotSerialized)
        {
            Return (PW90) /* \M16C.PW90 */
        }

        Method (M917, 0, NotSerialized)
        {
            Return (PR90) /* \M16C.PR90 */
        }

        Method (M918, 0, NotSerialized)
        {
            Return (TZ90) /* \M16C.TZ90 */
        }

        Method (M919, 0, NotSerialized)
        {
            Return (P900) /* \M16C.P900 */
        }

        Method (M91A, 0, NotSerialized)
        {
            Return (P901) /* \M16C.P901 */
        }

        Method (M91B, 0, NotSerialized)
        {
            Return (P902) /* \M16C.P902 */
        }

        Method (M91C, 0, NotSerialized)
        {
            Return (P903) /* \M16C.P903 */
        }

        Method (M91D, 0, NotSerialized)
        {
            Return (P904) /* \M16C.P904 */
        }

        Method (M91E, 0, NotSerialized)
        {
            Return (P905) /* \M16C.P905 */
        }

        Method (M91F, 0, NotSerialized)
        {
            Return (P906) /* \M16C.P906 */
        }

        Method (M920, 0, NotSerialized)
        {
            Return (P907) /* \M16C.P907 */
        }

        Method (M921, 0, NotSerialized)
        {
            Return (P908) /* \M16C.P908 */
        }

        Method (M922, 0, NotSerialized)
        {
            Return (P909) /* \M16C.P909 */
        }

        Method (M923, 0, NotSerialized)
        {
            Return (P90A) /* \M16C.P90A */
        }

        Method (M924, 0, NotSerialized)
        {
            Return (P90B) /* \M16C.P90B */
        }

        Method (M925, 0, NotSerialized)
        {
            Return (P90C) /* \M16C.P90C */
        }

        Method (M926, 0, NotSerialized)
        {
            Return (P90D) /* \M16C.P90D */
        }

        Method (M927, 0, NotSerialized)
        {
            Return (P90E) /* \M16C.P90E */
        }

        Method (M928, 0, NotSerialized)
        {
            Return (P90F) /* \M16C.P90F */
        }

        Method (M929, 0, NotSerialized)
        {
            Return (P910) /* \M16C.P910 */
        }

        Method (M92A, 0, NotSerialized)
        {
            Return (P911) /* \M16C.P911 */
        }

        Method (M92B, 0, NotSerialized)
        {
            Return (P912) /* \M16C.P912 */
        }

        Method (M92C, 0, NotSerialized)
        {
            Return (P913) /* \M16C.P913 */
        }

        Method (M92D, 0, NotSerialized)
        {
            Return (P914) /* \M16C.P914 */
        }

        Method (M92E, 0, NotSerialized)
        {
            Return (P915) /* \M16C.P915 */
        }

        Method (M92F, 0, NotSerialized)
        {
            Return (P916) /* \M16C.P916 */
        }

        Method (M930, 0, NotSerialized)
        {
            Return (P917) /* \M16C.P917 */
        }

        Method (M931, 0, NotSerialized)
        {
            Return (P918) /* \M16C.P918 */
        }

        Method (M932, 0, NotSerialized)
        {
            Return (P919) /* \M16C.P919 */
        }

        Method (M933, 0, NotSerialized)
        {
            Return (P91A) /* \M16C.P91A */
        }

        Method (M934, 0, NotSerialized)
        {
            Return (P91B) /* \M16C.P91B */
        }

        Method (M935, 0, NotSerialized)
        {
            Return (P91C) /* \M16C.P91C */
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
            0xABCD4018,
            0xABCD4019
        })
        Name (P954, Package (0x02)
        {
            0xABCD4018,
            0xABCD4019
        })
        /* Check that all the data (local) are not corrupted */

        Method (M000, 0, NotSerialized)
        {
            /* Computational Data */
            /* Integer */
            Local0 = ObjectType (I900)
            If ((Local0 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C009)
            }

            If ((I900 != 0xFE7CB391D65A4000))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, I900, 0xFE7CB391D65A4000)
            }

            Local0 = ObjectType (I901)
            If ((Local0 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C009)
            }

            If ((I901 != 0xC1794001))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, I901, 0xC1794001)
            }

            Local0 = ObjectType (I902)
            If ((Local0 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C009)
            }

            If ((I902 != 0x00))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, I902, 0x00)
            }

            Local0 = ObjectType (I903)
            If ((Local0 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C009)
            }

            If ((I903 != 0xFFFFFFFFFFFFFFFF))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, I903, 0xFFFFFFFFFFFFFFFF)
            }

            Local0 = ObjectType (I904)
            If ((Local0 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C009)
            }

            If ((I904 != 0xFFFFFFFF))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, I904, 0xFFFFFFFF)
            }

            /* String */

            Local0 = ObjectType (S900)
            If ((Local0 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C00A)
            }

            If ((S900 != "12344002"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, S900, "12344002")
            }

            Local0 = ObjectType (S901)
            If ((Local0 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C00A)
            }

            If ((S901 != "qwrtyu4003"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, S901, "qwrtyu4003")
            }

            /* Buffer */

            Local0 = ObjectType (B900)
            If ((Local0 != C00B))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C00B)
            }

            If ((B900 != Buffer (0x05)
                        {
                             0xE0, 0xE1, 0xE2, 0xE3, 0xE4                     // .....
                        }))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, B900, Buffer (0x05)
                    {
                         0xE0, 0xE1, 0xE2, 0xE3, 0xE4                     // .....
                    })
            }

            /* Buffer Field */

            Local0 = ObjectType (BF90)
            If ((Local0 != C016))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C016)
            }

            If (BF90 != Buffer() {0xE0})
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, BF90, Buffer(){0xE0})
            }

            /* One level Package */

            Store (P900 [0x00], Local0)
            Local1 = ObjectType (Local0)
            If ((Local1 != C008))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, C008)
            }

            Store (P901 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C009)
            }

            If ((Local1 != 0xABCD4004))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, 0xABCD4004)
            }

            Store (P901 [0x01], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C009)
            }

            If ((Local1 != 0x1122334455664005))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, 0x1122334455664005)
            }

            Store (P902 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C00A)
            }

            If ((Local1 != "12344006"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, "12344006")
            }

            Store (P902 [0x01], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C00A)
            }

            If ((Local1 != "q1w2e3r4t5y6u7i84007"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, "q1w2e3r4t5y6u7i84007")
            }

            Store (P903 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C00A)
            }

            If ((Local1 != "qwrtyuiop4008"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, "qwrtyuiop4008")
            }

            Store (P903 [0x01], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C00A)
            }

            If ((Local1 != "1234567890abdef0254009"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, "1234567890abdef0254009")
            }

            Store (P904 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C00B))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C00B)
            }

            If ((Local1 != Buffer (0x03)
                        {
                             0xE5, 0xE6, 0xE7                                 // ...
                        }))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, Buffer (0x03)
                    {
                         0xE5, 0xE6, 0xE7                                 // ...
                    })
            }

            Store (P904 [0x01], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C00B))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C00B)
            }

            If ((Local1 != Buffer (0x02)
                        {
                             0xE8, 0xE9                                       // ..
                        }))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, Buffer (0x02)
                    {
                         0xE8, 0xE9                                       // ..
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
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local4, C009)
            }

            If ((Local3 != 0x0ABC400A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local3, 0x0ABC400A)
            }

            Store (P905 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Store (Local1 [0x01], Local2)
            Local3 = DerefOf (Local2)
            Local4 = ObjectType (Local3)
            If ((Local4 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local4, C00A)
            }

            If ((Local3 != "0xabc400b"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local3, "0xabc400b")
            }

            Store (P905 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Store (Local1 [0x02], Local2)
            Local3 = DerefOf (Local2)
            Local4 = ObjectType (Local3)
            If ((Local4 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local4, C00A)
            }

            If ((Local3 != "abc400c"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local3, "abc400c")
            }

            Store (P906 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Store (Local1 [0x00], Local2)
            Local3 = DerefOf (Local2)
            Local4 = ObjectType (Local3)
            If ((Local4 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local4, C00A)
            }

            If ((Local3 != "abc400d"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local3, "abc400d")
            }

            Store (P907 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Store (Local1 [0x00], Local2)
            Local3 = DerefOf (Local2)
            Local4 = ObjectType (Local3)
            If ((Local4 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local4, C00A)
            }

            If ((Local3 != "aqwevbgnm400e"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local3, "aqwevbgnm400e")
            }

            Store (P908 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Store (Local1 [0x00], Local2)
            Local3 = DerefOf (Local2)
            Local4 = ObjectType (Local3)
            If ((Local4 != C00B))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local4, C00B)
            }

            If ((Local3 != Buffer (0x05)
                        {
                             0xEA, 0xEB, 0xEC, 0xED, 0xEE                     // .....
                        }))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local3, Buffer (0x05)
                    {
                         0xEA, 0xEB, 0xEC, 0xED, 0xEE                     // .....
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
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local6, C009)
            }

            If ((Local5 != 0x0ABC400F))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local5, 0x0ABC400F)
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
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local6, C00A)
            }

            If ((Local5 != "12344010"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local5, "12344010")
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
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local6, C00A)
            }

            If ((Local5 != "zxswefas4011"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local5, "zxswefas4011")
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
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local6, C00B)
            }

            If ((Local5 != Buffer (0x03)
                        {
                             0xEF, 0x30, 0x31                                 // .01
                        }))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local5, Buffer (0x03)
                    {
                         0xEF, 0x30, 0x31                                 // .01
                    })
            }

            Store (P953 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C009)
            }

            If ((Local1 != 0xABCD4018))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, 0xABCD4018)
            }

            Store (P953 [0x01], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C009)
            }

            If ((Local1 != 0xABCD4019))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, 0xABCD4019)
            }

            /* Not Computational Data */

            M1AA (C080, E900, C00F, 0x00, 0x013B)
            M1AA (C080, MX90, C011, 0x00, 0x013C)
            M1AA (C080, D900, C00E, 0x00, 0x013D)
            If (Y508)
            {
                M1AA (C080, TZ90, C015, 0x00, 0x013E)
            }

            M1AA (C080, PR90, C014, 0x00, 0x013F)
            M1AA (C080, R900, C012, 0x00, 0x0140)
            M1AA (C080, PW90, C013, 0x00, 0x0141)
                /*
         *	// Field Unit (Field)
         *
         *	if (LNotEqual(f900, 0xd7)) {
         *		err(c080, z077, __LINE__, 0, 0, f900, 0xd7)
         *	}
         *
         *	// Field Unit (IndexField)
         *
         *	if (LNotEqual(if90, 0xd7)) {
         *		err(c080, z077, __LINE__, 0, 0, if90, 0xd7)
         *	}
         */
        }

        /* m000 */
        /* Check and restore the global data after writing into them */
        Method (M001, 0, NotSerialized)
        {
            /* Computational Data */

            M1AA (C080, I900, C009, C08A, 0x0144)
            CopyObject (I9Z0, I900) /* \M16C.I900 */
            M1AA (C080, I901, C009, C08A, 0x0145)
            CopyObject (I9Z1, I901) /* \M16C.I901 */
            M1AA (C080, S900, C009, C08A, 0x0146)
            CopyObject (S9Z0, S900) /* \M16C.S900 */
            M1AA (C080, S901, C009, C08A, 0x0147)
            CopyObject (S9Z1, S901) /* \M16C.S901 */
            M1AA (C080, B900, C009, C08A, 0x0148)
            CopyObject (B9Z0, B900) /* \M16C.B900 */
            /* Package */

            M1AA (C080, P953, C009, C08A, 0x0149)
            CopyObject (P954, P953) /* \M16C.P953 */
            /* Not Computational Data */

            M1AA (C080, E900, C009, C08A, 0x014A)
            CopyObject (RefOf (E9Z0), E900) /* \M16C.E900 */
            M1AA (C080, MX90, C009, C08A, 0x014B)
            CopyObject (RefOf (MX91), MX90) /* \M16C.MX90 */
            M1AA (C080, D900, C009, C08A, 0x014C)
            CopyObject (RefOf (D9Z0), D900) /* \M16C.D900 */
            If (Y508)
            {
                M1AA (C080, TZ90, C009, C08A, 0x014D)
                CopyObject (RefOf (TZ91), TZ90) /* \M16C.TZ90 */
            }

            M1AA (C080, PR90, C009, C08A, 0x014E)
            CopyObject (RefOf (PR91), PR90) /* \M16C.PR90 */
            If (Y510)
            {
                M1AA (C080, R900, C009, C08A, 0x014F)
                CopyObject (RefOf (R9Z0), R900) /* \M16C.R900 */
            }

            M1AA (C080, PW90, C009, C08A, 0x0150)
            CopyObject (RefOf (PW91), PW90) /* \M16C.PW90 */
            M000 ()
        }

        /* m001 */
        /* T2:CR1-CR14 */
        /* Computational Data */
        Local1 = CondRefOf (I900, Local0)
        If (M1A4 (Local1, 0x024F))
        {
            M1A2 (Local0, C009, 0x00, 0x00, C009, 0xFE7CB391D65A4000, __LINE__)
        }

        Local1 = CondRefOf (I901, Local0)
        If (M1A4 (Local1, 0x0251))
        {
            M1A2 (Local0, C009, 0x00, 0x00, C009, 0xC1794001, __LINE__)
        }

        Local1 = CondRefOf (S900, Local0)
        If (M1A4 (Local1, 0x0253))
        {
            M1A2 (Local0, C00A, 0x00, 0x00, C00A, "12344002", __LINE__)
        }

        Local1 = CondRefOf (S901, Local0)
        If (M1A4 (Local1, 0x0255))
        {
            M1A2 (Local0, C00A, 0x00, 0x00, C00A, "qwrtyu4003", __LINE__)
        }

        Local1 = CondRefOf (B900, Local0)
        If (M1A4 (Local1, 0x0257))
        {
            M1A2 (Local0, C00B, 0x00, 0x00, C00B, Buffer (0x05)
                {
                     0xE0, 0xE1, 0xE2, 0xE3, 0xE4                     // .....
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
            M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xABCD4018, __LINE__)
        }

        If (Arg0)
        {
            M001 ()
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
            M1A2 (Local0, C016, 0x00, 0x00, C00B, Buffer(){0xE0}, __LINE__)
        }

        /* Elements of Package are Uninitialized */

        Local1 = CondRefOf (P900, Local0)
        M1A0 (Local0, C00C, Local1, 0x0268)
        /* Elements of Package are Computational Data */

        Local1 = CondRefOf (P901, Local0)
        If (M1A4 (Local1, 0x0269))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xABCD4004, __LINE__)
            M1A2 (Local0, C00C, 0x01, 0x01, C009, 0x1122334455664005, __LINE__)
        }

        Local1 = CondRefOf (P902, Local0)
        If (M1A4 (Local1, 0x026C))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C00A, "12344006", __LINE__)
            M1A2 (Local0, C00C, 0x01, 0x01, C00A, "q1w2e3r4t5y6u7i84007", __LINE__)
        }

        Local1 = CondRefOf (P903, Local0)
        If (M1A4 (Local1, 0x026F))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C00A, "qwrtyuiop4008", __LINE__)
            M1A2 (Local0, C00C, 0x01, 0x01, C00A, "1234567890abdef0254009", __LINE__)
        }

        Local1 = CondRefOf (P904, Local0)
        If (M1A4 (Local1, 0x0272))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C00B, Buffer (0x03)
                {
                     0xE5, 0xE6, 0xE7                                 // ...
                }, 0x0273)
        }

        Local1 = CondRefOf (P905, Local0)
        If (M1A4 (Local1, 0x0274))
        {
            M1A2 (Local0, C00C, 0x02, 0x00, C009, 0x0ABC400A, __LINE__)
            M1A2 (Local0, C00C, 0x02, 0x01, C00A, "0xabc400b", __LINE__)
        }

        Local1 = CondRefOf (P906, Local0)
        If (M1A4 (Local1, 0x0277))
        {
            M1A2 (Local0, C00C, 0x02, 0x00, C00A, "abc400d", __LINE__)
        }

        Local1 = CondRefOf (P907, Local0)
        If (M1A4 (Local1, 0x0279))
        {
            M1A2 (Local0, C00C, 0x02, 0x00, C00A, "aqwevbgnm400e", __LINE__)
        }

        Local1 = CondRefOf (P908, Local0)
        If (M1A4 (Local1, 0x027B))
        {
            M1A2 (Local0, C00C, 0x02, 0x00, C00B, Buffer (0x05)
                {
                     0xEA, 0xEB, 0xEC, 0xED, 0xEE                     // .....
                }, 0x027C)
        }

        Local1 = CondRefOf (P909, Local0)
        If (M1A4 (Local1, 0x027D))
        {
            M1A2 (Local0, C00C, 0x03, 0x00, C009, 0x0ABC400F, __LINE__)
        }

        Local1 = CondRefOf (P90A, Local0)
        If (M1A4 (Local1, 0x027F))
        {
            M1A2 (Local0, C00C, 0x03, 0x00, C00A, "12344010", __LINE__)
        }

        Local1 = CondRefOf (P90B, Local0)
        If (M1A4 (Local1, 0x0281))
        {
            M1A2 (Local0, C00C, 0x03, 0x00, C00A, "zxswefas4011", __LINE__)
        }

        Local1 = CondRefOf (P90C, Local0)
        If (M1A4 (Local1, 0x0283))
        {
            M1A2 (Local0, C00C, 0x03, 0x00, C00B, Buffer (0x03)
                {
                     0xEF, 0x30, 0x31                                 // .01
                }, 0x0284)
        }

        Local1 = CondRefOf (P90D, Local0)
        If (M1A4 (Local1, 0x0285))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xFE7CB391D65A4000, __LINE__)
        }

        Local1 = CondRefOf (P90E, Local0)
        If (M1A4 (Local1, 0x0287))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xC1794001, __LINE__)
        }

        Local1 = CondRefOf (P90F, Local0)
        If (M1A4 (Local1, 0x0289))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C00A, "12344002", __LINE__)
        }

        Local1 = CondRefOf (P910, Local0)
        If (M1A4 (Local1, 0x028B))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C00A, "qwrtyu4003", __LINE__)
        }

        Local1 = CondRefOf (P911, Local0)
        If (M1A4 (Local1, 0x028D))
        {
            M1A2 (Local0, C00C, 0x01, 0x00, C00B, Buffer (0x05)
                {
                     0xE0, 0xE1, 0xE2, 0xE3, 0xE4                     // .....
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
                M1A2 (Local0, C00C, 0x01, 0x00, C016, 0xE0, __LINE__)
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
        M000 ()
        M1A6 ()
        Return (Zero)
    }

    /* /////////////////////////////////////////////////////////////////////////// */
    /* */
    /* TABLE 3: all the legal ways to generate references to the */
    /*          immediate images (constants) being elements of Package */
    /* */
    /* /////////////////////////////////////////////////////////////////////////// */
    Method (M16D, 0, NotSerialized)
    {
        If (Y100)
        {
            TS00 ("m16d")
        }
        Else
        {
            Debug = "m16d"
        }

        If (!Y900)
        {
            Debug = "Test m16d skipped!"
            Return (Zero)
        }

        /* T3:I0-I4 */

        If (Y104)
        {
            Store (Index (Package (0x01){}, 0x00), Local0)
            M1A0 (Local0, C008, Ones, 0x0501)
        }

        Store (Index (Package (0x01)
                {
                    0x00ABCDEF
                }, 0x00), Local0)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0x00ABCDEF, __LINE__)
        Store (Index (Package (0x01)
                {
                    "123456789"
                }, 0x00), Local0)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "123456789", __LINE__)
        Store (Index (Package (0x01)
                {
                    "qwrtyuiop"
                }, 0x00), Local0)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "qwrtyuiop", __LINE__)
        Store (Index (Package (0x01)
                {
                    Buffer (0x08)
                    {
                         0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08   // ........
                    }
                }, 0x00), Local0)
        M1A2 (Local0, C00B, 0x00, 0x00, C00B, Buffer (0x08)
            {
                 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08   // ........
            }, 0x0505)
        Store (Index (Package (0x01)
                {
                    Package (0x01)
                    {
                        0x00ABCDEF
                    }
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0x00ABCDEF, __LINE__)
        Store (Index (Package (0x01)
                {
                    Package (0x01)
                    {
                        "123456789"
                    }
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "123456789", __LINE__)
        Store (Index (Package (0x01)
                {
                    Package (0x01)
                    {
                        "qwrtyuiop"
                    }
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "qwrtyuiop", __LINE__)
        Store (Index (Package (0x01)
                {
                    Package (0x01)
                    {
                        Buffer (0x09)
                        {
                            /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
                            /* 0008 */  0x09                                             // .
                        }
                    }
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C00B, Buffer (0x09)
            {
                /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
                /* 0008 */  0x09                                             // .
            }, 0x0509)
        Store (Index (Package (0x01)
                {
                    Package (0x01)
                    {
                        Package (0x01)
                        {
                            0x00ABCDEF
                        }
                    }
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x02, 0x00, C009, 0x00ABCDEF, __LINE__)
        Store (Index (Package (0x01)
                {
                    Package (0x01)
                    {
                        Package (0x01)
                        {
                            "123456789"
                        }
                    }
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x02, 0x00, C00A, "123456789", __LINE__)
        Store (Index (Package (0x01)
                {
                    Package (0x01)
                    {
                        Package (0x01)
                        {
                            "qwrtyuiop"
                        }
                    }
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x02, 0x00, C00A, "qwrtyuiop", __LINE__)
        Store (Index (Package (0x01)
                {
                    Package (0x01)
                    {
                        Package (0x01)
                        {
                            Buffer (0x09)
                            {
                                /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
                                /* 0008 */  0x09                                             // .
                            }
                        }
                    }
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x02, 0x00, C00B, Buffer (0x09)
            {
                /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
                /* 0008 */  0x09                                             // .
            }, 0x050D)
        Store (Index (Package (0x01)
                {
                    Package (0x01)
                    {
                        Package (0x01)
                        {
                            Package (0x01)
                            {
                                0x00ABCDEF
                            }
                        }
                    }
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x03, 0x00, C009, 0x00ABCDEF, __LINE__)
        Store (Index (Package (0x01)
                {
                    Package (0x01)
                    {
                        Package (0x01)
                        {
                            Package (0x01)
                            {
                                "123456789"
                            }
                        }
                    }
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x03, 0x00, C00A, "123456789", __LINE__)
        Store (Index (Package (0x01)
                {
                    Package (0x01)
                    {
                        Package (0x01)
                        {
                            Package (0x01)
                            {
                                "qwrtyuiop"
                            }
                        }
                    }
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x03, 0x00, C00A, "qwrtyuiop", __LINE__)
        Store (Index (Package (0x01)
                {
                    Package (0x01)
                    {
                        Package (0x01)
                        {
                            Package (0x01)
                            {
                                Buffer (0x09)
                                {
                                    /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
                                    /* 0008 */  0x09                                             // .
                                }
                            }
                        }
                    }
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x03, 0x00, C00B, Buffer (0x09)
            {
                /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
                /* 0008 */  0x09                                             // .
            }, 0x0511)
        /* T3:IR0-IR4 */

        If (Y104)
        {
            Local0 = Index (Package (0x01){}, 0x00, Local1)
            M1A0 (Local0, C008, Ones, 0x0512)
            M1A0 (Local1, C008, Ones, 0x0513)
        }

        Local0 = Index (Package (0x01)
                {
                    0x00ABCDEF
                }, 0x00, Local1)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0x00ABCDEF, __LINE__)
        M1A2 (Local1, C009, 0x00, 0x00, C009, 0x00ABCDEF, __LINE__)
        Local0 = Index (Package (0x01)
                {
                    "123456789"
                }, 0x00, Local1)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "123456789", __LINE__)
        M1A2 (Local1, C00A, 0x00, 0x00, C00A, "123456789", __LINE__)
        Local0 = Index (Package (0x01)
                {
                    "qwrtyuiop"
                }, 0x00, Local1)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "qwrtyuiop", __LINE__)
        M1A2 (Local1, C00A, 0x00, 0x00, C00A, "qwrtyuiop", __LINE__)
        Local0 = Index (Package (0x01)
                {
                    Buffer (0x08)
                    {
                         0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08   // ........
                    }
                }, 0x00, Local1)
        M1A2 (Local0, C00B, 0x00, 0x00, C00B, Buffer (0x08)
            {
                 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08   // ........
            }, 0x051A)
        M1A2 (Local1, C00B, 0x00, 0x00, C00B, Buffer (0x08)
            {
                 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08   // ........
            }, 0x051B)
        Local0 = Index (Package (0x01)
                {
                    Package (0x01)
                    {
                        0x00ABCDEF
                    }
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0x00ABCDEF, __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x00, C009, 0x00ABCDEF, __LINE__)
        Local0 = Index (Package (0x01)
                {
                    Package (0x01)
                    {
                        "123456789"
                    }
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "123456789", __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x00, C00A, "123456789", __LINE__)
        Local0 = Index (Package (0x01)
                {
                    Package (0x01)
                    {
                        "qwrtyuiop"
                    }
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "qwrtyuiop", __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x00, C00A, "qwrtyuiop", __LINE__)
        Local0 = Index (Package (0x01)
                {
                    Package (0x01)
                    {
                        Buffer (0x09)
                        {
                            /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
                            /* 0008 */  0x09                                             // .
                        }
                    }
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x01, 0x00, C00B, Buffer (0x09)
            {
                /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
                /* 0008 */  0x09                                             // .
            }, 0x0522)
        M1A2 (Local1, C00C, 0x01, 0x00, C00B, Buffer (0x09)
            {
                /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
                /* 0008 */  0x09                                             // .
            }, 0x0523)
        Local0 = Index (Package (0x01)
                {
                    Package (0x01)
                    {
                        Package (0x01)
                        {
                            0x00ABCDEF
                        }
                    }
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x02, 0x00, C009, 0x00ABCDEF, __LINE__)
        M1A2 (Local1, C00C, 0x02, 0x00, C009, 0x00ABCDEF, __LINE__)
        Local0 = Index (Package (0x01)
                {
                    Package (0x01)
                    {
                        Package (0x01)
                        {
                            "123456789"
                        }
                    }
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x02, 0x00, C00A, "123456789", __LINE__)
        M1A2 (Local1, C00C, 0x02, 0x00, C00A, "123456789", __LINE__)
        Local0 = Index (Package (0x01)
                {
                    Package (0x01)
                    {
                        Package (0x01)
                        {
                            "qwrtyuiop"
                        }
                    }
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x02, 0x00, C00A, "qwrtyuiop", __LINE__)
        M1A2 (Local1, C00C, 0x02, 0x00, C00A, "qwrtyuiop", __LINE__)
        Local0 = Index (Package (0x01)
                {
                    Package (0x01)
                    {
                        Package (0x01)
                        {
                            Buffer (0x09)
                            {
                                /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
                                /* 0008 */  0x09                                             // .
                            }
                        }
                    }
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x02, 0x00, C00B, Buffer (0x09)
            {
                /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
                /* 0008 */  0x09                                             // .
            }, 0x052A)
        M1A2 (Local1, C00C, 0x02, 0x00, C00B, Buffer (0x09)
            {
                /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
                /* 0008 */  0x09                                             // .
            }, 0x052B)
        Local0 = Index (Package (0x01)
                {
                    Package (0x01)
                    {
                        Package (0x01)
                        {
                            Package (0x01)
                            {
                                0x00ABCDEF
                            }
                        }
                    }
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x03, 0x00, C009, 0x00ABCDEF, __LINE__)
        M1A2 (Local1, C00C, 0x03, 0x00, C009, 0x00ABCDEF, __LINE__)
        Local0 = Index (Package (0x01)
                {
                    Package (0x01)
                    {
                        Package (0x01)
                        {
                            Package (0x01)
                            {
                                "123456789"
                            }
                        }
                    }
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x03, 0x00, C00A, "123456789", __LINE__)
        M1A2 (Local1, C00C, 0x03, 0x00, C00A, "123456789", __LINE__)
        Local0 = Index (Package (0x01)
                {
                    Package (0x01)
                    {
                        Package (0x01)
                        {
                            Package (0x01)
                            {
                                "qwrtyuiop"
                            }
                        }
                    }
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x03, 0x00, C00A, "qwrtyuiop", __LINE__)
        M1A2 (Local1, C00C, 0x03, 0x00, C00A, "qwrtyuiop", __LINE__)
        Local0 = Index (Package (0x01)
                {
                    Package (0x01)
                    {
                        Package (0x01)
                        {
                            Package (0x01)
                            {
                                Buffer (0x09)
                                {
                                    /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
                                    /* 0008 */  0x09                                             // .
                                }
                            }
                        }
                    }
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x03, 0x00, C00B, Buffer (0x09)
            {
                /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
                /* 0008 */  0x09                                             // .
            }, 0x0532)
        M1A2 (Local1, C00C, 0x03, 0x00, C00B, Buffer (0x09)
            {
                /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
                /* 0008 */  0x09                                             // .
            }, 0x0533)
    }

    /* /////////////////////////////////////////////////////////////////////////// */
    /* */
    /* TABLE 4: all the legal ways to generate references to the named objects */
    /*          being elements of Package */
    /* */
    /* /////////////////////////////////////////////////////////////////////////// */
    Method (M16E, 0, Serialized)
    {
        If (Y100)
        {
            TS00 ("m16e")
        }
        Else
        {
            Debug = "m16e"
        }

        If (!Y900)
        {
            Debug = "Test m16e skipped!"
            Return (Zero)
        }

        /* Not Computational Data */

        Event (E900)
        Mutex (MX90, 0x00)
        Device (D900)
        {
        }

        ThermalZone (TZ90)
        {
        }

        Processor (PR90, 0x00, 0xFFFFFFFF, 0x00){}
        OperationRegion (R900, SystemMemory, 0x0100, 0x0100)
        OperationRegion (R9Z0, SystemMemory, 0x0100, 0x0100)
        PowerResource (PW90, 0x01, 0x0000)
        {
            Method (MMMM, 0, NotSerialized)
            {
                Return (0x00)
            }
        }

        /* Computational Data */

        Name (I900, 0xFE7CB391D65A5000)
        Name (I901, 0x41795001)
        Name (I902, 0x00)
        Name (I903, 0xFFFFFFFFFFFFFFFF)
        Name (I904, 0xFFFFFFFF)
        Name (S900, "12345002")
        Name (S901, "qwrtyu5003")
        Name (B900, Buffer (0x05)
        {
             0xF0, 0xF1, 0xF2, 0xF3, 0xF4                     // .....
        })
        Name (B9Z0, Buffer (0x05)
        {
             0xF0, 0xF1, 0xF2, 0xF3, 0xF4                     // .....
        })
        CreateField (B900, 0x00, 0x08, BF90)
        Field (R900, ByteAcc, NoLock, Preserve)
        {
            F900,   8,
            F901,   8,
            F902,   8,
            F903,   8
        }

        BankField (R900, F901, 0x00, ByteAcc, NoLock, Preserve)
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
            0xABCD5004,
            0x1122334455665005
        })
        Name (P902, Package (0x02)
        {
            "12345006",
            "q1w2e3r4t5y6u7i85007"
        })
        Name (P903, Package (0x02)
        {
            "qwrtyuiop5008",
            "1234567890abdef0255009"
        })
        Name (P904, Package (0x02)
        {
            Buffer (0x03)
            {
                 0xF5, 0xF6, 0xF7                                 // ...
            },

            Buffer (0x02)
            {
                 0xF8, 0xF9                                       // ..
            }
        })
        Name (P905, Package (0x01)
        {
            Package (0x03)
            {
                0x0ABC500A,
                "0xabc500b",
                "abc500c"
            }
        })
        Name (P906, Package (0x01)
        {
            Package (0x01)
            {
                "abc500d"
            }
        })
        Name (P907, Package (0x01)
        {
            Package (0x01)
            {
                "aqwevbgnm500e"
            }
        })
        Name (P908, Package (0x01)
        {
            Package (0x01)
            {
                Buffer (0x05)
                {
                     0xFA, 0xFB, 0xFC, 0xFD, 0xFE                     // .....
                }
            }
        })
        Name (P909, Package (0x01)
        {
            Package (0x01)
            {
                Package (0x01)
                {
                    0x0ABC500F
                }
            }
        })
        Name (P90A, Package (0x01)
        {
            Package (0x01)
            {
                Package (0x01)
                {
                    "12345010"
                }
            }
        })
        Name (P90B, Package (0x01)
        {
            Package (0x01)
            {
                Package (0x01)
                {
                    "zxswefas5011"
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
                         0xFF, 0x40, 0x41                                 // .@A
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
            R900
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
            Return (0x0ABC5012)
        }

        Method (M902, 0, NotSerialized)
        {
            Return ("zxvgswquiy5013")
        }

        Method (M903, 0, NotSerialized)
        {
            Return (Buffer (0x01)
            {
                 0x42                                             // B
            })
        }

        Method (M904, 0, NotSerialized)
        {
            Return (Package (0x01)
            {
                0x0ABC5014
            })
        }

        Method (M905, 0, NotSerialized)
        {
            Return (Package (0x01)
            {
                "lkjhgtre5015"
            })
        }

        Method (M906, 0, NotSerialized)
        {
            Return (Package (0x01)
            {
                Buffer (0x01)
                {
                     0x43                                             // C
                }
            })
        }

        Method (M907, 0, NotSerialized)
        {
            Return (Package (0x01)
            {
                Package (0x01)
                {
                    0x0ABC5016
                }
            })
        }

        Method (M908, 0, NotSerialized)
        {
            Return (I900) /* \M16E.I900 */
        }

        Method (M909, 0, NotSerialized)
        {
            Return (I901) /* \M16E.I901 */
        }

        Method (M90A, 0, NotSerialized)
        {
            Return (S900) /* \M16E.S900 */
        }

        Method (M90B, 0, NotSerialized)
        {
            Return (S901) /* \M16E.S901 */
        }

        Method (M90C, 0, NotSerialized)
        {
            Return (B9Z0) /* \M16E.B9Z0 */
        }

        Method (M90D, 0, NotSerialized)
        {
            Return (F900) /* \M16E.F900 */
        }

        Method (M90E, 0, NotSerialized)
        {
            Return (BN90) /* \M16E.BN90 */
        }

        Method (M90F, 0, NotSerialized)
        {
            Return (IF90) /* \M16E.IF90 */
        }

        Method (M910, 0, NotSerialized)
        {
            Return (BF90) /* \M16E.BF90 */
        }

        Method (M911, 0, NotSerialized)
        {
            Return (D900) /* \M16E.D900 */
        }

        Method (M912, 0, NotSerialized)
        {
            Return (E900) /* \M16E.E900 */
        }

        Method (M913, 0, NotSerialized)
        {
            Return (M901 ())
        }

        Method (M914, 0, NotSerialized)
        {
            Return (MX90) /* \M16E.MX90 */
        }

        Method (M915, 0, NotSerialized)
        {
            Return (R900) /* \M16E.R900 */
        }

        Method (M916, 0, NotSerialized)
        {
            Return (PW90) /* \M16E.PW90 */
        }

        Method (M917, 0, NotSerialized)
        {
            Return (PR90) /* \M16E.PR90 */
        }

        Method (M918, 0, NotSerialized)
        {
            Return (TZ90) /* \M16E.TZ90 */
        }

        Method (M919, 0, NotSerialized)
        {
            Return (P900) /* \M16E.P900 */
        }

        Method (M91A, 0, NotSerialized)
        {
            Return (P901) /* \M16E.P901 */
        }

        Method (M91B, 0, NotSerialized)
        {
            Return (P902) /* \M16E.P902 */
        }

        Method (M91C, 0, NotSerialized)
        {
            Return (P903) /* \M16E.P903 */
        }

        Method (M91D, 0, NotSerialized)
        {
            Return (P904) /* \M16E.P904 */
        }

        Method (M91E, 0, NotSerialized)
        {
            Return (P905) /* \M16E.P905 */
        }

        Method (M91F, 0, NotSerialized)
        {
            Return (P906) /* \M16E.P906 */
        }

        Method (M920, 0, NotSerialized)
        {
            Return (P907) /* \M16E.P907 */
        }

        Method (M921, 0, NotSerialized)
        {
            Return (P908) /* \M16E.P908 */
        }

        Method (M922, 0, NotSerialized)
        {
            Return (P909) /* \M16E.P909 */
        }

        Method (M923, 0, NotSerialized)
        {
            Return (P90A) /* \M16E.P90A */
        }

        Method (M924, 0, NotSerialized)
        {
            Return (P90B) /* \M16E.P90B */
        }

        Method (M925, 0, NotSerialized)
        {
            Return (P90C) /* \M16E.P90C */
        }

        Method (M926, 0, NotSerialized)
        {
            Return (P90D) /* \M16E.P90D */
        }

        Method (M927, 0, NotSerialized)
        {
            Return (P90E) /* \M16E.P90E */
        }

        Method (M928, 0, NotSerialized)
        {
            Return (P90F) /* \M16E.P90F */
        }

        Method (M929, 0, NotSerialized)
        {
            Return (P910) /* \M16E.P910 */
        }

        Method (M92A, 0, NotSerialized)
        {
            Return (P911) /* \M16E.P911 */
        }

        Method (M92B, 0, NotSerialized)
        {
            Return (P912) /* \M16E.P912 */
        }

        Method (M92C, 0, NotSerialized)
        {
            Return (P913) /* \M16E.P913 */
        }

        Method (M92D, 0, NotSerialized)
        {
            Return (P914) /* \M16E.P914 */
        }

        Method (M92E, 0, NotSerialized)
        {
            Return (P915) /* \M16E.P915 */
        }

        Method (M92F, 0, NotSerialized)
        {
            Return (P916) /* \M16E.P916 */
        }

        Method (M930, 0, NotSerialized)
        {
            Return (P917) /* \M16E.P917 */
        }

        Method (M931, 0, NotSerialized)
        {
            Return (P918) /* \M16E.P918 */
        }

        Method (M932, 0, NotSerialized)
        {
            Return (P919) /* \M16E.P919 */
        }

        Method (M933, 0, NotSerialized)
        {
            Return (P91A) /* \M16E.P91A */
        }

        Method (M934, 0, NotSerialized)
        {
            Return (P91B) /* \M16E.P91B */
        }

        Method (M935, 0, NotSerialized)
        {
            Return (P91C) /* \M16E.P91C */
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
            0xABCD5018,
            0xABCD5019
        })
        Name (P954, Package (0x02)
        {
            0xABCD5018,
            0xABCD5019
        })
        /* Check that all the data (local) are not corrupted */

        Method (M000, 0, NotSerialized)
        {
            /* Computational Data */
            /* Integer */
            Local0 = ObjectType (I900)
            If ((Local0 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C009)
            }

            If ((I900 != 0xFE7CB391D65A5000))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, I900, 0xFE7CB391D65A5000)
            }

            Local0 = ObjectType (I901)
            If ((Local0 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C009)
            }

            If ((I901 != 0x41795001))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, I901, 0x41795001)
            }

            Local0 = ObjectType (I902)
            If ((Local0 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C009)
            }

            If ((I902 != 0x00))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, I902, 0x00)
            }

            Local0 = ObjectType (I903)
            If ((Local0 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C009)
            }

            If ((I903 != 0xFFFFFFFFFFFFFFFF))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, I903, 0xFFFFFFFFFFFFFFFF)
            }

            Local0 = ObjectType (I904)
            If ((Local0 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C009)
            }

            If ((I904 != 0xFFFFFFFF))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, I904, 0xFFFFFFFF)
            }

            /* String */

            Local0 = ObjectType (S900)
            If ((Local0 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C00A)
            }

            If ((S900 != "12345002"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, S900, "12345002")
            }

            Local0 = ObjectType (S901)
            If ((Local0 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C00A)
            }

            If ((S901 != "qwrtyu5003"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, S901, "qwrtyu5003")
            }

            /* Buffer */

            Local0 = ObjectType (B900)
            If ((Local0 != C00B))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C00B)
            }

            If ((B900 != Buffer (0x05)
                        {
                             0xF0, 0xF1, 0xF2, 0xF3, 0xF4                     // .....
                        }))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, B900, Buffer (0x05)
                    {
                         0xF0, 0xF1, 0xF2, 0xF3, 0xF4                     // .....
                    })
            }

            /* Buffer Field */

            Local0 = ObjectType (BF90)
            If ((Local0 != C016))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local0, C016)
            }

            If (BF90 != Buffer(){0xF0})
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, BF90, Buffer(){0xF0})
            }

            /* One level Package */

            Store (P900 [0x00], Local0)
            Local1 = ObjectType (Local0)
            If ((Local1 != C008))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, C008)
            }

            Store (P901 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C009)
            }

            If ((Local1 != 0xABCD5004))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, 0xABCD5004)
            }

            Store (P901 [0x01], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C009)
            }

            If ((Local1 != 0x1122334455665005))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, 0x1122334455665005)
            }

            Store (P902 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C00A)
            }

            If ((Local1 != "12345006"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, "12345006")
            }

            Store (P902 [0x01], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C00A)
            }

            If ((Local1 != "q1w2e3r4t5y6u7i85007"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, "q1w2e3r4t5y6u7i85007")
            }

            Store (P903 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C00A)
            }

            If ((Local1 != "qwrtyuiop5008"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, "qwrtyuiop5008")
            }

            Store (P903 [0x01], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C00A)
            }

            If ((Local1 != "1234567890abdef0255009"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, "1234567890abdef0255009")
            }

            Store (P904 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C00B))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C00B)
            }

            If ((Local1 != Buffer (0x03)
                        {
                             0xF5, 0xF6, 0xF7                                 // ...
                        }))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, Buffer (0x03)
                    {
                         0xF5, 0xF6, 0xF7                                 // ...
                    })
            }

            Store (P904 [0x01], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C00B))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C00B)
            }

            If ((Local1 != Buffer (0x02)
                        {
                             0xF8, 0xF9                                       // ..
                        }))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, Buffer (0x02)
                    {
                         0xF8, 0xF9                                       // ..
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
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local4, C009)
            }

            If ((Local3 != 0x0ABC500A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local3, 0x0ABC500A)
            }

            Store (P905 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Store (Local1 [0x01], Local2)
            Local3 = DerefOf (Local2)
            Local4 = ObjectType (Local3)
            If ((Local4 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local4, C00A)
            }

            If ((Local3 != "0xabc500b"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local3, "0xabc500b")
            }

            Store (P905 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Store (Local1 [0x02], Local2)
            Local3 = DerefOf (Local2)
            Local4 = ObjectType (Local3)
            If ((Local4 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local4, C00A)
            }

            If ((Local3 != "abc500c"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local3, "abc500c")
            }

            Store (P906 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Store (Local1 [0x00], Local2)
            Local3 = DerefOf (Local2)
            Local4 = ObjectType (Local3)
            If ((Local4 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local4, C00A)
            }

            If ((Local3 != "abc500d"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local3, "abc500d")
            }

            Store (P907 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Store (Local1 [0x00], Local2)
            Local3 = DerefOf (Local2)
            Local4 = ObjectType (Local3)
            If ((Local4 != C00A))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local4, C00A)
            }

            If ((Local3 != "aqwevbgnm500e"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local3, "aqwevbgnm500e")
            }

            Store (P908 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Store (Local1 [0x00], Local2)
            Local3 = DerefOf (Local2)
            Local4 = ObjectType (Local3)
            If ((Local4 != C00B))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local4, C00B)
            }

            If ((Local3 != Buffer (0x05)
                        {
                             0xFA, 0xFB, 0xFC, 0xFD, 0xFE                     // .....
                        }))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local3, Buffer (0x05)
                    {
                         0xFA, 0xFB, 0xFC, 0xFD, 0xFE                     // .....
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
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local6, C009)
            }

            If ((Local5 != 0x0ABC500F))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local5, 0x0ABC500F)
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
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local6, C00A)
            }

            If ((Local5 != "12345010"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local5, "12345010")
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
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local6, C00A)
            }

            If ((Local5 != "zxswefas5011"))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local5, "zxswefas5011")
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
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local6, C00B)
            }

            If ((Local5 != Buffer (0x03)
                        {
                             0xFF, 0x40, 0x41                                 // .@A
                        }))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local5, Buffer (0x03)
                    {
                         0xFF, 0x40, 0x41                                 // .@A
                    })
            }

            Store (P953 [0x00], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C009)
            }

            If ((Local1 != 0xABCD5018))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, 0xABCD5018)
            }

            Store (P953 [0x01], Local0)
            Local1 = DerefOf (Local0)
            Local2 = ObjectType (Local1)
            If ((Local2 != C009))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local2, C009)
            }

            If ((Local1 != 0xABCD5019))
            {
                ERR (C080, Z077, __LINE__, 0x00, 0x00, Local1, 0xABCD5019)
            }

            /* Not Computational Data */

            M1AA (C080, E900, C00F, 0x00, 0x013B)
            M1AA (C080, MX90, C011, 0x00, 0x013C)
            M1AA (C080, D900, C00E, 0x00, 0x013D)
            If (Y508)
            {
                M1AA (C080, TZ90, C015, 0x00, 0x013E)
            }

            M1AA (C080, PR90, C014, 0x00, 0x013F)
            M1AA (C080, R900, C012, 0x00, 0x0140)
            M1AA (C080, PW90, C013, 0x00, 0x0141)
                /*
         *	// Field Unit (Field)
         *
         *	if (LNotEqual(f900, 0xd7)) {
         *		err(c080, z077, __LINE__, 0, 0, f900, 0xd7)
         *	}
         *
         *	// Field Unit (IndexField)
         *
         *	if (LNotEqual(if90, 0xd7)) {
         *		err(c080, z077, __LINE__, 0, 0, if90, 0xd7)
         *	}
         */
        }

        /* m000 */
        /* T4:x,I1-I14,x,x */
        /* Computational Data */
        Store (Index (Package (0x01)
                {
                    I900
                }, 0x00), Local0)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xFE7CB391D65A5000, __LINE__)
        Store (Index (Package (0x01)
                {
                    I901
                }, 0x00), Local0)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0x41795001, __LINE__)
        Store (Index (Package (0x01)
                {
                    S900
                }, 0x00), Local0)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "12345002", __LINE__)
        Store (Index (Package (0x01)
                {
                    S901
                }, 0x00), Local0)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "qwrtyu5003", __LINE__)
        Store (Index (Package (0x01)
                {
                    B900
                }, 0x00), Local0)
        M1A2 (Local0, C00B, 0x00, 0x00, C00B, Buffer (0x05)
            {
                 0xF0, 0xF1, 0xF2, 0xF3, 0xF4                     // .....
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
            M1A2 (Local0, C016, 0x00, 0x00, C016, 0xF0, __LINE__)
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
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xABCD5004, __LINE__)
        M1A2 (Local0, C00C, 0x01, 0x01, C009, 0x1122334455665005, __LINE__)
        Store (Index (Package (0x01)
                {
                    P902
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "12345006", __LINE__)
        M1A2 (Local0, C00C, 0x01, 0x01, C00A, "q1w2e3r4t5y6u7i85007", __LINE__)
        Store (Index (Package (0x01)
                {
                    P903
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "qwrtyuiop5008", __LINE__)
        M1A2 (Local0, C00C, 0x01, 0x01, C00A, "1234567890abdef0255009", __LINE__)
        Store (Index (Package (0x01)
                {
                    P904
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C00B, Buffer (0x03)
            {
                 0xF5, 0xF6, 0xF7                                 // ...
            }, 0x032B)
        Store (Index (Package (0x01)
                {
                    P905
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x02, 0x00, C009, 0x0ABC500A, __LINE__)
        M1A2 (Local0, C00C, 0x02, 0x01, C00A, "0xabc500b", __LINE__)
        Store (Index (Package (0x01)
                {
                    P906
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x02, 0x00, C00A, "abc500d", __LINE__)
        Store (Index (Package (0x01)
                {
                    P907
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x02, 0x00, C00A, "aqwevbgnm500e", __LINE__)
        Store (Index (Package (0x01)
                {
                    P908
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x02, 0x00, C00B, Buffer (0x05)
            {
                 0xFA, 0xFB, 0xFC, 0xFD, 0xFE                     // .....
            }, 0x0330)
        Store (Index (Package (0x01)
                {
                    P909
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x03, 0x00, C009, 0x0ABC500F, __LINE__)
        Store (Index (Package (0x01)
                {
                    P90A
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x03, 0x00, C00A, "12345010", __LINE__)
        Store (Index (Package (0x01)
                {
                    P90B
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x03, 0x00, C00A, "zxswefas5011", __LINE__)
        Store (Index (Package (0x01)
                {
                    P90C
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x03, 0x00, C00B, Buffer (0x03)
            {
                 0xFF, 0x40, 0x41                                 // .@A
            }, 0x0334)
        Store (Index (Package (0x01)
                {
                    P90D
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xFE7CB391D65A5000, __LINE__)
        Store (Index (Package (0x01)
                {
                    P90E
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0x41795001, __LINE__)
        Store (Index (Package (0x01)
                {
                    P90F
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "12345002", __LINE__)
        Store (Index (Package (0x01)
                {
                    P910
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "qwrtyu5003", __LINE__)
        Store (Index (Package (0x01)
                {
                    P911
                }, 0x00), Local0)
        M1A2 (Local0, C00C, 0x01, 0x00, C00B, Buffer (0x05)
            {
                 0xF0, 0xF1, 0xF2, 0xF3, 0xF4                     // .....
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
            M1A2 (Local0, C00C, 0x01, 0x00, C016, 0xF0, __LINE__)
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
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0xFE7CB391D65A5000, __LINE__)
        M1A2 (Local1, C009, 0x00, 0x00, C009, 0xFE7CB391D65A5000, __LINE__)
        Local0 = Index (Package (0x01)
                {
                    I901
                }, 0x00, Local1)
        M1A2 (Local0, C009, 0x00, 0x00, C009, 0x41795001, __LINE__)
        M1A2 (Local1, C009, 0x00, 0x00, C009, 0x41795001, __LINE__)
        Local0 = Index (Package (0x01)
                {
                    S900
                }, 0x00, Local1)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "12345002", __LINE__)
        M1A2 (Local1, C00A, 0x00, 0x00, C00A, "12345002", __LINE__)
        Local0 = Index (Package (0x01)
                {
                    S901
                }, 0x00, Local1)
        M1A2 (Local0, C00A, 0x00, 0x00, C00A, "qwrtyu5003", __LINE__)
        M1A2 (Local1, C00A, 0x00, 0x00, C00A, "qwrtyu5003", __LINE__)
        Local0 = Index (Package (0x01)
                {
                    B900
                }, 0x00, Local1)
        M1A2 (Local0, C00B, 0x00, 0x00, C00B, Buffer (0x05)
            {
                 0xF0, 0xF1, 0xF2, 0xF3, 0xF4                     // .....
            }, 0x03B9)
        M1A2 (Local1, C00B, 0x00, 0x00, C00B, Buffer (0x05)
            {
                 0xF0, 0xF1, 0xF2, 0xF3, 0xF4                     // .....
            }, 0x03BA)
        If (Y118)
        {
            Local0 = Index (Package (0x01)
                    {
                        F900
                    }, 0x00, Local1)
            M1A2 (Local0, C00D, 0x00, 0x00, C009, 0x00, __LINE__)
            M1A2 (Local1, C00D, 0x00, 0x00, C009, 0x00, __LINE__)
            Local0 = Index (Package (0x01)
                    {
                        BN90
                    }, 0x00, Local1)
            M1A2 (Local0, C00D, 0x00, 0x00, C009, 0x00, __LINE__)
            M1A2 (Local1, C00D, 0x00, 0x00, C009, 0x00, __LINE__)
            Local0 = Index (Package (0x01)
                    {
                        IF90
                    }, 0x00, Local1)
            M1A2 (Local0, C00D, 0x00, 0x00, C009, 0x00, __LINE__)
            M1A2 (Local1, C00D, 0x00, 0x00, C009, 0x00, __LINE__)
            Local0 = Index (Package (0x01)
                    {
                        BF90
                    }, 0x00, Local1)
            M1A2 (Local0, C016, 0x00, 0x00, C009, 0xF0, __LINE__)
            M1A2 (Local1, C016, 0x00, 0x00, C009, 0xF0, __LINE__)
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
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xABCD5004, __LINE__)
        M1A2 (Local0, C00C, 0x01, 0x01, C009, 0x1122334455665005, __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x00, C009, 0xABCD5004, __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x01, C009, 0x1122334455665005, __LINE__)
        Local0 = Index (Package (0x01)
                {
                    P902
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "12345006", __LINE__)
        M1A2 (Local0, C00C, 0x01, 0x01, C00A, "q1w2e3r4t5y6u7i85007", __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x00, C00A, "12345006", __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x01, C00A, "q1w2e3r4t5y6u7i85007", __LINE__)
        Local0 = Index (Package (0x01)
                {
                    P903
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "qwrtyuiop5008", __LINE__)
        M1A2 (Local0, C00C, 0x01, 0x01, C00A, "1234567890abdef0255009", __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x00, C00A, "qwrtyuiop5008", __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x01, C00A, "1234567890abdef0255009", __LINE__)
        Local0 = Index (Package (0x01)
                {
                    P904
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x01, 0x00, C00B, Buffer (0x03)
            {
                 0xF5, 0xF6, 0xF7                                 // ...
            }, 0x03DF)
        M1A2 (Local1, C00C, 0x01, 0x00, C00B, Buffer (0x03)
            {
                 0xF5, 0xF6, 0xF7                                 // ...
            }, 0x03E0)
        Local0 = Index (Package (0x01)
                {
                    P905
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x02, 0x00, C009, 0x0ABC500A, __LINE__)
        M1A2 (Local0, C00C, 0x02, 0x01, C00A, "0xabc500b", __LINE__)
        M1A2 (Local1, C00C, 0x02, 0x00, C009, 0x0ABC500A, __LINE__)
        M1A2 (Local1, C00C, 0x02, 0x01, C00A, "0xabc500b", __LINE__)
        Local0 = Index (Package (0x01)
                {
                    P906
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x02, 0x00, C00A, "abc500d", __LINE__)
        M1A2 (Local1, C00C, 0x02, 0x00, C00A, "abc500d", __LINE__)
        Local0 = Index (Package (0x01)
                {
                    P907
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x02, 0x00, C00A, "aqwevbgnm500e", __LINE__)
        M1A2 (Local1, C00C, 0x02, 0x00, C00A, "aqwevbgnm500e", __LINE__)
        Local0 = Index (Package (0x01)
                {
                    P908
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x02, 0x00, C00B, Buffer (0x05)
            {
                 0xFA, 0xFB, 0xFC, 0xFD, 0xFE                     // .....
            }, 0x03E9)
        M1A2 (Local1, C00C, 0x02, 0x00, C00B, Buffer (0x05)
            {
                 0xFA, 0xFB, 0xFC, 0xFD, 0xFE                     // .....
            }, 0x03EA)
        Local0 = Index (Package (0x01)
                {
                    P909
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x03, 0x00, C009, 0x0ABC500F, __LINE__)
        M1A2 (Local1, C00C, 0x03, 0x00, C009, 0x0ABC500F, __LINE__)
        Local0 = Index (Package (0x01)
                {
                    P90A
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x03, 0x00, C00A, "12345010", __LINE__)
        M1A2 (Local1, C00C, 0x03, 0x00, C00A, "12345010", __LINE__)
        Local0 = Index (Package (0x01)
                {
                    P90B
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x03, 0x00, C00A, "zxswefas5011", __LINE__)
        M1A2 (Local1, C00C, 0x03, 0x00, C00A, "zxswefas5011", __LINE__)
        Local0 = Index (Package (0x01)
                {
                    P90C
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x03, 0x00, C00B, Buffer (0x03)
            {
                 0xFF, 0x40, 0x41                                 // .@A
            }, 0x03F1)
        M1A2 (Local1, C00C, 0x03, 0x00, C00B, Buffer (0x03)
            {
                 0xFF, 0x40, 0x41                                 // .@A
            }, 0x03F2)
        Local0 = Index (Package (0x01)
                {
                    P90D
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0xFE7CB391D65A5000, __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x00, C009, 0xFE7CB391D65A5000, __LINE__)
        Local0 = Index (Package (0x01)
                {
                    P90E
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x01, 0x00, C009, 0x41795001, __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x00, C009, 0x41795001, __LINE__)
        Local0 = Index (Package (0x01)
                {
                    P90F
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "12345002", __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x00, C00A, "12345002", __LINE__)
        Local0 = Index (Package (0x01)
                {
                    P910
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x01, 0x00, C00A, "qwrtyu5003", __LINE__)
        M1A2 (Local1, C00C, 0x01, 0x00, C00A, "qwrtyu5003", __LINE__)
        Local0 = Index (Package (0x01)
                {
                    P911
                }, 0x00, Local1)
        M1A2 (Local0, C00C, 0x01, 0x00, C00B, Buffer (0x05)
            {
                 0xF0, 0xF1, 0xF2, 0xF3, 0xF4                     // .....
            }, 0x03FB)
        M1A2 (Local1, C00C, 0x01, 0x00, C00B, Buffer (0x05)
            {
                 0xF0, 0xF1, 0xF2, 0xF3, 0xF4                     // .....
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
            M1A2 (Local0, C00C, 0x01, 0x00, C016, 0xF0, __LINE__)
            M1A2 (Local1, C00C, 0x01, 0x00, C016, 0xF0, __LINE__)
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
        M000 ()
        M1A6 ()
    }

    Method (M16F, 7, NotSerialized)
    {
        C081 = Z077       /* absolute index of file initiating the checking */ /* \Z077 */
        C089 = 0x01      /* flag of Reference, object otherwise */
        If (Arg0)
        {
            M168 ()
        }

        If (Arg1)
        {
            M169 ()
        }

        If (Arg2)
        {
            M16A (C083)
        }

        If (Arg3)
        {
            M16B ()
        }

        If (Arg4)
        {
            M16C (C083)
        }

        If (Arg5)
        {
            M16D ()
        }

        If (Arg6)
        {
            M16E ()
        }
    }

    /* Usual mode */

    Method (M178, 0, NotSerialized)
    {
        C084 = 0x01  /* run verification of references (reading) */
        C085 = 0x00  /* create the chain of references to LocalX, then dereference them */
        Debug = "Usual mode:"
        M16F (0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01)
    }

    /* The mode with the chain of references to LocalX */

    Method (M179, 0, NotSerialized)
    {
        C084 = 0x01  /* run verification of references (reading) */
        C085 = 0x01  /* create the chain of references to LocalX, then dereference them */
        Debug = "The mode with the chain of references to LocalX:"
        M16F (0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01)
    }

    /* Run-method */

    Method (REF1, 0, NotSerialized)
    {
        Debug = "TEST: REF1, References"
        C080 = "REF1" /* name of test */
        C082 = 0x00      /* flag of test of exceptions */
        C083 = 0x00      /* run verification of references (write/read) */
        C086 = 0x00      /* flag, run test till the first error */
        C087 = 0x01      /* apply DeRefOf to ArgX-ObjectReference */
        M178 ()
        M179 ()
    }
