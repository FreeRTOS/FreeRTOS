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
     * Integer arithmetic
     */
    Name (Z083, 0x53)
    /* Verifying 2-parameters, 1-result operator */

    Method (M000, 6, Serialized)
    {
        Local5 = 0x00
        Local3 = Arg1
        While (Local3)
        {
            /* Operands */

            Local6 = (Local5 * 0x02)
            Local0 = DerefOf (Arg3 [Local6])
            Local6++
            Local1 = DerefOf (Arg3 [Local6])
            /* Expected result */

            Local2 = DerefOf (Arg4 [Local5])
            Switch (ToInteger (Arg5))
            {
                Case (0x00)
                {
                    Local7 = (Local0 + Local1)
                    If ((Local7 != Local2))
                    {
                        ERR (Arg0, Z083, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }

                    Local7 = (Local1 + Local0)
                    If ((Local7 != Local2))
                    {
                        ERR (Arg0, Z083, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }
                }
                Case (0x01)
                {
                    Local7 = (Local0 - Local1)
                    If ((Local7 != Local2))
                    {
                        ERR (Arg0, Z083, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }
                }
                Case (0x02)
                {
                    Local7 = (Local0 * Local1)
                    If ((Local7 != Local2))
                    {
                        ERR (Arg0, Z083, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }

                    Local7 = (Local1 * Local0)
                    If ((Local7 != Local2))
                    {
                        ERR (Arg0, Z083, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }
                }
                Case (0x03)
                {
                    Local7 = (Local0 & Local1)
                    If ((Local7 != Local2))
                    {
                        ERR (Arg0, Z083, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }

                    Local7 = (Local1 & Local0)
                    If ((Local7 != Local2))
                    {
                        ERR (Arg0, Z083, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }
                }
                Case (0x04)
                {
                    NAnd (Local0, Local1, Local7)
                    If ((Local7 != Local2))
                    {
                        ERR (Arg0, Z083, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }

                    NAnd (Local1, Local0, Local7)
                    If ((Local7 != Local2))
                    {
                        ERR (Arg0, Z083, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }
                }
                Case (0x05)
                {
                    NOr (Local0, Local1, Local7)
                    If ((Local7 != Local2))
                    {
                        ERR (Arg0, Z083, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }

                    NOr (Local1, Local0, Local7)
                    If ((Local7 != Local2))
                    {
                        ERR (Arg0, Z083, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }
                }
                Case (0x06)
                {
                    Local7 = (Local0 | Local1)
                    If ((Local7 != Local2))
                    {
                        ERR (Arg0, Z083, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }

                    Local7 = (Local1 | Local0)
                    If ((Local7 != Local2))
                    {
                        ERR (Arg0, Z083, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }
                }
                Case (0x07)
                {
                    Local7 = (Local0 ^ Local1)
                    If ((Local7 != Local2))
                    {
                        ERR (Arg0, Z083, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }

                    Local7 = (Local1 ^ Local0)
                    If ((Local7 != Local2))
                    {
                        ERR (Arg0, Z083, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }
                }
                Case (0x08)
                {
                    Local7 = (Local0 % Local1)
                    If ((Local7 != Local2))
                    {
                        ERR (Arg0, Z083, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }
                }
                Case (0x09)
                {
                    Local7 = (Local0 << Local1)
                    If ((Local7 != Local2))
                    {
                        ERR (Arg0, Z083, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }
                }
                Case (0x0A)
                {
                    Local7 = (Local0 >> Local1)
                    If ((Local7 != Local2))
                    {
                        ERR (Arg0, Z083, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }
                }

            }

            Local5++
            Local3--
        }
    }

    /* Verifying 2-parameters, 2-results operator */

    Method (M001, 6, Serialized)
    {
        Local5 = 0x00
        Local4 = Arg1
        While (Local4)
        {
            /* Operands */

            Local6 = (Local5 * 0x02)
            Local0 = DerefOf (Arg3 [Local6])
            Local6++
            Local1 = DerefOf (Arg3 [Local6])
            /* Expected result */

            Local6 = (Local5 * 0x02)
            Local2 = DerefOf (Arg4 [Local6])
            Local6++
            Local3 = DerefOf (Arg4 [Local6])
            Switch (ToInteger (Arg5))
            {
                Case (0x00)
                {
                    Divide (Local0, Local1, Local6, Local7)
                    If ((Local7 != Local2))
                    {
                        ERR (Arg0, Z083, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }

                    If ((Local6 != Local3))
                    {
                        ERR (Arg0, Z083, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }
                }

            }

            Local5++
            Local4--
        }
    }

    /* Verifying 1-parameter, 1-result operator */

    Method (M002, 6, Serialized)
    {
        Local5 = 0x00
        Local3 = Arg1
        While (Local3)
        {
            /* Operand */

            Local0 = DerefOf (Arg3 [Local5])
            /* Expected result */

            Local1 = DerefOf (Arg4 [Local5])
            Switch (ToInteger (Arg5))
            {
                Case (0x00)
                {
                    Local0++
                    If ((Local0 != Local1))
                    {
                        ERR (Arg0, Z083, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }
                }
                Case (0x01)
                {
                    Local0--
                    If ((Local0 != Local1))
                    {
                        ERR (Arg0, Z083, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }
                }
                Case (0x02)
                {
                    Local2 = ~Local0
                    If ((Local2 != Local1))
                    {
                        ERR (Arg0, Z083, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }
                }
                Case (0x03)
                {
                    FindSetLeftBit (Local0, Local2)
                    If ((Local2 != Local1))
                    {
                        ERR (Arg0, Z083, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }
                }
                Case (0x04)
                {
                    FindSetRightBit (Local0, Local2)
                    If ((Local2 != Local1))
                    {
                        ERR (Arg0, Z083, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }
                }

            }

            Local5++
            Local3--
        }
    }

    /* =================================== // */
    /*          Bitwise operands           // */
    /*                                     // */
    /*  (utilized by different operators)  // */
    /* =================================== // */
    Name (P030, Package (0x14)
    {
        0x00,
        0x00,
        0x00,
        0xFFFFFFFF,
        0xFFFFFFFF,
        0xFFFFFFFF,
        0xF0F0F0F0,
        0xFFFFFFFF,
        0x0F0F0F0F,
        0xFFFFFFFF,
        0xF0F0F0F0,
        0x00,
        0x0F0F0F0F,
        0x00,
        0xF0F0F0F0,
        0x11111111,
        0x0F0F0F0F,
        0x11111111,
        0x87654321,
        0x90ABCDFE
    })
    Name (P031, Package (0x14)
    {
        0x00,
        0x00,
        0x00,
        0xFFFFFFFFFFFFFFFF,
        0xFFFFFFFFFFFFFFFF,
        0xFFFFFFFFFFFFFFFF,
        0xF0F0F0F0F0F0F0F0,
        0xFFFFFFFFFFFFFFFF,
        0x0F0F0F0F0F0F0F0F,
        0xFFFFFFFFFFFFFFFF,
        0xF0F0F0F0F0F0F0F0,
        0x00,
        0x0F0F0F0F0F0F0F0F,
        0x00,
        0xF0F0F0F0F0F0F0F0,
        0x1111111111111111,
        0x0F0F0F0F0F0F0F0F,
        0x1111111111111111,
        0x8765432199118822,
        0x90AB66887799CDFE
    })
    Name (P032, Package (0x05)
    {
        0x00,
        0xFFFFFFFF,
        0xF0F0F0F0,
        0x0F0F0F0F,
        0x12345678
    })
    Name (P033, Package (0x05)
    {
        0x00,
        0xFFFFFFFFFFFFFFFF,
        0xF0F0F0F0F0F0F0F0,
        0x0F0F0F0F0F0F0F0F,
        0x123456780AF9BCED
    })
    /* ===================================== Add */

    Name (P000, Package (0x14)
    {
        0x12345678,
        0x6BCDEF01,
        0x62345678,
        0x4BCDEF01,
        0x00,
        0x00,
        0x10000000,
        0x90000000,
        0x00,
        0xFF,
        0x00,
        0xFFFF,
        0x00,
        0xFFFFFFFF,
        /* 32-overflow */

        0x12345678,
        0xF0000000,
        0xFFFFFFFF,
        0xFFFFFFFF,
        0x01,
        0xFFFFFFFF
    })
    Name (P001, Package (0x0A)
    {
        0x7E024579,
        0xAE024579,
        0x00,
        0xA0000000,
        0xFF,
        0xFFFF,
        0xFFFFFFFF,
        /* 32-overflow */

        0x02345678,
        0xFFFFFFFE,
        0x00
    })
    Name (P002, Package (0x1A)
    {
        /* 32-overflow */

        0x12345678,
        0xF0000000,
        0xFFFFFFFF,
        0xFFFFFFFF,
        0x12345678DCABEF98,
        0x6BCDEF0119283746,
        0x72345678DCABEF98,
        0x5BCDEF0119283746,
        0x00,
        0x00,
        0x1000000000000000,
        0x9000000000000000,
        0x00,
        0xFF,
        0x00,
        0xFFFF,
        0x00,
        0xFFFFFFFF,
        0x00,
        0xFFFFFFFFFFFFFFFF,
        /* 64-overflow */

        0x12345678DCABEF98,
        0xF000000000000000,
        0xFFFFFFFFFFFFFFFF,
        0xFFFFFFFFFFFFFFFF,
        0x01,
        0xFFFFFFFFFFFFFFFF
    })
    Name (P003, Package (0x0D)
    {
        /* 32-overflow */

        0x0000000102345678,
        0x00000001FFFFFFFE,
        0x7E024579F5D426DE,
        0xCE024579F5D426DE,
        0x00,
        0xA000000000000000,
        0xFF,
        0xFFFF,
        0xFFFFFFFF,
        0xFFFFFFFFFFFFFFFF,
        /* 64-overflow */

        0x02345678DCABEF98,
        0xFFFFFFFFFFFFFFFE,
        0x00
    })
    Method (ADD0, 0, Serialized)
    {
        Debug = "TEST: ADD0, Integer Add"
        If ((F64 == 0x01))
        {
            M000 (__METHOD__, 0x07, "p000", P000, P001, 0x00)
            M000 (__METHOD__, 0x0D, "p002", P002, P003, 0x00)
        }
        Else
        {
            M000 (__METHOD__, 0x0A, "p000", P000, P001, 0x00)
        }
    }

    /* ===================================== Subtract */

    Name (P004, Package (0x18)
    {
        0x62345678,
        0x4BCDEF01,
        0x00,
        0x00,
        0x90000000,
        0x10000000,
        0xFF,
        0x00,
        0xFFFF,
        0x00,
        0xFFFFFFFF,
        0xFFFFFFFF,
        0xFFFFFFFF,
        0x00,
        /* 32-overflow */

        0x00,
        0x87654321,
        0x12345678,
        0x6BCDEF01,
        0x10000000,
        0x90000000,
        0x00,
        0xFF,
        0x00,
        0xFFFF
    })
    Name (P005, Package (0x0C)
    {
        0x16666777,
        0x00,
        0x80000000,
        0xFF,
        0xFFFF,
        0x00,
        0xFFFFFFFF,
        /* 32-overflow */

        0x789ABCDF,
        0xA6666777,
        0x80000000,
        0xFFFFFF01,
        0xFFFF0001
    })
    Name (P006, Package (0x28)
    {
        /* 32-overflow */

        0x00,
        0x87654321,
        0x12345678,
        0x6BCDEF01,
        0x10000000,
        0x90000000,
        0x00,
        0xFF,
        0x00,
        0xFFFF,
        0x12345678DCABEF98,
        0x6BCDEF0119283746,
        0x72345678DCABEF98,
        0x5BCDEF0119283746,
        0x00,
        0x00,
        0xFFFFFFFFFFFFFFFF,
        0x00,
        0x00,
        0xFFFFFFFFFFFFFFFF,
        0x9000000000000000,
        0x1000000000000000,
        0x1000000000000000,
        0x9000000000000000,
        0xFF,
        0x00,
        0x00,
        0xFF,
        0xFFFF,
        0x00,
        0x00,
        0xFFFF,
        0xFFFFFFFF,
        0x00,
        0x00,
        0xFFFFFFFF,
        0xFFFFFFFFFFFFFFFF,
        0xFFFFFFFFFFFFFFFF,
        0x12345678DCABEF98,
        0xF000000000000000
    })
    Name (P007, Package (0x14)
    {
        /* 32-overflow */

        0xFFFFFFFF789ABCDF,
        0xFFFFFFFFA6666777,
        0xFFFFFFFF80000000,
        0xFFFFFFFFFFFFFF01,
        0xFFFFFFFFFFFF0001,
        0xA6666777C383B852,
        0x16666777C383B852,
        0x00,
        0xFFFFFFFFFFFFFFFF,
        0x01,
        0x8000000000000000,
        0x8000000000000000,
        0xFF,
        0xFFFFFFFFFFFFFF01,
        0xFFFF,
        0xFFFFFFFFFFFF0001,
        0xFFFFFFFF,
        0xFFFFFFFF00000001,
        0x00,
        0x22345678DCABEF98
    })
    Method (SUB0, 0, Serialized)
    {
        Debug = "TEST: SUB0, Integer Subtract"
        If ((F64 == 0x01))
        {
            M000 (__METHOD__, 0x07, "p004", P004, P005, 0x01)
            M000 (__METHOD__, 0x14, "p006", P006, P007, 0x01)
        }
        Else
        {
            M000 (__METHOD__, 0x0C, "p004", P004, P005, 0x01)
        }
    }

    /* ===================================== Multiply */

    Name (P008, Package (0x14)
    {
        0x00,
        0x00,
        0x00,
        0xFFFFFFFF,
        0x00012345,
        0x7ABC,
        0x12,
        0x34,
        0x01,
        0xFF,
        0x01,
        0xFFFF,
        0x01,
        0xFFFFFFFF,
        /* bit-size of multiplicand */

        0x67812345,
        0x02,
        /* bit-size of multiplier */

        0x03,
        0x45678123,
        0xFFFFFFFF,
        0xFFFFFFFF
        /* ACPI: Overflow conditions are ignored and results are undefined. */
    })
    Name (P009, Package (0x0A)
    {
        0x00,
        0x00,
        0x8BA4C8AC,
        0x03A8,
        0xFF,
        0xFFFF,
        0xFFFFFFFF,
        /* bit-size of multiplicand */

        0xCF02468A,
        /* bit-size of multiplier */

        0xD0368369,
        0x01
        /* ACPI: Overflow conditions are ignored and results are undefined. */
    })
    Name (P00A, Package (0x0E)
    {
        0x92345678,
        0xABCDEF68,
        0xF2345678,
        0xABCDEF68,
        0x00,
        0xFFFFFFFFFFFFFFFF,
        0x01,
        0xFFFFFFFFFFFFFFFF,
        /* bit-size of multiplicand */

        0x6781234511992288,
        0x02,
        /* bit-size of multiplier */

        0x03,
        0x4567812377665544,
        0xFFFFFFFFFFFFFFFF,
        0xFFFFFFFFFFFFFFFF
        /* ACPI: Overflow conditions are ignored and results are undefined. */
    })
    Name (P00B, Package (0x07)
    {
        0x621E9265A81528C0,
        0xA28BCC2CA81528C0,
        0x00,
        0xFFFFFFFFFFFFFFFF,
        /* bit-size of multiplicand */

        0xCF02468A23324510,
        /* bit-size of multiplier */

        0xD036836A6632FFCC,
        0x01
        /* ACPI: Overflow conditions are ignored and results are undefined. */
    })
    Method (MTP0, 0, Serialized)
    {
        Debug = "TEST: MTP0, Integer Multiply"
        If ((F64 == 0x01))
        {
            M000 (__METHOD__, 0x09, "p008", P008, P009, 0x02)
            M000 (__METHOD__, 0x07, "p00a", P00A, P00B, 0x02)
        }
        Else
        {
            M000 (__METHOD__, 0x0A, "p008", P008, P009, 0x02)
        }
    }

    /* ===================================== Divide */

    Name (P00C, Package (0x10)
    {
        /* divident divisor */

        0x12345678,
        0x1000,
        0xFFFFFFFF,
        0x00400000,
        /* bit-size of operands */

        0x78123456,
        0x80000000,
        0x78123456,
        0x02,
        0x00,
        0x01,
        0x78123456,
        0x11223344,
        /* bit-size of result */

        0xFFFFFFFF,
        0x01,
        /* bit-size of remainder */

        0xFFFFFFFF,
        0x80000000
    })
    Name (P00D, Package (0x10)
    {
        /* result   remainder */

        0x00012345,
        0x0678,
        0x03FF,
        0x003FFFFF,
        0x00,
        0x78123456,
        0x3C091A2B,
        0x00,
        0x00,
        0x00,
        0x07,
        0x0022CD7A,
        0xFFFFFFFF,
        0x00,
        0x01,
        0x7FFFFFFF
    })
    Name (P00E, Package (0x10)
    {
        /* divident         divisor */

        0x1234567811223344,
        0x1000,
        0xFFFFFFFFFFFFFFFF,
        0x4000000000000000,
        0x7812345699887766,
        0x8000000000000000,
        0x7812345600448866,
        0x02,
        0x00,
        0x01,
        0x78123456AABBCCDD,
        0x110022BD33CA4784,
        0xFFFFFFFFFFFFFFFF,
        0x01,
        0xFFFFFFFFFFFFFFFF,
        0x8000000000000000
    })
    Name (P00F, Package (0x10)
    {
        /* result           remainder */

        0x0001234567811223,
        0x0344,
        0x03,
        0x3FFFFFFFFFFFFFFF,
        0x00,
        0x7812345699887766,
        0x3C091A2B00224433,
        0x00,
        0x00,
        0x00,
        0x07,
        0x0111412A4033D841,
        0xFFFFFFFFFFFFFFFF,
        0x00,
        0x01,
        0x7FFFFFFFFFFFFFFF
    })
    Method (DVD0, 0, Serialized)
    {
        Debug = "TEST: DVD0, Integer Divide"
        If ((F64 == 0x01))
        {
            M001 (__METHOD__, 0x08, "p00c", P00C, P00D, 0x00)
            M001 (__METHOD__, 0x08, "p00e", P00E, P00F, 0x00)
        }
        Else
        {
            M001 (__METHOD__, 0x08, "p00c", P00C, P00D, 0x00)
        }
    }

    /* ===================================== Increment */

    Name (P014, Package (0x06)
    {
        0x00,
        0xFFFFFFFE,
        0x12334579,
        0x7FFFFFFF,
        0x80000000,
        0xFFFFFFFF
    })
    Name (P015, Package (0x06)
    {
        0x01,
        0xFFFFFFFF,
        0x1233457A,
        0x80000000,
        0x80000001,
        0x00
    })
    Name (P016, Package (0x06)
    {
        0xFFFFFFFF,
        0xFFFFFFFFFFFFFFFE,
        0x1233457988339042,
        0x7FFFFFFFFFFFFFFF,
        0x8000000000000000,
        0xFFFFFFFFFFFFFFFF
    })
    Name (P017, Package (0x06)
    {
        0x0000000100000000,
        0xFFFFFFFFFFFFFFFF,
        0x1233457988339043,
        0x8000000000000000,
        0x8000000000000001,
        0x00
    })
    Method (ICR0, 0, Serialized)
    {
        Debug = "TEST: ICR0, Increment an Integer"
        If ((F64 == 0x01))
        {
            M002 (__METHOD__, 0x05, "p014", P014, P015, 0x00)
            M002 (__METHOD__, 0x06, "p016", P016, P017, 0x00)
        }
        Else
        {
            M002 (__METHOD__, 0x06, "p014", P014, P015, 0x00)
        }
    }

    /* ===================================== Decrement */

    Name (P018, Package (0x06)
    {
        0xFFFFFFFF,
        0x12334579,
        0x80000000,
        0x7FFFFFFF,
        0x80000001,
        0x00
    })
    Name (P019, Package (0x06)
    {
        0xFFFFFFFE,
        0x12334578,
        0x7FFFFFFF,
        0x7FFFFFFE,
        0x80000000,
        0xFFFFFFFF
    })
    Name (P01A, Package (0x06)
    {
        0x00,
        0xFFFFFFFFFFFFFFFF,
        0x1233457966887700,
        0x8000000000000000,
        0x7FFFFFFFFFFFFFFF,
        0x8000000000000001
    })
    Name (P01B, Package (0x06)
    {
        0xFFFFFFFFFFFFFFFF,
        0xFFFFFFFFFFFFFFFE,
        0x12334579668876FF,
        0x7FFFFFFFFFFFFFFF,
        0x7FFFFFFFFFFFFFFE,
        0x8000000000000000
    })
    Method (DCR0, 0, Serialized)
    {
        Debug = "TEST: DCR0, Decrement an Integer"
        If ((F64 == 0x01))
        {
            M002 (__METHOD__, 0x05, "p018", P018, P019, 0x01)
            M002 (__METHOD__, 0x06, "p01a", P01A, P01B, 0x01)
        }
        Else
        {
            M002 (__METHOD__, 0x06, "p018", P018, P019, 0x01)
        }
    }

    /* ===================================== And */

    Name (P01C, Package (0x0A)
    {
        0x00,
        0x00,
        0xFFFFFFFF,
        0xF0F0F0F0,
        0x0F0F0F0F,
        0x00,
        0x00,
        0x10101010,
        0x01010101,
        0x80214120
    })
    Name (P01D, Package (0x0A)
    {
        0x00,
        0x00,
        0xFFFFFFFFFFFFFFFF,
        0xF0F0F0F0F0F0F0F0,
        0x0F0F0F0F0F0F0F0F,
        0x00,
        0x00,
        0x1010101010101010,
        0x0101010101010101,
        0x8021420011118822
    })
    Method (AND0, 0, Serialized)
    {
        Debug = "TEST: AND0, Integer Bitwise And"
        If ((F64 == 0x01))
        {
            M000 (__METHOD__, C000, "p030", P030, P01C, 0x03)
            M000 (__METHOD__, C000, "p031", P031, P01D, 0x03)
        }
        Else
        {
            M000 (__METHOD__, C000, "p030", P030, P01C, 0x03)
        }
    }

    /* ===================================== Nand */

    Name (P01E, Package (0x02)
    {
        0x9A3353AC,
        0x39A966CA
    })
    Name (P01F, Package (0x01)
    {
        0xE7DEBD77
    })
    Name (P020, Package (0x01)
    {
        0xFFFFFFFFE7DEBD77
    })
    Name (P021, Package (0x02)
    {
        0x9A3353AC395C9353,
        0x39A966CAA36A3A66
    })
    Name (P022, Package (0x01)
    {
        0xE7DEBD77DEB7EDBD
    })
    Name (P023, Package (0x0A)
    {
        0xFFFFFFFF,
        0xFFFFFFFF,
        0x00,
        0x0F0F0F0F,
        0xF0F0F0F0,
        0xFFFFFFFF,
        0xFFFFFFFF,
        0xEFEFEFEF,
        0xFEFEFEFE,
        0x7FDEBEDF
    })
    Name (P024, Package (0x0A)
    {
        0xFFFFFFFFFFFFFFFF,
        0xFFFFFFFFFFFFFFFF,
        0xFFFFFFFF00000000,
        0xFFFFFFFF0F0F0F0F,
        0xFFFFFFFFF0F0F0F0,
        0xFFFFFFFFFFFFFFFF,
        0xFFFFFFFFFFFFFFFF,
        0xFFFFFFFFEFEFEFEF,
        0xFFFFFFFFFEFEFEFE,
        0xFFFFFFFF7FDEBEDF
    })
    Name (P025, Package (0x0A)
    {
        0xFFFFFFFFFFFFFFFF,
        0xFFFFFFFFFFFFFFFF,
        0x00,
        0x0F0F0F0F0F0F0F0F,
        0xF0F0F0F0F0F0F0F0,
        0xFFFFFFFFFFFFFFFF,
        0xFFFFFFFFFFFFFFFF,
        0xEFEFEFEFEFEFEFEF,
        0xFEFEFEFEFEFEFEFE,
        0x7FDEBDFFEEEE77DD
    })
    Method (NAN0, 0, Serialized)
    {
        Debug = "TEST: NAN0, Integer Bitwise Nand"
        If ((F64 == 0x01))
        {
            M000 (__METHOD__, 0x01, "p01e", P01E, P020, 0x04)
            M000 (__METHOD__, 0x01, "p021", P021, P022, 0x04)
            M000 (__METHOD__, C000, "p030", P030, P024, 0x04)
            M000 (__METHOD__, C000, "p031", P031, P025, 0x04)
        }
        Else
        {
            M000 (__METHOD__, 0x01, "p01e", P01E, P01F, 0x04)
            M000 (__METHOD__, C000, "p030", P030, P023, 0x04)
        }
    }

    /* ===================================== Nor */

    Name (P026, Package (0x02)
    {
        0x9A3353AC,
        0x39A966CA
    })
    Name (P027, Package (0x01)
    {
        0x44448811
    })
    Name (P028, Package (0x01)
    {
        0xFFFFFFFF44448811
    })
    Name (P029, Package (0x02)
    {
        0x9A3353AC993CA39C,
        0x39A966CA3356A5C9
    })
    Name (P02A, Package (0x01)
    {
        0x4444881144815822
    })
    Name (P02B, Package (0x0A)
    {
        0xFFFFFFFF,
        0x00,
        0x00,
        0x00,
        0x00,
        0x0F0F0F0F,
        0xF0F0F0F0,
        0x0E0E0E0E,
        0xE0E0E0E0,
        0x68103000
    })
    Name (P02C, Package (0x0A)
    {
        0xFFFFFFFFFFFFFFFF,
        0xFFFFFFFF00000000,
        0xFFFFFFFF00000000,
        0xFFFFFFFF00000000,
        0xFFFFFFFF00000000,
        0xFFFFFFFF0F0F0F0F,
        0xFFFFFFFFF0F0F0F0,
        0xFFFFFFFF0E0E0E0E,
        0xFFFFFFFFE0E0E0E0,
        0xFFFFFFFF68103000
    })
    Name (P02D, Package (0x0A)
    {
        0xFFFFFFFFFFFFFFFF,
        0x00,
        0x00,
        0x00,
        0x00,
        0x0F0F0F0F0F0F0F0F,
        0xF0F0F0F0F0F0F0F0,
        0x0E0E0E0E0E0E0E0E,
        0xE0E0E0E0E0E0E0E0,
        0x6810985600663201
    })
    Method (NOR0, 0, Serialized)
    {
        Debug = "TEST: NOR0, Integer Bitwise Nor"
        If ((F64 == 0x01))
        {
            M000 (__METHOD__, 0x01, "p026", P026, P028, 0x05)
            M000 (__METHOD__, 0x01, "p029", P029, P02A, 0x05)
            M000 (__METHOD__, C000, "p030", P030, P02C, 0x05)
            M000 (__METHOD__, C000, "p031", P031, P02D, 0x05)
        }
        Else
        {
            M000 (__METHOD__, 0x01, "p026", P026, P027, 0x05)
            M000 (__METHOD__, C000, "p030", P030, P02B, 0x05)
        }
    }

    /* ===================================== Not */

    Name (P02E, Package (0x05)
    {
        0xFFFFFFFF,
        0x00,
        0x0F0F0F0F,
        0xF0F0F0F0,
        0xEDCBA987
    })
    Name (P02F, Package (0x05)
    {
        0xFFFFFFFFFFFFFFFF,
        0xFFFFFFFF00000000,
        0xFFFFFFFF0F0F0F0F,
        0xFFFFFFFFF0F0F0F0,
        0xFFFFFFFFEDCBA987
    })
    Name (P040, Package (0x05)
    {
        0xFFFFFFFFFFFFFFFF,
        0x00,
        0x0F0F0F0F0F0F0F0F,
        0xF0F0F0F0F0F0F0F0,
        0xEDCBA987F5064312
    })
    Method (NOT0, 0, Serialized)
    {
        Debug = "TEST: NOT0, Integer Bitwise Not"
        If ((F64 == 0x01))
        {
            M002 (__METHOD__, C001, "p032", P032, P02F, 0x02)
            M002 (__METHOD__, C001, "p033", P033, P040, 0x02)
        }
        Else
        {
            M002 (__METHOD__, C001, "p032", P032, P02E, 0x02)
        }
    }

    /* ===================================== Or */

    Name (P041, Package (0x02)
    {
        0x9A3353AC,
        0x39A966CA
    })
    Name (P042, Package (0x01)
    {
        0xBBBB77EE
    })
    Name (P043, Package (0x02)
    {
        0x9A3353AC99A3DCEB,
        0x39A966CA12887634
    })
    Name (P044, Package (0x01)
    {
        0xBBBB77EE9BABFEFF
    })
    Name (P045, Package (0x0A)
    {
        0x00,
        0xFFFFFFFF,
        0xFFFFFFFF,
        0xFFFFFFFF,
        0xFFFFFFFF,
        0xF0F0F0F0,
        0x0F0F0F0F,
        0xF1F1F1F1,
        0x1F1F1F1F,
        0x97EFCFFF
    })
    Name (P046, Package (0x0A)
    {
        0x00,
        0xFFFFFFFFFFFFFFFF,
        0xFFFFFFFFFFFFFFFF,
        0xFFFFFFFFFFFFFFFF,
        0xFFFFFFFFFFFFFFFF,
        0xF0F0F0F0F0F0F0F0,
        0x0F0F0F0F0F0F0F0F,
        0xF1F1F1F1F1F1F1F1,
        0x1F1F1F1F1F1F1F1F,
        0x97EF67A9FF99CDFE
    })
    Method (OR00, 0, Serialized)
    {
        Debug = "TEST: OR00, Integer Bitwise Or"
        If ((F64 == 0x01))
        {
            M000 (__METHOD__, 0x01, "p041", P041, P042, 0x06)
            M000 (__METHOD__, 0x01, "p043", P043, P044, 0x06)
            M000 (__METHOD__, C000, "p030", P030, P045, 0x06)
            M000 (__METHOD__, C000, "p031", P031, P046, 0x06)
        }
        Else
        {
            M000 (__METHOD__, 0x01, "p041", P041, P042, 0x06)
            M000 (__METHOD__, C000, "p030", P030, P045, 0x06)
        }
    }

    /* ===================================== Xor */

    Name (P047, Package (0x02)
    {
        0x9A3653AC,
        0x39A966CA
    })
    Name (P048, Package (0x01)
    {
        0xA39F3566
    })
    Name (P049, Package (0x02)
    {
        0x9A3653AC19283745,
        0x39A966CABBAAEF45
    })
    Name (P04A, Package (0x01)
    {
        0xA39F3566A282D800
    })
    Name (P04B, Package (0x0A)
    {
        0x00,
        0xFFFFFFFF,
        0x00,
        0x0F0F0F0F,
        0xF0F0F0F0,
        0xF0F0F0F0,
        0x0F0F0F0F,
        0xE1E1E1E1,
        0x1E1E1E1E,
        0x17CE8EDF
    })
    Name (P04C, Package (0x0A)
    {
        0x00,
        0xFFFFFFFFFFFFFFFF,
        0x00,
        0x0F0F0F0F0F0F0F0F,
        0xF0F0F0F0F0F0F0F0,
        0xF0F0F0F0F0F0F0F0,
        0x0F0F0F0F0F0F0F0F,
        0xE1E1E1E1E1E1E1E1,
        0x1E1E1E1E1E1E1E1E,
        0x17CE25A9EE8845DC
    })
    Name (P04D, Package (0x0A)
    {
        0x00,
        0xFFFFFFFF,
        0x00,
        0x0F0F0F0F,
        0xF0F0F0F0,
        0xF0F0F0F0,
        0x0F0F0F0F,
        0xE1E1E1E1,
        0x1E1E1E1E,
        0x17CE8EDF
    })
    Method (XOR0, 0, Serialized)
    {
        Debug = "TEST: XOR0, Integer Bitwise Xor"
        If ((F64 == 0x01))
        {
            M000 (__METHOD__, 0x01, "p047", P047, P048, 0x07)
            M000 (__METHOD__, 0x01, "p049", P049, P04A, 0x07)
            M000 (__METHOD__, C000, "p030", P030, P04B, 0x07)
            M000 (__METHOD__, 0x01, "p031", P031, P04C, 0x07)
            M000 (__METHOD__, C000, "p031", P031, P04C, 0x07)
        }
        Else
        {
            M000 (__METHOD__, 0x01, "p047", P047, P048, 0x07)
            M000 (__METHOD__, C000, "p030", P030, P04D, 0x07)
        }
    }

    /* ===================================== Mod */

    Name (P04E, Package (0x08)
    {
        /* remainder */

        0x0678,
        0x003FFFFF,
        0x78123456,
        0x00,
        0x00,
        0x0022CD7A,
        0x00,
        0x7FFFFFFF
    })
    Name (P04F, Package (0x08)
    {
        /* remainder */

        0x0344,
        0x3FFFFFFFFFFFFFFF,
        0x7812345699887766,
        0x00,
        0x00,
        0x0111412A4033D841,
        0x00,
        0x7FFFFFFFFFFFFFFF
    })
    Method (MOD0, 0, Serialized)
    {
        Debug = "TEST: MOD0, Integer Modulo"
        If ((F64 == 0x01))
        {
            M000 (__METHOD__, 0x08, "p00c", P00C, P04E, 0x08)
            M000 (__METHOD__, 0x08, "p00e", P00E, P04F, 0x08)
        }
        Else
        {
            M000 (__METHOD__, 0x08, "p00c", P00C, P04E, 0x08)
        }
    }

    /* ===================================== ShiftLeft */

    Name (P050, Package (0x34)
    {
        0x00,
        0x00,
        0x00,
        0x01,
        0x00,
        0x11,
        0x00,
        0x1F,
        0x00,
        0x20,
        0x00,
        0x21,
        0x00,
        0x40,
        0x00,
        0x41,
        0xFFFFFFFF,
        0x00,
        0xFFFFFFFF,
        0x01,
        0xFFFFFFFF,
        0x0E,
        0xFFFFFFFF,
        0x1F,
        0xFFFFFFFF,
        0x20,
        0xFFFFFFFF,
        0x21,
        0xFFFFFFFF,
        0x40,
        0xFFFFFFFF,
        0x41,
        0xF0F0F0F0,
        0x00,
        0xF0F0F0F0,
        0x01,
        0xF0F0F0F0,
        0x11,
        0xF0F0F0F0,
        0x1F,
        0xF0F0F0F0,
        0x20,
        0x87654321,
        0x00,
        0x87654321,
        0x01,
        0x87654321,
        0x11,
        0x87654321,
        0x1F,
        0x87654321,
        0x20
    })
    Name (P051, Package (0x1A)
    {
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0xFFFFFFFF,
        0xFFFFFFFE,
        0xFFFFC000,
        0x80000000,
        0x00,
        0x00,
        0x00,
        0x00,
        0xF0F0F0F0,
        0xE1E1E1E0,
        0xE1E00000,
        0x00,
        0x00,
        0x87654321,
        0x0ECA8642,
        0x86420000,
        0x80000000,
        0x00
    })
    Name (P052, Package (0x1A)
    {
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0xFFFFFFFF,
        0x00000001FFFFFFFE,
        0x00003FFFFFFFC000,
        0x7FFFFFFF80000000,
        0xFFFFFFFF00000000,
        0xFFFFFFFE00000000,
        0x00,
        0x00,
        0xF0F0F0F0,
        0x00000001E1E1E1E0,
        0x0001E1E1E1E00000,
        0x7878787800000000,
        0xF0F0F0F000000000,
        0x87654321,
        0x000000010ECA8642,
        0x00010ECA86420000,
        0x43B2A19080000000,
        0x8765432100000000
    })
    Name (P053, Package (0x14)
    {
        0xFFFFFFFFFFFFFFFF,
        0x00,
        0xFFFFFFFFFFFFFFFF,
        0x01,
        0xFFFFFFFFFFFFFFFF,
        0x11,
        0xFFFFFFFFFFFFFFFF,
        0x31,
        0xFFFFFFFFFFFFFFFF,
        0x40,
        0xFFFFFFFFFFFFFFFF,
        0x41,
        0xF0F0F0F0F0F0F0F0,
        0x0F,
        0xF0F0F0F0F0F0F0F0,
        0x23,
        0x87654321BCDEF098,
        0x0B,
        0x87654321BCDEF098,
        0x32
    })
    Name (P054, Package (0x0A)
    {
        0xFFFFFFFFFFFFFFFF,
        0xFFFFFFFFFFFFFFFE,
        0xFFFFFFFFFFFE0000,
        0xFFFE000000000000,
        0x00,
        0x00,
        0x7878787878780000,
        0x8787878000000000,
        0x2A190DE6F784C000,
        0xC260000000000000
    })
    Method (SHL0, 0, Serialized)
    {
        Debug = "TEST: SHL0, Integer shift value left"
        If ((F64 == 0x01))
        {
            M000 (__METHOD__, 0x1A, "p050", P050, P052, 0x09)
            M000 (__METHOD__, 0x0A, "p053", P053, P054, 0x09)
        }
        Else
        {
            M000 (__METHOD__, 0x1A, "p050", P050, P051, 0x09)
        }
    }

    /* ===================================== ShiftRight */

    Name (P055, Package (0x1A)
    {
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0xFFFFFFFF,
        0x7FFFFFFF,
        0x0003FFFF,
        0x01,
        0x00,
        0x00,
        0x00,
        0x00,
        0xF0F0F0F0,
        0x78787878,
        0x7878,
        0x01,
        0x00,
        0x87654321,
        0x43B2A190,
        0x43B2,
        0x01,
        0x00
    })
    Name (P056, Package (0x0A)
    {
        0xFFFFFFFFFFFFFFFF,
        0x7FFFFFFFFFFFFFFF,
        0x00007FFFFFFFFFFF,
        0x7FFF,
        0x00,
        0x00,
        0x0001E1E1E1E1E1E1,
        0x1E1E1E1E,
        0x0010ECA864379BDE,
        0x21D9
    })
    Method (SHR0, 0, Serialized)
    {
        Debug = "TEST: SHR0, Integer shift value right"
        If ((F64 == 0x01))
        {
            M000 (__METHOD__, 0x1A, "p050", P050, P055, 0x0A)
            M000 (__METHOD__, 0x0A, "p053", P053, P056, 0x0A)
        }
        Else
        {
            M000 (__METHOD__, 0x1A, "p050", P050, P055, 0x0A)
        }
    }

    /* ===================================== FindSetLeftBit */

    Name (P057, Package (0x06)
    {
        0x00,
        0xFFFFFFFF,
        0x80000000,
        0x01,
        0x02A0FD40,
        0x0456F200
    })
    Name (P058, Package (0x06)
    {
        0x00,
        0x20,
        0x20,
        0x01,
        0x1A,
        0x1B
    })
    Name (P059, Package (0x06)
    {
        0x00,
        0xFFFFFFFFFFFFFFFF,
        0x8000000000000000,
        0x01,
        0x02A0FD4119FD0560,
        0x0456F2007CED8400
    })
    Name (P05A, Package (0x06)
    {
        0x00,
        0x40,
        0x40,
        0x01,
        0x3A,
        0x3B
    })
    Method (FSL0, 0, Serialized)
    {
        Debug = "TEST: FSL0, Index of first least significant bit set"
        If ((F64 == 0x01))
        {
            M002 (__METHOD__, 0x06, "p057", P057, P058, 0x03)
            M002 (__METHOD__, 0x06, "p059", P059, P05A, 0x03)
        }
        Else
        {
            M002 (__METHOD__, 0x06, "p057", P057, P058, 0x03)
        }

        If ((F64 == 0x01))
        {
            Local0 = 0x40
        }
        Else
        {
            Local0 = 0x20
        }

        Local1 = 0x00
        Local5 = 0x00
        While (Local0)
        {
            If ((Local1 == 0x00))
            {
                Local2 = 0x01
            }
            Else
            {
                Local2 = (0x03 << Local5)
                Local5++
            }

            FindSetLeftBit (Local2, Local3)
            Local4 = (Local1 + 0x01)
            If ((Local3 != Local4))
            {
                ERR (__METHOD__, Z083, __LINE__, 0x00, 0x00, Local0, 0x00)
            }

            Local1++
            Local0--
        }
    }

    /* ===================================== FindSetRightBit */

    Name (P05B, Package (0x06)
    {
        0x00,
        0x01,
        0x20,
        0x01,
        0x07,
        0x0A
    })
    Name (P05C, Package (0x06)
    {
        0x00,
        0x01,
        0x40,
        0x01,
        0x06,
        0x0B
    })
    Method (FSR0, 0, Serialized)
    {
        Debug = "TEST: FSR0, Index of first most significant bit set"
        If ((F64 == 0x01))
        {
            M002 (__METHOD__, 0x06, "p057", P057, P05B, 0x04)
            M002 (__METHOD__, 0x06, "p059", P059, P05C, 0x04)
        }
        Else
        {
            M002 (__METHOD__, 0x06, "p057", P057, P05B, 0x04)
        }

        If ((F64 == 0x01))
        {
            Local0 = 0x40
        }
        Else
        {
            Local0 = 0x20
        }

        Local1 = 0x00
        Local5 = 0x00
        While (Local0)
        {
            If ((Local1 == 0x00))
            {
                Local2 = 0x01
                Local4 = 0x01
            }
            Else
            {
                Local2 = (0x03 << Local5)
                Local4 = Local1
                Local5++
            }

            FindSetRightBit (Local2, Local3)
            If ((Local3 != Local4))
            {
                ERR (__METHOD__, Z083, __LINE__, 0x00, 0x00, Local0, 0x00)
            }

            Local1++
            Local0--
        }
    }
