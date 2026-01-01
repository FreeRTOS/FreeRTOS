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
     * Logical operators
     */
    Name (Z035, 0x23)
    /* Verifying 2-parameters, 1-result operator */

    Method (M003, 6, Serialized)
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
                    Local7 = (Local0 != Local1)
                    If ((Local7 != Local2))
                    {
                        ERR (Arg0, Z035, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }

                    Local7 = (Local1 != Local0)
                    If ((Local7 != Local2))
                    {
                        ERR (Arg0, Z035, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }
                }
                Case (0x01)
                {
                    Local7 = (Local0 && Local1)
                    If ((Local7 != Local2))
                    {
                        ERR (Arg0, Z035, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }

                    Local7 = (Local1 && Local0)
                    If ((Local7 != Local2))
                    {
                        ERR (Arg0, Z035, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }
                }
                Case (0x02)
                {
                    Local7 = (Local0 || Local1)
                    If ((Local7 != Local2))
                    {
                        ERR (Arg0, Z035, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }

                    Local7 = (Local1 || Local0)
                    If ((Local7 != Local2))
                    {
                        ERR (Arg0, Z035, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }
                }
                Case (0x03)
                {
                    Local7 = (Local0 == Local1)
                    If ((Local7 != Local2))
                    {
                        ERR (Arg0, Z035, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }

                    Local7 = (Local1 == Local0)
                    If ((Local7 != Local2))
                    {
                        ERR (Arg0, Z035, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }
                }
                Case (0x04)
                {
                    Local7 = (Local0 > Local1)
                    If ((Local7 != Local2))
                    {
                        ERR (Arg0, Z035, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }
                }
                Case (0x05)
                {
                    Local7 = (Local0 >= Local1)
                    If ((Local7 != Local2))
                    {
                        ERR (Arg0, Z035, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }
                }
                Case (0x06)
                {
                    Local7 = (Local0 < Local1)
                    If ((Local7 != Local2))
                    {
                        ERR (Arg0, Z035, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }
                }
                Case (0x07)
                {
                    Local7 = (Local0 <= Local1)
                    If ((Local7 != Local2))
                    {
                        ERR (Arg0, Z035, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }
                }

            }

            If (0x00)
            {
                Debug = "==============:"
                Debug = Local0
                Debug = Local1
                Debug = Local2
                Debug = Local7
                Debug = "=============="
            }

            Local5++
            Local3--
        }
    }

    /* Verifying 1-parameter, 1-result operator */

    Method (M004, 6, Serialized)
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
                    Local2 = !Local0
                    If ((Local2 != Local1))
                    {
                        ERR (Arg0, Z035, __LINE__, 0x00, 0x00, Local5, Arg2)
                    }
                }

            }

            Local5++
            Local3--
        }
    }

    /* ====================================================== // */
    /*    Generic operands utilized by different operators    // */
    /* ====================================================== // */
    Name (P060, Package (0x1A)
    {
        /* 32-bit integers */

        0x12345678,
        0x12345678,
        0xF2345678,
        0xF2345678,
        0x00,
        0x00,
        0xFFFFFFFF,
        0xFFFFFFFF,
        0x04000000,
        0x10,
        0x20000000,
        0x40000000,
        0x80000000,
        0x01,
        0x40000000,
        0x80000000,
        0x04000000,
        0xFF,
        0xFF,
        0x00100000,
        0x00,
        0x80,
        0x00,
        0x8000,
        0x00,
        0x80000000
    })
    Name (P061, Package (0x18)
    {
        /* 64-bit integers */

        0x12345678BDEFAC98,
        0x12345678BDEFAC98,
        0xF234567811994657,
        0xF234567811994657,
        0x00,
        0x00,
        0xFFFFFFFFFFFFFFFF,
        0xFFFFFFFFFFFFFFFF,
        0x0400000000000000,
        0x0000001000000000,
        0x2000000000000000,
        0x4000000000000000,
        0x8000000000000000,
        0x01,
        0x4000000000000000,
        0x8000000000000000,
        0x0400000000000000,
        0xFF,
        0xFF,
        0x00100000,
        0x00,
        0x80000000,
        0x00,
        0x8000000000000000
    })
    Name (P062, Package (0x06)
    {
        /* 32-bit integers */

        0x00,
        0xFFFFFFFF,
        0xFF,
        0x10,
        0x12334567,
        0x9BCDFE18
    })
    Name (P063, Package (0x04)
    {
        /* 64-bit integers */

        0x00,
        0xFFFFFFFFFFFFFFFF,
        0x12334567BDCFEB46,
        0xFBDEC6709BCDFE18
    })
    Name (P064, Package (0x3E)
    {
        /* Strings */

        "qwertyuiop",
        "qwertyuiop",
        "qwertyuiop",
        "qwertyuiop0",
        "qwertyuiop",
        "qwertyuio",
        "",
        "",
        " ",
        "",
        "",
        " ",
        " ",
        " ",
        "  ",
        " ",
        " ",
        "  ",
        "a",
        "",
        "",
        "a",
        " a",
        "a",
        "a",
        " a",
        "a ",
        "a",
        "a",
        "a ",
        "a b",
        "ab",
        "ab",
        "a b",
        "a  b",
        "a b",
        "a b",
        "a  b",
        "abcDef",
        "abcdef",
        "mnbvcxzlkHjhgf",
        "mnbvcxzlkHjhgf",
        "mnbvcxzlkHjhgf",
        "mnbvcxzlkIjhgf",
        "mnbvcxzlkIjhgf",
        "mnbvcxzlkHjhgf",
        "mnbvcxzlkHjhgf0",
        "mnbvcxzlkHjhgf",
        "mnbvcxzlkHjhgf0",
        "mnbvcxzlkIjhgf",
        "mnbvcxzlkIjhgf0",
        "mnbvcxzlkHjhgf",
        "mnbvcxzlkHjhgf",
        "mnbvcxzlkHjhgf0",
        "mnbvcxzlkHjhgf",
        "mnbvcxzlkIjhgf0",
        "mnbvcxzlkIjhgf",
        "mnbvcxzlkHjhgf0",
        "mnbvcxzlkIHjhgf",
        "mnbvcxzlkHIjhgf",
        "mnbvcxzlkHIjhgf",
        "mnbvcxzlkIHjhgf"
    })
    Name (P065, Package (0x66)
    {
        /* Buffers */

        Buffer (0x07)
        {
             0x00, 0x20, 0x21, 0x22, 0x23, 0x24, 0x25         // . !"#$%
        },

        Buffer (0x07)
        {
             0x00, 0x20, 0x21, 0x22, 0x23, 0x24, 0x25         // . !"#$%
        },

        Buffer (0x07)
        {
             0x00, 0x20, 0x21, 0x22, 0x23, 0x24, 0x25         // . !"#$%
        },

        Buffer (0x06)
        {
             0x20, 0x21, 0x22, 0x23, 0x24, 0x25               //  !"#$%
        },

        Buffer (0x06)
        {
             0x20, 0x21, 0x22, 0x23, 0x24, 0x25               //  !"#$%
        },

        Buffer (0x07)
        {
             0x00, 0x20, 0x21, 0x22, 0x23, 0x24, 0x25         // . !"#$%
        },

        Buffer (0x08)
        {
             0x00, 0x00, 0x20, 0x21, 0x22, 0x23, 0x24, 0x25   // .. !"#$%
        },

        Buffer (0x07)
        {
             0x00, 0x20, 0x21, 0x22, 0x23, 0x24, 0x25         // . !"#$%
        },

        Buffer (0x07)
        {
             0x00, 0x20, 0x21, 0x22, 0x23, 0x24, 0x25         // . !"#$%
        },

        Buffer (0x08)
        {
             0x00, 0x00, 0x20, 0x21, 0x22, 0x23, 0x24, 0x25   // .. !"#$%
        },

        Buffer (0x06)
        {
             0x20, 0x21, 0x22, 0x23, 0x24, 0x25               //  !"#$%
        },

        Buffer (0x06)
        {
             0x20, 0x21, 0x22, 0x23, 0x24, 0x25               //  !"#$%
        },

        Buffer (0x07)
        {
            " !\"#$%"
        },

        Buffer (0x06)
        {
             0x20, 0x21, 0x22, 0x23, 0x24, 0x25               //  !"#$%
        },

        Buffer (0x06)
        {
             0x20, 0x21, 0x22, 0x23, 0x24, 0x25               //  !"#$%
        },

        Buffer (0x07)
        {
            " !\"#$%"
        },

        Buffer (0x08)
        {
             0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x00, 0x00   //  !"#$%..
        },

        Buffer (0x07)
        {
            " !\"#$%"
        },

        Buffer (0x07)
        {
            " !\"#$%"
        },

        Buffer (0x08)
        {
             0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x00, 0x00   //  !"#$%..
        },

        Buffer (0x06)
        {
             0x20, 0x21, 0x22, 0x00, 0x24, 0x25               //  !".$%
        },

        Buffer (0x06)
        {
             0x20, 0x21, 0x22, 0x00, 0x24, 0x25               //  !".$%
        },

        Buffer (0x06)
        {
             0x20, 0x21, 0x22, 0x00, 0x24, 0x25               //  !".$%
        },

        Buffer (0x06)
        {
             0x20, 0x21, 0x22, 0x00, 0x24, 0x26               //  !".$&
        },

        Buffer (0x06)
        {
             0x20, 0x21, 0x22, 0x00, 0x24, 0x26               //  !".$&
        },

        Buffer (0x06)
        {
             0x20, 0x21, 0x22, 0x00, 0x24, 0x25               //  !".$%
        },

        Buffer (0x07)
        {
             0x20, 0x21, 0x22, 0x00, 0x24, 0x25, 0x00         //  !".$%.
        },

        Buffer (0x06)
        {
             0x20, 0x21, 0x22, 0x00, 0x24, 0x25               //  !".$%
        },

        Buffer (0x06)
        {
             0x20, 0x21, 0x22, 0x00, 0x24, 0x25               //  !".$%
        },

        Buffer (0x07)
        {
             0x20, 0x21, 0x22, 0x00, 0x24, 0x25, 0x00         //  !".$%.
        },

        Buffer (0x08)
        {
             0x20, 0x21, 0x22, 0x00, 0x24, 0x25, 0x00, 0x00   //  !".$%..
        },

        Buffer (0x07)
        {
             0x20, 0x21, 0x22, 0x00, 0x24, 0x25, 0x00         //  !".$%.
        },

        Buffer (0x07)
        {
             0x20, 0x21, 0x22, 0x00, 0x24, 0x25, 0x00         //  !".$%.
        },

        Buffer (0x08)
        {
             0x20, 0x21, 0x22, 0x00, 0x24, 0x25, 0x00, 0x00   //  !".$%..
        },

        Buffer (0x64){},
        Buffer (0x64){},
        Buffer (0x64){},
        Buffer (0x65){},
        Buffer (0x64){},
        Buffer (0x63){},
        Buffer (0x01)
        {
             0x00                                             // .
        },

        Buffer (0x01)
        {
             0x00                                             // .
        },

        Buffer (0x02)
        {
            " "
        },

        Buffer (0x01)
        {
             0x00                                             // .
        },

        Buffer (0x01)
        {
             0x00                                             // .
        },

        Buffer (0x02)
        {
            " "
        },

        Buffer (0x02)
        {
            " "
        },

        Buffer (0x02)
        {
            " "
        },

        Buffer (0x03)
        {
            "  "
        },

        Buffer (0x02)
        {
            " "
        },

        Buffer (0x02)
        {
            " "
        },

        Buffer (0x03)
        {
            "  "
        },

        Buffer (0x02)
        {
            "a"
        },

        Buffer (0x01)
        {
             0x00                                             // .
        },

        Buffer (0x01)
        {
             0x00                                             // .
        },

        Buffer (0x02)
        {
            "a"
        },

        Buffer (0x03)
        {
            " a"
        },

        Buffer (0x02)
        {
            "a"
        },

        Buffer (0x02)
        {
            "a"
        },

        Buffer (0x03)
        {
            " a"
        },

        Buffer (0x03)
        {
            "a "
        },

        Buffer (0x02)
        {
            "a"
        },

        Buffer (0x02)
        {
            "a"
        },

        Buffer (0x03)
        {
            "a "
        },

        Buffer (0x04)
        {
            "a b"
        },

        Buffer (0x03)
        {
            "ab"
        },

        Buffer (0x03)
        {
            "ab"
        },

        Buffer (0x04)
        {
            "a b"
        },

        Buffer (0x05)
        {
            "a  b"
        },

        Buffer (0x04)
        {
            "a b"
        },

        Buffer (0x04)
        {
            "a b"
        },

        Buffer (0x05)
        {
            "a  b"
        },

        Buffer (0x07)
        {
            "abcDef"
        },

        Buffer (0x07)
        {
            "abcdef"
        },

        Buffer (0x16)
        {
            "asdfGHJKLIq0987654312"
        },

        Buffer (0x16)
        {
            "asdfGHJKLIq0987654312"
        },

        Buffer (0x16)
        {
            "asdfGHJKLIq0987654312"
        },

        Buffer (0x17)
        {
            "asdfGHJKLIq09876543123"
        },

        Buffer (0x16)
        {
            "asdfGHJKLIq0987654312"
        },

        Buffer (0x15)
        {
            "asdfGHJKLIq098765431"
        },

        Buffer (0x0F)
        {
            "mnbvcxzlkHjhgf"
        },

        Buffer (0x0F)
        {
            "mnbvcxzlkHjhgf"
        },

        Buffer (0x0F)
        {
            "mnbvcxzlkHjhgf"
        },

        Buffer (0x0F)
        {
            "mnbvcxzlkIjhgf"
        },

        Buffer (0x0F)
        {
            "mnbvcxzlkIjhgf"
        },

        Buffer (0x0F)
        {
            "mnbvcxzlkHjhgf"
        },

        Buffer (0x10)
        {
            "mnbvcxzlkHjhgf0"
        },

        Buffer (0x0F)
        {
            "mnbvcxzlkHjhgf"
        },

        Buffer (0x10)
        {
            "mnbvcxzlkHjhgf0"
        },

        Buffer (0x0F)
        {
            "mnbvcxzlkIjhgf"
        },

        Buffer (0x10)
        {
            "mnbvcxzlkIjhgf0"
        },

        Buffer (0x0F)
        {
            "mnbvcxzlkHjhgf"
        },

        Buffer (0x0F)
        {
            "mnbvcxzlkHjhgf"
        },

        Buffer (0x10)
        {
            "mnbvcxzlkHjhgf0"
        },

        Buffer (0x0F)
        {
            "mnbvcxzlkHjhgf"
        },

        Buffer (0x10)
        {
            "mnbvcxzlkIjhgf0"
        },

        Buffer (0x0F)
        {
            "mnbvcxzlkIjhgf"
        },

        Buffer (0x10)
        {
            "mnbvcxzlkHjhgf0"
        },

        Buffer (0x10)
        {
            "mnbvcxzlkIHjhgf"
        },

        Buffer (0x10)
        {
            "mnbvcxzlkHIjhgf"
        },

        Buffer (0x10)
        {
            "mnbvcxzlkHIjhgf"
        },

        Buffer (0x10)
        {
            "mnbvcxzlkIHjhgf"
        }
    })
    /* ===================================== LAnd */

    Name (P05D, Package (0x0D)
    {
        Ones,
        Ones,
        Zero,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Zero,
        Zero,
        Zero
    })
    Name (P05E, Package (0x0C)
    {
        Ones,
        Ones,
        Zero,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Zero,
        Zero
    })
    Method (LAN0, 0, Serialized)
    {
        Debug = "TEST: LAN0, Logical And"
        /* Integers */

        If ((F64 == 0x01))
        {
            M003 (__METHOD__, C002, "p060", P060, P05D, 0x01)
            M003 (__METHOD__, C003, "p061", P061, P05E, 0x01)
        }
        Else
        {
            M003 (__METHOD__, C002, "p060", P060, P05D, 0x01)
        }
    }

    /* ===================================== LNot */

    Name (P05F, Package (0x06)
    {
        Ones,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero
    })
    Name (P070, Package (0x04)
    {
        Ones,
        Zero,
        Zero,
        Zero
    })
    Method (LN00, 0, Serialized)
    {
        Debug = "TEST: LN00, Logical Not"
        /* Integers */

        If ((F64 == 0x01))
        {
            M004 (__METHOD__, C004, "p062", P062, P05F, 0x00)
            M004 (__METHOD__, C005, "p063", P063, P070, 0x00)
        }
        Else
        {
            M004 (__METHOD__, C004, "p062", P062, P05F, 0x00)
        }
    }

    /* ===================================== LOr */

    Name (P071, Package (0x0D)
    {
        Ones,
        Ones,
        Zero,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones
    })
    Name (P072, Package (0x0C)
    {
        Ones,
        Ones,
        Zero,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones
    })
    Method (LOR0, 0, Serialized)
    {
        Debug = "TEST: LOR0, Logical Or"
        /* Integers */

        If ((F64 == 0x01))
        {
            M003 (__METHOD__, C002, "p060", P060, P071, 0x02)
            M003 (__METHOD__, C003, "p061", P061, P072, 0x02)
        }
        Else
        {
            M003 (__METHOD__, C002, "p060", P060, P071, 0x02)
        }
    }

    /* ===================================== LEqual */

    Name (P073, Package (0x0D)
    {
        Ones,
        Ones,
        Ones,
        Ones,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero
    })
    Name (P074, Package (0x0C)
    {
        Ones,
        Ones,
        Ones,
        Ones,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero
    })
    Name (P075, Package (0x1F)
    {
        Ones,
        Zero,
        Zero,
        Ones,
        Zero,
        Zero,
        Ones,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Ones,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero
    })
    Name (P076, Package (0x33)
    {
        Ones,
        Zero,
        Zero,
        Zero,
        Zero,
        Ones,
        Zero,
        Zero,
        Zero,
        Zero,
        Ones,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Ones,
        Zero,
        Zero,
        Ones,
        Zero,
        Zero,
        Ones,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Ones,
        Zero,
        Zero,
        Ones,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Zero
    })
    Method (LEQ0, 0, Serialized)
    {
        Debug = "TEST: LEQ0, Logical Equal"
        /* Integers */

        If ((F64 == 0x01))
        {
            M003 (__METHOD__, C002, "p060", P060, P073, 0x03)
            M003 (__METHOD__, C003, "p061", P061, P074, 0x03)
        }
        Else
        {
            M003 (__METHOD__, C002, "p060", P060, P073, 0x03)
        }

        /* Strings */

        M003 (__METHOD__, C006, "p064", P064, P075, 0x03)
        Local0 = (BIG0 == BIG0)
        If ((Local0 != Ones))
        {
            ERR (__METHOD__, Z035, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        /* Buffers */

        M003 (__METHOD__, C007, "p065", P065, P076, 0x03)
    }

    /* ===================================== LGreater */

    Name (P077, Package (0x0D)
    {
        Zero,
        Zero,
        Zero,
        Zero,
        Ones,
        Zero,
        Ones,
        Zero,
        Ones,
        Zero,
        Zero,
        Zero,
        Zero
    })
    Name (P078, Package (0x0C)
    {
        Zero,
        Zero,
        Zero,
        Zero,
        Ones,
        Zero,
        Ones,
        Zero,
        Ones,
        Zero,
        Zero,
        Zero
    })
    Name (P079, Package (0x1F)
    {
        Zero,
        Zero,
        Ones,
        Zero,
        Ones,
        Zero,
        Zero,
        Ones,
        Zero,
        Ones,
        Zero,
        Zero,
        Ones,
        Ones,
        Zero,
        Zero,
        Ones,
        Zero,
        Ones,
        Zero,
        Zero,
        Zero,
        Ones,
        Ones,
        Zero,
        Ones,
        Zero,
        Zero,
        Ones,
        Ones,
        Zero
    })
    Name (P07A, Package (0x33)
    {
        Zero,
        Zero,
        Ones,
        Zero,
        Ones,
        Zero,
        Ones,
        Zero,
        Ones,
        Zero,
        Zero,
        Zero,
        Ones,
        Ones,
        Zero,
        Ones,
        Zero,
        Zero,
        Zero,
        Ones,
        Zero,
        Ones,
        Zero,
        Zero,
        Ones,
        Zero,
        Ones,
        Zero,
        Zero,
        Ones,
        Ones,
        Zero,
        Zero,
        Ones,
        Zero,
        Ones,
        Zero,
        Zero,
        Zero,
        Ones,
        Zero,
        Zero,
        Ones,
        Ones,
        Zero,
        Ones,
        Zero,
        Zero,
        Ones,
        Ones,
        Zero
    })
    Method (LGR0, 0, Serialized)
    {
        Debug = "TEST: LGR0, Logical Greater"
        /* Integers */

        If ((F64 == 0x01))
        {
            M003 (__METHOD__, C002, "p060", P060, P077, 0x04)
            M003 (__METHOD__, C003, "p061", P061, P078, 0x04)
        }
        Else
        {
            M003 (__METHOD__, C002, "p060", P060, P077, 0x04)
        }

        /* Strings */

        M003 (__METHOD__, C006, "p064", P064, P079, 0x04)
        Local0 = (BIG0 > BIG0)
        If ((Local0 != Zero))
        {
            ERR (__METHOD__, Z035, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        /* Buffers */

        M003 (__METHOD__, C007, "p065", P065, P07A, 0x04)
    }

    /* ===================================== LGreaterEqual */

    Name (P07B, Package (0x0D)
    {
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Zero,
        Ones,
        Zero,
        Ones,
        Zero,
        Zero,
        Zero,
        Zero
    })
    Name (P07C, Package (0x0C)
    {
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Zero,
        Ones,
        Zero,
        Ones,
        Zero,
        Zero,
        Zero
    })
    Name (P07D, Package (0x1F)
    {
        Ones,
        Zero,
        Ones,
        Ones,
        Ones,
        Zero,
        Ones,
        Ones,
        Zero,
        Ones,
        Zero,
        Zero,
        Ones,
        Ones,
        Zero,
        Zero,
        Ones,
        Zero,
        Ones,
        Zero,
        Ones,
        Zero,
        Ones,
        Ones,
        Zero,
        Ones,
        Zero,
        Zero,
        Ones,
        Ones,
        Zero
    })
    Name (P07E, Package (0x33)
    {
        Ones,
        Zero,
        Ones,
        Zero,
        Ones,
        Ones,
        Ones,
        Zero,
        Ones,
        Zero,
        Ones,
        Zero,
        Ones,
        Ones,
        Zero,
        Ones,
        Zero,
        Ones,
        Zero,
        Ones,
        Ones,
        Ones,
        Zero,
        Ones,
        Ones,
        Zero,
        Ones,
        Zero,
        Zero,
        Ones,
        Ones,
        Zero,
        Zero,
        Ones,
        Zero,
        Ones,
        Zero,
        Ones,
        Zero,
        Ones,
        Ones,
        Zero,
        Ones,
        Ones,
        Zero,
        Ones,
        Zero,
        Zero,
        Ones,
        Ones,
        Zero
    })
    Method (LGE0, 0, Serialized)
    {
        Debug = "TEST: LGE0, Logical Greater Than Or Equal"
        /* Integers */

        If ((F64 == 0x01))
        {
            M003 (__METHOD__, C002, "p060", P060, P07B, 0x05)
            M003 (__METHOD__, C003, "p061", P061, P07C, 0x05)
        }
        Else
        {
            M003 (__METHOD__, C002, "p060", P060, P07B, 0x05)
        }

        /* Strings */

        M003 (__METHOD__, C006, "p064", P064, P07D, 0x05)
        Local0 = (BIG0 >= BIG0)
        If ((Local0 != Ones))
        {
            ERR (__METHOD__, Z035, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        /* Buffers */

        M003 (__METHOD__, C007, "p065", P065, P07E, 0x05)
    }

    /* ===================================== LLess */

    Name (P07F, Package (0x0D)
    {
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Ones,
        Zero,
        Ones,
        Zero,
        Ones,
        Ones,
        Ones,
        Ones
    })
    Name (P080, Package (0x0C)
    {
        Zero,
        Zero,
        Zero,
        Zero,
        Zero,
        Ones,
        Zero,
        Ones,
        Zero,
        Ones,
        Ones,
        Ones
    })
    Name (P081, Package (0x1F)
    {
        Zero,
        Ones,
        Zero,
        Zero,
        Zero,
        Ones,
        Zero,
        Zero,
        Ones,
        Zero,
        Ones,
        Ones,
        Zero,
        Zero,
        Ones,
        Ones,
        Zero,
        Ones,
        Zero,
        Ones,
        Zero,
        Ones,
        Zero,
        Zero,
        Ones,
        Zero,
        Ones,
        Ones,
        Zero,
        Zero,
        Ones
    })
    Name (P082, Package (0x33)
    {
        Zero,
        Ones,
        Zero,
        Ones,
        Zero,
        Zero,
        Zero,
        Ones,
        Zero,
        Ones,
        Zero,
        Ones,
        Zero,
        Zero,
        Ones,
        Zero,
        Ones,
        Zero,
        Ones,
        Zero,
        Zero,
        Zero,
        Ones,
        Zero,
        Zero,
        Ones,
        Zero,
        Ones,
        Ones,
        Zero,
        Zero,
        Ones,
        Ones,
        Zero,
        Ones,
        Zero,
        Ones,
        Zero,
        Ones,
        Zero,
        Zero,
        Ones,
        Zero,
        Zero,
        Ones,
        Zero,
        Ones,
        Ones,
        Zero,
        Zero,
        Ones
    })
    Method (LL00, 0, Serialized)
    {
        Debug = "TEST: LL00, Logical Less"
        /* Integers */

        If ((F64 == 0x01))
        {
            M003 (__METHOD__, C002, "p060", P060, P07F, 0x06)
            M003 (__METHOD__, C003, "p061", P061, P080, 0x06)
        }
        Else
        {
            M003 (__METHOD__, C002, "p060", P060, P07F, 0x06)
        }

        /* Strings */

        M003 (__METHOD__, C006, "p064", P064, P081, 0x06)
        Local0 = (BIG0 < BIG0)
        If ((Local0 != Zero))
        {
            ERR (__METHOD__, Z035, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        /* Buffers */

        M003 (__METHOD__, C007, "p065", P065, P082, 0x06)
    }

    /* ===================================== LLessEqual */

    Name (P083, Package (0x0D)
    {
        Ones,
        Ones,
        Ones,
        Ones,
        Zero,
        Ones,
        Zero,
        Ones,
        Zero,
        Ones,
        Ones,
        Ones,
        Ones
    })
    Name (P084, Package (0x0C)
    {
        Ones,
        Ones,
        Ones,
        Ones,
        Zero,
        Ones,
        Zero,
        Ones,
        Zero,
        Ones,
        Ones,
        Ones
    })
    Name (P085, Package (0x1F)
    {
        Ones,
        Ones,
        Zero,
        Ones,
        Zero,
        Ones,
        Ones,
        Zero,
        Ones,
        Zero,
        Ones,
        Ones,
        Zero,
        Zero,
        Ones,
        Ones,
        Zero,
        Ones,
        Zero,
        Ones,
        Ones,
        Ones,
        Zero,
        Zero,
        Ones,
        Zero,
        Ones,
        Ones,
        Zero,
        Zero,
        Ones
    })
    Name (P086, Package (0x33)
    {
        Ones,
        Ones,
        Zero,
        Ones,
        Zero,
        Ones,
        Zero,
        Ones,
        Zero,
        Ones,
        Ones,
        Ones,
        Zero,
        Zero,
        Ones,
        Zero,
        Ones,
        Ones,
        Ones,
        Zero,
        Ones,
        Zero,
        Ones,
        Ones,
        Zero,
        Ones,
        Zero,
        Ones,
        Ones,
        Zero,
        Zero,
        Ones,
        Ones,
        Zero,
        Ones,
        Zero,
        Ones,
        Ones,
        Ones,
        Zero,
        Ones,
        Ones,
        Zero,
        Zero,
        Ones,
        Zero,
        Ones,
        Ones,
        Zero,
        Zero,
        Ones
    })
    Method (LLE0, 0, Serialized)
    {
        Debug = "TEST: LLE0, Logical Less Than Or Equal"
        /* Integers */

        If ((F64 == 0x01))
        {
            M003 (__METHOD__, C002, "p060", P060, P083, 0x07)
            M003 (__METHOD__, C003, "p061", P061, P084, 0x07)
        }
        Else
        {
            M003 (__METHOD__, C002, "p060", P060, P083, 0x07)
        }

        /* Strings */

        M003 (__METHOD__, C006, "p064", P064, P085, 0x07)
        Local0 = (BIG0 <= BIG0)
        If ((Local0 != Ones))
        {
            ERR (__METHOD__, Z035, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        /* Buffers */

        M003 (__METHOD__, C007, "p065", P065, P086, 0x07)
    }

    /* ===================================== LNotEqual */

    Name (P087, Package (0x0D)
    {
        Zero,
        Zero,
        Zero,
        Zero,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones
    })
    Name (P088, Package (0x0C)
    {
        Zero,
        Zero,
        Zero,
        Zero,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones
    })
    Name (P089, Package (0x1F)
    {
        Zero,
        Ones,
        Ones,
        Zero,
        Ones,
        Ones,
        Zero,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Zero,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones
    })
    Name (P08A, Package (0x33)
    {
        Zero,
        Ones,
        Ones,
        Ones,
        Ones,
        Zero,
        Ones,
        Ones,
        Ones,
        Ones,
        Zero,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Zero,
        Ones,
        Ones,
        Zero,
        Ones,
        Ones,
        Zero,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Zero,
        Ones,
        Ones,
        Zero,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones,
        Ones
    })
    Method (LNE0, 0, Serialized)
    {
        Debug = "TEST: LNE0, Logical Not equal"
        /* Integers */

        If ((F64 == 0x01))
        {
            M003 (__METHOD__, C002, "p060", P060, P087, 0x00)
            M003 (__METHOD__, C003, "p061", P061, P088, 0x00)
        }
        Else
        {
            M003 (__METHOD__, C002, "p060", P060, P087, 0x00)
        }

        /* Strings */

        M003 (__METHOD__, C006, "p064", P064, P089, 0x00)
        Local0 = (BIG0 != BIG0)
        If ((Local0 != Zero))
        {
            ERR (__METHOD__, Z035, __LINE__, 0x00, 0x00, 0x00, 0x00)
        }

        /* Buffers */

        M003 (__METHOD__, C007, "p065", P065, P08A, 0x00)
    }

    /* Run-method */

    Method (LOG0, 0, NotSerialized)
    {
        SRMT ("LAN0")
        LAN0 ()
        SRMT ("LN00")
        LN00 ()
        SRMT ("LOR0")
        LOR0 ()
        SRMT ("LEQ0")
        LEQ0 ()
        SRMT ("LGR0")
        LGR0 ()
        SRMT ("LGE0")
        LGE0 ()
        SRMT ("LL00")
        LL00 ()
        SRMT ("LLE0")
        LLE0 ()
        SRMT ("LNE0")
        LNE0 ()
    }
