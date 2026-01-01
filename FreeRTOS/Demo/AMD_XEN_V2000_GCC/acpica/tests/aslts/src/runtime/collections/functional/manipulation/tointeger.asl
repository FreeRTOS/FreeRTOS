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
     * Data type conversion and manipulation
     */
    /* Convert data to integer */
    Name (Z047, 0x2F)
    /* Integer */
    /* 32-bit */
    Name (P300, Package (0x06)
    {
        0x00,
        0x81,
        0x8232,
        0x76543201,
        0xF89ABCDE,
        0xFFFFFFFF
    })
    /* 64-bit */

    Name (P302, Package (0x05)
    {
        0x0000008123456789,
        0x00008CDAE2376890,
        0x76543201F89ABCDE,
        0xF89ABCDE76543201,
        0xFFFFFFFFFFFFFFFF
    })
    /* Hexadecimal numeric String */
    /* 32-bit */
    Name (P304, Package (0x20)
    {
        "0x0",       /* 0 */
        "0x00",
        "0x1",
        "0x83",
        "0x456",
        "0x8232",
        "0xbcdef",
        "0x123456",
        "0x789abcd",
        "0xffffffff",
        "0x01234567",    /* 10 */
        "0X12345678",
        "0x23456789",
        "0x3456789a",
        "0x456789ab",
        "0x56789abc",
        "0x6789abcd",
        "0x789abcde",
        "0x89abcdef",
        "0x9abcdefA",
        "0xabcdefAB",    /* 20 */
        "0xbcdefABC",
        "0xcdefABCD",
        "0xdefABCDE",
        "0xefABCDEF",
        "0xfABCDEF0",
        "0xABCDEF01",
        "0xBCDEF012",
        "0xCDEF0123",
        "0xDEF01234",
        "0xEF012345",    /* 30 */
        "0xF0123456"
    })
    Name (P305, Package (0x20)
    {
        0x00,
        0x00,
        0x01,
        0x83,
        0x0456,
        0x8232,
        0x000BCDEF,
        0x00123456,
        0x0789ABCD,
        0xFFFFFFFF,
        0x01234567,
        0x12345678,
        0x23456789,
        0x3456789A,
        0x456789AB,
        0x56789ABC,
        0x6789ABCD,
        0x789ABCDE,
        0x89ABCDEF,
        0x9ABCDEFA,
        0xABCDEFAB,
        0xBCDEFABC,
        0xCDEFABCD,
        0xDEFABCDE,
        0xEFABCDEF,
        0xFABCDEF0,
        0xABCDEF01,
        0xBCDEF012,
        0xCDEF0123,
        0xDEF01234,
        0xEF012345,
        0xF0123456
    })
    /* 64-bit */

    Name (P306, Package (0x20)
    {
        "0x123456789",       /* 0 */
        "0x8123456789",
        "0xabcdef01234",
        "0x876543210abc",
        "0x1234567abcdef",
        "0x8234567abcdef1",
        "0x6789abcdef01234",
        "0x76543201f89abcde",
        "0xf89abcde76543201",
        "0xffffffffffffffff",
        "0X0123456789abcdef",    /* 10 */
        "0x123456789abcdefA",
        "0x23456789abcdefAB",
        "0x3456789abcdefABC",
        "0x456789abcdefABCD",
        "0x56789abcdefABCDE",
        "0x6789abcdefABCDEF",
        "0x789abcdefABCDEF0",
        "0x89abcdefABCDEF01",
        "0x9abcdefABCDEF012",
        "0xabcdefABCDEF0123",    /* 20 */
        "0xbcdefABCDEF01234",
        "0xcdefABCDEF012345",
        "0xdefABCDEF0123456",
        "0xefABCDEF01234567",
        "0xfABCDEF012345678",
        "0xABCDEF0123456789",
        "0xBCDEF0123456789a",
        "0xCDEF0123456789ab",
        "0xDEF0123456789abc",
        "0xEF0123456789abcd",    /* 30 */
        "0xF0123456789abcde"
    })
    Name (P307, Package (0x20)
    {
        0x0000000123456789,
        0x0000008123456789,
        0x00000ABCDEF01234,
        0x0000876543210ABC,
        0x0001234567ABCDEF,
        0x008234567ABCDEF1,
        0x06789ABCDEF01234,
        0x76543201F89ABCDE,
        0xF89ABCDE76543201,
        0xFFFFFFFFFFFFFFFF,
        0x0123456789ABCDEF,
        0x123456789ABCDEFA,
        0x23456789ABCDEFAB,
        0x3456789ABCDEFABC,
        0x456789ABCDEFABCD,
        0x56789ABCDEFABCDE,
        0x6789ABCDEFABCDEF,
        0x789ABCDEFABCDEF0,
        0x89ABCDEFABCDEF01,
        0x9ABCDEFABCDEF012,
        0xABCDEFABCDEF0123,
        0xBCDEFABCDEF01234,
        0xCDEFABCDEF012345,
        0xDEFABCDEF0123456,
        0xEFABCDEF01234567,
        0xFABCDEF012345678,
        0xABCDEF0123456789,
        0xBCDEF0123456789A,
        0xCDEF0123456789AB,
        0xDEF0123456789ABC,
        0xEF0123456789ABCD,
        0xF0123456789ABCDE
    })
    /* Decimal numeric String */
    /* 32-bit */
    Name (P308, Package (0x15)
    {
        "0",
        "12",
        "345",
        "6789",
        "12345",
        "678901",
        "2345678",
        "90123456",
        "789012345",
        "4294967295",    /* == "0xffffffff" */
        "4294967295",    /* == "0xffffffff" */
        "0123456789",
        "1234567890",
        "2345678901",
        "3456789012",
        "1567890123",
        "2678901234",
        "3789012345",
        "1890123456",
        "2901234567",
        "3012345678"
    })
    Name (P309, Package (0x15)
    {
        0x00,
        0x0C,
        0x0159,
        0x1A85,
        0x3039,
        0x000A5BF5,
        0x0023CACE,
        0x055F2CC0,
        0x2F075F79,
        0xFFFFFFFF,
        0xFFFFFFFF,
        0x075BCD15,
        0x499602D2,
        0x8BD03835,
        0xCE0A6A14,
        0x5D741ACB,
        0x9FACC9F2,
        0xE1D7BD79,
        0x70A8FEC0,
        0xACED5387,
        0xB38CBF4E
    })
    /* 64-bit */

    Name (P310, Package (0x15)
    {
        "30123456790",
        "123456789012",
        "3456789012345",
        "26789012346789",
        "123456789012345",
        "3789012345678901",
        "23456789012345678",
        "301234567890123456",
        "1890123456789012345",
        "18446744073709551615",  /* == "0xffffffffffffffff" */
        "18446744073709551615",  /* == "0xffffffffffffffff" */
        "01234567890123456789",
        "12345678901234567890",
        "13456789012345678901",
        "14567890123456789012",
        "15678901231567890123",
        "16789012342678901234",
        "17890123453789012345",
        "18301234561890123456",
        "18012345672901234567",
        "10123456783012345678"
    })
    Name (P311, Package (0x15)
    {
        0x00000007037F7916,
        0x0000001CBE991A14,
        0x00000324D8AE5F79,
        0x0000185D4D9097A5,
        0x00007048860DDF79,
        0x000D76162EE9EC35,
        0x005355D348A6F34E,
        0x042E333E5528BAC0,
        0x1A3B1145078ADF79,
        0xFFFFFFFFFFFFFFFF,
        0xFFFFFFFFFFFFFFFF,
        0x112210F47DE98115,
        0xAB54A98CEB1F0AD2,
        0xBAC01E4F423E6C35,
        0xCA2B8AE21F903A14,
        0xD996A5998809E6CB,
        0xE8FE8DC60F0651F2,
        0xF8467C7ECAFA8179,
        0xFDFB0BDEB48FFEC0,
        0xF9F8B4F4BCD28F87,
        0x8C7DBE4ECA78374E
    })
    /* Buffer */
    /* 32-bit */
    Name (P312, Package (0x05)
    {
        /* buffer, 32-bit integer */

        Buffer (0x01)
        {
             0x81                                             // .
        },

        Buffer (0x02)
        {
             0x82, 0x83                                       // ..
        },

        Buffer (0x03)
        {
             0x84, 0x85, 0x86                                 // ...
        },

        Buffer (0x04)
        {
             0x87, 0x88, 0x89, 0x8A                           // ....
        },

        /* for 32-bit mode only */

        Buffer (0x05)
        {
             0x8B, 0x8C, 0x8D, 0x8E, 0x8F                     // .....
        }
    })
    Name (P313, Package (0x05)
    {
        0x81,
        0x8382,
        0x00868584,
        0x8A898887,
        0x8E8D8C8B
    })
    /* 64-bit */

    Name (P314, Package (0x05)
    {
        Buffer (0x05)
        {
             0x85, 0x84, 0x83, 0x82, 0x81                     // .....
        },

        Buffer (0x06)
        {
             0x8B, 0x8A, 0x89, 0x88, 0x87, 0x86               // ......
        },

        Buffer (0x07)
        {
             0x82, 0x81, 0x80, 0x8F, 0x8E, 0x8D, 0x8C         // .......
        },

        Buffer (0x08)
        {
             0x8A, 0x89, 0x88, 0x87, 0x86, 0x85, 0x84, 0x83   // ........
        },

        Buffer (0x09)
        {
            /* 0000 */  0x83, 0x82, 0x81, 0x80, 0x8F, 0x8E, 0x8D, 0x8C,  // ........
            /* 0008 */  0x8B                                             // .
        }
    })
    Name (P315, Package (0x05)
    {
        /* buffer, 32-bit integer */

        0x0000008182838485,
        0x0000868788898A8B,
        0x008C8D8E8F808182,
        0x838485868788898A,
        0x8C8D8E8F80818283
    })
    /* Run-method */

    Method (TOI0, 0, Serialized)
    {
        Debug = "TEST: TOI0, Convert data to integer"
        /* From integer */

        If ((F64 == 0x01))
        {
            M302 (__METHOD__, 0x06, "p300", P300, P300, 0x00)
            M302 (__METHOD__, 0x05, "p302", P302, P302, 0x00)
        }
        Else
        {
            M302 (__METHOD__, 0x06, "p300", P300, P300, 0x00)
        }

        /* From hexadecimal numeric string */

        If ((F64 == 0x01))
        {
            M302 (__METHOD__, 0x20, "p304", P304, P305, 0x00)
            M302 (__METHOD__, 0x20, "p306", P306, P307, 0x00)
        }
        Else
        {
            M302 (__METHOD__, 0x20, "p304", P304, P305, 0x00)
        }

        /* From decimal numeric string */

        If ((F64 == 0x01))
        {
            M302 (__METHOD__, 0x15, "p308", P308, P309, 0x00)
            M302 (__METHOD__, 0x15, "p310", P310, P311, 0x00)
        }
        Else
        {
            M302 (__METHOD__, 0x15, "p308", P308, P309, 0x00)
        }

        /* From buffer */

        If ((F64 == 0x01))
        {
            M302 (__METHOD__, 0x04, "p312", P312, P313, 0x00)
            M302 (__METHOD__, 0x05, "p314", P314, P315, 0x00)
        }
        Else
        {
            M302 (__METHOD__, 0x05, "p312", P312, P313, 0x00)
        }

        /* Suppression of zeroes */

        If (Y602)
        {
            CH03 (__METHOD__, Z047, __LINE__, 0x00, 0x00)
            Local0 = "0x0123456789abcdefa"
            ToInteger (Local0, Local2)
            CH04 (__METHOD__, 0x00, 0x22, Z047, __LINE__, 0x00, 0x00)
            CH03 (__METHOD__, Z047, __LINE__, 0x00, 0x00)
            Local0 = "0x000123456789abcdefa"
            ToInteger (Local0, Local2)
            CH04 (__METHOD__, 0x00, 0x22, Z047, __LINE__, 0x00, 0x00)
        }
        Else
        {
            Local0 = "0x0123456789abcdefa"
            Local1 = 0x123456789ABCDEFA
            ToInteger (Local0, Local2)
            If ((Local2 != Local1))
            {
                ERR (__METHOD__, Z047, __LINE__, 0x00, 0x00, Local0, 0x00)
            }

            Local0 = "0x000123456789abcdefa"
            ToInteger (Local0, Local2)
            If ((Local2 != Local1))
            {
                ERR (__METHOD__, Z047, __LINE__, 0x00, 0x00, Local0, 0x00)
            }
        }
    }
