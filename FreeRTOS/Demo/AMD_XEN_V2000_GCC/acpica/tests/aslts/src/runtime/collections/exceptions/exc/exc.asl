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
     * Initiate exceptional conditions by all the known ways.
     * Verify the reaction.
     *
     * Current max index of checking is 170
     */
    Name (Z058, 0x3A)
    /* Divide by zero */

    Method (M140, 0, Serialized)
    {
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        Local1 = 0x01
        Local0 = 0x02
        Divide (Local1, Local0, Local2)
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        Local0 = 0x00
        Divide (Local1, Local0, Local2)
        CH04 (__METHOD__, 0x00, 0x38, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_DIVIDE_BY_ZERO */
        Local0 = 0x02
        Divide (Local1, Local0, Local2)
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
    }

    /* Modulo divide by zero */

    Method (M141, 0, Serialized)
    {
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        Local1 = 0x01
        Local0 = 0x02
        Local2 = (Local1 % Local0)
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        Local0 = 0x00
        Local2 = (Local1 % Local0)
        CH04 (__METHOD__, 0x00, 0x38, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_DIVIDE_BY_ZERO */
        Local0 = 0x02
        Local2 = (Local1 % Local0)
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
    }

    /* Release ownership on a Mutex that is not currently owned */

    Method (M142, 0, Serialized)
    {
        Mutex (MTX0, 0x00)
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        Release (MTX0)
        CH04 (__METHOD__, 0x00, 0x41, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_MUTEX_NOT_ACQUIRED */
    }

    /* SizeOf for data types not an Integer, Buffer, String or Package object */

    Method (M143, 0, Serialized)
    {
        /* Method */
        /* DDB Handle */
        /* Debug Object */
        /* Uninitialized */
        /* Integer */
        Name (INT0, 0x00)
        /* String */

        Name (STR0, "string")
        /* Buffer */

        Name (BUF0, Buffer (0x0A)
        {
             0x00                                             // .
        })
        /* Package */

        Name (PAC0, Package (0x01)
        {
            0x00
        })
        /* Device */

        Device (DEV0)
        {
        }

        /* Event */

        Event (EVE0)
        /* Mutex */

        Mutex (MTX0, 0x00)
        /* Operation Region */

        OperationRegion (OPR0, SystemMemory, 0x00, 0x04)
        /* Power Resource */

        PowerResource (PWR0, 0x00, 0x0000){}
        /* Processor */

        Processor (CPU0, 0x00, 0xFFFFFFFF, 0x00){}
        /* Thermal Zone */

        ThermalZone (TZN0)
        {
        }

        /* Buffer Field */

        Local0 = BUF0 [0x00]
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        Local5 = SizeOf (STR0)
        Local5 = SizeOf (BUF0)
        Local5 = SizeOf (PAC0)
        Local5 = SizeOf (INT0)
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        If (INT0)
        {
            Local1 = 0x00
        }

        Local5 = SizeOf (Local1)
        CH04 (__METHOD__, 0x01, 0x31, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_UNINITIALIZED_LOCAL */
        /* These are now caught by the compiler - Aug 2015 */
    /*	Store(SizeOf(DEV0), Local5) */
    /*	CH04(ts, 1, 47, z058, __LINE__, 0, 0)	// AE_AML_OPERAND_TYPE */
    /* */
    /*	Store(SizeOf(EVE0), Local5) */
    /*	CH04(ts, 1, 47, z058, __LINE__, 0, 0)	// AE_AML_OPERAND_TYPE */
    /* */
    /*	Store(SizeOf(MTX0), Local5) */
    /*	CH04(ts, 1, 47, z058, __LINE__, 0, 0)	// AE_AML_OPERAND_TYPE */
    /* */
    /*	Store(SizeOf(OPR0), Local5) */
    /*	CH04(ts, 1, 47, z058, __LINE__, 0, 0)	// AE_AML_OPERAND_TYPE */
    /* */
    /*	Store(SizeOf(PWR0), Local5) */
    /*	CH04(ts, 1, 47, z058, __LINE__, 0, 0)	// AE_AML_OPERAND_TYPE */
    /* */
    /*	Store(SizeOf(CPU0), Local5) */
    /*	CH04(ts, 1, 47, z058, __LINE__, 0, 0)	// AE_AML_OPERAND_TYPE */
    /* */
    /*	Store(SizeOf(TZN0), Local5) */
    /*	CH04(ts, 1, 47, z058, __LINE__, 0, 0)	// AE_AML_OPERAND_TYPE */
    }

    /* ToString() when the number of characters copied from buffer exceeds 200 */

    Method (M144, 0, Serialized)
    {
        Name (B000, Buffer (0xC8){})
        Local0 = 0x00
        While ((Local0 < 0xC8))
        {
            B000 [Local0] = 0xFF
            Local0++
        }

        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        ToString (B000, Ones, Local5)
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        Name (B001, Buffer (0xC9){})
        Local0 = 0x00
        While ((Local0 < 0xC9))
        {
            B001 [Local0] = 0xFF
            Local0++
        }

        ToString (B001, Ones, Local5)
        /*
         * CH04(ts, 0, 61, z058, __LINE__, 0, 0)	// AE_AML_STRING_LIMIT
         *
         * 20.12.2005.
         * No more limit of string size.
         */
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
    }

    /* Access out of Package */

    Method (M145, 0, Serialized)
    {
        Name (P000, Package (0x03)
        {
            0x00,
            0x01,
            0x02
        })
        Name (P001, Package (0x03)
        {
            0x00,
            0x01,
            0x02
        })
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        /* Package() */

        Store (P000 [0x02], Local5)
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        Store (P000 [0x03], Local5)
        CH04 (__METHOD__, 0x01, 0x37, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_PACKAGE_LIMIT */
        Local0 = P000 [0x02]
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        Local0 = P000 [0x03]
        CH04 (__METHOD__, 0x00, 0x37, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_PACKAGE_LIMIT */
        /* Package(3) */

        Store (P001 [0x02], Local5)
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        Local5 = P001 [0x03]
        CH04 (__METHOD__, 0x00, 0x37, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_PACKAGE_LIMIT */
        Local0 = P001 [0x02]
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        Local0 = P001 [0x03]
        CH04 (__METHOD__, 0x00, 0x37, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_PACKAGE_LIMIT */
    }

    /* Access out of String */

    Method (M085, 0, Serialized)
    {
        Name (S000, "123")
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        Local5 = S000 [0x02]
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        Local5 = S000 [0x03]
        /* Bug 177, Bugzilla 5480. */

        CH04 (__METHOD__, 0x00, 0x3D, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_STRING_LIMIT */
        Local0 = S000 [0x02]
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        Local0 = S000 [0x03]
        CH04 (__METHOD__, 0x00, 0x3D, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_STRING_LIMIT */
    }

    /* Access out of Buffer */

    Method (M086, 0, Serialized)
    {
        Name (B000, Buffer (0x03)
        {
             0x00, 0x01, 0x02                                 // ...
        })
        Name (B001, Buffer (0x03)
        {
             0x00, 0x01, 0x02                                 // ...
        })
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        /* Buffer() */

        Local5 = B000 [0x02]
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        Local5 = B000 [0x03]
        CH04 (__METHOD__, 0x00, 0x36, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_BUFFER_LIMIT */
        Local0 = B000 [0x02]
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        Local0 = B000 [0x03]
        CH04 (__METHOD__, 0x00, 0x36, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_BUFFER_LIMIT */
        /* Buffer(3) */

        Local5 = B001 [0x02]
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        Local5 = B001 [0x03]
        CH04 (__METHOD__, 0x00, 0x36, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_BUFFER_LIMIT */
        Local0 = B001 [0x02]
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        Local0 = B001 [0x03]
        CH04 (__METHOD__, 0x00, 0x36, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_BUFFER_LIMIT */
    }

    /* ToInteger() passed with an image of a number which value */
    /* exceeds the maximum of an integer for the current mode. */
    Method (M146, 0, Serialized)
    {
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        If ((F64 == 0x01))
        {
            Local0 = "0xffffffffffffffff"
        }
        Else
        {
            Local0 = "0xffffffff"
        }

        ToInteger (Local0, Local5)
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        If ((F64 == 0x01))
        {
            Local0 = "0x11111111111111111"
        }
        Else
        {
            Local0 = "0x111111111"
        }

        ToInteger (Local0, Local5)
        CH04 (__METHOD__, 0x00, 0x2E, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_NO_OPERAND */
    }

    /* [Uninitialized] None. */
    /* Causes a fatal error when used as a source */
    /* operand in any ASL statement. */
    Method (M147, 1, Serialized)
    {
        If (Arg0)
        {
            Local0 = 0x00
        }

        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        Local0++
        CH04 (__METHOD__, 0x00, 0x31, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_UNINITIALIZED_LOCAL */
    }

    Method (M148, 0, NotSerialized)
    {
        M147 (0x00)
    }

    /* Stall, Time parameter is too large (> 100) */

    Method (M149, 1, Serialized)
    {
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        Stall (Arg0)
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
    }

    Method (M14A, 1, Serialized)
    {
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        Stall (Arg0)
        /* It is now bug 14. */

        CH04 (__METHOD__, 0x00, 0x30, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_OPERAND_VALUE */
    }

    /* Bug 14. */

    Method (M14B, 0, NotSerialized)
    {
        M149 (0x64)
        /*
     * We are forced by Windows and BIOS code to increase the maximum stall
     * time to 255, this is in violation of the ACPI specification.
     * ACPI specification requires that Stall() does not relinquish the
     * processor, and delays longer than 100 usec should use Sleep()
     * instead. We allow stall up to 255 usec for compatibility with other
     * interpreters and existing BIOS.
     *
     * So we remove this test from test suite.
     *
     * m14a(101)
     */
    }

    /* Concatenate() when the number of result characters in string exceeds 200 */

    Method (M14C, 0, Serialized)
    {
        /* 100 characters */

        Local0 = "0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"
        /* 101 characters */

        Local1 = "01234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890"
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        Concatenate (Local0, Local0, Local5)
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        Concatenate (Local0, Local1, Local5)
        /*
         * CH04(ts, 0, 61, z058, __LINE__, 0, 0)	// AE_AML_STRING_LIMIT
         *
         * 20.12.2005.
         * No more limit of string size.
         */
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
    }

    /* ToDecimalString() when the number of result characters in string exceeds 200 */

    Method (M14D, 0, Serialized)
    {
        /* Results into 200 (99 * 2 + 2) characters */

        Name (B000, Buffer (0x64)
        {
            /* 0000 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0008 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0010 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0018 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0020 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0028 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0030 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0038 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0040 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0048 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0050 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0058 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0060 */  0x01, 0x01, 0x01, 0x0B                           // ....
        })
        /* Results into 201 (100 * 2 + 1) characters */

        Name (B001, Buffer (0x65)
        {
            /* 0000 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0008 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0010 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0018 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0020 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0028 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0030 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0038 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0040 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0048 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0050 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0058 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0060 */  0x01, 0x01, 0x01, 0x01, 0x01                     // .....
        })
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        ToDecimalString (B000, Local5)
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        ToDecimalString (B001, Local5)
        /*
         * CH04(ts, 0, 61, z058, __LINE__, 0, 0)	// AE_AML_STRING_LIMIT
         *
         * 20.12.2005.
         * No more limit of string size.
         */
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
    }

    /* ToBCD() when a specified integer overflows a number of the BCD format */

    Method (M14E, 0, Serialized)
    {
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        If ((F64 == 0x01))
        {
            Local4 = 0x002386F26FC0FFFF
            ToBCD (Local4, Local5)
        }
        Else
        {
            ToBCD (0x05F5E0FF, Local5)
        }

        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        If ((F64 == 0x01))
        {
            Local4 = 0x002386F26FC10000
            ToBCD (Local4, Local5)
        }
        Else
        {
            Local4 = 0x05F5E100
            ToBCD (Local4, Local5)
        }

        CH04 (__METHOD__, 0x00, 0x34, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_NUMERIC_OVERFLOW */
    }

    /* Create field out of buffer */

    Method (M14F, 0, Serialized)
    {
        Name (B001, Buffer (0x10){})
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        CreateBitField (B001, 0x7F, F000)
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        CreateBitField (B001, 0x80, F001)
        CH04 (__METHOD__, 0x00, 0x36, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_BUFFER_LIMIT */
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        CreateByteField (B001, 0x0F, F002)
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        CreateByteField (B001, 0x10, F003)
        CH04 (__METHOD__, 0x00, 0x36, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_BUFFER_LIMIT */
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        CreateWordField (B001, 0x0E, F004)
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        CreateWordField (B001, 0x0F, F005)
        CH04 (__METHOD__, 0x00, 0x36, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_BUFFER_LIMIT */
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        CreateDWordField (B001, 0x0C, F006)
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        CreateDWordField (B001, 0x0D, F007)
        CH04 (__METHOD__, 0x00, 0x36, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_BUFFER_LIMIT */
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        CreateQWordField (B001, 0x08, F008)
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        CreateQWordField (B001, 0x09, F009)
        CH04 (__METHOD__, 0x00, 0x36, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_BUFFER_LIMIT */
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        CreateField (B001, 0x7F, 0x01, F00A)
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        CreateField (B001, 0x80, 0x01, F00B)
        CH04 (__METHOD__, 0x00, 0x36, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_BUFFER_LIMIT */
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        CreateField (B001, 0x78, 0x08, F00C)
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        CreateField (B001, 0x78, 0x09, F00D)
        CH04 (__METHOD__, 0x00, 0x36, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_BUFFER_LIMIT */
    }

    /* Access to uninitialized local */

    Method (M150, 1, Serialized)
    {
        If (Arg0)
        {
            Local0 = 0x00
        }

        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        Local5 = Local0 [0x00]
        CH04 (__METHOD__, 0x00, 0x31, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_UNINITIALIZED_LOCAL */
    }

    /* Access to an uninitialized element of package */

    Method (M151, 0, Serialized)
    {
        Name (P000, Package (0x04)
        {
            0x00,
            0x01,
            0x02
        })
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        Local5 = DerefOf (P000 [0x02])
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        Local5 = DerefOf (P000 [0x03])
        /*
         * Obsolete:
         * CH04(ts, 0, 51, z058, __LINE__, 0, 0)	// AE_AML_UNINITIALIZED_ELEMENT
         *
         * Updated according to Bug 85 fix: no exception is expected
         * since the value is not processed.
         */
        /*
         * OBSOLETE July 2013. DerefOf on an empty package element now causes error
         * CH04(ts, 0, 62, z058, __LINE__, 0, 0)
         */
        CH04 (__METHOD__, 0x01, 0x33, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_UNINITIALIZED_ELEMENT */
        Local5 = (DerefOf (P000 [0x03]) + 0x01)
        If (EXCV)
        {
            CH04 (__METHOD__, 0x00, 0x33, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_UNINITIALIZED_ELEMENT */
        }
        Else
        {
            CH04 (__METHOD__, 0x00, 0xFF, Z058, __LINE__, 0x00, 0x00)
        }

        Return (0x00)
    }

    /* ToHexString() when the number of result characters in string exceeds 200 */

    Method (M152, 0, Serialized)
    {
        /* Results into 200 (67 * 3 - 1) characters */

        Name (B000, Buffer (0x43)
        {
            /* 0000 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0008 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0010 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0018 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0020 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0028 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0030 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0038 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0040 */  0x01, 0x01, 0x01                                 // ...
        })
        /* Results into 203 (68 * 3 - 1) characters */

        Name (B001, Buffer (0x44)
        {
            /* 0000 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0008 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0010 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0018 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0020 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0028 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0030 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0038 */  0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,  // ........
            /* 0040 */  0x01, 0x01, 0x01, 0x01                           // ....
        })
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        ToHexString (B000, Local5)
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        ToHexString (B001, Local5)
        /*
         * CH04(ts, 0, 61, z058, __LINE__, 0, 0)	// AE_AML_STRING_LIMIT
         *
         * 20.12.2005.
         * No more limit of string size.
         */
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
    }

    /* StartIndex in Match greater than the package size */

    Method (M153, 0, Serialized)
    {
        Name (PAC0, Package (0x01)
        {
            0x00
        })
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        Local5 = Match (PAC0, MTR, 0x00, MTR, 0x00, 0x00)
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        Local5 = Match (PAC0, MTR, 0x00, MTR, 0x00, 0x01)
        CH04 (__METHOD__, 0x01, 0x37, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_PACKAGE_LIMIT */
    }

    /* Exceptional conditions of ConcatenateResTemplate */

    Method (M154, 0, Serialized)
    {
        Name (RT00, ResourceTemplate ()
        {
            IRQNoFlags ()
                {1}
        })
        /* Empty buffer */

        Local0 = 0x00
        Local2 = Buffer (Local0){}
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        ConcatenateResTemplate (RT00, RT00, Local5)
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        ConcatenateResTemplate (RT00, Local2, Local5)
        /* Bug 188. */

        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        /* CH04(ts, 0, 71, z058, __LINE__, 0, 0)	// AE_AML_NO_RESOURCE_END_TAG */
        /* One-element buffer */
        Local2 = Buffer (0x01)
            {
                 0x00                                             // .
            }
        ConcatenateResTemplate (RT00, Local2, Local5)
        /*
         * Note: As for there is not a separate type for ResourceTemplate,
         * ResourceTemplate is in fact a buffer but interpreted as
         * ResourceTemplate. If the buffer has no complete END_TAG descriptor,
         * we get AE_AML_NO_RESOURCE_END_TAG instead of AE_AML_OPERAND_TYPE.
         */
        If (EXCV)
        {
            CH04 (__METHOD__, 0x00, 0x47, Z058, __LINE__, 0x00, 0x00) /* AE_AML_NO_RESOURCE_END_TAG */
        }
        Else
        {
            CH04 (__METHOD__, 0x00, 0xFF, Z058, __LINE__, 0x00, 0x00)
        }

        /* One-element 0x79 buffer */

        Local2 = Buffer (0x01)
            {
                 0x79                                             // y
            }
        ConcatenateResTemplate (RT00, Local2, Local5)
        /* Bug 189. */

        CH04 (__METHOD__, 0x00, 0x47, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_NO_RESOURCE_END_TAG */
        /* Not resource template buffer */

        Local2 = Buffer (0x03)
            {
                 0x2A, 0x04, 0x02                                 // *..
            }
        ConcatenateResTemplate (RT00, Local2, Local5)
        If (EXCV)
        {
            CH04 (__METHOD__, 0x00, 0x47, Z058, __LINE__, 0x00, 0x00) /* AE_AML_NO_RESOURCE_END_TAG */
        }
        Else
        {
            CH04 (__METHOD__, 0x00, 0xFF, Z058, __LINE__, 0x00, 0x00)
        }

        /* Nearly resource template buffer */

        Local2 = Buffer (0x04)
            {
                 0x2A, 0x10, 0x05, 0x79                           // *..y
            }
        ConcatenateResTemplate (RT00, Local2, Local5)
        /* Bug 190. */

        CH04 (__METHOD__, 0x00, 0x47, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_NO_RESOURCE_END_TAG */
        /* Like resource template buffer */

        Local2 = Buffer (0x05)
            {
                 0x00, 0x00, 0x00, 0x79, 0x00                     // ...y.
            }
        ConcatenateResTemplate (RT00, Local2, Local5)
        If (EXCV)
        {
            CH04 (__METHOD__, 0x00, 0x47, Z058, __LINE__, 0x00, 0x00) /* AE_AML_NO_RESOURCE_END_TAG */
        }
        Else
        {
            CH04 (__METHOD__, 0x00, 0xFF, Z058, __LINE__, 0x00, 0x00)
        }

        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
    }

    /*
     * Obsolete:
     * Bug 63: The following operation should initiate
     * AE_BAD_HEX_CONSTANT exception
     *
     *
     * Bug 63, Bugzilla 5329.
     *
     * Updated specs 12.03.05:
     * "Note: the first non-hex character terminates the conversion
     * without error, and a '0x' prefix is not allowed."
     *
     * Update 08.10.17
     * Allow '0x' prefix for usability and clarity.
     */
    Method (M155, 0, Serialized)
    {
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        Local0 = ("0x1111" + 0x00)
        /*
         * Obsolete:
         * CH04(ts, 0, 34, z058, __LINE__, 0, 0)	// AE_BAD_HEX_CONSTANT
         *
         * New:
         */
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        If ((Local0 != 0x1111))
        {
            /* Bug 63, Bugzilla 5329. */

            ERR (__METHOD__, Z058, __LINE__, 0x00, 0x00, Local0, 0x00)
        }
    }

    /*
     * Bug 64: The following operations should initiate exceptions.
     * AE_BAD_HEX_CONSTANT is the most appropreate, but it was decided
     * to weaken demands - it is enough that some exception arises
     * even if it is not the most appropreate one.
     * See 111,112,113.
     */
    Method (M156, 0, Serialized)
    {
        Local0 = 0x00
        Name (B000, Buffer (Local0){})
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        /* Add, empty String */

        Local5 = ("" + 0x00)
        /*	CH04(ts, 0, 34, z058, __LINE__, 0, 0)	// AE_BAD_HEX_CONSTANT */

        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        /* Add, String filled with blanks */

        Local5 = ("                 " + 0x00)
        /*	CH04(ts, 0, 34, z058, __LINE__, 0, 0)	// AE_BAD_HEX_CONSTANT */

        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        /* ToInteger, empty String */

        Local4 = ""
        ToInteger (Local4, Local5)
        CH04 (__METHOD__, 0x00, 0x24, Z058, __LINE__, 0x00, 0x00)   /* AE_BAD_DECIMAL_CONSTANT */
        /* ToInteger, String filled with blanks */

        Local4 = "                 "
        ToInteger (Local4, Local5)
        /*	CH04(ts, 0, 34, z058, __LINE__, 0, 0)	// AE_BAD_HEX_CONSTANT */

        CH04 (__METHOD__, 0x00, 0x24, Z058, __LINE__, 0x00, 0x00)   /* AE_BAD_DECIMAL_CONSTANT */
        /* Add, zero-length Buffer */

        Local5 = (B000 + 0x00)
        /*	CH04(ts, 0, 34, z058, __LINE__, 0, 0)	// AE_BAD_HEX_CONSTANT */

        CH04 (__METHOD__, 0x00, 0x36, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_BUFFER_LIMIT */
        /* ToInteger, zero-length Buffer */

        ToInteger (B000, Local5)
        /*	CH04(ts, 0, 34, z058, __LINE__, 0, 0)	// AE_BAD_HEX_CONSTANT */

        CH04 (__METHOD__, 0x00, 0x36, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_BUFFER_LIMIT */
    }

    /* ////////////////////////////////////////////////////////// */
    /* */
    /* Attempt to generate references upon an arbitrary addresses */
    /* */
    /* ////////////////////////////////////////////////////////// */
    /* Index(Integer) */
    Method (M157, 0, Serialized)
    {
        Name (I000, 0xAAAAAAAA)
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        Store (I000 [0x00], Local5)
        CH04 (__METHOD__, 0x01, 0x2F, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_OPERAND_TYPE */
        Local0 = I000 [0x00]
        CH04 (__METHOD__, 0x00, 0x2F, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_OPERAND_TYPE */
        Store (I000 [0x00], Local0)
        CH04 (__METHOD__, 0x00, 0xFF, Z058, __LINE__, 0x00, 0x00)
        Local1 = Local0 = I000 [0x00]
        CH04 (__METHOD__, 0x00, 0xFF, Z058, __LINE__, 0x00, 0x00)
    }

    /* Bug 83 */
    /* DerefOf(Integer) */
    Method (M158, 0, Serialized)
    {
        Name (I000, 0xAAAAAAAA)
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        /* Bug 83, Bugzilla 5387. */

        Local5 = DerefOf (I000)
        CH04 (__METHOD__, 0x00, 0xFF, Z058, __LINE__, 0x00, 0x00)
        Local0 = DerefOf (I000)
        /* Bug 83, Bugzilla 5387. */

        CH04 (__METHOD__, 0x00, 0xFF, Z058, __LINE__, 0x00, 0x00)
    }

    /* Index(Local7-Integer) */
    /* DerefOf(Integer) */
    Method (M087, 0, Serialized)
    {
        Name (I000, 0xAAAAAAAA)
        Local7 = I000 /* \M087.I000 */
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        /* Index(Integer) */

        Store (Local7 [0x00], Local5)
        CH04 (__METHOD__, 0x01, 0x2F, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_OPERAND_TYPE */
        Local0 = Local7 [0x00]
        CH04 (__METHOD__, 0x00, 0x2F, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_OPERAND_TYPE */
        Store (Local7 [0x00], Local0)
        CH04 (__METHOD__, 0x00, 0xFF, Z058, __LINE__, 0x00, 0x00)
        Local1 = Local0 = Local7 [0x00]
        CH04 (__METHOD__, 0x00, 0xFF, Z058, __LINE__, 0x00, 0x00)
        /* DerefOf(Integer) */

        Local5 = DerefOf (Local7)
        CH04 (__METHOD__, 0x00, 0xFF, Z058, __LINE__, 0x00, 0x00)
        Local0 = DerefOf (Local7)
        CH04 (__METHOD__, 0x00, 0xFF, Z058, __LINE__, 0x00, 0x00)
    }

    /* Index(Buffer Field) */

    Method (M159, 0, Serialized)
    {
        Name (B000, Buffer (0x09)
        {
            /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
            /* 0008 */  0x09                                             // .
        })
        CreateField (B000, 0x00, 0x08, BF00)
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        Store (BF00 [0x00], Local5)
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        Local0 = BF00 [0x00]
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        Store (BF00 [0x00], Local0)
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        Store (BF00 [0x00], Local0)
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        Local1 = Local0 = BF00 [0x00]
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
    }

    /* Bug 83 */
    /* DerefOf(Buffer Field) */
    Method (M15A, 0, Serialized)
    {
        Name (B000, Buffer (0x09)
        {
            /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
            /* 0008 */  0x09                                             // .
        })
        CreateField (B000, 0x00, 0x08, BF00)
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        Local5 = DerefOf (BF00)
        /* Bug 83, Bugzilla 5387. */

        CH04 (__METHOD__, 0x00, 0xFF, Z058, __LINE__, 0x00, 0x00)
        Local0 = DerefOf (BF00)
        /* Bug 83, Bugzilla 5387. */

        CH04 (__METHOD__, 0x00, 0xFF, Z058, __LINE__, 0x00, 0x00)
    }

    /* Index(Field Unit) */

    Method (M15D, 0, Serialized)
    {
        OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
        Field (R000, ByteAcc, NoLock, Preserve)
        {
            F000,   8
        }

        Field (R000, ByteAcc, NoLock, Preserve)
        {
            BNK0,   8,
            F00A,   8,
            F00B,   8
        }

        BankField (R000, BNK0, 0x00, ByteAcc, NoLock, Preserve)
        {
            BKF0,   4
        }

        IndexField (F00A, F00B, ByteAcc, NoLock, Preserve)
        {
            IF00,   1,
            IF01,   1
        }

        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        /* Field */

        Store (F000 [0x00], Local5)
        CH04 (__METHOD__, 0x01, 0x2F, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_OPERAND_TYPE */
        Local0 = F000 [0x00]
        CH04 (__METHOD__, 0x00, 0x2F, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_OPERAND_TYPE */
        Store (F000 [0x00], Local0)
        CH04 (__METHOD__, 0x00, 0xFF, Z058, __LINE__, 0x00, 0x00)
        Store (F000 [0x00], Local0)
        CH04 (__METHOD__, 0x00, 0xFF, Z058, __LINE__, 0x00, 0x00)
        Local1 = Local0 = F000 [0x00]
        CH04 (__METHOD__, 0x00, 0xFF, Z058, __LINE__, 0x00, 0x00)
        /* BankField */

        Store (BKF0 [0x00], Local5)
        CH04 (__METHOD__, 0x01, 0x2F, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_OPERAND_TYPE */
        Local0 = BKF0 [0x00]
        CH04 (__METHOD__, 0x00, 0x2F, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_OPERAND_TYPE */
        Store (BKF0 [0x00], Local0)
        CH04 (__METHOD__, 0x00, 0xFF, Z058, __LINE__, 0x00, 0x00)
        Store (BKF0 [0x00], Local0)
        CH04 (__METHOD__, 0x00, 0xFF, Z058, __LINE__, 0x00, 0x00)
        Local1 = Local0 = BKF0 [0x00]
        CH04 (__METHOD__, 0x00, 0xFF, Z058, __LINE__, 0x00, 0x00)
        /* IndexField */

        Store (IF00 [0x00], Local5)
        CH04 (__METHOD__, 0x01, 0x2F, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_OPERAND_TYPE */
        Local0 = IF00 [0x00]
        CH04 (__METHOD__, 0x00, 0x2F, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_OPERAND_TYPE */
        Store (IF00 [0x00], Local0)
        CH04 (__METHOD__, 0x00, 0xFF, Z058, __LINE__, 0x00, 0x00)
        Store (IF00 [0x00], Local0)
        CH04 (__METHOD__, 0x00, 0xFF, Z058, __LINE__, 0x00, 0x00)
        Local1 = Local0 = IF00 [0x00]
        CH04 (__METHOD__, 0x00, 0xFF, Z058, __LINE__, 0x00, 0x00)
    }

    /* Bug 83 */
    /* DerefOf(Field Unit) */
    Method (M15E, 0, Serialized)
    {
        OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
        Field (R000, ByteAcc, NoLock, Preserve)
        {
            F000,   8
        }

        Field (R000, ByteAcc, NoLock, Preserve)
        {
            BNK0,   8,
            F00A,   8,
            F00B,   8
        }

        BankField (R000, BNK0, 0x00, ByteAcc, NoLock, Preserve)
        {
            BKF0,   4
        }

        IndexField (F00A, F00B, ByteAcc, NoLock, Preserve)
        {
            IF00,   1,
            IF01,   1
        }

        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        /* Field */

        Local5 = DerefOf (F000)
        /* Bug 83, Bugzilla 5387. */

        CH04 (__METHOD__, 0x00, 0xFF, Z058, __LINE__, 0x00, 0x00)
        Local0 = DerefOf (F000)
        /* Bug 83, Bugzilla 5387. */

        CH04 (__METHOD__, 0x00, 0xFF, Z058, __LINE__, 0x00, 0x00)
        /* BankField */

        Local5 = DerefOf (BKF0)
        /* Bug 83, Bugzilla 5387. */

        CH04 (__METHOD__, 0x00, 0xFF, Z058, __LINE__, 0x00, 0x00)
        Local0 = DerefOf (BKF0)
        /* Bug 83, Bugzilla 5387. */

        CH04 (__METHOD__, 0x00, 0xFF, Z058, __LINE__, 0x00, 0x00)
        /* IndexField */

        Local5 = DerefOf (IF00)
        /* Bug 83, Bugzilla 5387. */

        CH04 (__METHOD__, 0x00, 0xFF, Z058, __LINE__, 0x00, 0x00)
        Local0 = DerefOf (IF00)
        /* Bug 83, Bugzilla 5387. */

        CH04 (__METHOD__, 0x00, 0xFF, Z058, __LINE__, 0x00, 0x00)
    }

    /* UPDATE exc.m084: Implement this test for all the types of objects */
    /*                  (see for example ref.asl files about objects) and */
    /*                  all the types of operators. */
    Method (M084, 1, Serialized)
    {
        If (Arg0)
        {
            Name (I000, 0x12345678)
            Name (S000, "12345678")
            Name (B000, Buffer (0x01)
            {
                 0x12                                             // .
            })
            Name (P000, Package (0x01)
            {
                0x12345678
            })
        }

        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        /*
         Discuss: now the ObjectType doesn't cause exception!
         Is it correct? Understand and discuss it.
         Store(ObjectType(i000), Local0)
         CH04(ts, 0, 46, z058, __LINE__, 0, 0)	// AE_AML_NO_OPERAND
         Store(ObjectType(s000), Local0)
         CH04(ts, 0, 46, z058, __LINE__, 0, 0)	// AE_AML_NO_OPERAND
         Store(ObjectType(b000), Local0)
         CH04(ts, 0, 46, z058, __LINE__, 0, 0)	// AE_AML_NO_OPERAND
         Store(ObjectType(p000), Local0)
         CH04(ts, 0, 46, z058, __LINE__, 0, 0)	// AE_AML_NO_OPERAND
         */
        Store (P000 [0x00], Local0)
        If (!Arg0)
        {
            CH04 (__METHOD__, 0x00, 0xFF, Z058, __LINE__, 0x00, 0x00)
        }
        Else
        {
            CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        }

        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
    }

    Method (MF9D, 0, NotSerialized)
    {
        Method (M000, 0, NotSerialized)
        {
            Local7 = 0x00
            Divide (0x01, Local7, Local2)
            If ((Local2 != 0x00))
            {
                M002 ()
            }
        }

        Method (M001, 0, NotSerialized)
        {
            Local7 = 0x00
            If (Divide (0x01, Local7, Local2))
            {
                M002 ()
            }
        }

        Method (M002, 0, NotSerialized)
        {
        }

        CH03 ("mf9d", Z058, __LINE__, 0x00, 0x00)
        M000 ()
        CH04 ("mf9d", 0x00, 0xFF, Z058, __LINE__, 0x00, 0x00)
        CH03 ("mf9d", Z058, __LINE__, 0x00, 0x00)
        M001 ()
        CH04 ("mf9d", 0x00, 0xFF, Z058, __LINE__, 0x00, 0x00)
    }

    /* Access out of OpRegion and DataTableRegion */

    Method (M708, 0, Serialized)
    {
        Method (M000, 1, Serialized)
        {
            OperationRegion (RGN0, SystemMemory, 0x00, Arg0)
            OperationRegion (RGN1, SystemIO, 0x0200, Arg0)
            /* UserDefRegionSpace */

            OperationRegion (RGN2, 0x80, 0x0D00, Arg0)
            DataTableRegion (DR00, "SSDT", "", "")
            Field (RGN0, ByteAcc, NoLock, Preserve)
            {
                FU00,   2049
            }

            Field (RGN1, ByteAcc, NoLock, Preserve)
            {
                FU01,   2049
            }

            Field (RGN2, ByteAcc, NoLock, Preserve)
            {
                FU02,   2049
            }

            Field (DR00, AnyAcc, NoLock, Preserve)
            {
                FU03,   497
            }

            /* 0x1F0 == length of SSDT */

            Local0 = 0x04
            Local1 = 0x00
            While (Local0)
            {
                Switch (Local1)
                {
                    Case (0x00)
                    {
                        Local2 = RefOf (FU00)
                    }
                    Case (0x01)
                    {
                        Local2 = RefOf (FU01)
                    }
                    Case (0x02)
                    {
                        Local2 = RefOf (FU02)
                    }
                    Case (0x03)
                    {
                        Local2 = RefOf (FU03)
                    }

                }

                Local3 = RefOf (Local2)
                CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
                /* Write: except DataTableRegion */

                If ((Local1 < 0x03))
                {
                    DerefOf (Local3) = 0x12345678
                    CH04 (__METHOD__, 0x00, 0x35, Z058, __LINE__, 0x00, 0x00)/* AE_AML_REGION_LIMIT */
                }

                /* Read */

                Local4 = DerefOf (Local2)
                /* July 2013
                 *
                 * The Store above should actually cause two errors
                 * 1) AE_AML_REGION_LIMIT
                 * 2) AE_AML_NO_RETURN_VALUE
                 *
                 * Indicate we only care about the first by placing a 1
                 * in the second argument
                 */
                CH04 (__METHOD__, 0x01, 0x35, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_REGION_LIMIT */
                Local0--
                Local1++
            }
        }

        M000 (0x0100)
    }

    /* Try non-copmputational data OpRegion arguments */

    Method (M709, 0, Serialized)
    {
        Name (OFFP, Package (0x01)
        {
            0xFEDCBA987654321F
        })
        Name (LENP, Package (0x01)
        {
            0x0123
        })
        Name (I000, 0x0100)
        /* These are now caught by the compiler - Aug 2015 */
    /* */
    /*	Method(m000,, Serialized) { */
    /*		OperationRegion(OPR0, SystemMemory, offp, 1) */
    /*	} */
    /*	 */
    /*	CH03(ts, z058, 188, __LINE__, 0) */
    /* */
    /*	m000() */
    /* */
    /*	CH04(ts, 0, 47, z058, __LINE__, 0, 0)	// AE_AML_OPERAND_TYPE */
    /* */
    /*	OperationRegion(OPR1, SystemMemory, 1, lenp) */
    /* */
    /*	CH04(ts, 0, 47, z058, __LINE__, 0, 0)	// AE_AML_OPERAND_TYPE */
    }

    /* Try OpRegion arguments when Offset + Length > MaxInteger */

    Method (M70A, 0, Serialized)
    {
        Name (OFF0, 0xFFFFFFFFFFFFFFF0)
        Name (LEN0, 0x11)
        OperationRegion (OPR0, SystemMemory, OFF0, LEN0)
        /*17+1 > 17. */

        Field (OPR0, AnyAcc, NoLock, Preserve)
        {
            Offset (0x11),
            FU00,   8
        }

        /*16+2 > 17. */

        Field (OPR0, WordAcc, NoLock, Preserve)
        {
            Offset (0x10),
            FU01,   8
        }

        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        FU00 = 0x12
        CH04 (__METHOD__, 0x00, 0x35, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_REGION_LIMIT */
        FU01 = 0x12
        CH04 (__METHOD__, 0x00, 0x35, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_REGION_LIMIT */
    }

    /* Attempt to write into DataTableRegion */

    Method (M70B, 0, Serialized)
    {
        DataTableRegion (DR00, "SSDT", "", "")
        Field (DR00, AnyAcc, NoLock, Preserve)
        {
            FU00,   384
        }

        Local0 = FU00 /* \M70B.FU00 */
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        FU00 = 0x00
        CH04 (__METHOD__, 0x00, 0x10, Z058, __LINE__, 0x00, 0x00)   /* AE_SUPPORT */
    }

    /* Check non-String DataTableRegion *String arguments */

    Method (M7F5, 0, Serialized)
    {
        Name (B000, Buffer (0x01)
        {
             0x12                                             // .
        })
        Name (I000, 0x12)
        Name (P000, Package (0x01)
        {
            0x12
        })
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        DataTableRegion (DR00, B000, "", "")
        CH04 (__METHOD__, 0x00, 0x05, Z058, __LINE__, 0x00, 0x00)    /* AE_NOT_FOUND */
        DataTableRegion (DR01, "SSDT", B000, "")
        CH04 (__METHOD__, 0x00, 0x05, Z058, __LINE__, 0x00, 0x00)    /* AE_NOT_FOUND */
        DataTableRegion (DR02, "SSDT", "", B000)
        CH04 (__METHOD__, 0x00, 0x05, Z058, __LINE__, 0x00, 0x00)    /* AE_NOT_FOUND */
        DataTableRegion (DR03, I000, "", "")
        CH04 (__METHOD__, 0x00, 0x05, Z058, __LINE__, 0x00, 0x00)    /* AE_NOT_FOUND */
        DataTableRegion (DR04, "SSDT", I000, "")
        CH04 (__METHOD__, 0x00, 0x05, Z058, __LINE__, 0x00, 0x00)    /* AE_NOT_FOUND */
        DataTableRegion (DR05, "SSDT", "", I000)
        CH04 (__METHOD__, 0x00, 0x05, Z058, __LINE__, 0x00, 0x00)    /* AE_NOT_FOUND */
        /* These are now caught by the compiler - Aug 2015 */
    /* */
    /*	DataTableRegion (DR06, p000, "", i000) */
    /*	CH04(ts, 0, 47, z058, __LINE__, 0, 0)	// AE_AML_OPERAND_TYPE */
    /* */
    /*	DataTableRegion (DR07, "SSDT", p000, "") */
    /*	CH04(ts, 0, 47, z058, __LINE__, 0, 0)	// AE_AML_OPERAND_TYPE */
    /* */
    /*	DataTableRegion (DR08, "SSDT", "", p000) */
    /*	CH04(ts, 0, 47, z058, __LINE__, 0, 0)	// AE_AML_OPERAND_TYPE */
    }

    /* Check SMBus OpRegion restictions */

    Method (M7F6, 0, Serialized)
    {
        OperationRegion (SMBD, SMBus, 0x4200, 0x0100)
        Field (SMBD, BufferAcc, NoLock, Preserve)
        {
            AccessAs (BufferAcc, AttribQuick),
            FLD0,   8
        }

        /* Create improper SMBus data buffer */

        Name (BUFF, Buffer (0x21){})
        CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
        /* Invoke Write Quick transaction */

        FLD0 = BUFF /* \M7F6.BUFF */
        CH04 (__METHOD__, 0x00, 0x36, Z058, __LINE__, 0x00, 0x00)   /* AE_AML_BUFFER_LIMIT */
    }

    /* Name space issues */

    Method (M0BC, 0, Serialized)
    {
        Method (M000, 0, NotSerialized)
        {
            Return (0xABCD0000)
        }

        Method (M001, 0, NotSerialized)
        {
            Local0 = M000 ()
            Method (M000, 0, NotSerialized)
            {
                Return (0xABCD0001)
            }

            Local1 = M000 ()
            If ((Local0 != 0xABCD0000))
            {
                ERR (__METHOD__, Z058, __LINE__, 0x00, 0x00, Local0, 0xABCD0000)
            }

            If ((Local1 != 0xABCD0001))
            {
                ERR (__METHOD__, Z058, __LINE__, 0x00, 0x00, Local1, 0xABCD0001)
            }
        }

        Method (M002, 0, NotSerialized)
        {
            Method (M004, 0, NotSerialized)
            {
                Return (0xABCD0002)
            }

            CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
            M004 ()
            CH04 (__METHOD__, 0x00, 0x05, Z058, __LINE__, 0x00, 0x00) /* AE_NOT_FOUND */
        }

        Method (M003, 0, NotSerialized)
        {
            /* Recursion */

            CH03 (__METHOD__, Z058, __LINE__, 0x00, 0x00)
            M003 ()
            CH04 (__METHOD__, 0x00, 0x54, Z058, __LINE__, 0x00, 0x00) /* AE_AML_METHOD_LIMIT */
            Method (M003, 0, NotSerialized)
            {
                Return (0xABCD0002)
            }
        }

        M001 ()
        M002 ()
        /* m003() */
    }

    /* Run-method */

    Method (EXCP, 0, NotSerialized)
    {
        SRMT ("m140")
        M140 ()
        SRMT ("m141")
        M141 ()
        SRMT ("m142")
        M142 ()
        SRMT ("m143")
        M143 ()
        SRMT ("m144")
        M144 ()
        SRMT ("m145")
        M145 ()
        SRMT ("m085")
        M085 ()
        SRMT ("m086")
        M086 ()
        SRMT ("m148")
        M148 ()
        SRMT ("m14b")
        M14B ()
        SRMT ("m14c")
        M14C ()
        SRMT ("m14d")
        M14D ()
        SRMT ("m14e")
        M14E ()
        SRMT ("m14f")
        M14F ()
        SRMT ("m150")
        M150 (0x00)
        SRMT ("m151")
        M151 ()
        SRMT ("m152")
        M152 ()
        SRMT ("m153")
        M153 ()
        SRMT ("m154")
        M154 ()
        SRMT ("m155")
        M155 ()
        SRMT ("m156")
        M156 ()
        SRMT ("m157")
        M157 ()
        SRMT ("m158")
        M158 ()
        SRMT ("m087")
        M087 ()
        SRMT ("m159")
        M159 ()
        SRMT ("m15a")
        M15A ()
        SRMT ("m15d")
        M15D ()
        SRMT ("m15e")
        M15E ()
        /* The sequence of calls below is important, */
        /* since not initialized names can refer to */
        /* the objects moved improperly into the cash */
        /* between two calls to the same Method: */
        SRMT ("m084-0")
        M084 (0x00)
        SRMT ("m084-1")
        M084 (0x01)
        SRMT ("m084-0-2")
        M084 (0x00)
        SRMT ("m1b3")
        M1B3 ()
        SRMT ("mf9d")
        If (Y200)
        {
            MF9D ()
        }
        Else
        {
            BLCK ()
        }

        SRMT ("m708")
        M708 ()
        SRMT ("m709")
        M709 ()
        SRMT ("m70a")
        M70A ()
        SRMT ("m70b")
        M70B ()
        SRMT ("m7f5")
        If (Y223)
        {
            M7F5 ()
        }
        Else
        {
            BLCK ()
        }

        SRMT ("m7f6")
        M7F6 ()
        SRMT ("m0bc")
        M0BC ()
    }
