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
     * Miscellaneous not systematized tests
     */
    Name (Z054, 0x36)
    /* Looks like Default is at all not implemented */

    Method (M110, 1, Serialized)
    {
        Local0 = 0x00
        Local1 = 0x00
        /* Bug XXX. This Switch code below causes ASL-compiler to fail */
        /* for full.asl file with the diagnostics like this: */
        /* nssearch-0397: *** Error: NsSearchAndEnter: */
        /*                    Bad character in ACPI Name: 5B5F545F */
        /* and fall into recursion: */
        /* Remark   3040 -     Recursive method call ^  (ERR_) */
        /* Note: (0x5B5F545F is equal to "[_T_") */
        Switch (ToInteger (Local1))
        {
            Case (0x05)
            {
                Local0 = 0x05
            }
            Default
            {
                Local0 = 0x01
            }

        }

        If ((Local0 != 0x01))
        {
            ERR (Arg0, Z054, __LINE__, 0x00, 0x00, Local0, 0x00)
        }
    }

    /* Concatenate operator affects the object passed as Source2 parameter */

    Method (M111, 1, NotSerialized)
    {
        Local5 = Concatenate ("qwertyuiop", Arg0)
    }

    Method (M112, 1, NotSerialized)
    {
        Local0 = 0x00
        M111 (Local0)
        If ((Local0 != 0x00))
        {
            ERR (Arg0, Z054, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        Local0 = 0x00
        Local5 = Concatenate ("qwertyuiop", Local0)
        If ((Local0 != 0x00))
        {
            ERR (Arg0, Z054, __LINE__, 0x00, 0x00, Local0, 0x00)
        }
    }

    /* Unexpected value returned by ObjectType for Field Unit objects */
    /* The field passed as explicit reference (RefOf) */
    Method (M113, 1, Serialized)
    {
        OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
        Field (R000, ByteAcc, NoLock, Preserve)
        {
            F000,   32
        }

        Local0 = ObjectType (RefOf (F000))
        If ((Local0 != 0x05))
        {
            ERR (Arg0, Z054, __LINE__, 0x00, 0x00, Local0, 0x00)
        }
    }

    /* The BankField corrupts the contents of OperationRegion */

    Method (M114, 1, Serialized)
    {
        OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
        Field (R000, ByteAcc, NoLock, Preserve)
        {
            BNK0,   8
        }

        BankField (R000, BNK0, 0x00, ByteAcc, NoLock, Preserve)
        {
            Offset (0x10),
            BF00,   8
        }

        BankField (R000, BNK0, 0x01, ByteAcc, NoLock, Preserve)
        {
            Offset (0x11),
            BF01,   8
        }

        /* Deal with 0-th bank layout: */

        BNK0 = 0x00
        If ((BNK0 != 0x00))
        {
            ERR (Arg0, Z054, __LINE__, 0x00, 0x00, BNK0, 0x00)
        }

        BF00 = 0x87
        If ((BNK0 != 0x00))
        {
            ERR (Arg0, Z054, __LINE__, 0x00, 0x00, BNK0, 0x00)
        }

        If ((BF00 != 0x87))
        {
            ERR (Arg0, Z054, __LINE__, 0x00, 0x00, BF00, 0x87)
        }

        /* Deal with 1-th bank layout: */

        BNK0 = 0x01
        If ((BNK0 != 0x01))
        {
            ERR (Arg0, Z054, __LINE__, 0x00, 0x00, BNK0, 0x01)
        }

        BF01 = 0x96
        If (X192)
        {
            If ((BNK0 != 0x01))
            {
                ERR (Arg0, Z054, __LINE__, 0x00, 0x00, BNK0, 0x01)
            }
        }

        If ((BF01 != 0x96))
        {
            ERR (Arg0, Z054, __LINE__, 0x00, 0x00, BF01, 0x96)
        }
    }

    /* ToBuffer caused destroying of source buffer passed by Data parameter */

    Method (M115, 1, NotSerialized)
    {
        Local0 = Buffer (0x04)
            {
                 0x0A, 0x0B, 0x0C, 0x0D                           // ....
            }
        Local1 = ObjectType (Local0)
        If ((Local1 != C00B))
        {
            ERR (Arg0, Z054, __LINE__, 0x00, 0x00, Local1, 0x00)
        }

        ToBuffer (Local0, Local2)
        Local3 = 0xAA
        Local3 = ObjectType (Local0)
        If ((Local3 != C00B))
        {
            ERR (Arg0, Z054, __LINE__, 0x00, 0x00, Local3, 0x00)
        }
    }

    /* ObjectType() operator should be allowed to deal with the */
    /* uninitialized objects. */
    /* Uncomment this when the problem will be fixed and compile */
    /* will not fail in this case like it do now: "Method local */
    /* variable is not initialized (Local0)". */
    Method (M116, 1, NotSerialized)
    {
        Local1 = ObjectType (Local0)
    }

    /* Now, this cause exception but should not */

    Method (M117, 2, Serialized)
    {
        If (Arg1)
        {
            Local0 = 0x00
        }

        CH03 (__METHOD__, Z054, __LINE__, 0x00, 0x00)
        Local1 = ObjectType (Local0)
        If ((Local1 != 0x00))
        {
            ERR (Arg0, Z054, __LINE__, 0x00, 0x00, Local1, 0x00)
        }

        CH03 (__METHOD__, Z054, __LINE__, 0x00, 0x00)
    }

    Method (M118, 1, NotSerialized)
    {
        M117 (Arg0, 0x00)
    }

    /*
     * Bug 12, Bugzilla 5360.
     * DerefOf. If the Source evaluates to a string, the string is evaluated
     * as an ASL name (relative to the current scope) and the contents of that
     * object are returned.
     */
    Method (M119, 1, Serialized)
    {
        Name (B000, Buffer (0x08)
        {
             0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08   // ........
        })
        Local0 = "b000"
        Debug = "================ 0:"
        Local1 = DerefOf (Local0)
        Debug = "================ 1:"
        Local2 = ObjectType (Local1)
        If ((Local2 != 0x03))
        {
            ERR (Arg0, Z054, __LINE__, 0x00, 0x00, Local2, 0x00)
        }

        Debug = "================ 2:"
        Debug = Local1
        Debug = Local2
        CH03 (Arg0, Z054, __LINE__, 0x00, 0x00)
        Return (0x00)
    }

    /*
     // Currently, incorrect test
     // The size of Strings in Package is determined incorrectly
     Method(m11a, 1)
     {
     Name(p000, Package() {
     "012",
     "0123456789abcdef",
     Buffer() {17,28,69,11,22,34,35,56,67,11},
     "012345",
     })
     Store(DeRefOf(Index(p000, 1)), Local0)
     Store(0, Index(Local0, 5))
     Store(0, Index(p000, 1))
     Store(DeRefOf(Index(p000, 1)), Local0)
     //	Store(0, Index(Local0, 5))
     Store("=================:", Debug)
     Store(Local0, Debug)
     // 0
     Store(DeRefOf(Index(p000, 0)), Local2)
     Store(SizeOf(Local2), Local3)
     Store(Local3, Debug)
     if (LNotEqual(Local3, 3)) {
     err(arg0, z054, __LINE__, 0, 0, Local3, 3)
     }
     // 1
     Store(DeRefOf(Index(p000, 1)), Local2)
     Store(SizeOf(Local2), Local3)
     Store(Local3, Debug)
     if (LNotEqual(Local3, 9)) {
     err(arg0, z054, __LINE__, 0, 0, Local3, 9)
     }
     // 2
     Store(DeRefOf(Index(p000, 2)), Local2)
     Store(SizeOf(Local2), Local3)
     Store(Local3, Debug)
     if (LNotEqual(Local3, 6)) {
     err(arg0, z054, __LINE__, 0, 0, Local3, 6)
     }
     Store(SizeOf(p000), Local0)
     Store(Local0, Debug)
     if (LNotEqual(Local0, 3)) {
     err(arg0, z054, __LINE__, 0, 0, Local0, 3)
     }
     }
     */
    /*
     // ATTENTION: such type tests have to be added and extended
     Method(m11b, 1)
     {
     Name(p000, Package() {
     0x12345678, 0x90abcdef,
     })
     Name(b000, Buffer() {0x78,0x56,0x34,0x12, 0xef,0xcd,0xab,0x90})
     Store(DeRefOf(Index(p000, 0)), Local7)
     if (LEqual(b000, Local7)) {
     err(arg0, z054, __LINE__, 0, 0, b000, Local7)
     }
     if (LEqual(Local7, b000)) {
     err(arg0, z054, __LINE__, 0, 0, Local7, b000)
     }
     return (0)
     }
     */
    /* Bug 54: All the ASL Operators which deal with at least two Buffer type */
    /* objects cause unexpected exceptions in cases when both Buffer type objects */
    /* are passed immediately */
    Method (M11C, 1, Serialized)
    {
        CH03 (__METHOD__, Z054, __LINE__, 0x00, 0x00)
        Store ((Buffer (0x01)
                {
                     0x79                                             // y
                } + Buffer (0x01)
                {
                     0x79                                             // y
                }), Local5)
        CH03 (__METHOD__, Z054, __LINE__, 0x00, 0x00)
    }

    /* Bug 57: The empty Return operator (without specifying the returning value) */
    /* is processed incorrectly */
    Method (M11D, 1, NotSerialized)
    {
        Method (M11E, 2, NotSerialized)
        {
            If (Arg1)
            {
                Return (0x1234)
                        /* ASL-compiler report Warning in this case */
            /* Store("ERROR 0: m121, after Return !!!", Debug) */
            }

            ERR (Arg0, Z054, __LINE__, 0x00, 0x00, 0x00, 0x00)
            Return (0x5678)
        }

        Method (M11F, 2, NotSerialized)
        {
            If (Arg1)
            {
                Return (                /* ASL-compiler DOESN'T report Warning in this case!!! */
                /* And the Store operator below is actually processed!!! */
Zero)
                ERR (Arg0, Z054, __LINE__, 0x00, 0x00, 0x00, 0x00)
            }

            ERR (Arg0, Z054, __LINE__, 0x00, 0x00, 0x00, 0x00)
            Return (Zero)
        }

        Local7 = M11E (Arg0, 0x01)
        M11F (Arg0, 0x01)
        Return (0x00)
    }

    /*
     * Obsolete:
     * Bug 59: The String to Buffer Rule from the Table 17-8 "Object Conversion
     * Rules" says "If the string is shorter than the buffer, the buffer size is
     * reduced".
     * Updated specs 12.03.05:
     * "If the string is shorter than the buffer,
     * the remaining buffer bytes are set to zero".
     */
    Method (M11E, 1, Serialized)
    {
        Name (STR0, "\x01\x02")
        Name (BUF0, Buffer (0x04)
        {
             0x03, 0x04, 0x05, 0x06                           // ....
        })
        BUF0 = STR0 /* \M11E.STR0 */
        /*
         * Obsolete:
         *
         * if (LNotEqual(Sizeof(buf0), 3)) {
         *	// Error: length of the buffer not reduced to the stored string
         *	err(arg0, z054, __LINE__, 0, 0, 0, 0)
         * }
         *
         * New:
         */
        If ((BUF0 != Buffer (0x04)
                    {
                         0x01, 0x02, 0x00, 0x00                           // ....
                    }))
        {
            ERR (Arg0, Z054, __LINE__, 0x00, 0x00, BUF0, Buffer (0x04)
                {
                     0x01, 0x02, 0x00, 0x00                           // ....
                })
        }

        Return (0x00)
    }

    /* Bug 65: The Buffer Field type objects should be passed */
    /* to Methods without any conversion, but instead */
    /* they are converted to Buffers or Integers depending */
    /* on the size of the Buffer Field object and the */
    /* run mode (32-bit or 64/bit mode). */
    /* */
    /* CANCELED: now it should perform opposite assertion because */
    /* this bug was canceled. */
    Method (M11F, 1, Serialized)
    {
        Name (B000, Buffer (0xC8){})
        CreateField (B000, 0x00, 0x1F, BF00)
        CreateField (B000, 0x1F, 0x20, BF01)
        CreateField (B000, 0x3F, 0x21, BF02)
        CreateField (B000, 0x60, 0x3F, BF03)
        CreateField (B000, 0x9F, 0x40, BF04)
        CreateField (B000, 0xDF, 0x41, BF05)
        Method (M000, 4, NotSerialized)
        {
            Local0 = ObjectType (Arg1)
            If ((Local0 != Arg2))
            {
                ERR (Arg0, Z054, __LINE__, 0x00, 0x00, Local0, Arg2)
            }

            Local0 = SizeOf (Arg1)
            If ((Local0 != Arg3))
            {
                ERR (Arg0, Z054, __LINE__, 0x00, 0x00, Local0, Arg3)
            }
        }

        Method (M001, 1, NotSerialized)
        {
            Local0 = ObjectType (BF00)
            If ((Local0 != 0x0E))
            {
                ERR (Arg0, Z054, __LINE__, 0x00, 0x00, Local0, 0x0E)
            }

            Local0 = ObjectType (BF01)
            If ((Local0 != 0x0E))
            {
                ERR (Arg0, Z054, __LINE__, 0x00, 0x00, Local0, 0x0E)
            }

            Local0 = ObjectType (BF02)
            If ((Local0 != 0x0E))
            {
                ERR (Arg0, Z054, __LINE__, 0x00, 0x00, Local0, 0x0E)
            }

            Local0 = ObjectType (BF03)
            If ((Local0 != 0x0E))
            {
                ERR (Arg0, Z054, __LINE__, 0x00, 0x00, Local0, 0x0E)
            }

            Local0 = ObjectType (BF04)
            If ((Local0 != 0x0E))
            {
                ERR (Arg0, Z054, __LINE__, 0x00, 0x00, Local0, 0x0E)
            }

            Local0 = ObjectType (BF05)
            If ((Local0 != 0x0E))
            {
                ERR (Arg0, Z054, __LINE__, 0x00, 0x00, Local0, 0x0E)
            }

            M000 (Arg0, BF00, 0x03, 0x04)
            M000 (Arg0, BF01, 0x03, 0x04)
            M000 (Arg0, BF02, 0x03, 0x05)
            M000 (Arg0, BF03, 0x03, 0x08)
            M000 (Arg0, BF04, 0x03, 0x08)
            M000 (Arg0, BF05, 0x03, 0x09)
        }

        M001 (Arg0)
    }

    /* Bug 66: The Field Unit type objects should be passed */
    /* to Methods without any conversion, but instead */
    /* they are converted to Buffers or Integers depending */
    /* on the size of the Buffer Field object and the */
    /* run mode (32-bit or 64/bit mode). */
    /* */
    /* CANCELED: now it should perform opposite assertion because */
    /* this bug was canceled. */
    Method (M120, 1, Serialized)
    {
        OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
        Field (R000, ByteAcc, NoLock, Preserve)
        {
            F000,   31,
            F001,   32,
            F002,   33,
            F003,   63,
            F004,   64,
            F005,   65
        }

        Method (M000, 4, NotSerialized)
        {
            Local0 = ObjectType (Arg1)
            If ((Local0 != Arg2))
            {
                ERR (Arg0, Z054, __LINE__, 0x00, 0x00, Local0, Arg2)
            }

            Local0 = SizeOf (Arg1)
            If ((Local0 != Arg3))
            {
                ERR (Arg0, Z054, __LINE__, 0x00, 0x00, Local0, Arg3)
            }
        }

        Method (M001, 1, NotSerialized)
        {
            Local0 = ObjectType (F000)
            If ((Local0 != 0x05))
            {
                ERR (Arg0, Z054, __LINE__, 0x00, 0x00, Local0, 0x05)
            }

            Local0 = ObjectType (F001)
            If ((Local0 != 0x05))
            {
                ERR (Arg0, Z054, __LINE__, 0x00, 0x00, Local0, 0x05)
            }

            Local0 = ObjectType (F002)
            If ((Local0 != 0x05))
            {
                ERR (Arg0, Z054, __LINE__, 0x00, 0x00, Local0, 0x05)
            }

            Local0 = ObjectType (F003)
            If ((Local0 != 0x05))
            {
                ERR (Arg0, Z054, __LINE__, 0x00, 0x00, Local0, 0x05)
            }

            Local0 = ObjectType (F004)
            If ((Local0 != 0x05))
            {
                ERR (Arg0, Z054, __LINE__, 0x00, 0x00, Local0, 0x05)
            }

            Local0 = ObjectType (F005)
            If ((Local0 != 0x05))
            {
                ERR (Arg0, Z054, __LINE__, 0x00, 0x00, Local0, 0x05)
            }

            If (F64)
            {
                M000 (Arg0, F000, 0x01, 0x08)
                M000 (Arg0, F001, 0x01, 0x08)
                M000 (Arg0, F002, 0x01, 0x08)
                M000 (Arg0, F003, 0x01, 0x08)
                M000 (Arg0, F004, 0x01, 0x08)
                M000 (Arg0, F005, 0x03, 0x09)
            }
            Else
            {
                M000 (Arg0, F000, 0x01, 0x04)
                M000 (Arg0, F001, 0x01, 0x04)
                M000 (Arg0, F002, 0x03, 0x05)
                M000 (Arg0, F003, 0x03, 0x08)
                M000 (Arg0, F004, 0x03, 0x08)
                M000 (Arg0, F005, 0x03, 0x09)
            }
        }

        M001 (Arg0)
    }

    /* Bug 67: The Buffer Field type objects should be RETURNED */
    /* by Methods without any conversion, but instead */
    /* they are converted to Buffers or Integers depending */
    /* on the size of the Buffer Field object and the */
    /* run mode (32-bit or 64/bit mode). */
    /* */
    /* CANCELED: now it should perform opposite assertion because */
    /* this bug was canceled. */
    Method (M121, 1, Serialized)
    {
        Name (B000, Buffer (0xC8){})
        CreateField (B000, 0x00, 0x1F, BF00)
        CreateField (B000, 0x1F, 0x20, BF01)
        CreateField (B000, 0x3F, 0x21, BF02)
        CreateField (B000, 0x60, 0x3F, BF03)
        CreateField (B000, 0x9F, 0x40, BF04)
        CreateField (B000, 0xDF, 0x41, BF05)
        Method (M000, 1, NotSerialized)
        {
            If ((Arg0 == 0x00))
            {
                Return (BF00) /* \M121.BF00 */
            }
            ElseIf ((Arg0 == 0x01))
            {
                Return (BF01) /* \M121.BF01 */
            }
            ElseIf ((Arg0 == 0x02))
            {
                Return (BF02) /* \M121.BF02 */
            }
            ElseIf ((Arg0 == 0x03))
            {
                Return (BF03) /* \M121.BF03 */
            }
            ElseIf ((Arg0 == 0x04))
            {
                Return (BF04) /* \M121.BF04 */
            }
            ElseIf ((Arg0 == 0x05))
            {
                Return (BF05) /* \M121.BF05 */
            }

            Return ("qw")
        }

        Method (M001, 4, NotSerialized)
        {
            Local1 = M000 (Arg1)
            Local0 = ObjectType (Local1)
            If ((Local0 != Arg2))
            {
                ERR (Arg0, Z054, __LINE__, 0x00, 0x00, Local0, Arg2)
            }

            Local0 = SizeOf (Local1)
            If ((Local0 != Arg3))
            {
                ERR (Arg0, Z054, __LINE__, 0x00, 0x00, Local0, Arg3)
            }
        }

        Method (M002, 1, NotSerialized)
        {
            M001 (Arg0, 0x00, 0x03, 0x04)
            M001 (Arg0, 0x01, 0x03, 0x04)
            M001 (Arg0, 0x02, 0x03, 0x05)
            M001 (Arg0, 0x03, 0x03, 0x08)
            M001 (Arg0, 0x04, 0x03, 0x08)
            M001 (Arg0, 0x05, 0x03, 0x09)
        }

        M002 (Arg0)
    }

    /* Bug 68: The Field Unit type objects should be RETURNED */
    /* by Methods without any conversion, but instead */
    /* they are converted to Buffers or Integers depending */
    /* on the size of the Buffer Field object and the */
    /* run mode (32-bit or 64/bit mode). */
    /* */
    /* CANCELED: now it should perform opposite assertion because */
    /* this bug was canceled. */
    Method (M122, 1, Serialized)
    {
        OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
        Field (R000, ByteAcc, NoLock, Preserve)
        {
            F000,   31,
            F001,   32,
            F002,   33,
            F003,   63,
            F004,   64,
            F005,   65
        }

        Method (M000, 1, NotSerialized)
        {
            If ((Arg0 == 0x00))
            {
                Return (F000) /* \M122.F000 */
            }
            ElseIf ((Arg0 == 0x01))
            {
                Return (F001) /* \M122.F001 */
            }
            ElseIf ((Arg0 == 0x02))
            {
                Return (F002) /* \M122.F002 */
            }
            ElseIf ((Arg0 == 0x03))
            {
                Return (F003) /* \M122.F003 */
            }
            ElseIf ((Arg0 == 0x04))
            {
                Return (F004) /* \M122.F004 */
            }
            ElseIf ((Arg0 == 0x05))
            {
                Return (F005) /* \M122.F005 */
            }

            Return ("qw")
        }

        Method (M001, 4, NotSerialized)
        {
            Local1 = M000 (Arg1)
            Local0 = ObjectType (Local1)
            If ((Local0 != Arg2))
            {
                ERR (Arg0, Z054, __LINE__, 0x00, 0x00, Local0, Arg2)
            }

            Local0 = SizeOf (Local1)
            If ((Local0 != Arg3))
            {
                ERR (Arg0, Z054, __LINE__, 0x00, 0x00, Local0, Arg3)
            }
        }

        Method (M002, 1, NotSerialized)
        {
            If (F64)
            {
                M001 (Arg0, 0x00, 0x01, 0x08)
                M001 (Arg0, 0x01, 0x01, 0x08)
                M001 (Arg0, 0x02, 0x01, 0x08)
                M001 (Arg0, 0x03, 0x01, 0x08)
                M001 (Arg0, 0x04, 0x01, 0x08)
                M001 (Arg0, 0x05, 0x03, 0x09)
            }
            Else
            {
                M001 (Arg0, 0x00, 0x01, 0x04)
                M001 (Arg0, 0x01, 0x01, 0x04)
                M001 (Arg0, 0x02, 0x03, 0x05)
                M001 (Arg0, 0x03, 0x03, 0x08)
                M001 (Arg0, 0x04, 0x03, 0x08)
                M001 (Arg0, 0x05, 0x03, 0x09)
            }
        }

        M002 (Arg0)
    }

    /* Bug 30. This test may be removed there after */
    /* the Field relative tests will be implemented. */
    /* Caused crash. */
    Method (M123, 1, NotSerialized)
    {
        Method (M000, 0, Serialized)
        {
            /* Field Unit */

            OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
            Field (R000, ByteAcc, NoLock, Preserve)
            {
                F000,   8,
                F001,   16,
                F002,   32,
                F003,   33,
                F004,   1,
                F005,   64
            }

            Debug = "------------ Fields:"
            Debug = F000 /* \M123.M000.F000 */
            Debug = F001 /* \M123.M000.F001 */
            Debug = F002 /* \M123.M000.F002 */
            Debug = F003 /* \M123.M000.F003 */
            Debug = F004 /* \M123.M000.F004 */
            Debug = F005 /* \M123.M000.F005 */
            Debug = "------------."
            Return (0x00)
        }

        Method (M001, 0, Serialized)
        {
            /* Field Unit */

            OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
            Field (R000, ByteAcc, NoLock, Preserve)
            {
                F000,   8,
                F001,   16,
                F002,   32,
                F003,   33,
                F004,   7,
                F005,   64
            }

            Debug = "------------ Fields:"
            Debug = F000 /* \M123.M001.F000 */
            Debug = F001 /* \M123.M001.F001 */
            Debug = F002 /* \M123.M001.F002 */
            Debug = F003 /* \M123.M001.F003 */
            Debug = F004 /* \M123.M001.F004 */
            Debug = F005 /* \M123.M001.F005 */
            Debug = "------------."
            Return (0x00)
        }

        M000 ()
        M001 ()
        Return (0x00)
    }

    /* Bug 81. */

    Method (M124, 1, NotSerialized)
    {
        Method (M000, 0, NotSerialized)
        {
            Return (0x12345678)
        }

        Method (M001, 1, NotSerialized)
        {
            Return (0x12345678)
        }

        CH03 (Arg0, Z054, __LINE__, 0x00, 0x00)
        Local0 = ObjectType (M000)
        If ((Local0 != C010))
        {
            ERR (Arg0, Z054, __LINE__, 0x00, 0x00, Local0, C010)
        }
        /* Bug 81. */
    /*
     * Removed, invalid test.
     * Compiler disallow method invocation as an operand to ObjectType.
     */
    /* Nov. 2012: Method invocation as arg to ObjectType is now illegal */
    /*Store(ObjectType(m000()), Local0) */
    /*if (LNotEqual(Local0, c009)) { */
    /*	err(arg0, z054, __LINE__, 0, 0, Local0, c009) */
    /*} */
    /* */
    /*Store(ObjectType(m001(123)), Local1) */
    /*if (LNotEqual(Local1, c009)) { */
    /*	err(arg0, z054, __LINE__, 0, 0, Local1, c009) */
    /*} */
    /* */
    /*CH03(arg0, z054, 0x106, __LINE__, 0) */
    }

    /*
     * Bug 117. Modification of the duplicated String
     * modifies the initial String Object also.
     *
     * This test should be a part of another complex test.
     *
     * New objects creation and safety of the source
     * objects referred as parameters to operators.
     */
    Method (M125, 1, NotSerialized)
    {
        Method (M001, 1, Serialized)
        {
            Name (S000, "String")
            Local0 = S000 /* \M125.M001.S000 */
            Local0 [0x03] = 0x61
            If ((Local0 != "Strang"))
            {
                ERR (Arg0, Z054, __LINE__, 0x00, 0x00, Local0, "Strang")
            }

            If ((S000 != "String"))
            {
                ERR (Arg0, Z054, __LINE__, 0x00, 0x00, S000, "String")
            }
        }

        Method (M002, 1, Serialized)
        {
            Name (B000, Buffer (0x06)
            {
                 0xA0, 0xA1, 0xA2, 0xA3, 0xA4, 0xA5               // ......
            })
            Local0 = B000 /* \M125.M002.B000 */
            Local0 [0x03] = 0x61
            If ((Local0 != Buffer (0x06)
                        {
                             0xA0, 0xA1, 0xA2, 0x61, 0xA4, 0xA5               // ...a..
                        }))
            {
                ERR (Arg0, Z054, __LINE__, 0x00, 0x00, Local0, Buffer (0x06)
                    {
                         0xA0, 0xA1, 0xA2, 0x61, 0xA4, 0xA5               // ...a..
                    })
            }

            If ((B000 != Buffer (0x06)
                        {
                             0xA0, 0xA1, 0xA2, 0xA3, 0xA4, 0xA5               // ......
                        }))
            {
                ERR (Arg0, Z054, __LINE__, 0x00, 0x00, B000, Buffer (0x06)
                    {
                         0xA0, 0xA1, 0xA2, 0xA3, 0xA4, 0xA5               // ......
                    })
            }
        }

        Method (M003, 1, Serialized)
        {
            Name (P000, Package (0x06)
            {
                0xFFF0,
                0xFFF1,
                0xFFF2,
                0xFFF3,
                0xFFF4,
                0xFFF5
            })
            Local0 = P000 /* \M125.M003.P000 */
            Local0 [0x03] = 0x61
            If ((DerefOf (Local0 [0x00]) != 0xFFF0))
            {
                ERR (Arg0, Z054, __LINE__, 0x00, 0x00, DerefOf (Local0 [0x00]), 0xFFF0)
            }

            If ((DerefOf (Local0 [0x01]) != 0xFFF1))
            {
                ERR (Arg0, Z054, __LINE__, 0x00, 0x00, DerefOf (Local0 [0x01]), 0xFFF1)
            }

            If ((DerefOf (Local0 [0x02]) != 0xFFF2))
            {
                ERR (Arg0, Z054, __LINE__, 0x00, 0x00, DerefOf (Local0 [0x02]), 0xFFF2)
            }

            If ((DerefOf (Local0 [0x03]) != 0x61))
            {
                ERR (Arg0, Z054, __LINE__, 0x00, 0x00, DerefOf (Local0 [0x03]), 0x61)
            }

            If ((DerefOf (Local0 [0x04]) != 0xFFF4))
            {
                ERR (Arg0, Z054, __LINE__, 0x00, 0x00, DerefOf (Local0 [0x04]), 0xFFF4)
            }

            If ((DerefOf (Local0 [0x05]) != 0xFFF5))
            {
                ERR (Arg0, Z054, __LINE__, 0x00, 0x00, DerefOf (Local0 [0x05]), 0xFFF5)
            }

            If ((DerefOf (P000 [0x00]) != 0xFFF0))
            {
                ERR (Arg0, Z054, __LINE__, 0x00, 0x00, DerefOf (P000 [0x00]), 0xFFF0)
            }

            If ((DerefOf (P000 [0x01]) != 0xFFF1))
            {
                ERR (Arg0, Z054, __LINE__, 0x00, 0x00, DerefOf (P000 [0x01]), 0xFFF1)
            }

            If ((DerefOf (P000 [0x02]) != 0xFFF2))
            {
                ERR (Arg0, Z054, __LINE__, 0x00, 0x00, DerefOf (P000 [0x02]), 0xFFF2)
            }

            If ((DerefOf (P000 [0x03]) != 0xFFF3))
            {
                ERR (Arg0, Z054, __LINE__, 0x00, 0x00, DerefOf (P000 [0x03]), 0xFFF3)
            }

            If ((DerefOf (P000 [0x04]) != 0xFFF4))
            {
                ERR (Arg0, Z054, __LINE__, 0x00, 0x00, DerefOf (P000 [0x04]), 0xFFF4)
            }

            If ((DerefOf (P000 [0x05]) != 0xFFF5))
            {
                ERR (Arg0, Z054, __LINE__, 0x00, 0x00, DerefOf (P000 [0x05]), 0xFFF5)
            }
        }

        M001 (Arg0)
        M002 (Arg0)
        M003 (Arg0)
    }

    /* No exception should arisen. */

    Method (MF74, 0, Serialized)
    {
        Local0 = 0x00
        Switch (ToInteger (Local0))
        {
            Case (0x65)
            {
                Device (D000)
                {
                }

                Method (M002, 0, NotSerialized)
                {
                }
            }

        }
    }

    Method (MF75, 1, NotSerialized)
    {
        Method (MM00, 0, Serialized)
        {
            Local0 = 0x00
            Switch (ToInteger (Local0))
            {
                Case (0x65)
                {
                    Method (M000, 0, NotSerialized)
                    {
                    }

                    Method (M001, 0, NotSerialized)
                    {
                    }
                }

            }
        }

        Method (MM01, 0, Serialized)
        {
            Local0 = 0x00
            Switch (ToInteger (Local0))
            {
                Case (0x65)
                {
                    Method (M002, 0, NotSerialized)
                    {
                    }

                    Device (DV00)
                    {
                    }
                }

            }
        }

        Method (MM02, 0, Serialized)
        {
            Local0 = 0x00
            Switch (ToInteger (Local0))
            {
                Case (0x65)
                {
                    Device (DV01)
                    {
                    }

                    Method (M003, 0, NotSerialized)
                    {
                    }
                }

            }
        }

        Method (MM03, 0, Serialized)
        {
            Local0 = 0x00
            Switch (ToInteger (Local0))
            {
                Case (0x65)
                {
                    Device (DV02)
                    {
                    }

                    Device (DV03)
                    {
                    }
                }

            }
        }

        CH03 (Arg0, Z054, __LINE__, 0x00, 0x00)
        MF74 ()
        CH03 (Arg0, Z054, __LINE__, 0x00, 0x00)
        CH03 (Arg0, Z054, __LINE__, 0x00, 0x00)
        MM00 ()
        CH03 (Arg0, Z054, __LINE__, 0x00, 0x00)
        CH03 (Arg0, Z054, __LINE__, 0x00, 0x00)
        MM01 ()
        CH03 (Arg0, Z054, __LINE__, 0x00, 0x00)
        CH03 (Arg0, Z054, __LINE__, 0x00, 0x00)
        MM02 ()
        CH03 (Arg0, Z054, __LINE__, 0x00, 0x00)
        CH03 (Arg0, Z054, __LINE__, 0x00, 0x00)
        MM03 ()
        CH03 (Arg0, Z054, __LINE__, 0x00, 0x00)
    }

    /*
     * Bug 153, Bugzilla 5314.
     * The corresponding bug has been fixed.
     * This is an invalid test, should be removed from test suite.
     * Method mf77 will fail on ABBU unexpectedly even without Method mf76.
     *
     * Method(mf76, 1)
     * {
     *	if (LNotEqual(arg0, "Strang")) {
     *		err(arg0, z054, __LINE__, 0, 0, arg0, "Strang")
     *	}
     * }
     *
     * Method(mf77, 1)
     * {
     *	Name(s000, "String")
     *	Name(p000, Package(){0})
     *
     *	Store(s000, p000)
     *
     *	Store(s000, Debug)
     *	Store(p000, Debug)
     *
     *	Store (0x61, Index(p000, 3))
     *
     *	mf76(p000)
     *	if (LNotEqual(s000, "String")) {
     *		err(arg0, z054, __LINE__, 0, 0, s000, "String")
     *	}
     * }
     */
    /* Bug 196 */
    Method (MF86, 1, NotSerialized)
    {
        CH03 ("mf86", Z054, __LINE__, 0x00, 0x00)
        Local1 = "0x0x12345678"
        ToInteger (Local1, Local0)
        If ((Local0 != 0x00))
        {
            ERR (Arg0, Z054, __LINE__, 0x00, 0x00, Local0, 0x00)
        }

        CH04 ("mf86", 0x00, 0xFF, Z054, __LINE__, 0x00, 0x00)
    }

    Method (MF87, 1, NotSerialized)
    {
        CH03 ("mf87", Z054, __LINE__, 0x00, 0x00)
        Local0 = ("0x0xabcdef" + 0x00010234)
        If ((Local0 != 0x00010234))
        {
            ERR (Arg0, Z054, __LINE__, 0x00, 0x00, Local0, 0x00010234)
        }

        CH03 ("mf87", Z054, __LINE__, 0x00, 0x00)
        Local0 = (0x00010234 + "0x0xabcdef")
        If ((Local0 != 0x00010234))
        {
            ERR (Arg0, Z054, __LINE__, 0x00, 0x00, Local0, 0x00010234)
        }

        CH03 ("mf87", Z054, __LINE__, 0x00, 0x00)
    }

    Method (M15B, 0, Serialized)
    {
        /* **************** Definitions **************** */

        Method (MM00, 0, NotSerialized)
        {
            Return (0xABCD0000)
        }

        Name (P000, Package (0x03)
        {
            0xABCD0001,
            MM00,
            0xABCD0002
        })
        /* **************** Run checkings **************** */
        /* Store */
        Method (M000, 0, NotSerialized)
        {
            Local0 = MM00 ()
            If ((Local0 != 0xABCD0000))
            {
                ERR (__METHOD__, Z054, __LINE__, 0x00, 0x00, Local0, 0xABCD0000)
            }
        }

        Method (M001, 0, NotSerialized)
        {
            CH03 (__METHOD__, Z054, __LINE__, 0x00, 0x00)
            Local0 = DerefOf (RefOf (MM00))
            If (SLCK)
            {
                CH03 (__METHOD__, Z054, __LINE__, 0x00, 0x00)
                Local1 = ObjectType (Local0)
                If ((Local1 != C010))
                {
                    ERR (__METHOD__, Z054, __LINE__, 0x00, 0x00, Local1, C010)
                }
            }
            Else
            {
                CH04 (__METHOD__, 0x00, 0x2F, Z054, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            }
        }

        Method (M002, 0, NotSerialized)
        {
            CH03 (__METHOD__, Z054, __LINE__, 0x00, 0x00)
            Local0 = DerefOf (P000 [0x01])
            If (SLCK)
            {
                CH03 (__METHOD__, Z054, __LINE__, 0x00, 0x00)
                Local1 = ObjectType (Local0)
                If ((Local1 != C010))
                {
                    ERR (__METHOD__, Z054, __LINE__, 0x00, 0x00, Local1, C010)
                }
            }
            Else
            {
                CH04 (__METHOD__, 0x00, 0x2F, Z054, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            }
        }

        Method (M003, 0, NotSerialized)
        {
                /* 10/2016: Compiler now catches illegal DerefOf(StringConstant) */
        /*		CH03(ts, z054, 0x009, __LINE__, 0) */
        /*		Store(DerefOf("mm00"), Local0) */
        /*		if (SLCK) { */
        /*			CH03(ts, z054, 0x00a, __LINE__, 0) */
        /*			Store(ObjectType(Local0), Local1) */
        /*			if (LNotEqual(Local1, c010)) { */
        /*				err(ts, z054, __LINE__, 0, 0, Local1, c010) */
        /*			} */
        /*		} else { */
        /*			CH04(ts, 0, 47, z054, __LINE__, 0, 0) // AE_AML_OPERAND_TYPE */
        /*		} */
        }

        /* CopyObject */

        Method (M004, 0, NotSerialized)
        {
            CopyObject (MM00 (), Local0)
            If ((Local0 != 0xABCD0000))
            {
                ERR (__METHOD__, Z054, __LINE__, 0x00, 0x00, Local0, 0xABCD0000)
            }
        }

        Method (M005, 0, NotSerialized)
        {
            CH03 (__METHOD__, Z054, __LINE__, 0x00, 0x00)
            CopyObject (DerefOf (RefOf (MM00)), Local0)
            CH03 (__METHOD__, Z054, __LINE__, 0x00, 0x00)
            Local1 = ObjectType (Local0)
            If ((Local1 != C010))
            {
                ERR (__METHOD__, Z054, __LINE__, 0x00, 0x00, Local1, C010)
            }
        }

        Method (M006, 0, NotSerialized)
        {
            CH03 (__METHOD__, Z054, __LINE__, 0x00, 0x00)
            CopyObject (DerefOf (P000 [0x01]), Local0)
            CH03 (__METHOD__, Z054, __LINE__, 0x00, 0x00)
            Local1 = ObjectType (Local0)
            If ((Local1 != C010))
            {
                ERR (__METHOD__, Z054, __LINE__, 0x00, 0x00, Local1, C010)
            }
        }

        Method (M007, 0, NotSerialized)
        {
                /* 10/2016: Compiler now catches illegal DerefOf(StringConstant) */
        /*		CH03(ts, z054, 0x014, __LINE__, 0) */
        /*		CopyObject(DerefOf("mm00"), Local0) */
        /*		CH03(ts, z054, 0x015, __LINE__, 0) */
        /* */
        /*		Store(ObjectType(Local0), Local1) */
        /*		if (LNotEqual(Local1, c010)) { */
        /*			err(ts, z054, __LINE__, 0, 0, Local1, c010) */
        /*		} */
        }

        /* Add */

        Method (M008, 0, NotSerialized)
        {
            Local0 = (MM00 () + 0x01)
            If ((Local0 != 0xABCD0001))
            {
                ERR (__METHOD__, Z054, __LINE__, 0x00, 0x00, Local0, 0xABCD0001)
            }
        }

        Method (M009, 0, NotSerialized)
        {
            CH03 (__METHOD__, Z054, __LINE__, 0x00, 0x00)
            Local0 = (DerefOf (RefOf (MM00)) + 0x02)
            CH04 (__METHOD__, 0x00, 0x2F, Z054, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
        }

        Method (M00A, 0, NotSerialized)
        {
            CH03 (__METHOD__, Z054, __LINE__, 0x00, 0x00)
            Local0 = (DerefOf (P000 [0x01]) + 0x03)
            CH04 (__METHOD__, 0x00, 0x2F, Z054, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
        }

        Method (M00B, 0, NotSerialized)
        {
                /* 10/2016: Compiler now catches illegal DerefOf(StringConstant) */
        /*		CH03(ts, z054, 0x01c, __LINE__, 0) */
        /*		Add(DerefOf("mm00"), 4, Local0) */
        /*		CH04(ts, 0, 47, z054, __LINE__, 0, 0) // AE_AML_OPERAND_TYPE */
        }

        /* ObjectType */

        Method (M00C, 0, NotSerialized)
        {
            Local0 = ObjectType (MM00)
            If ((Local0 != C010))
            {
                ERR (__METHOD__, Z054, __LINE__, 0x00, 0x00, Local0, C010)
            }
        }

        Method (M00D, 0, NotSerialized)
        {
            Local0 = ObjectType (DerefOf (RefOf (MM00)))
            If ((Local0 != C010))
            {
                ERR (__METHOD__, Z054, __LINE__, 0x00, 0x00, Local0, C010)
            }
        }

        Method (M00E, 0, NotSerialized)
        {
            Local0 = ObjectType (DerefOf (P000 [0x01]))
            If ((Local0 != C010))
            {
                ERR (__METHOD__, Z054, __LINE__, 0x00, 0x00, Local0, C010)
            }
        }

        Method (M00F, 0, NotSerialized)
        {
                /* 10/2016: Compiler now catches illegal DerefOf(StringConstant) */
        /*		Store(ObjectType(DerefOf("mm00")), Local0) */
        /*		if (LNotEqual(Local0, c010)) { */
        /*			err(ts, z054, __LINE__, 0, 0, Local0, c010) */
        /*		} */
        }

        Method (M100, 0, NotSerialized)
        {
            SRMT ("m15b-0")
            M000 ()
            SRMT ("m15b-1")
            M001 ()
            SRMT ("m15b-2")
            M002 ()
            SRMT ("m15b-3")
            M003 ()
            SRMT ("m15b-4")
            M004 ()
            SRMT ("m15b-5")
            M005 ()
            SRMT ("m15b-6")
            M006 ()
            SRMT ("m15b-7")
            M007 ()
            SRMT ("m15b-8")
            M008 ()
            SRMT ("m15b-9")
            M009 ()
            SRMT ("m15b-a")
            M00A ()
            SRMT ("m15b-b")
            M00B ()
            SRMT ("m15b-c")
            M00C ()
            SRMT ("m15b-d")
            M00D ()
            SRMT ("m15b-e")
            M00E ()
            SRMT ("m15b-f")
            M00F ()
        }

        M100 ()
    }

    /* Run-method */

    Method (MSC0, 0, Serialized)
    {
        SRMT ("m110")
        M110 (__METHOD__)
        SRMT ("m112")
        M112 (__METHOD__)
        SRMT ("m113")
        M113 (__METHOD__)
        SRMT ("m114")
        M114 (__METHOD__)
        SRMT ("m115")
        M115 (__METHOD__)
        SRMT ("m116")
        M116 (__METHOD__)
        SRMT ("m118")
        M118 (__METHOD__)
        SRMT ("m119")
        M119 (__METHOD__)
        SRMT ("m11c")
        M11C (__METHOD__)
        SRMT ("m11d")
        M11D (__METHOD__)
        SRMT ("m11e")
        M11E (__METHOD__)
        SRMT ("m11f")
        M11F (__METHOD__)
        SRMT ("m120")
        M120 (__METHOD__)
        SRMT ("m121")
        M121 (__METHOD__)
        SRMT ("m122")
        M122 (__METHOD__)
        SRMT ("m123")
        M123 (__METHOD__)
        SRMT ("m124")
        M124 (__METHOD__)
        SRMT ("m125")
        M125 (__METHOD__)
        SRMT ("mf75")
        MF75 (__METHOD__)
        /*SRMT("mf77") */
        /*mf77(ts) */
        SRMT ("mf86")
        MF86 (__METHOD__)
        SRMT ("mf87")
        MF87 (__METHOD__)
        M15B ()
    }
