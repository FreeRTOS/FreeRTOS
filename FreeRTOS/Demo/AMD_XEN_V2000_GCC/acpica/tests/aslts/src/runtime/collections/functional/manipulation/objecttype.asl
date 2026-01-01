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
    /*
     !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
     SEE: to be a few updated, see below
     !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
     */
    /* ObjectType, Type of object */
    /* Check ObjectType operator for: */
    /* - all the Types of objects, */
    /* - all the ways Obtaining those objects, */
    /* - all the ways Passing objects to ObjectType. */
    /* */
    /* Types     - {0-16}, see specs. */
    /* Obtaining - different creating operators,... */
    /* Passing   - immediately local, immediately global, */
    /*             by ArgX, by LocalX,... */
    Name (Z040, 0x28)
    /* Global objects */

    Name (N002, 0x90801020)
    Name (N003, 0x9189192989396949)
    Name (N005, "9876")
    Name (B003, Buffer (0x04)
    {
         0x0C, 0x0D, 0x0E, 0x0F                           // ....
    })
    /* Exercise all the ways creating the source objects of different types */
    /* */
    /*  0 - Uninitialized */
    /* */
    /*  Integers */
    /* */
    /*      One, Ones, Zero, Revision, Timer          (compile error) */
    /*      immediate 32-bit Integer constant imagine (compile error) */
    /*      immediate 64-bit Integer constant imagine (compile error) */
    /* */
    /*  1 - 32-bit Integers */
    /* */
    /*      32-bit Integer passed by LocalX */
    /*      32-bit Integer passed by ArgX */
    /*      32-bit Integer passed by local Name */
    /*      32-bit Integer passed by global Name */
    /* */
    /*  2 - 64-bit Integers */
    /* */
    /*      64-bit Integer passed by LocalX */
    /*      64-bit Integer passed by ArgX */
    /*      64-bit Integer passed by local Name */
    /*      64-bit Integer passed by global Name */
    /* */
    /* String */
    /* */
    /*  3 - String */
    /* */
    /* Field Units */
    /* */
    /*  4 - Field Unit created by Field */
    /*  5 - Field Unit created by BankField */
    /*  6 - Field Unit created by IndexField */
    /* */
    /* Buffers */
    /* */
    /*    - buffer passed immediately (compile error) */
    /*  7 - buffer passed by LocalX */
    /*  8 - buffer passed by ArgX */
    /*  9 - buffer passed by local Name */
    /* 10 - buffer passed by global Name */
    /* */
    /* Buffer Fields */
    /* */
    /* 11 - CreateBitField          (bit field) */
    /* 12 - CreateByteField         (byte field) */
    /* 13 - CreateDWordField        (DWord field) */
    /* 14 - CreateField      32-bit (arbitrary length bit field) */
    /* 15 - CreateField      64-bit (arbitrary length bit field) */
    /* 16 - CreateField      65-bit (arbitrary length bit field) */
    /* 17 - CreateQWordField        (QWord field) */
    /* 18 - CreateWordField         (Word field) */
    /* */
    /* 19 - Index, Index with String   (reference to Buffer Fields) */
    /* 20 - Index, Index with Buffer   (reference to Buffer Fields) */
    /* 21 - Index, Index with Package  (reference to object in Package) */
    /* */
    /* 22 - Data Table Operation Region */
    /* 23 - Debug Object */
    /* 24 - Device */
    /* 25 - Event */
    /* 26 - Method */
    /* 27 - Function */
    /* 28 - Mutex */
    /* 29 - Operation Region */
    /* 30 - Package */
    /* 31 - Power Resource */
    /* 32 - Processor */
    /* 33 - Thermal Zone */
    /* 34 - DDB Handle */
    /* */
    /* */
    /* Name - add all other objects by the name and so on ... !!!!!!!!!!!!!!!!! */
    /* */
    /* */
    /* Local7 - returned result */
    /* */
    Method (M0F1, 7, Serialized)
    {
        OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
        OperationRegion (R001, SystemMemory, 0x0100, 0x0100)
        If (Arg1)
        {
            Local7 = 0x00
        }

        Switch (ToInteger (Arg1))
        {
            Case (0x00)
            {
                /* Uninitialized */
                /*
                 * Bug 9 fixed.
                 * if (arg1) {
                 *	Store(0, Local0)
                 *	Store(0, Local1)
                 *	Store(0, Local2)
                 *	Store(0, Local3)
                 *	Store(0, Local4)
                 *	Store(0, Local5)
                 *	Store(0, Local6)
                 *	Store(0, Local7)
                 * }
                 */
                Local7 = ObjectType (Local0)
                If ((Local7 != C008))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C008)
                }

                Local7 = ObjectType (Local1)
                If ((Local7 != C008))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C008)
                }

                Local7 = ObjectType (Local2)
                If ((Local7 != C008))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C008)
                }

                Local7 = ObjectType (Local3)
                If ((Local7 != C008))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C008)
                }

                Local7 = ObjectType (Local4)
                If ((Local7 != C008))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C008)
                }

                Local7 = ObjectType (Local5)
                If ((Local7 != C008))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C008)
                }

                Local7 = ObjectType (Local6)
                If ((Local7 != C008))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C008)
                }
            }
            Case (0x01)
            {
                /* 32-bit Integers */
                /* By LocalX */
                Local0 = 0x12345678
                Local7 = ObjectType (Local0)
                If ((Local7 != C009))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C009)
                }

                If ((Local0 != 0x12345678))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local0, 0x12345678)
                }

                /* By ArgX */

                Local7 = ObjectType (Arg2)
                If ((Local7 != C009))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C009)
                }

                If ((Arg2 != 0x81223344))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Arg2, 0x81223344)
                }

                /* By Name locally */

                Name (N000, 0x98127364)
                Local7 = ObjectType (N000)
                If ((Local7 != C009))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C009)
                }

                If ((N000 != 0x98127364))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, N000, 0x98127364)
                }

                /* By Name globally */

                Local7 = ObjectType (N002)
                If ((Local7 != C009))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C009)
                }

                If ((N002 != 0x90801020))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, N002, 0x90801020)
                }

                /* Not a Buffer in 32-bit mode */

                Local0 = 0xA1B2C3D4E5C6E7F8
                Local7 = ObjectType (Local0)
                If ((Local7 != C009))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C009)
                }
            }
            Case (0x02)
            {
                /* 64-bit Integers */

                If ((F64 == 0x01))
                {
                    /* By LocalX */

                    Local0 = 0xA1B2C3D4E5C6E7F8
                    Local7 = ObjectType (Local0)
                    If ((Local7 != C009))
                    {
                        ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C009)
                    }

                    If ((Local0 != 0xA1B2C3D4E5C6E7F8))
                    {
                        ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local0, 0xA1B2C3D4E5C6E7F8)
                    }

                    /* By ArgX */

                    Local7 = ObjectType (Arg2)
                    If ((Local7 != C009))
                    {
                        ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C009)
                    }

                    If ((Arg2 != 0xFABEFAC489501248))
                    {
                        ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Arg2, 0xFABEFAC489501248)
                    }

                    /* By Name locally */

                    Name (N001, 0x9081122384356647)
                    Local7 = ObjectType (N001)
                    If ((Local7 != C009))
                    {
                        ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C009)
                    }

                    If ((N001 != 0x9081122384356647))
                    {
                        ERR (Arg0, Z040, __LINE__, 0x00, 0x00, N001, 0x9081122384356647)
                    }

                    /* By Name globally */

                    Local7 = ObjectType (N003)
                    If ((Local7 != C009))
                    {
                        ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C009)
                    }

                    If ((N003 != 0x9189192989396949))
                    {
                        ERR (Arg0, Z040, __LINE__, 0x00, 0x00, N003, 0x9189192989396949)
                    }
                }
            }
            Case (0x03)
            {
                /* String */
                /* By LocalX */
                Local0 = ""
                Local7 = ObjectType (Local0)
                If ((Local7 != C00A))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00A)
                }

                Local0 = "1"
                Local7 = ObjectType (Local0)
                If ((Local7 != C00A))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00A)
                }

                Local0 = "abcd"
                Local7 = ObjectType (Local0)
                If ((Local7 != C00A))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00A)
                }

                Local0 = "qwrt"
                Local7 = ObjectType (Local0)
                If ((Local7 != C00A))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00A)
                }

                /* By ArgX */

                Local7 = ObjectType (Arg2)
                If ((Local7 != C00A))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00A)
                }

                If ((Arg2 != "zxcvbnm0912345678ok"))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Arg2, "zxcvbnm0912345678ok")
                }

                /* By Name locally */

                Name (N004, "")
                Local7 = ObjectType (N004)
                If ((Local7 != C00A))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00A)
                }

                If ((N004 != ""))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, N004, "")
                }

                /* By Name globally */

                Local7 = ObjectType (N005)
                If ((Local7 != C00A))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00A)
                }

                If ((N005 != "9876"))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, N005, "9876")
                }
            }
            Case (0x04)
            {
                /* Field Unit */
                /* OperationRegion(r000, SystemMemory, 0x100, 0x100) */
                Field (R000, ByteAcc, NoLock, Preserve)
                {
                    F000,   8,
                    F222,   32,
                    F223,   57,
                    F224,   64,
                    F225,   71
                }

                F000 = 0x8D
                Local7 = ObjectType (F000)
                If ((Local7 != C00D))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00D)
                }

                If ((F000 != 0x8D))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, F000, 0x8D)
                }

                Local7 = ObjectType (F222)
                If ((Local7 != C00D))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00D)
                }

                Local7 = ObjectType (F223)
                If ((Local7 != C00D))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00D)
                }

                Local7 = ObjectType (F224)
                If ((Local7 != C00D))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00D)
                }

                Local7 = ObjectType (F225)
                If ((Local7 != C00D))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00D)
                }
            }
            Case (0x05)
            {
                /* BankField */
                /* OperationRegion(r001, SystemMemory, 0x100, 0x100) */
                Field (R001, ByteAcc, NoLock, Preserve)
                {
                    BNK0,   8
                }

                BankField (R001, BNK0, 0x00, ByteAcc, NoLock, Preserve)
                {
                    Offset (0x10),
                    BKF0,   8
                }

                BKF0 = 0x95
                Local7 = ObjectType (BKF0)
                If ((Local7 != C00D))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00D)
                }

                If ((BKF0 != 0x95))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, BKF0, 0x95)
                }
            }
            Case (0x06)
            {
                /* IndexField */

                OperationRegion (R002, SystemMemory, 0x0100, 0x0100)
                Field (R002, ByteAcc, NoLock, Preserve)
                {
                    F00A,   16,
                    F00B,   16
                }

                IndexField (F00A, F00B, ByteAcc, NoLock, Preserve)
                {
                    IF00,   8,
                    IF01,   8
                }

                F00A = 0xA0
                F00B = 0xA1
                IF00 = 0xA2
                IF01 = 0xA3
                Local7 = ObjectType (F00A)
                If ((Local7 != C00D))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00D)
                }

                Local7 = ObjectType (F00B)
                If ((Local7 != C00D))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00D)
                }

                Local7 = ObjectType (IF00)
                If ((Local7 != C00D))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00D)
                }

                Local7 = ObjectType (IF01)
                If ((Local7 != C00D))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00D)
                }
            }
            Case (0x07)
            {
                /* Buffer */

                Local0 = Buffer (0x04)
                    {
                         0x00, 0x01, 0x02, 0x03                           // ....
                    }
                Local7 = ObjectType (Local0)
                If ((Local7 != C00B))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00B)
                }

                If ((Local0 != Buffer (0x04)
                            {
                                 0x00, 0x01, 0x02, 0x03                           // ....
                            }))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, 0x00, 0x00)
                }
            }
            Case (0x08)
            {
                /* Buffer */

                Local7 = ObjectType (Arg2)
                If ((Local7 != C00B))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00B)
                }

                If ((Arg2 != Buffer (0x04)
                            {
                                 0x04, 0x05, 0x06, 0x07                           // ....
                            }))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, 0x00, 0x00)
                }
            }
            Case (0x09)
            {
                /* Buffer */

                Name (B000, Buffer (0x04)
                {
                     0x08, 0x09, 0x0A, 0x0B                           // ....
                })
                Local7 = ObjectType (B000)
                If ((Local7 != C00B))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00B)
                }

                If ((B000 != Buffer (0x04)
                            {
                                 0x08, 0x09, 0x0A, 0x0B                           // ....
                            }))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, 0x00, 0x00)
                }
            }
            Case (0x0A)
            {
                /* Buffer */

                Local7 = ObjectType (B003)
                If ((Local7 != C00B))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00B)
                }

                If ((B003 != Buffer (0x04)
                            {
                                 0x0C, 0x0D, 0x0E, 0x0F                           // ....
                            }))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, 0x00, 0x00)
                }
            }
            Case (0x0B)
            {
                /* Buffer Field */

                Local0 = Buffer (0x04)
                    {
                         0x10, 0x11, 0x12, 0x13                           // ....
                    }
                CreateBitField (Local0, 0x03, F001)
                Local7 = ObjectType (F001)
                If ((Local7 != C016))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C016)
                }

                If ((Local0 != Buffer (0x04)
                            {
                                 0x10, 0x11, 0x12, 0x13                           // ....
                            }))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, 0x00, 0x00)
                }
            }
            Case (0x0C)
            {
                /* Buffer Field */

                Local0 = Buffer (0x04)
                    {
                         0x14, 0x15, 0x16, 0x17                           // ....
                    }
                CreateByteField (Local0, 0x03, F002)
                Local7 = ObjectType (F002)
                If ((Local7 != C016))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C016)
                }

                If ((Local0 != Buffer (0x04)
                            {
                                 0x14, 0x15, 0x16, 0x17                           // ....
                            }))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, 0x00, 0x00)
                }
            }
            Case (0x0D)
            {
                /* Buffer Field */

                Local0 = Buffer (0x04)
                    {
                         0x18, 0x19, 0x1A, 0x1B                           // ....
                    }
                CreateDWordField (Local0, 0x00, F003)
                Local7 = ObjectType (F003)
                If ((Local7 != C016))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C016)
                }

                If ((Local0 != Buffer (0x04)
                            {
                                 0x18, 0x19, 0x1A, 0x1B                           // ....
                            }))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, 0x00, 0x00)
                }
            }
            Case (0x0E)
            {
                /* Buffer Field */

                Local0 = Buffer (0x04)
                    {
                         0x1C, 0x1D, 0x1E, 0x1F                           // ....
                    }
                CreateField (Local0, 0x00, 0x20, F004)
                Local7 = ObjectType (F004)
                If ((Local7 != C016))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C016)
                }

                If ((Local0 != Buffer (0x04)
                            {
                                 0x1C, 0x1D, 0x1E, 0x1F                           // ....
                            }))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, 0x00, 0x00)
                }
            }
            Case (0x0F)
            {
                /* Buffer Field */

                Local0 = Buffer (0x09)
                    {
                        /* 0000 */  0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28,  // !"#$%&'(
                        /* 0008 */  0x29                                             // )
                    }
                CreateField (Local0, 0x00, 0x40, F005)
                Local7 = ObjectType (F005)
                If ((Local7 != C016))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C016)
                }

                If ((Local0 != Buffer (0x09)
                            {
                                /* 0000 */  0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28,  // !"#$%&'(
                                /* 0008 */  0x29                                             // )
                            }))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, 0x00, 0x00)
                }
            }
            Case (0x10)
            {
                /* Buffer Field */

                Local0 = Buffer (0x09)
                    {
                        /* 0000 */  0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F, 0x30, 0x31,  // *+,-./01
                        /* 0008 */  0x32                                             // 2
                    }
                CreateField (Local0, 0x00, 0x41, F006)
                Local7 = ObjectType (F006)
                If ((Local7 != C016))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C016)
                }

                If ((Local0 != Buffer (0x09)
                            {
                                /* 0000 */  0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F, 0x30, 0x31,  // *+,-./01
                                /* 0008 */  0x32                                             // 2
                            }))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, 0x00, 0x00)
                }

                CreateField (Local0, 0x00, 0x11, F111)
                Local7 = ObjectType (F111)
                If ((Local7 != C016))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C016)
                }

                CreateField (Local0, 0x00, 0x39, F112)
                Local7 = ObjectType (F112)
                If ((Local7 != C016))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C016)
                }
            }
            Case (0x11)
            {
                /* Buffer Field */

                Local0 = Buffer (0x09)
                    {
                        /* 0000 */  0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F, 0x30, 0x31,  // *+,-./01
                        /* 0008 */  0x32                                             // 2
                    }
                CreateQWordField (Local0, 0x00, F007)
                Local7 = ObjectType (F007)
                If ((Local7 != C016))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C016)
                }

                If ((Local0 != Buffer (0x09)
                            {
                                /* 0000 */  0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F, 0x30, 0x31,  // *+,-./01
                                /* 0008 */  0x32                                             // 2
                            }))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, 0x00, 0x00)
                }
            }
            Case (0x12)
            {
                /* Buffer Field */

                Local0 = Buffer (0x04)
                    {
                         0x33, 0x34, 0x35, 0x36                           // 3456
                    }
                CreateWordField (Local0, 0x00, F008)
                Local7 = ObjectType (F008)
                If ((Local7 != C016))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C016)
                }

                If ((Local0 != Buffer (0x04)
                            {
                                 0x33, 0x34, 0x35, 0x36                           // 3456
                            }))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, 0x00, 0x00)
                }
            }
            Case (0x13)
            {
                /* Buffer Field */

                Local0 = "q"
                Store (Local0 [0x00], Local1)
                Local7 = ObjectType (Local1)
                If ((Local7 != C016))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C016)
                }

                If ((Local0 != "q"))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, 0x00, 0x00)
                }

                Local0 = "qw"
                Store (Local0 [0x00], Local1)
                Local7 = ObjectType (Local1)
                If ((Local7 != C016))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C016)
                }

                If ((Local0 != "qw"))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, 0x00, 0x00)
                }

                Local0 = "qwertyu"
                Store (Local0 [0x00], Local1)
                Local7 = ObjectType (Local1)
                If ((Local7 != C016))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C016)
                }

                If ((Local0 != "qwertyu"))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, 0x00, 0x00)
                }

                Local0 = "qwertyuiop"
                Store (Local0 [0x00], Local1)
                Local7 = ObjectType (Local1)
                If ((Local7 != C016))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C016)
                }

                If ((Local0 != "qwertyuiop"))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, 0x00, 0x00)
                }
            }
            Case (0x14)
            {
                /* Buffer Field */

                Local0 = Buffer (0x04)
                    {
                         0x2A, 0x2B, 0x2C, 0x2D                           // *+,-
                    }
                Store (Local0 [0x00], Local1)
                Local7 = ObjectType (Local1)
                If ((Local7 != C016))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C016)
                }

                If ((Local0 != Buffer (0x04)
                            {
                                 0x2A, 0x2B, 0x2C, 0x2D                           // *+,-
                            }))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, 0x00, 0x00)
                }

                Local0 = Buffer (0x08)
                    {
                         0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F, 0x30, 0x31   // *+,-./01
                    }
                Store (Local0 [0x00], Local1)
                Local7 = ObjectType (Local1)
                If ((Local7 != C016))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C016)
                }

                If ((Local0 != Buffer (0x08)
                            {
                                 0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F, 0x30, 0x31   // *+,-./01
                            }))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, 0x00, 0x00)
                }

                Local0 = Buffer (0x09)
                    {
                        /* 0000 */  0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F, 0x30, 0x31,  // *+,-./01
                        /* 0008 */  0x32                                             // 2
                    }
                Store (Local0 [0x00], Local1)
                Local7 = ObjectType (Local1)
                If ((Local7 != C016))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C016)
                }

                If ((Local0 != Buffer (0x09)
                            {
                                /* 0000 */  0x2A, 0x2B, 0x2C, 0x2D, 0x2E, 0x2F, 0x30, 0x31,  // *+,-./01
                                /* 0008 */  0x32                                             // 2
                            }))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, 0x00, 0x00)
                }
            }
            Case (0x15)
            {
                /* Index with ... */

                Local0 = Package (0x04)
                    {
                        Package (0x04)
                        {
                            0x98765432,
                            Buffer (0x01)
                            {
                                 0x12                                             // .
                            },

                            Package (0x01)
                            {
                                0x12345678
                            },

                            "qwertyui"
                        },

                        Buffer (0x01)
                        {
                             0x12                                             // .
                        },

                        "q",
                        0x98765432
                    }
                /* Package */

                Store (Local0 [0x00], Local1)
                Local7 = ObjectType (Local1)
                If ((Local7 != C00C))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00C)
                }

                /* Buffer */

                Store (Local0 [0x01], Local1)
                Local7 = ObjectType (Local1)
                If ((Local7 != C00B))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00B)
                }

                /* String */

                Store (Local0 [0x02], Local1)
                Local7 = ObjectType (Local1)
                If ((Local7 != C00A))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00A)
                }

                /* Integer */

                Store (Local0 [0x03], Local1)
                Local7 = ObjectType (Local1)
                If ((Local7 != C009))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C009)
                }
            }
            Case (0x16)
            {
                /* Operation Region */

                DataTableRegion (HDR0, "DSDT", "", "")
                Local7 = ObjectType (HDR0)
                If ((Local7 != C012))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C012)
                }
            }
            Case (0x17)
            {
                /* Debug Object */

                Local7 = ObjectType (Debug)
                If ((Local7 != C018))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C018)
                }
            }
            Case (0x18)
            {
                /* Device */

                Device (DV00)
                {
                }

                Local7 = ObjectType (DV00)
                If ((Local7 != C00E))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00E)
                }
            }
            Case (0x19)
            {
                /* Event */

                Event (EVT0)
                Local7 = ObjectType (EVT0)
                If ((Local7 != C00F))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00F)
                }
            }
            Case (0x1A)
            {
                /* Method */

                Method (M0F2, 0, NotSerialized)
                {
                    Return (0x1234)
                }

                Local7 = ObjectType (M0F2)
                If ((Local7 != C010))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C010)
                }
            }
            Case (0x1B)
            {
                        /*
             *			// Function
             *
             *			Function(mof3) { return (0) }
             *			Store(ObjectType(m0f3), Local7)
             *			if (LNotEqual(Local7, c010)) {
             *				err(arg0, z040, __LINE__, 0, 0, Local7, c010)
             *			}
             */
            }
            Case (0x1C)
            {
                /* Mutex */

                Mutex (MT00, 0x00)
                Local7 = ObjectType (MT00)
                If ((Local7 != C011))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C011)
                }
            }
            Case (0x1D)
            {
                /* Operation Region */

                Local7 = ObjectType (R000)
                If ((Local7 != C012))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C012)
                }

                Local7 = ObjectType (R001)
                If ((Local7 != C012))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C012)
                }
            }
            Case (0x1E)
            {
                /* Package */

                Name (P000, Package (0x01)
                {
                    0x12345678
                })
                Name (P001, Package (0x02)
                {
                    0x12345678,
                    0x9ABCDEF0
                })
                Name (P002, Package (0x03)
                {
                    0x12345678,
                    0x9ABCDEF0,
                    0x9ABCDEF0
                })
                Name (P003, Package (0x01)
                {
                    0x123456789ABCDEF0
                })
                Name (P004, Package (0x02)
                {
                    0x123456789ABCDEF0,
                    0x123456789ABCDEF0
                })
                Name (P005, Package (0x03)
                {
                    0x123456789ABCDEF0,
                    0x123456789ABCDEF0,
                    0x123456789ABCDEF0
                })
                Name (P006, Package (0x01)
                {
                    Buffer (0x01){}
                })
                Name (P007, Package (0x01)
                {
                    Buffer (0x20){}
                })
                Name (P008, Package (0x01)
                {
                    Buffer (0x40){}
                })
                Name (P009, Package (0x01)
                {
                    Buffer (0x7D){}
                })
                Name (P00A, Package (0x02)
                {
                    0x12,
                    Buffer (0x01)
                    {
                         0x12                                             // .
                    }
                })
                Name (P00B, Package (0x02)
                {
                    0x12,
                    Package (0x01)
                    {
                        0x12
                    }
                })
                Name (P00C, Package (0x01)
                {
                    Buffer (0x01)
                    {
                         0x12                                             // .
                    }
                })
                Name (P00D, Package (0x02)
                {
                    Buffer (0x01)
                    {
                         0x12                                             // .
                    },

                    0x12345678
                })
                Name (P00E, Package (0x02)
                {
                    Buffer (0x01)
                    {
                         0x12                                             // .
                    },

                    Buffer (0x01)
                    {
                         0x12                                             // .
                    }
                })
                Name (P00F, Package (0x02)
                {
                    Buffer (0x01)
                    {
                         0x12                                             // .
                    },

                    Package (0x01)
                    {
                        0x12
                    }
                })
                Name (P010, Package (0x01)
                {
                    Package (0x01)
                    {
                        0x12345678
                    }
                })
                Name (P011, Package (0x02)
                {
                    Package (0x01)
                    {
                        0x12345678
                    },

                    0x12345678
                })
                Name (P012, Package (0x02)
                {
                    Package (0x01)
                    {
                        0x12345678
                    },

                    Buffer (0x01)
                    {
                         0x12                                             // .
                    }
                })
                Name (P013, Package (0x02)
                {
                    Package (0x01)
                    {
                        0x12345678
                    },

                    Package (0x01)
                    {
                        0x12
                    }
                })
                Local7 = ObjectType (P000)
                If ((Local7 != C00C))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00C)
                }

                Local7 = ObjectType (P001)
                If ((Local7 != C00C))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00C)
                }

                Local7 = ObjectType (P002)
                If ((Local7 != C00C))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00C)
                }

                Local7 = ObjectType (P003)
                If ((Local7 != C00C))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00C)
                }

                Local7 = ObjectType (P004)
                If ((Local7 != C00C))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00C)
                }

                Local7 = ObjectType (P005)
                If ((Local7 != C00C))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00C)
                }

                Local7 = ObjectType (P006)
                If ((Local7 != C00C))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00C)
                }

                Local7 = ObjectType (P007)
                If ((Local7 != C00C))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00C)
                }

                Local7 = ObjectType (P008)
                If ((Local7 != C00C))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00C)
                }

                Local7 = ObjectType (P009)
                If ((Local7 != C00C))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00C)
                }

                Local7 = ObjectType (P00A)
                If ((Local7 != C00C))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00C)
                }

                Local7 = ObjectType (P00B)
                If ((Local7 != C00C))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00C)
                }

                Local7 = ObjectType (P00C)
                If ((Local7 != C00C))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00C)
                }

                Local7 = ObjectType (P00D)
                If ((Local7 != C00C))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00C)
                }

                Local7 = ObjectType (P00E)
                If ((Local7 != C00C))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00C)
                }

                Local7 = ObjectType (P00F)
                If ((Local7 != C00C))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00C)
                }

                Local7 = ObjectType (P010)
                If ((Local7 != C00C))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00C)
                }

                Local7 = ObjectType (P011)
                If ((Local7 != C00C))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00C)
                }

                Local7 = ObjectType (P012)
                If ((Local7 != C00C))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00C)
                }

                Local7 = ObjectType (P013)
                If ((Local7 != C00C))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C00C)
                }
            }
            Case (0x1F)
            {
                /* Power Resource */

                PowerResource (PWR0, 0x01, 0x0000)
                {
                    Method (M000, 0, NotSerialized)
                    {
                        Return (0x00)
                    }
                }

                Local7 = ObjectType (PWR0)
                If ((Local7 != C013))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C013)
                }
            }
            Case (0x20)
            {
                /* Processor */

                Processor (PR00, 0x00, 0xFFFFFFFF, 0x00){}
                Local7 = ObjectType (PR00)
                If ((Local7 != C014))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C014)
                }
            }
            Case (0x21)
            {
                ThermalZone (TZ00)
                {
                }

                Local7 = ObjectType (TZ00)
                If ((Local7 != C015))
                {
                    ERR (Arg0, Z040, __LINE__, 0x00, 0x00, Local7, C015)
                }
            }
            Case (0x22)
            {
                        /*
             // Reserved for DDB Handle
             Store("==================================== zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz", Debug)
             //			Store (LoadTable ("OEM1", "MYOEM", "TABLE1", "\\_SB.PCI0", "MYD",
             //					 	Package () {0, "\\_SB.PCI0"}), Local0)
             Store (LoadTable("OEM1", "MYOEM", "TABLE1"), Local0)
             Store(ObjectType(Local0), Local7)
             if (LNotEqual(Local7, c017)) {
             err(arg0, z040, __LINE__, 0, 0, Local7, c017)
             }
             Store("==================================== uuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuu", Debug)
             */
            }
            Default
            {
                ERR (Arg0, Z040, __LINE__, 0x00, 0x00, 0x00, 0x00)
            }

        }

        Return (Local7)
    }

    Method (M0F0, 0, Serialized)
    {
        Debug = "TEST: m0f0, ObjectType"
        Local5 = 0x00
        Local4 = 0x23
        While (Local4)
        {
            Local2 = 0x00
            Switch (ToInteger (Local5))
            {
                Case (0x01)
                {
                    Local2 = 0x81223344
                }
                Case (0x02)
                {
                    Local2 = 0xFABEFAC489501248
                }
                Case (0x03)
                {
                    Local2 = "zxcvbnm0912345678ok"
                }
                Case (0x08)
                {
                    Local2 = Buffer (0x04)
                        {
                             0x04, 0x05, 0x06, 0x07                           // ....
                        }
                }

            }

            M0F1 (__METHOD__, Local5, Local2, 0x00, 0x00, 0x00, 0x00)
            Local5++
            Local4--
        }
    }

    /* Run-method */

    Method (OBT0, 0, NotSerialized)
    {
        Debug = "TEST: OBT0, Type of object"
        M0F0 ()
    }
