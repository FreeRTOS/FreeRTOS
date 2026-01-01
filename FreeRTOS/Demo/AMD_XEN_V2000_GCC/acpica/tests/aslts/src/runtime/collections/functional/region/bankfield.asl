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
     * BankField objects definition and processing
     */
    /*
     * On testing following issues should be covered:
     * - Operation Regions of different Region Space types application
     *   for BankField objects definition,
     * - Operation Regions of different Region Space types application
     *   for definition of bank selection register Field object used in
     *   BankField objects definition,
     * - application of any TermArg as a BankValue Integer,
     * - application of any allowed AccessType Keywords,
     * - application of any allowed LockRule Keywords,
     * - application of any allowed UpdateRule Keywords,
     * - application of the Offset macros in the FieldUnitList,
     * - application of the AccessAs macros in the FieldUnitList,
     * - on writing taking into account the Access Type in accord with
     the Update Rule,
     * - AccessAs macros influence on the remaining Field Units within the list,
     * - access to BankField objects in accord with the bank selection register
     *   functionality,
     * - integer/buffer representation of the Unit contents as depends on its
     *   Length and DSDT ComplianceRevision (32/64-bit Integer),
     * - Data Type Conversion Rules on storing to BankFields,
     * - check that Bank value can be computational data.
     *
     * Can not be tested following issues:
     * - exact use of given Access Type alignment on Access to Unit data,
     * - exact functioning of data exchange based on BankField functionality,
     * - exact use of specific Conversion Rules on storing of Buffers or Strings.
     */
    Name (Z145, 0x91)
    OperationRegion (OPRI, SystemIO, 0x0200, 0x10)
    OperationRegion (OPRJ, SystemIO, 0x0230, 0x0133)
    /* Check against benchmark value */
    /* m7bf(msg, result, benchmark, errnum) */
    Method (M7BF, 4, NotSerialized)
    {
        If ((ObjectType (Arg1) != ObjectType (Arg2)))
        {
            ERR (Arg0, Z145, __LINE__, 0x00, 0x00, ObjectType (Arg1), ObjectType (Arg2))
        }
        ElseIf ((Arg1 != Arg2))
        {
            ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg1, Arg2)
        }
    }

    /* Simple BankField test */

    Method (M7C0, 1, Serialized)
    {
        Field (OPRI, ByteAcc, NoLock, Preserve)
        {
            BNK0,   8
        }

        BankField (OPRJ, BNK0, 0x02, ByteAcc, NoLock, Preserve)
        {
            Offset (0x08),
            BF00,   8
        }

        BankField (OPRJ, BNK0, 0x03, ByteAcc, NoLock, Preserve)
        {
            Offset (0x08),
            BF01,   8
        }

        Concatenate (Arg0, "-m7c0", Arg0)
        /* */
        /* Full support for bank fields not implemented in acpiexec, so */
        /* we have to perform write/reads in order. Otherwise, we would */
        /* interleave them. */
        /* Write bf00 */
        BNK0 = 0xFF
        M7BF (Arg0, BNK0, 0xFF, 0x01)
        BF00 = 0x67
        M7BF (Arg0, BNK0, 0x02, 0x02)
        /* Read bf00 */

        BNK0 = 0xFF
        M7BF (Arg0, BNK0, 0xFF, 0x05)
        Local1 = BF00 /* \M7C0.BF00 */
        M7BF (Arg0, Local1, 0x67, 0x06)
        M7BF (Arg0, BNK0, 0x02, 0x07)
        /* Write bf01 */

        BNK0 = 0xFF
        M7BF (Arg0, BNK0, 0xFF, 0x03)
        BF01 = 0x89
        M7BF (Arg0, BNK0, 0x03, 0x04)
        /* Read bf01 */

        BNK0 = 0xFF
        M7BF (Arg0, BNK0, 0xFF, 0x08)
        Local1 = BF01 /* \M7C0.BF01 */
        M7BF (Arg0, Local1, 0x89, 0x09)
        M7BF (Arg0, BNK0, 0x03, 0x0A)
    }

    /* Testing parameters Packages */
    /* Layout see in regionfield.asl */
    /* (ByteAcc, NoLock, Preserve) */
    Name (PP20, Package (0x05)
    {
        0x00,
        0x08,
        0x00,
        0x08,
        Package (0x06)
        {
            0x00,
            0x01,
            0x01,
            0x00,
            0x01,
            "m7d0"
        }
    })
    /* (WordAcc, NoLock, WriteAsOnes) */

    Name (PP21, Package (0x05)
    {
        0x00,
        0x08,
        0x08,
        0x08,
        Package (0x06)
        {
            0x00,
            0x02,
            0x02,
            0x01,
            0x01,
            "m7d1"
        }
    })
    /* (DWordAcc, NoLock, WriteAsZeros) */

    Name (PP22, Package (0x05)
    {
        0x08,
        0x08,
        0x00,
        0x08,
        Package (0x06)
        {
            0x01,
            0x02,
            0x03,
            0x02,
            0x01,
            "m7d2"
        }
    })
    /* (QWordAcc, NoLock, Preserve) */

    Name (PP23, Package (0x05)
    {
        0x08,
        0x04,
        0x08,
        0x08,
        Package (0x06)
        {
            0x01,
            0x00,
            0x03,
            0x00,
            0x01,
            "m7d3"
        }
    })
    /* (AnyAcc, Lock, Preserve) */

    Name (PP24, Package (0x05)
    {
        0x0C,
        0x04,
        0x08,
        0x08,
        Package (0x06)
        {
            0x00,
            0x01,
            0x00,
            0x00,
            0x00,
            "m7d4"
        }
    })
    /* Check BankField access: ByteAcc, NoLock, Preserve */
    /* m7c1(CallChain) */
    Method (M7C1, 1, NotSerialized)
    {
        Concatenate (Arg0, "-m7c1", Arg0)
        Debug = "TEST: m7c1, Check BankFields specified as (ByteAcc, NoLock, Preserve)"
        M72F (Arg0, 0x01, "pp20", PP20)
    }

    /* Check BankField access: WordAcc, NoLock, WriteAsOnes */
    /* m7c2(CallChain) */
    Method (M7C2, 1, NotSerialized)
    {
        Concatenate (Arg0, "-m7c2", Arg0)
        Debug = "TEST: m7c2, Check BankFields specified as (WordAcc, NoLock, WriteAsOnes)"
        M72F (Arg0, 0x01, "pp21", PP21)
    }

    /* Check BankField access: DWordAcc, NoLock, WriteAsZeros */
    /* m7c3(CallChain) */
    Method (M7C3, 1, NotSerialized)
    {
        Concatenate (Arg0, "-m7c3", Arg0)
        Debug = "TEST: m7c3, Check BankFields specified as (DWordAcc, NoLock, WriteAsZeros)"
        M72F (Arg0, 0x01, "pp22", PP22)
    }

    /* Check BankField access: QWordAcc, NoLock, Preserve */
    /* m7c4(CallChain) */
    Method (M7C4, 1, NotSerialized)
    {
        Concatenate (Arg0, "-m7c4", Arg0)
        Debug = "TEST: m7c4, Check BankFields specified as (QWordAcc, NoLock, Preserve)"
        M72F (Arg0, 0x01, "pp23", PP23)
    }

    /* Check BankField access: AnyAcc, Lock, Preserve */
    /* m7c5(CallChain) */
    Method (M7C5, 1, NotSerialized)
    {
        Concatenate (Arg0, "-m7c5", Arg0)
        Debug = "TEST: m7c5, Check BankFields specified as (AnyAcc, Lock, Preserve)"
        M72F (Arg0, 0x01, "pp24", PP24)
    }

    /* Create BankField Unit */
    /* (ByteAcc, NoLock, Preserve) */
    Method (M7D0, 6, Serialized)
    {
        OperationRegion (OPRB, SystemIO, 0x00, 0x09)
        OperationRegion (OPR0, SystemIO, 0x0B, 0x0100)
        Field (OPRB, ByteAcc, NoLock, Preserve)
        {
            BNK0,   8
        }

        BankField (OPR0, BNK0, 0x00, ByteAcc, NoLock, Preserve)
        {
            G000,   2048
        }

        BankField (OPR0, BNK0, 0x01, ByteAcc, NoLock, Preserve)
        {
            G001,   2048
        }

        BankField (OPR0, BNK0, 0x02, ByteAcc, NoLock, Preserve)
        {
            G002,   2048
        }

        BankField (OPR0, BNK0, 0x03, ByteAcc, NoLock, Preserve)
        {
            G003,   2048
        }

        BankField (OPR0, BNK0, 0x04, ByteAcc, NoLock, Preserve)
        {
            G004,   2048
        }

        BankField (OPR0, BNK0, 0x05, ByteAcc, NoLock, Preserve)
        {
            G005,   2048
        }

        BankField (OPR0, BNK0, 0x06, ByteAcc, NoLock, Preserve)
        {
            G006,   2048
        }

        BankField (OPR0, BNK0, 0x07, ByteAcc, NoLock, Preserve)
        {
            G007,   2048
        }

        BankField (OPR0, BNK0, 0x08, ByteAcc, NoLock, Preserve)
        {
            G008,   2048
        }

        BankField (OPR0, BNK0, 0x09, ByteAcc, NoLock, Preserve)
        {
            G009,   2048
        }

        BankField (OPR0, BNK0, 0x3F, ByteAcc, NoLock, Preserve)
        {
            G00A,   2048
        }

        BankField (OPR0, BNK0, 0x40, ByteAcc, NoLock, Preserve)
        {
            G00B,   2048
        }

        BankField (OPR0, BNK0, 0x7F, ByteAcc, NoLock, Preserve)
        {
            G00C,   2048
        }

        BankField (OPR0, BNK0, 0x80, ByteAcc, NoLock, Preserve)
        {
            G00D,   2048
        }

        BankField (OPR0, BNK0, 0xFF, ByteAcc, NoLock, Preserve)
        {
            G00E,   2048
        }

        Concatenate (Arg0, "-m7d0", Arg0)
        Switch (ToInteger (Arg2))
        {
            Case (0x00)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F000,   1
                        }

                        Local3 = RefOf (F000)
                        Local4 = RefOf (G000)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x00),
                            F001,   6
                        }

                        Local3 = RefOf (F001)
                        Local4 = RefOf (G001)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F002,   7
                        }

                        Local3 = RefOf (F002)
                        Local4 = RefOf (G002)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x00),
                            F003,   8
                        }

                        Local3 = RefOf (F003)
                        Local4 = RefOf (G003)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F004,   9
                        }

                        Local3 = RefOf (F004)
                        Local4 = RefOf (G004)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x00),
                            F005,   31
                        }

                        Local3 = RefOf (F005)
                        Local4 = RefOf (G005)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F006,   32
                        }

                        Local3 = RefOf (F006)
                        Local4 = RefOf (G006)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x00),
                            F007,   33
                        }

                        Local3 = RefOf (F007)
                        Local4 = RefOf (G007)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F008,   63
                        }

                        Local3 = RefOf (F008)
                        Local4 = RefOf (G008)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x00),
                            F009,   64
                        }

                        Local3 = RefOf (F009)
                        Local4 = RefOf (G009)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F00A,   65
                        }

                        Local3 = RefOf (F00A)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x00),
                            F00B,   69
                        }

                        Local3 = RefOf (F00B)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F00C,   129
                        }

                        Local3 = RefOf (F00C)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x00),
                            F00D,   256
                        }

                        Local3 = RefOf (F00D)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F00E,   1023
                        }

                        Local3 = RefOf (F00E)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x00),
                            F00F,   1983
                        }

                        Local3 = RefOf (F00F)
                        Local4 = RefOf (G000)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x01)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   1,
                            F010,   1
                        }

                        Local3 = RefOf (F010)
                        Local4 = RefOf (G001)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, ByteAcc, NoLock, Preserve)
                        {
                                ,   1,
                            F011,   6
                        }

                        Local3 = RefOf (F011)
                        Local4 = RefOf (G002)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   1,
                            F012,   7
                        }

                        Local3 = RefOf (F012)
                        Local4 = RefOf (G003)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, ByteAcc, NoLock, Preserve)
                        {
                                ,   1,
                            F013,   8
                        }

                        Local3 = RefOf (F013)
                        Local4 = RefOf (G004)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   1,
                            F014,   9
                        }

                        Local3 = RefOf (F014)
                        Local4 = RefOf (G005)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, ByteAcc, NoLock, Preserve)
                        {
                                ,   1,
                            F015,   31
                        }

                        Local3 = RefOf (F015)
                        Local4 = RefOf (G006)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   1,
                            F016,   32
                        }

                        Local3 = RefOf (F016)
                        Local4 = RefOf (G007)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, ByteAcc, NoLock, Preserve)
                        {
                                ,   1,
                            F017,   33
                        }

                        Local3 = RefOf (F017)
                        Local4 = RefOf (G008)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   1,
                            F018,   63
                        }

                        Local3 = RefOf (F018)
                        Local4 = RefOf (G009)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, ByteAcc, NoLock, Preserve)
                        {
                                ,   1,
                            F019,   64
                        }

                        Local3 = RefOf (F019)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   1,
                            F01A,   65
                        }

                        Local3 = RefOf (F01A)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, ByteAcc, NoLock, Preserve)
                        {
                                ,   1,
                            F01B,   69
                        }

                        Local3 = RefOf (F01B)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   1,
                            F01C,   129
                        }

                        Local3 = RefOf (F01C)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, ByteAcc, NoLock, Preserve)
                        {
                                ,   1,
                            F01D,   256
                        }

                        Local3 = RefOf (F01D)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   1,
                            F01E,   1023
                        }

                        Local3 = RefOf (F01E)
                        Local4 = RefOf (G000)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, ByteAcc, NoLock, Preserve)
                        {
                                ,   1,
                            F01F,   1983
                        }

                        Local3 = RefOf (F01F)
                        Local4 = RefOf (G001)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x02)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, ByteAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F020,   1
                        }

                        Local3 = RefOf (F020)
                        Local4 = RefOf (G002)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   2,
                            F021,   6
                        }

                        Local3 = RefOf (F021)
                        Local4 = RefOf (G003)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, ByteAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F022,   7
                        }

                        Local3 = RefOf (F022)
                        Local4 = RefOf (G004)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   2,
                            F023,   8
                        }

                        Local3 = RefOf (F023)
                        Local4 = RefOf (G005)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, ByteAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F024,   9
                        }

                        Local3 = RefOf (F024)
                        Local4 = RefOf (G006)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   2,
                            F025,   31
                        }

                        Local3 = RefOf (F025)
                        Local4 = RefOf (G007)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, ByteAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F026,   32
                        }

                        Local3 = RefOf (F026)
                        Local4 = RefOf (G008)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   2,
                            F027,   33
                        }

                        Local3 = RefOf (F027)
                        Local4 = RefOf (G009)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, ByteAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F028,   63
                        }

                        Local3 = RefOf (F028)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   2,
                            F029,   64
                        }

                        Local3 = RefOf (F029)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, ByteAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F02A,   65
                        }

                        Local3 = RefOf (F02A)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   2,
                            F02B,   69
                        }

                        Local3 = RefOf (F02B)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x81)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, ByteAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F02C,   129
                        }

                        Local3 = RefOf (F02C)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   2,
                            F02D,   256
                        }

                        Local3 = RefOf (F02D)
                        Local4 = RefOf (G000)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, ByteAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F02E,   1023
                        }

                        Local3 = RefOf (F02E)
                        Local4 = RefOf (G001)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   2,
                            F02F,   1983
                        }

                        Local3 = RefOf (F02F)
                        Local4 = RefOf (G002)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x03)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   3,
                            F030,   1
                        }

                        Local3 = RefOf (F030)
                        Local4 = RefOf (G003)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, ByteAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F031,   6
                        }

                        Local3 = RefOf (F031)
                        Local4 = RefOf (G004)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   3,
                            F032,   7
                        }

                        Local3 = RefOf (F032)
                        Local4 = RefOf (G005)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, ByteAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F033,   8
                        }

                        Local3 = RefOf (F033)
                        Local4 = RefOf (G006)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   3,
                            F034,   9
                        }

                        Local3 = RefOf (F034)
                        Local4 = RefOf (G007)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, ByteAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F035,   31
                        }

                        Local3 = RefOf (F035)
                        Local4 = RefOf (G008)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   3,
                            F036,   32
                        }

                        Local3 = RefOf (F036)
                        Local4 = RefOf (G009)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, ByteAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F037,   33
                        }

                        Local3 = RefOf (F037)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   3,
                            F038,   63
                        }

                        Local3 = RefOf (F038)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, ByteAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F039,   64
                        }

                        Local3 = RefOf (F039)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   3,
                            F03A,   65
                        }

                        Local3 = RefOf (F03A)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x45)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, ByteAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F03B,   69
                        }

                        Local3 = RefOf (F03B)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   3,
                            F03C,   129
                        }

                        Local3 = RefOf (F03C)
                        Local4 = RefOf (G000)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, ByteAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F03D,   256
                        }

                        Local3 = RefOf (F03D)
                        Local4 = RefOf (G001)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   3,
                            F03E,   1023
                        }

                        Local3 = RefOf (F03E)
                        Local4 = RefOf (G002)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, ByteAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F03F,   1983
                        }

                        Local3 = RefOf (F03F)
                        Local4 = RefOf (G003)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x04)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, ByteAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F040,   1
                        }

                        Local3 = RefOf (F040)
                        Local4 = RefOf (G004)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   4,
                            F041,   6
                        }

                        Local3 = RefOf (F041)
                        Local4 = RefOf (G005)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, ByteAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F042,   7
                        }

                        Local3 = RefOf (F042)
                        Local4 = RefOf (G006)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   4,
                            F043,   8
                        }

                        Local3 = RefOf (F043)
                        Local4 = RefOf (G007)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, ByteAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F044,   9
                        }

                        Local3 = RefOf (F044)
                        Local4 = RefOf (G008)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   4,
                            F045,   31
                        }

                        Local3 = RefOf (F045)
                        Local4 = RefOf (G009)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, ByteAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F046,   32
                        }

                        Local3 = RefOf (F046)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   4,
                            F047,   33
                        }

                        Local3 = RefOf (F047)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, ByteAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F048,   63
                        }

                        Local3 = RefOf (F048)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   4,
                            F049,   64
                        }

                        Local3 = RefOf (F049)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x41)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, ByteAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F04A,   65
                        }

                        Local3 = RefOf (F04A)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   4,
                            F04B,   69
                        }

                        Local3 = RefOf (F04B)
                        Local4 = RefOf (G000)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, ByteAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F04C,   129
                        }

                        Local3 = RefOf (F04C)
                        Local4 = RefOf (G001)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   4,
                            F04D,   256
                        }

                        Local3 = RefOf (F04D)
                        Local4 = RefOf (G002)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, ByteAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F04E,   1023
                        }

                        Local3 = RefOf (F04E)
                        Local4 = RefOf (G003)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   4,
                            F04F,   1983
                        }

                        Local3 = RefOf (F04F)
                        Local4 = RefOf (G004)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x05)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   5,
                            F050,   1
                        }

                        Local3 = RefOf (F050)
                        Local4 = RefOf (G005)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, ByteAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F051,   6
                        }

                        Local3 = RefOf (F051)
                        Local4 = RefOf (G006)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   5,
                            F052,   7
                        }

                        Local3 = RefOf (F052)
                        Local4 = RefOf (G007)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, ByteAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F053,   8
                        }

                        Local3 = RefOf (F053)
                        Local4 = RefOf (G008)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   5,
                            F054,   9
                        }

                        Local3 = RefOf (F054)
                        Local4 = RefOf (G009)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, ByteAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F055,   31
                        }

                        Local3 = RefOf (F055)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   5,
                            F056,   32
                        }

                        Local3 = RefOf (F056)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, ByteAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F057,   33
                        }

                        Local3 = RefOf (F057)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   5,
                            F058,   63
                        }

                        Local3 = RefOf (F058)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x40)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, ByteAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F059,   64
                        }

                        Local3 = RefOf (F059)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   5,
                            F05A,   65
                        }

                        Local3 = RefOf (F05A)
                        Local4 = RefOf (G000)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, ByteAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F05B,   69
                        }

                        Local3 = RefOf (F05B)
                        Local4 = RefOf (G001)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   5,
                            F05C,   129
                        }

                        Local3 = RefOf (F05C)
                        Local4 = RefOf (G002)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, ByteAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F05D,   256
                        }

                        Local3 = RefOf (F05D)
                        Local4 = RefOf (G003)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   5,
                            F05E,   1023
                        }

                        Local3 = RefOf (F05E)
                        Local4 = RefOf (G004)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, ByteAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F05F,   1983
                        }

                        Local3 = RefOf (F05F)
                        Local4 = RefOf (G005)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x06)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, ByteAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F060,   1
                        }

                        Local3 = RefOf (F060)
                        Local4 = RefOf (G006)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   6,
                            F061,   6
                        }

                        Local3 = RefOf (F061)
                        Local4 = RefOf (G007)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, ByteAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F062,   7
                        }

                        Local3 = RefOf (F062)
                        Local4 = RefOf (G008)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   6,
                            F063,   8
                        }

                        Local3 = RefOf (F063)
                        Local4 = RefOf (G009)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, ByteAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F064,   9
                        }

                        Local3 = RefOf (F064)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   6,
                            F065,   31
                        }

                        Local3 = RefOf (F065)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, ByteAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F066,   32
                        }

                        Local3 = RefOf (F066)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   6,
                            F067,   33
                        }

                        Local3 = RefOf (F067)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, ByteAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F068,   63
                        }

                        Local3 = RefOf (F068)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   6,
                            F069,   64
                        }

                        Local3 = RefOf (F069)
                        Local4 = RefOf (G000)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, ByteAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F06A,   65
                        }

                        Local3 = RefOf (F06A)
                        Local4 = RefOf (G001)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   6,
                            F06B,   69
                        }

                        Local3 = RefOf (F06B)
                        Local4 = RefOf (G002)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, ByteAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F06C,   129
                        }

                        Local3 = RefOf (F06C)
                        Local4 = RefOf (G003)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   6,
                            F06D,   256
                        }

                        Local3 = RefOf (F06D)
                        Local4 = RefOf (G004)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, ByteAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F06E,   1023
                        }

                        Local3 = RefOf (F06E)
                        Local4 = RefOf (G005)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   6,
                            F06F,   1983
                        }

                        Local3 = RefOf (F06F)
                        Local4 = RefOf (G006)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x07)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   7,
                            F070,   1
                        }

                        Local3 = RefOf (F070)
                        Local4 = RefOf (G007)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, ByteAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F071,   6
                        }

                        Local3 = RefOf (F071)
                        Local4 = RefOf (G008)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   7,
                            F072,   7
                        }

                        Local3 = RefOf (F072)
                        Local4 = RefOf (G009)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, ByteAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F073,   8
                        }

                        Local3 = RefOf (F073)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   7,
                            F074,   9
                        }

                        Local3 = RefOf (F074)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, ByteAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F075,   31
                        }

                        Local3 = RefOf (F075)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   7,
                            F076,   32
                        }

                        Local3 = RefOf (F076)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x21)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, ByteAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F077,   33
                        }

                        Local3 = RefOf (F077)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   7,
                            F078,   63
                        }

                        Local3 = RefOf (F078)
                        Local4 = RefOf (G000)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, ByteAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F079,   64
                        }

                        Local3 = RefOf (F079)
                        Local4 = RefOf (G001)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   7,
                            F07A,   65
                        }

                        Local3 = RefOf (F07A)
                        Local4 = RefOf (G002)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, ByteAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F07B,   69
                        }

                        Local3 = RefOf (F07B)
                        Local4 = RefOf (G003)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   7,
                            F07C,   129
                        }

                        Local3 = RefOf (F07C)
                        Local4 = RefOf (G004)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, ByteAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F07D,   256
                        }

                        Local3 = RefOf (F07D)
                        Local4 = RefOf (G005)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   7,
                            F07E,   1023
                        }

                        Local3 = RefOf (F07E)
                        Local4 = RefOf (G006)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, ByteAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F07F,   1983
                        }

                        Local3 = RefOf (F07F)
                        Local4 = RefOf (G007)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x08)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F080,   1
                        }

                        Local3 = RefOf (F080)
                        Local4 = RefOf (G008)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x01),
                            F081,   6
                        }

                        Local3 = RefOf (F081)
                        Local4 = RefOf (G009)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F082,   7
                        }

                        Local3 = RefOf (F082)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x01),
                            F083,   8
                        }

                        Local3 = RefOf (F083)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F084,   9
                        }

                        Local3 = RefOf (F084)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x01),
                            F085,   31
                        }

                        Local3 = RefOf (F085)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x20)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F086,   32
                        }

                        Local3 = RefOf (F086)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x01),
                            F087,   33
                        }

                        Local3 = RefOf (F087)
                        Local4 = RefOf (G000)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F088,   63
                        }

                        Local3 = RefOf (F088)
                        Local4 = RefOf (G001)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x01),
                            F089,   64
                        }

                        Local3 = RefOf (F089)
                        Local4 = RefOf (G002)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F08A,   65
                        }

                        Local3 = RefOf (F08A)
                        Local4 = RefOf (G003)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x01),
                            F08B,   69
                        }

                        Local3 = RefOf (F08B)
                        Local4 = RefOf (G004)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F08C,   129
                        }

                        Local3 = RefOf (F08C)
                        Local4 = RefOf (G005)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x01),
                            F08D,   256
                        }

                        Local3 = RefOf (F08D)
                        Local4 = RefOf (G006)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F08E,   1023
                        }

                        Local3 = RefOf (F08E)
                        Local4 = RefOf (G007)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x01),
                            F08F,   1983
                        }

                        Local3 = RefOf (F08F)
                        Local4 = RefOf (G008)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x09)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   9,
                            F090,   1
                        }

                        Local3 = RefOf (F090)
                        Local4 = RefOf (G009)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, ByteAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F091,   6
                        }

                        Local3 = RefOf (F091)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   9,
                            F092,   7
                        }

                        Local3 = RefOf (F092)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, ByteAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F093,   8
                        }

                        Local3 = RefOf (F093)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   9,
                            F094,   9
                        }

                        Local3 = RefOf (F094)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, ByteAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F095,   31
                        }

                        Local3 = RefOf (F095)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   9,
                            F096,   32
                        }

                        Local3 = RefOf (F096)
                        Local4 = RefOf (G000)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, ByteAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F097,   33
                        }

                        Local3 = RefOf (F097)
                        Local4 = RefOf (G001)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   9,
                            F098,   63
                        }

                        Local3 = RefOf (F098)
                        Local4 = RefOf (G002)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, ByteAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F099,   64
                        }

                        Local3 = RefOf (F099)
                        Local4 = RefOf (G003)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   9,
                            F09A,   65
                        }

                        Local3 = RefOf (F09A)
                        Local4 = RefOf (G004)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, ByteAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F09B,   69
                        }

                        Local3 = RefOf (F09B)
                        Local4 = RefOf (G005)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   9,
                            F09C,   129
                        }

                        Local3 = RefOf (F09C)
                        Local4 = RefOf (G006)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, ByteAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F09D,   256
                        }

                        Local3 = RefOf (F09D)
                        Local4 = RefOf (G007)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   9,
                            F09E,   1023
                        }

                        Local3 = RefOf (F09E)
                        Local4 = RefOf (G008)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, ByteAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F09F,   1983
                        }

                        Local3 = RefOf (F09F)
                        Local4 = RefOf (G009)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x1F)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A0,   1
                        }

                        Local3 = RefOf (F0A0)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0A1,   6
                        }

                        Local3 = RefOf (F0A1)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A2,   7
                        }

                        Local3 = RefOf (F0A2)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0A3,   8
                        }

                        Local3 = RefOf (F0A3)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x09)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A4,   9
                        }

                        Local3 = RefOf (F0A4)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0A5,   31
                        }

                        Local3 = RefOf (F0A5)
                        Local4 = RefOf (G000)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A6,   32
                        }

                        Local3 = RefOf (F0A6)
                        Local4 = RefOf (G001)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0A7,   33
                        }

                        Local3 = RefOf (F0A7)
                        Local4 = RefOf (G002)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A8,   63
                        }

                        Local3 = RefOf (F0A8)
                        Local4 = RefOf (G003)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0A9,   64
                        }

                        Local3 = RefOf (F0A9)
                        Local4 = RefOf (G004)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0AA,   65
                        }

                        Local3 = RefOf (F0AA)
                        Local4 = RefOf (G005)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0AB,   69
                        }

                        Local3 = RefOf (F0AB)
                        Local4 = RefOf (G006)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0AC,   129
                        }

                        Local3 = RefOf (F0AC)
                        Local4 = RefOf (G007)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0AD,   256
                        }

                        Local3 = RefOf (F0AD)
                        Local4 = RefOf (G008)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0AE,   1023
                        }

                        Local3 = RefOf (F0AE)
                        Local4 = RefOf (G009)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0AF,   1983
                        }

                        Local3 = RefOf (F0AF)
                        Local4 = RefOf (G00A)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x20)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x04),
                            F0B0,   1
                        }

                        Local3 = RefOf (F0B0)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0B1,   6
                        }

                        Local3 = RefOf (F0B1)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x04),
                            F0B2,   7
                        }

                        Local3 = RefOf (F0B2)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x08)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0B3,   8
                        }

                        Local3 = RefOf (F0B3)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x04),
                            F0B4,   9
                        }

                        Local3 = RefOf (F0B4)
                        Local4 = RefOf (G000)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0B5,   31
                        }

                        Local3 = RefOf (F0B5)
                        Local4 = RefOf (G001)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x04),
                            F0B6,   32
                        }

                        Local3 = RefOf (F0B6)
                        Local4 = RefOf (G002)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0B7,   33
                        }

                        Local3 = RefOf (F0B7)
                        Local4 = RefOf (G003)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x04),
                            F0B8,   63
                        }

                        Local3 = RefOf (F0B8)
                        Local4 = RefOf (G004)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0B9,   64
                        }

                        Local3 = RefOf (F0B9)
                        Local4 = RefOf (G005)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x04),
                            F0BA,   65
                        }

                        Local3 = RefOf (F0BA)
                        Local4 = RefOf (G006)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0BB,   69
                        }

                        Local3 = RefOf (F0BB)
                        Local4 = RefOf (G007)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x04),
                            F0BC,   129
                        }

                        Local3 = RefOf (F0BC)
                        Local4 = RefOf (G008)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0BD,   256
                        }

                        Local3 = RefOf (F0BD)
                        Local4 = RefOf (G009)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x04),
                            F0BE,   1023
                        }

                        Local3 = RefOf (F0BE)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0BF,   1983
                        }

                        Local3 = RefOf (F0BF)
                        Local4 = RefOf (G00B)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x21)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, ByteAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0C0,   1
                        }

                        Local3 = RefOf (F0C0)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   33,
                            F0C1,   6
                        }

                        Local3 = RefOf (F0C1)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x07)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, ByteAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0C2,   7
                        }

                        Local3 = RefOf (F0C2)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   33,
                            F0C3,   8
                        }

                        Local3 = RefOf (F0C3)
                        Local4 = RefOf (G000)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, ByteAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0C4,   9
                        }

                        Local3 = RefOf (F0C4)
                        Local4 = RefOf (G001)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   33,
                            F0C5,   31
                        }

                        Local3 = RefOf (F0C5)
                        Local4 = RefOf (G002)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, ByteAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0C6,   32
                        }

                        Local3 = RefOf (F0C6)
                        Local4 = RefOf (G003)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   33,
                            F0C7,   33
                        }

                        Local3 = RefOf (F0C7)
                        Local4 = RefOf (G004)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, ByteAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0C8,   63
                        }

                        Local3 = RefOf (F0C8)
                        Local4 = RefOf (G005)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   33,
                            F0C9,   64
                        }

                        Local3 = RefOf (F0C9)
                        Local4 = RefOf (G006)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, ByteAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0CA,   65
                        }

                        Local3 = RefOf (F0CA)
                        Local4 = RefOf (G007)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   33,
                            F0CB,   69
                        }

                        Local3 = RefOf (F0CB)
                        Local4 = RefOf (G008)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, ByteAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0CC,   129
                        }

                        Local3 = RefOf (F0CC)
                        Local4 = RefOf (G009)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   33,
                            F0CD,   256
                        }

                        Local3 = RefOf (F0CD)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, ByteAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0CE,   1023
                        }

                        Local3 = RefOf (F0CE)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   33,
                            F0CF,   1983
                        }

                        Local3 = RefOf (F0CF)
                        Local4 = RefOf (G00C)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x3F)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   63,
                            F0D0,   1
                        }

                        Local3 = RefOf (F0D0)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x06)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, ByteAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0D1,   6
                        }

                        Local3 = RefOf (F0D1)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   63,
                            F0D2,   7
                        }

                        Local3 = RefOf (F0D2)
                        Local4 = RefOf (G000)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, ByteAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0D3,   8
                        }

                        Local3 = RefOf (F0D3)
                        Local4 = RefOf (G001)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   63,
                            F0D4,   9
                        }

                        Local3 = RefOf (F0D4)
                        Local4 = RefOf (G002)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, ByteAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0D5,   31
                        }

                        Local3 = RefOf (F0D5)
                        Local4 = RefOf (G003)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   63,
                            F0D6,   32
                        }

                        Local3 = RefOf (F0D6)
                        Local4 = RefOf (G004)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, ByteAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0D7,   33
                        }

                        Local3 = RefOf (F0D7)
                        Local4 = RefOf (G005)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   63,
                            F0D8,   63
                        }

                        Local3 = RefOf (F0D8)
                        Local4 = RefOf (G006)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, ByteAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0D9,   64
                        }

                        Local3 = RefOf (F0D9)
                        Local4 = RefOf (G007)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   63,
                            F0DA,   65
                        }

                        Local3 = RefOf (F0DA)
                        Local4 = RefOf (G008)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, ByteAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0DB,   69
                        }

                        Local3 = RefOf (F0DB)
                        Local4 = RefOf (G009)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   63,
                            F0DC,   129
                        }

                        Local3 = RefOf (F0DC)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, ByteAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0DD,   256
                        }

                        Local3 = RefOf (F0DD)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                                ,   63,
                            F0DE,   1023
                        }

                        Local3 = RefOf (F0DE)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, ByteAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0DF,   1983
                        }

                        Local3 = RefOf (F0DF)
                        Local4 = RefOf (G00D)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x40)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0E0,   1
                        }

                        Local3 = RefOf (F0E0)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x08),
                            F0E1,   6
                        }

                        Local3 = RefOf (F0E1)
                        Local4 = RefOf (G000)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0E2,   7
                        }

                        Local3 = RefOf (F0E2)
                        Local4 = RefOf (G001)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x08),
                            F0E3,   8
                        }

                        Local3 = RefOf (F0E3)
                        Local4 = RefOf (G002)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0E4,   9
                        }

                        Local3 = RefOf (F0E4)
                        Local4 = RefOf (G003)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x08),
                            F0E5,   31
                        }

                        Local3 = RefOf (F0E5)
                        Local4 = RefOf (G004)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0E6,   32
                        }

                        Local3 = RefOf (F0E6)
                        Local4 = RefOf (G005)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x08),
                            F0E7,   33
                        }

                        Local3 = RefOf (F0E7)
                        Local4 = RefOf (G006)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0E8,   63
                        }

                        Local3 = RefOf (F0E8)
                        Local4 = RefOf (G007)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x08),
                            F0E9,   64
                        }

                        Local3 = RefOf (F0E9)
                        Local4 = RefOf (G008)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0EA,   65
                        }

                        Local3 = RefOf (F0EA)
                        Local4 = RefOf (G009)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x08),
                            F0EB,   69
                        }

                        Local3 = RefOf (F0EB)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0EC,   129
                        }

                        Local3 = RefOf (F0EC)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x08),
                            F0ED,   256
                        }

                        Local3 = RefOf (F0ED)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0EE,   1023
                        }

                        Local3 = RefOf (F0EE)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x08),
                            F0EF,   1983
                        }

                        Local3 = RefOf (F0EF)
                        Local4 = RefOf (G00E)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x41)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0F0,   1
                        }

                        Local3 = RefOf (F0F0)
                        Local4 = RefOf (G000)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F1,   6
                        }

                        Local3 = RefOf (F0F1)
                        Local4 = RefOf (G001)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0F2,   7
                        }

                        Local3 = RefOf (F0F2)
                        Local4 = RefOf (G002)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F3,   8
                        }

                        Local3 = RefOf (F0F3)
                        Local4 = RefOf (G003)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0F4,   9
                        }

                        Local3 = RefOf (F0F4)
                        Local4 = RefOf (G004)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F5,   31
                        }

                        Local3 = RefOf (F0F5)
                        Local4 = RefOf (G005)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0F6,   32
                        }

                        Local3 = RefOf (F0F6)
                        Local4 = RefOf (G006)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F7,   33
                        }

                        Local3 = RefOf (F0F7)
                        Local4 = RefOf (G007)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0F8,   63
                        }

                        Local3 = RefOf (F0F8)
                        Local4 = RefOf (G008)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F9,   64
                        }

                        Local3 = RefOf (F0F9)
                        Local4 = RefOf (G009)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0FA,   65
                        }

                        Local3 = RefOf (F0FA)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0FB,   69
                        }

                        Local3 = RefOf (F0FB)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0FC,   129
                        }

                        Local3 = RefOf (F0FC)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0FD,   256
                        }

                        Local3 = RefOf (F0FD)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0FE,   1023
                        }

                        Local3 = RefOf (F0FE)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0FF,   1983
                        }

                        Local3 = RefOf (F0FF)
                        Local4 = RefOf (G000)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Default
            {
                ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                Return (Zero)
            }

        }

        FCP0 [0x00] = 0x02
        FCP0 [0x01] = RefOf (BNK0)
        FCP0 [0x02] = Local2
        M72D (Arg0, Local3, Arg2, Arg3, Arg4, Arg5, Local4)
        FCP0 [0x00] = 0x00
    }

    /* Create BankField Unit */
    /* (WordAcc, NoLock, WriteAsOnes) */
    Method (M7D1, 6, Serialized)
    {
        OperationRegion (OPRB, SystemIO, 0x00, 0x09)
        OperationRegion (OPR0, SystemIO, 0x0B, 0x0100)
        Field (OPRB, ByteAcc, NoLock, Preserve)
        {
            BNK0,   8
        }

        BankField (OPR0, BNK0, 0x00, ByteAcc, NoLock, Preserve)
        {
            G000,   2048
        }

        BankField (OPR0, BNK0, 0x01, ByteAcc, NoLock, Preserve)
        {
            G001,   2048
        }

        BankField (OPR0, BNK0, 0x02, ByteAcc, NoLock, Preserve)
        {
            G002,   2048
        }

        BankField (OPR0, BNK0, 0x03, ByteAcc, NoLock, Preserve)
        {
            G003,   2048
        }

        BankField (OPR0, BNK0, 0x04, ByteAcc, NoLock, Preserve)
        {
            G004,   2048
        }

        BankField (OPR0, BNK0, 0x05, ByteAcc, NoLock, Preserve)
        {
            G005,   2048
        }

        BankField (OPR0, BNK0, 0x06, ByteAcc, NoLock, Preserve)
        {
            G006,   2048
        }

        BankField (OPR0, BNK0, 0x07, ByteAcc, NoLock, Preserve)
        {
            G007,   2048
        }

        BankField (OPR0, BNK0, 0x08, ByteAcc, NoLock, Preserve)
        {
            G008,   2048
        }

        BankField (OPR0, BNK0, 0x09, ByteAcc, NoLock, Preserve)
        {
            G009,   2048
        }

        BankField (OPR0, BNK0, 0x3F, ByteAcc, NoLock, Preserve)
        {
            G00A,   2048
        }

        BankField (OPR0, BNK0, 0x40, ByteAcc, NoLock, Preserve)
        {
            G00B,   2048
        }

        BankField (OPR0, BNK0, 0x7F, ByteAcc, NoLock, Preserve)
        {
            G00C,   2048
        }

        BankField (OPR0, BNK0, 0x80, ByteAcc, NoLock, Preserve)
        {
            G00D,   2048
        }

        BankField (OPR0, BNK0, 0xFF, DWordAcc, NoLock, Preserve)
        {
            G00E,   2048
        }

        Concatenate (Arg0, "-m7d1", Arg0)
        Switch (ToInteger (Arg2))
        {
            Case (0x00)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                            F000,   1
                        }

                        Local3 = RefOf (F000)
                        Local4 = RefOf (G000)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, WordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x00),
                            F001,   6
                        }

                        Local3 = RefOf (F001)
                        Local4 = RefOf (G001)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                            F002,   7
                        }

                        Local3 = RefOf (F002)
                        Local4 = RefOf (G002)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, DWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x00),
                            F003,   8
                        }

                        Local3 = RefOf (F003)
                        Local4 = RefOf (G003)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                            F004,   9
                        }

                        Local3 = RefOf (F004)
                        Local4 = RefOf (G004)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, QWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x00),
                            F005,   31
                        }

                        Local3 = RefOf (F005)
                        Local4 = RefOf (G005)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                            F006,   32
                        }

                        Local3 = RefOf (F006)
                        Local4 = RefOf (G006)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, AnyAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x00),
                            F007,   33
                        }

                        Local3 = RefOf (F007)
                        Local4 = RefOf (G007)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                            F008,   63
                        }

                        Local3 = RefOf (F008)
                        Local4 = RefOf (G008)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, ByteAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x00),
                            F009,   64
                        }

                        Local3 = RefOf (F009)
                        Local4 = RefOf (G009)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                            F00A,   65
                        }

                        Local3 = RefOf (F00A)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, WordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x00),
                            F00B,   69
                        }

                        Local3 = RefOf (F00B)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                            F00C,   129
                        }

                        Local3 = RefOf (F00C)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x00),
                            F00D,   256
                        }

                        Local3 = RefOf (F00D)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                            F00E,   1023
                        }

                        Local3 = RefOf (F00E)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x00),
                            F00F,   1983
                        }

                        Local3 = RefOf (F00F)
                        Local4 = RefOf (G000)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x01)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, AnyAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   1,
                            F010,   1
                        }

                        Local3 = RefOf (F010)
                        Local4 = RefOf (G001)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   1,
                            F011,   6
                        }

                        Local3 = RefOf (F011)
                        Local4 = RefOf (G002)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, ByteAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   1,
                            F012,   7
                        }

                        Local3 = RefOf (F012)
                        Local4 = RefOf (G003)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   1,
                            F013,   8
                        }

                        Local3 = RefOf (F013)
                        Local4 = RefOf (G004)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, WordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   1,
                            F014,   9
                        }

                        Local3 = RefOf (F014)
                        Local4 = RefOf (G005)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   1,
                            F015,   31
                        }

                        Local3 = RefOf (F015)
                        Local4 = RefOf (G006)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, DWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   1,
                            F016,   32
                        }

                        Local3 = RefOf (F016)
                        Local4 = RefOf (G007)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   1,
                            F017,   33
                        }

                        Local3 = RefOf (F017)
                        Local4 = RefOf (G008)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, QWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   1,
                            F018,   63
                        }

                        Local3 = RefOf (F018)
                        Local4 = RefOf (G009)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   1,
                            F019,   64
                        }

                        Local3 = RefOf (F019)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, AnyAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   1,
                            F01A,   65
                        }

                        Local3 = RefOf (F01A)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   1,
                            F01B,   69
                        }

                        Local3 = RefOf (F01B)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, ByteAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   1,
                            F01C,   129
                        }

                        Local3 = RefOf (F01C)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   1,
                            F01D,   256
                        }

                        Local3 = RefOf (F01D)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   1,
                            F01E,   1023
                        }

                        Local3 = RefOf (F01E)
                        Local4 = RefOf (G000)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   1,
                            F01F,   1983
                        }

                        Local3 = RefOf (F01F)
                        Local4 = RefOf (G001)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x02)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   2,
                            F020,   1
                        }

                        Local3 = RefOf (F020)
                        Local4 = RefOf (G002)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, DWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   2,
                            F021,   6
                        }

                        Local3 = RefOf (F021)
                        Local4 = RefOf (G003)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   2,
                            F022,   7
                        }

                        Local3 = RefOf (F022)
                        Local4 = RefOf (G004)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, QWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   2,
                            F023,   8
                        }

                        Local3 = RefOf (F023)
                        Local4 = RefOf (G005)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   2,
                            F024,   9
                        }

                        Local3 = RefOf (F024)
                        Local4 = RefOf (G006)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, AnyAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   2,
                            F025,   31
                        }

                        Local3 = RefOf (F025)
                        Local4 = RefOf (G007)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   2,
                            F026,   32
                        }

                        Local3 = RefOf (F026)
                        Local4 = RefOf (G008)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, ByteAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   2,
                            F027,   33
                        }

                        Local3 = RefOf (F027)
                        Local4 = RefOf (G009)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   2,
                            F028,   63
                        }

                        Local3 = RefOf (F028)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, WordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   2,
                            F029,   64
                        }

                        Local3 = RefOf (F029)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   2,
                            F02A,   65
                        }

                        Local3 = RefOf (F02A)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   2,
                            F02B,   69
                        }

                        Local3 = RefOf (F02B)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x81)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   2,
                            F02C,   129
                        }

                        Local3 = RefOf (F02C)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   2,
                            F02D,   256
                        }

                        Local3 = RefOf (F02D)
                        Local4 = RefOf (G000)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   2,
                            F02E,   1023
                        }

                        Local3 = RefOf (F02E)
                        Local4 = RefOf (G001)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, AnyAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   2,
                            F02F,   1983
                        }

                        Local3 = RefOf (F02F)
                        Local4 = RefOf (G002)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x03)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, ByteAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   3,
                            F030,   1
                        }

                        Local3 = RefOf (F030)
                        Local4 = RefOf (G003)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   3,
                            F031,   6
                        }

                        Local3 = RefOf (F031)
                        Local4 = RefOf (G004)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, WordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   3,
                            F032,   7
                        }

                        Local3 = RefOf (F032)
                        Local4 = RefOf (G005)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   3,
                            F033,   8
                        }

                        Local3 = RefOf (F033)
                        Local4 = RefOf (G006)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, DWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   3,
                            F034,   9
                        }

                        Local3 = RefOf (F034)
                        Local4 = RefOf (G007)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   3,
                            F035,   31
                        }

                        Local3 = RefOf (F035)
                        Local4 = RefOf (G008)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, QWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   3,
                            F036,   32
                        }

                        Local3 = RefOf (F036)
                        Local4 = RefOf (G009)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   3,
                            F037,   33
                        }

                        Local3 = RefOf (F037)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, AnyAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   3,
                            F038,   63
                        }

                        Local3 = RefOf (F038)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   3,
                            F039,   64
                        }

                        Local3 = RefOf (F039)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, ByteAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   3,
                            F03A,   65
                        }

                        Local3 = RefOf (F03A)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x45)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   3,
                            F03B,   69
                        }

                        Local3 = RefOf (F03B)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   3,
                            F03C,   129
                        }

                        Local3 = RefOf (F03C)
                        Local4 = RefOf (G000)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   3,
                            F03D,   256
                        }

                        Local3 = RefOf (F03D)
                        Local4 = RefOf (G001)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, DWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   3,
                            F03E,   1023
                        }

                        Local3 = RefOf (F03E)
                        Local4 = RefOf (G002)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   3,
                            F03F,   1983
                        }

                        Local3 = RefOf (F03F)
                        Local4 = RefOf (G003)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x04)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   4,
                            F040,   1
                        }

                        Local3 = RefOf (F040)
                        Local4 = RefOf (G004)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, QWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   4,
                            F041,   6
                        }

                        Local3 = RefOf (F041)
                        Local4 = RefOf (G005)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   4,
                            F042,   7
                        }

                        Local3 = RefOf (F042)
                        Local4 = RefOf (G006)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, AnyAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   4,
                            F043,   8
                        }

                        Local3 = RefOf (F043)
                        Local4 = RefOf (G007)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   4,
                            F044,   9
                        }

                        Local3 = RefOf (F044)
                        Local4 = RefOf (G008)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, ByteAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   4,
                            F045,   31
                        }

                        Local3 = RefOf (F045)
                        Local4 = RefOf (G009)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   4,
                            F046,   32
                        }

                        Local3 = RefOf (F046)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, WordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   4,
                            F047,   33
                        }

                        Local3 = RefOf (F047)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   4,
                            F048,   63
                        }

                        Local3 = RefOf (F048)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   4,
                            F049,   64
                        }

                        Local3 = RefOf (F049)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x41)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   4,
                            F04A,   65
                        }

                        Local3 = RefOf (F04A)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   4,
                            F04B,   69
                        }

                        Local3 = RefOf (F04B)
                        Local4 = RefOf (G000)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   4,
                            F04C,   129
                        }

                        Local3 = RefOf (F04C)
                        Local4 = RefOf (G001)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, AnyAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   4,
                            F04D,   256
                        }

                        Local3 = RefOf (F04D)
                        Local4 = RefOf (G002)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   4,
                            F04E,   1023
                        }

                        Local3 = RefOf (F04E)
                        Local4 = RefOf (G003)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, ByteAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   4,
                            F04F,   1983
                        }

                        Local3 = RefOf (F04F)
                        Local4 = RefOf (G004)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x05)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, WordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   5,
                            F050,   1
                        }

                        Local3 = RefOf (F050)
                        Local4 = RefOf (G005)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   5,
                            F051,   6
                        }

                        Local3 = RefOf (F051)
                        Local4 = RefOf (G006)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, DWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   5,
                            F052,   7
                        }

                        Local3 = RefOf (F052)
                        Local4 = RefOf (G007)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   5,
                            F053,   8
                        }

                        Local3 = RefOf (F053)
                        Local4 = RefOf (G008)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, QWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   5,
                            F054,   9
                        }

                        Local3 = RefOf (F054)
                        Local4 = RefOf (G009)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   5,
                            F055,   31
                        }

                        Local3 = RefOf (F055)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, AnyAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   5,
                            F056,   32
                        }

                        Local3 = RefOf (F056)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   5,
                            F057,   33
                        }

                        Local3 = RefOf (F057)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, ByteAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   5,
                            F058,   63
                        }

                        Local3 = RefOf (F058)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x40)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   5,
                            F059,   64
                        }

                        Local3 = RefOf (F059)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   5,
                            F05A,   65
                        }

                        Local3 = RefOf (F05A)
                        Local4 = RefOf (G000)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   5,
                            F05B,   69
                        }

                        Local3 = RefOf (F05B)
                        Local4 = RefOf (G001)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, DWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   5,
                            F05C,   129
                        }

                        Local3 = RefOf (F05C)
                        Local4 = RefOf (G002)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   5,
                            F05D,   256
                        }

                        Local3 = RefOf (F05D)
                        Local4 = RefOf (G003)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, QWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   5,
                            F05E,   1023
                        }

                        Local3 = RefOf (F05E)
                        Local4 = RefOf (G004)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   5,
                            F05F,   1983
                        }

                        Local3 = RefOf (F05F)
                        Local4 = RefOf (G005)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x06)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   6,
                            F060,   1
                        }

                        Local3 = RefOf (F060)
                        Local4 = RefOf (G006)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, AnyAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   6,
                            F061,   6
                        }

                        Local3 = RefOf (F061)
                        Local4 = RefOf (G007)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   6,
                            F062,   7
                        }

                        Local3 = RefOf (F062)
                        Local4 = RefOf (G008)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, ByteAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   6,
                            F063,   8
                        }

                        Local3 = RefOf (F063)
                        Local4 = RefOf (G009)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   6,
                            F064,   9
                        }

                        Local3 = RefOf (F064)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, WordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   6,
                            F065,   31
                        }

                        Local3 = RefOf (F065)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   6,
                            F066,   32
                        }

                        Local3 = RefOf (F066)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   6,
                            F067,   33
                        }

                        Local3 = RefOf (F067)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   6,
                            F068,   63
                        }

                        Local3 = RefOf (F068)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   6,
                            F069,   64
                        }

                        Local3 = RefOf (F069)
                        Local4 = RefOf (G000)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   6,
                            F06A,   65
                        }

                        Local3 = RefOf (F06A)
                        Local4 = RefOf (G001)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, AnyAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   6,
                            F06B,   69
                        }

                        Local3 = RefOf (F06B)
                        Local4 = RefOf (G002)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   6,
                            F06C,   129
                        }

                        Local3 = RefOf (F06C)
                        Local4 = RefOf (G003)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, ByteAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   6,
                            F06D,   256
                        }

                        Local3 = RefOf (F06D)
                        Local4 = RefOf (G004)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   6,
                            F06E,   1023
                        }

                        Local3 = RefOf (F06E)
                        Local4 = RefOf (G005)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, WordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   6,
                            F06F,   1983
                        }

                        Local3 = RefOf (F06F)
                        Local4 = RefOf (G006)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x07)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, DWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   7,
                            F070,   1
                        }

                        Local3 = RefOf (F070)
                        Local4 = RefOf (G007)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   7,
                            F071,   6
                        }

                        Local3 = RefOf (F071)
                        Local4 = RefOf (G008)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, QWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   7,
                            F072,   7
                        }

                        Local3 = RefOf (F072)
                        Local4 = RefOf (G009)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   7,
                            F073,   8
                        }

                        Local3 = RefOf (F073)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, AnyAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   7,
                            F074,   9
                        }

                        Local3 = RefOf (F074)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   7,
                            F075,   31
                        }

                        Local3 = RefOf (F075)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, ByteAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   7,
                            F076,   32
                        }

                        Local3 = RefOf (F076)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x21)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   7,
                            F077,   33
                        }

                        Local3 = RefOf (F077)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   7,
                            F078,   63
                        }

                        Local3 = RefOf (F078)
                        Local4 = RefOf (G000)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   7,
                            F079,   64
                        }

                        Local3 = RefOf (F079)
                        Local4 = RefOf (G001)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, DWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   7,
                            F07A,   65
                        }

                        Local3 = RefOf (F07A)
                        Local4 = RefOf (G002)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   7,
                            F07B,   69
                        }

                        Local3 = RefOf (F07B)
                        Local4 = RefOf (G003)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, QWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   7,
                            F07C,   129
                        }

                        Local3 = RefOf (F07C)
                        Local4 = RefOf (G004)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   7,
                            F07D,   256
                        }

                        Local3 = RefOf (F07D)
                        Local4 = RefOf (G005)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, AnyAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   7,
                            F07E,   1023
                        }

                        Local3 = RefOf (F07E)
                        Local4 = RefOf (G006)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   7,
                            F07F,   1983
                        }

                        Local3 = RefOf (F07F)
                        Local4 = RefOf (G007)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x08)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x01),
                            F080,   1
                        }

                        Local3 = RefOf (F080)
                        Local4 = RefOf (G008)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, ByteAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x01),
                            F081,   6
                        }

                        Local3 = RefOf (F081)
                        Local4 = RefOf (G009)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x01),
                            F082,   7
                        }

                        Local3 = RefOf (F082)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, WordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x01),
                            F083,   8
                        }

                        Local3 = RefOf (F083)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x01),
                            F084,   9
                        }

                        Local3 = RefOf (F084)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x01),
                            F085,   31
                        }

                        Local3 = RefOf (F085)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x20)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x01),
                            F086,   32
                        }

                        Local3 = RefOf (F086)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x01),
                            F087,   33
                        }

                        Local3 = RefOf (F087)
                        Local4 = RefOf (G000)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x01),
                            F088,   63
                        }

                        Local3 = RefOf (F088)
                        Local4 = RefOf (G001)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, AnyAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x01),
                            F089,   64
                        }

                        Local3 = RefOf (F089)
                        Local4 = RefOf (G002)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x01),
                            F08A,   65
                        }

                        Local3 = RefOf (F08A)
                        Local4 = RefOf (G003)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, ByteAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x01),
                            F08B,   69
                        }

                        Local3 = RefOf (F08B)
                        Local4 = RefOf (G004)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x01),
                            F08C,   129
                        }

                        Local3 = RefOf (F08C)
                        Local4 = RefOf (G005)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, WordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x01),
                            F08D,   256
                        }

                        Local3 = RefOf (F08D)
                        Local4 = RefOf (G006)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x01),
                            F08E,   1023
                        }

                        Local3 = RefOf (F08E)
                        Local4 = RefOf (G007)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, DWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x01),
                            F08F,   1983
                        }

                        Local3 = RefOf (F08F)
                        Local4 = RefOf (G008)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x09)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, QWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   9,
                            F090,   1
                        }

                        Local3 = RefOf (F090)
                        Local4 = RefOf (G009)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   9,
                            F091,   6
                        }

                        Local3 = RefOf (F091)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, AnyAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   9,
                            F092,   7
                        }

                        Local3 = RefOf (F092)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   9,
                            F093,   8
                        }

                        Local3 = RefOf (F093)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, ByteAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   9,
                            F094,   9
                        }

                        Local3 = RefOf (F094)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   9,
                            F095,   31
                        }

                        Local3 = RefOf (F095)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   9,
                            F096,   32
                        }

                        Local3 = RefOf (F096)
                        Local4 = RefOf (G000)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   9,
                            F097,   33
                        }

                        Local3 = RefOf (F097)
                        Local4 = RefOf (G001)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, DWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   9,
                            F098,   63
                        }

                        Local3 = RefOf (F098)
                        Local4 = RefOf (G002)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   9,
                            F099,   64
                        }

                        Local3 = RefOf (F099)
                        Local4 = RefOf (G003)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, QWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   9,
                            F09A,   65
                        }

                        Local3 = RefOf (F09A)
                        Local4 = RefOf (G004)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   9,
                            F09B,   69
                        }

                        Local3 = RefOf (F09B)
                        Local4 = RefOf (G005)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, AnyAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   9,
                            F09C,   129
                        }

                        Local3 = RefOf (F09C)
                        Local4 = RefOf (G006)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   9,
                            F09D,   256
                        }

                        Local3 = RefOf (F09D)
                        Local4 = RefOf (G007)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, ByteAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   9,
                            F09E,   1023
                        }

                        Local3 = RefOf (F09E)
                        Local4 = RefOf (G008)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   9,
                            F09F,   1983
                        }

                        Local3 = RefOf (F09F)
                        Local4 = RefOf (G009)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x1F)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A0,   1
                        }

                        Local3 = RefOf (F0A0)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, WordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0A1,   6
                        }

                        Local3 = RefOf (F0A1)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A2,   7
                        }

                        Local3 = RefOf (F0A2)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0A3,   8
                        }

                        Local3 = RefOf (F0A3)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x09)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A4,   9
                        }

                        Local3 = RefOf (F0A4)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0A5,   31
                        }

                        Local3 = RefOf (F0A5)
                        Local4 = RefOf (G000)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A6,   32
                        }

                        Local3 = RefOf (F0A6)
                        Local4 = RefOf (G001)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, AnyAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0A7,   33
                        }

                        Local3 = RefOf (F0A7)
                        Local4 = RefOf (G002)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A8,   63
                        }

                        Local3 = RefOf (F0A8)
                        Local4 = RefOf (G003)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, ByteAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0A9,   64
                        }

                        Local3 = RefOf (F0A9)
                        Local4 = RefOf (G004)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x03),
                                ,   7,
                            F0AA,   65
                        }

                        Local3 = RefOf (F0AA)
                        Local4 = RefOf (G005)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, WordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0AB,   69
                        }

                        Local3 = RefOf (F0AB)
                        Local4 = RefOf (G006)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x03),
                                ,   7,
                            F0AC,   129
                        }

                        Local3 = RefOf (F0AC)
                        Local4 = RefOf (G007)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, DWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0AD,   256
                        }

                        Local3 = RefOf (F0AD)
                        Local4 = RefOf (G008)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x03),
                                ,   7,
                            F0AE,   1023
                        }

                        Local3 = RefOf (F0AE)
                        Local4 = RefOf (G009)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, QWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0AF,   1983
                        }

                        Local3 = RefOf (F0AF)
                        Local4 = RefOf (G00A)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x20)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, AnyAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x04),
                            F0B0,   1
                        }

                        Local3 = RefOf (F0B0)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x04),
                            F0B1,   6
                        }

                        Local3 = RefOf (F0B1)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, ByteAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x04),
                            F0B2,   7
                        }

                        Local3 = RefOf (F0B2)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x08)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x04),
                            F0B3,   8
                        }

                        Local3 = RefOf (F0B3)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x04),
                            F0B4,   9
                        }

                        Local3 = RefOf (F0B4)
                        Local4 = RefOf (G000)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x04),
                            F0B5,   31
                        }

                        Local3 = RefOf (F0B5)
                        Local4 = RefOf (G001)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, DWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x04),
                            F0B6,   32
                        }

                        Local3 = RefOf (F0B6)
                        Local4 = RefOf (G002)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x04),
                            F0B7,   33
                        }

                        Local3 = RefOf (F0B7)
                        Local4 = RefOf (G003)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, QWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x04),
                            F0B8,   63
                        }

                        Local3 = RefOf (F0B8)
                        Local4 = RefOf (G004)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x04),
                            F0B9,   64
                        }

                        Local3 = RefOf (F0B9)
                        Local4 = RefOf (G005)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, AnyAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x04),
                            F0BA,   65
                        }

                        Local3 = RefOf (F0BA)
                        Local4 = RefOf (G006)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x04),
                            F0BB,   69
                        }

                        Local3 = RefOf (F0BB)
                        Local4 = RefOf (G007)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, ByteAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x04),
                            F0BC,   129
                        }

                        Local3 = RefOf (F0BC)
                        Local4 = RefOf (G008)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x04),
                            F0BD,   256
                        }

                        Local3 = RefOf (F0BD)
                        Local4 = RefOf (G009)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, WordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x04),
                            F0BE,   1023
                        }

                        Local3 = RefOf (F0BE)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x04),
                            F0BF,   1983
                        }

                        Local3 = RefOf (F0BF)
                        Local4 = RefOf (G00B)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x21)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   33,
                            F0C0,   1
                        }

                        Local3 = RefOf (F0C0)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   33,
                            F0C1,   6
                        }

                        Local3 = RefOf (F0C1)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x07)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   33,
                            F0C2,   7
                        }

                        Local3 = RefOf (F0C2)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   33,
                            F0C3,   8
                        }

                        Local3 = RefOf (F0C3)
                        Local4 = RefOf (G000)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   33,
                            F0C4,   9
                        }

                        Local3 = RefOf (F0C4)
                        Local4 = RefOf (G001)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, AnyAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   33,
                            F0C5,   31
                        }

                        Local3 = RefOf (F0C5)
                        Local4 = RefOf (G002)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   33,
                            F0C6,   32
                        }

                        Local3 = RefOf (F0C6)
                        Local4 = RefOf (G003)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, ByteAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   33,
                            F0C7,   33
                        }

                        Local3 = RefOf (F0C7)
                        Local4 = RefOf (G004)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   33,
                            F0C8,   63
                        }

                        Local3 = RefOf (F0C8)
                        Local4 = RefOf (G005)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, WordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   33,
                            F0C9,   64
                        }

                        Local3 = RefOf (F0C9)
                        Local4 = RefOf (G006)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   33,
                            F0CA,   65
                        }

                        Local3 = RefOf (F0CA)
                        Local4 = RefOf (G007)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, DWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   33,
                            F0CB,   69
                        }

                        Local3 = RefOf (F0CB)
                        Local4 = RefOf (G008)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   33,
                            F0CC,   129
                        }

                        Local3 = RefOf (F0CC)
                        Local4 = RefOf (G009)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, QWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   33,
                            F0CD,   256
                        }

                        Local3 = RefOf (F0CD)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   33,
                            F0CE,   1023
                        }

                        Local3 = RefOf (F0CE)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, AnyAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   33,
                            F0CF,   1983
                        }

                        Local3 = RefOf (F0CF)
                        Local4 = RefOf (G00C)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x3F)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, WordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   63,
                            F0D0,   1
                        }

                        Local3 = RefOf (F0D0)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x06)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, ByteAcc, NoLock, WriteAsOnes)
                        {
                                ,   63,
                            F0D1,   6
                        }

                        Local3 = RefOf (F0D1)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   63,
                            F0D2,   7
                        }

                        Local3 = RefOf (F0D2)
                        Local4 = RefOf (G000)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   63,
                            F0D3,   8
                        }

                        Local3 = RefOf (F0D3)
                        Local4 = RefOf (G001)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, DWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   63,
                            F0D4,   9
                        }

                        Local3 = RefOf (F0D4)
                        Local4 = RefOf (G002)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   63,
                            F0D5,   31
                        }

                        Local3 = RefOf (F0D5)
                        Local4 = RefOf (G003)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, QWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   63,
                            F0D6,   32
                        }

                        Local3 = RefOf (F0D6)
                        Local4 = RefOf (G004)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   63,
                            F0D7,   33
                        }

                        Local3 = RefOf (F0D7)
                        Local4 = RefOf (G005)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, AnyAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   63,
                            F0D8,   63
                        }

                        Local3 = RefOf (F0D8)
                        Local4 = RefOf (G006)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   63,
                            F0D9,   64
                        }

                        Local3 = RefOf (F0D9)
                        Local4 = RefOf (G007)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, ByteAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   63,
                            F0DA,   65
                        }

                        Local3 = RefOf (F0DA)
                        Local4 = RefOf (G008)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   63,
                            F0DB,   69
                        }

                        Local3 = RefOf (F0DB)
                        Local4 = RefOf (G009)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, WordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   63,
                            F0DC,   129
                        }

                        Local3 = RefOf (F0DC)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   63,
                            F0DD,   256
                        }

                        Local3 = RefOf (F0DD)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, DWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                                ,   63,
                            F0DE,   1023
                        }

                        Local3 = RefOf (F0DE)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   63,
                            F0DF,   1983
                        }

                        Local3 = RefOf (F0DF)
                        Local4 = RefOf (G00D)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x40)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                            F0E0,   1
                        }

                        Local3 = RefOf (F0E0)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x08),
                            F0E1,   6
                        }

                        Local3 = RefOf (F0E1)
                        Local4 = RefOf (G000)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                            F0E2,   7
                        }

                        Local3 = RefOf (F0E2)
                        Local4 = RefOf (G001)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, AnyAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x08),
                            F0E3,   8
                        }

                        Local3 = RefOf (F0E3)
                        Local4 = RefOf (G002)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                            F0E4,   9
                        }

                        Local3 = RefOf (F0E4)
                        Local4 = RefOf (G003)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, ByteAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x08),
                            F0E5,   31
                        }

                        Local3 = RefOf (F0E5)
                        Local4 = RefOf (G004)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                            F0E6,   32
                        }

                        Local3 = RefOf (F0E6)
                        Local4 = RefOf (G005)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, WordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x08),
                            F0E7,   33
                        }

                        Local3 = RefOf (F0E7)
                        Local4 = RefOf (G006)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                            F0E8,   63
                        }

                        Local3 = RefOf (F0E8)
                        Local4 = RefOf (G007)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, DWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x08),
                            F0E9,   64
                        }

                        Local3 = RefOf (F0E9)
                        Local4 = RefOf (G008)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                            F0EA,   65
                        }

                        Local3 = RefOf (F0EA)
                        Local4 = RefOf (G009)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, QWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x08),
                            F0EB,   69
                        }

                        Local3 = RefOf (F0EB)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                            F0EC,   129
                        }

                        Local3 = RefOf (F0EC)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, AnyAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x08),
                            F0ED,   256
                        }

                        Local3 = RefOf (F0ED)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                            F0EE,   1023
                        }

                        Local3 = RefOf (F0EE)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, ByteAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x08),
                            F0EF,   1983
                        }

                        Local3 = RefOf (F0EF)
                        Local4 = RefOf (G00E)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x41)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0F0,   1
                        }

                        Local3 = RefOf (F0F0)
                        Local4 = RefOf (G000)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F1,   6
                        }

                        Local3 = RefOf (F0F1)
                        Local4 = RefOf (G001)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, DWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0F2,   7
                        }

                        Local3 = RefOf (F0F2)
                        Local4 = RefOf (G002)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F3,   8
                        }

                        Local3 = RefOf (F0F3)
                        Local4 = RefOf (G003)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, QWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0F4,   9
                        }

                        Local3 = RefOf (F0F4)
                        Local4 = RefOf (G004)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F5,   31
                        }

                        Local3 = RefOf (F0F5)
                        Local4 = RefOf (G005)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, AnyAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0F6,   32
                        }

                        Local3 = RefOf (F0F6)
                        Local4 = RefOf (G006)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F7,   33
                        }

                        Local3 = RefOf (F0F7)
                        Local4 = RefOf (G007)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, ByteAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0F8,   63
                        }

                        Local3 = RefOf (F0F8)
                        Local4 = RefOf (G008)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F9,   64
                        }

                        Local3 = RefOf (F0F9)
                        Local4 = RefOf (G009)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, WordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0FA,   65
                        }

                        Local3 = RefOf (F0FA)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                                ,   1,
                            F0FB,   69
                        }

                        Local3 = RefOf (F0FB)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, DWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0FC,   129
                        }

                        Local3 = RefOf (F0FC)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                                ,   1,
                            F0FD,   256
                        }

                        Local3 = RefOf (F0FD)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, QWordAcc, NoLock, WriteAsOnes)
                        {
                            AccessAs (WordAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0FE,   1023
                        }

                        Local3 = RefOf (F0FE)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                                ,   1,
                            F0FF,   1983
                        }

                        Local3 = RefOf (F0FF)
                        Local4 = RefOf (G000)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Default
            {
                ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                Return (Zero)
            }

        }

        FCP0 [0x00] = 0x02
        FCP0 [0x01] = RefOf (BNK0)
        FCP0 [0x02] = Local2
        M72D (Arg0, Local3, Arg2, Arg3, Arg4, Arg5, Local4)
        FCP0 [0x00] = 0x00
    }

    /* Create BankField Unit */
    /* (DWordAcc, NoLock, WriteAsZeros) */
    Method (M7D2, 6, Serialized)
    {
        OperationRegion (OPRB, SystemIO, 0x00, 0x09)
        OperationRegion (OPR0, SystemIO, 0x0B, 0x0100)
        Field (OPRB, ByteAcc, NoLock, Preserve)
        {
            BNK0,   8
        }

        BankField (OPR0, BNK0, 0x00, ByteAcc, NoLock, Preserve)
        {
            G000,   2048
        }

        BankField (OPR0, BNK0, 0x01, ByteAcc, NoLock, Preserve)
        {
            G001,   2048
        }

        BankField (OPR0, BNK0, 0x02, ByteAcc, NoLock, Preserve)
        {
            G002,   2048
        }

        BankField (OPR0, BNK0, 0x03, ByteAcc, NoLock, Preserve)
        {
            G003,   2048
        }

        BankField (OPR0, BNK0, 0x04, ByteAcc, NoLock, Preserve)
        {
            G004,   2048
        }

        BankField (OPR0, BNK0, 0x05, ByteAcc, NoLock, Preserve)
        {
            G005,   2048
        }

        BankField (OPR0, BNK0, 0x06, ByteAcc, NoLock, Preserve)
        {
            G006,   2048
        }

        BankField (OPR0, BNK0, 0x07, ByteAcc, NoLock, Preserve)
        {
            G007,   2048
        }

        BankField (OPR0, BNK0, 0x08, ByteAcc, NoLock, Preserve)
        {
            G008,   2048
        }

        BankField (OPR0, BNK0, 0x09, ByteAcc, NoLock, Preserve)
        {
            G009,   2048
        }

        BankField (OPR0, BNK0, 0x3F, ByteAcc, NoLock, Preserve)
        {
            G00A,   2048
        }

        BankField (OPR0, BNK0, 0x40, ByteAcc, NoLock, Preserve)
        {
            G00B,   2048
        }

        BankField (OPR0, BNK0, 0x7F, ByteAcc, NoLock, Preserve)
        {
            G00C,   2048
        }

        BankField (OPR0, BNK0, 0x80, ByteAcc, NoLock, Preserve)
        {
            G00D,   2048
        }

        BankField (OPR0, BNK0, 0xFF, ByteAcc, NoLock, Preserve)
        {
            G00E,   2048
        }

        Concatenate (Arg0, "-m7d2", Arg0)
        Switch (ToInteger (Arg2))
        {
            Case (0x00)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                            F000,   1
                        }

                        Local3 = RefOf (F000)
                        Local4 = RefOf (G000)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, WordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x00),
                            F001,   6
                        }

                        Local3 = RefOf (F001)
                        Local4 = RefOf (G001)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                            F002,   7
                        }

                        Local3 = RefOf (F002)
                        Local4 = RefOf (G002)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, DWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x00),
                            F003,   8
                        }

                        Local3 = RefOf (F003)
                        Local4 = RefOf (G003)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                            F004,   9
                        }

                        Local3 = RefOf (F004)
                        Local4 = RefOf (G004)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, QWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x00),
                            F005,   31
                        }

                        Local3 = RefOf (F005)
                        Local4 = RefOf (G005)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                            F006,   32
                        }

                        Local3 = RefOf (F006)
                        Local4 = RefOf (G006)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, AnyAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x00),
                            F007,   33
                        }

                        Local3 = RefOf (F007)
                        Local4 = RefOf (G007)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                            F008,   63
                        }

                        Local3 = RefOf (F008)
                        Local4 = RefOf (G008)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, ByteAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x00),
                            F009,   64
                        }

                        Local3 = RefOf (F009)
                        Local4 = RefOf (G009)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                            F00A,   65
                        }

                        Local3 = RefOf (F00A)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, WordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x00),
                            F00B,   69
                        }

                        Local3 = RefOf (F00B)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                            F00C,   129
                        }

                        Local3 = RefOf (F00C)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x00),
                            F00D,   256
                        }

                        Local3 = RefOf (F00D)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                            F00E,   1023
                        }

                        Local3 = RefOf (F00E)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x00),
                            F00F,   1983
                        }

                        Local3 = RefOf (F00F)
                        Local4 = RefOf (G000)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x01)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, AnyAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   1,
                            F010,   1
                        }

                        Local3 = RefOf (F010)
                        Local4 = RefOf (G001)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   1,
                            F011,   6
                        }

                        Local3 = RefOf (F011)
                        Local4 = RefOf (G002)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, ByteAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   1,
                            F012,   7
                        }

                        Local3 = RefOf (F012)
                        Local4 = RefOf (G003)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   1,
                            F013,   8
                        }

                        Local3 = RefOf (F013)
                        Local4 = RefOf (G004)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, WordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   1,
                            F014,   9
                        }

                        Local3 = RefOf (F014)
                        Local4 = RefOf (G005)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   1,
                            F015,   31
                        }

                        Local3 = RefOf (F015)
                        Local4 = RefOf (G006)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, DWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   1,
                            F016,   32
                        }

                        Local3 = RefOf (F016)
                        Local4 = RefOf (G007)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   1,
                            F017,   33
                        }

                        Local3 = RefOf (F017)
                        Local4 = RefOf (G008)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, QWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   1,
                            F018,   63
                        }

                        Local3 = RefOf (F018)
                        Local4 = RefOf (G009)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   1,
                            F019,   64
                        }

                        Local3 = RefOf (F019)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, AnyAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   1,
                            F01A,   65
                        }

                        Local3 = RefOf (F01A)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   1,
                            F01B,   69
                        }

                        Local3 = RefOf (F01B)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, ByteAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   1,
                            F01C,   129
                        }

                        Local3 = RefOf (F01C)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   1,
                            F01D,   256
                        }

                        Local3 = RefOf (F01D)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   1,
                            F01E,   1023
                        }

                        Local3 = RefOf (F01E)
                        Local4 = RefOf (G000)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   1,
                            F01F,   1983
                        }

                        Local3 = RefOf (F01F)
                        Local4 = RefOf (G001)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x02)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   2,
                            F020,   1
                        }

                        Local3 = RefOf (F020)
                        Local4 = RefOf (G002)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, DWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   2,
                            F021,   6
                        }

                        Local3 = RefOf (F021)
                        Local4 = RefOf (G003)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   2,
                            F022,   7
                        }

                        Local3 = RefOf (F022)
                        Local4 = RefOf (G004)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, QWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   2,
                            F023,   8
                        }

                        Local3 = RefOf (F023)
                        Local4 = RefOf (G005)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   2,
                            F024,   9
                        }

                        Local3 = RefOf (F024)
                        Local4 = RefOf (G006)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, AnyAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   2,
                            F025,   31
                        }

                        Local3 = RefOf (F025)
                        Local4 = RefOf (G007)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   2,
                            F026,   32
                        }

                        Local3 = RefOf (F026)
                        Local4 = RefOf (G008)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, ByteAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   2,
                            F027,   33
                        }

                        Local3 = RefOf (F027)
                        Local4 = RefOf (G009)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   2,
                            F028,   63
                        }

                        Local3 = RefOf (F028)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, WordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   2,
                            F029,   64
                        }

                        Local3 = RefOf (F029)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   2,
                            F02A,   65
                        }

                        Local3 = RefOf (F02A)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   2,
                            F02B,   69
                        }

                        Local3 = RefOf (F02B)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x81)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   2,
                            F02C,   129
                        }

                        Local3 = RefOf (F02C)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   2,
                            F02D,   256
                        }

                        Local3 = RefOf (F02D)
                        Local4 = RefOf (G000)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   2,
                            F02E,   1023
                        }

                        Local3 = RefOf (F02E)
                        Local4 = RefOf (G001)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, AnyAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   2,
                            F02F,   1983
                        }

                        Local3 = RefOf (F02F)
                        Local4 = RefOf (G002)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x03)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, ByteAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   3,
                            F030,   1
                        }

                        Local3 = RefOf (F030)
                        Local4 = RefOf (G003)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   3,
                            F031,   6
                        }

                        Local3 = RefOf (F031)
                        Local4 = RefOf (G004)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, WordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   3,
                            F032,   7
                        }

                        Local3 = RefOf (F032)
                        Local4 = RefOf (G005)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   3,
                            F033,   8
                        }

                        Local3 = RefOf (F033)
                        Local4 = RefOf (G006)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, DWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   3,
                            F034,   9
                        }

                        Local3 = RefOf (F034)
                        Local4 = RefOf (G007)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   3,
                            F035,   31
                        }

                        Local3 = RefOf (F035)
                        Local4 = RefOf (G008)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, QWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   3,
                            F036,   32
                        }

                        Local3 = RefOf (F036)
                        Local4 = RefOf (G009)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   3,
                            F037,   33
                        }

                        Local3 = RefOf (F037)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, AnyAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   3,
                            F038,   63
                        }

                        Local3 = RefOf (F038)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   3,
                            F039,   64
                        }

                        Local3 = RefOf (F039)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, ByteAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   3,
                            F03A,   65
                        }

                        Local3 = RefOf (F03A)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x45)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   3,
                            F03B,   69
                        }

                        Local3 = RefOf (F03B)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   3,
                            F03C,   129
                        }

                        Local3 = RefOf (F03C)
                        Local4 = RefOf (G000)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   3,
                            F03D,   256
                        }

                        Local3 = RefOf (F03D)
                        Local4 = RefOf (G001)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, DWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   3,
                            F03E,   1023
                        }

                        Local3 = RefOf (F03E)
                        Local4 = RefOf (G002)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   3,
                            F03F,   1983
                        }

                        Local3 = RefOf (F03F)
                        Local4 = RefOf (G003)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x04)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   4,
                            F040,   1
                        }

                        Local3 = RefOf (F040)
                        Local4 = RefOf (G004)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, QWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   4,
                            F041,   6
                        }

                        Local3 = RefOf (F041)
                        Local4 = RefOf (G005)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   4,
                            F042,   7
                        }

                        Local3 = RefOf (F042)
                        Local4 = RefOf (G006)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, AnyAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   4,
                            F043,   8
                        }

                        Local3 = RefOf (F043)
                        Local4 = RefOf (G007)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   4,
                            F044,   9
                        }

                        Local3 = RefOf (F044)
                        Local4 = RefOf (G008)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, ByteAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   4,
                            F045,   31
                        }

                        Local3 = RefOf (F045)
                        Local4 = RefOf (G009)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   4,
                            F046,   32
                        }

                        Local3 = RefOf (F046)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, WordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   4,
                            F047,   33
                        }

                        Local3 = RefOf (F047)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   4,
                            F048,   63
                        }

                        Local3 = RefOf (F048)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   4,
                            F049,   64
                        }

                        Local3 = RefOf (F049)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x41)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   4,
                            F04A,   65
                        }

                        Local3 = RefOf (F04A)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   4,
                            F04B,   69
                        }

                        Local3 = RefOf (F04B)
                        Local4 = RefOf (G000)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   4,
                            F04C,   129
                        }

                        Local3 = RefOf (F04C)
                        Local4 = RefOf (G001)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, AnyAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   4,
                            F04D,   256
                        }

                        Local3 = RefOf (F04D)
                        Local4 = RefOf (G002)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   4,
                            F04E,   1023
                        }

                        Local3 = RefOf (F04E)
                        Local4 = RefOf (G003)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, ByteAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   4,
                            F04F,   1983
                        }

                        Local3 = RefOf (F04F)
                        Local4 = RefOf (G004)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x05)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, WordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   5,
                            F050,   1
                        }

                        Local3 = RefOf (F050)
                        Local4 = RefOf (G005)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   5,
                            F051,   6
                        }

                        Local3 = RefOf (F051)
                        Local4 = RefOf (G006)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, DWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   5,
                            F052,   7
                        }

                        Local3 = RefOf (F052)
                        Local4 = RefOf (G007)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   5,
                            F053,   8
                        }

                        Local3 = RefOf (F053)
                        Local4 = RefOf (G008)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, QWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   5,
                            F054,   9
                        }

                        Local3 = RefOf (F054)
                        Local4 = RefOf (G009)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   5,
                            F055,   31
                        }

                        Local3 = RefOf (F055)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, AnyAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   5,
                            F056,   32
                        }

                        Local3 = RefOf (F056)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   5,
                            F057,   33
                        }

                        Local3 = RefOf (F057)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, ByteAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   5,
                            F058,   63
                        }

                        Local3 = RefOf (F058)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x40)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   5,
                            F059,   64
                        }

                        Local3 = RefOf (F059)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   5,
                            F05A,   65
                        }

                        Local3 = RefOf (F05A)
                        Local4 = RefOf (G000)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   5,
                            F05B,   69
                        }

                        Local3 = RefOf (F05B)
                        Local4 = RefOf (G001)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, DWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   5,
                            F05C,   129
                        }

                        Local3 = RefOf (F05C)
                        Local4 = RefOf (G002)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   5,
                            F05D,   256
                        }

                        Local3 = RefOf (F05D)
                        Local4 = RefOf (G003)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, QWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   5,
                            F05E,   1023
                        }

                        Local3 = RefOf (F05E)
                        Local4 = RefOf (G004)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   5,
                            F05F,   1983
                        }

                        Local3 = RefOf (F05F)
                        Local4 = RefOf (G005)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x06)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   6,
                            F060,   1
                        }

                        Local3 = RefOf (F060)
                        Local4 = RefOf (G006)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, AnyAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   6,
                            F061,   6
                        }

                        Local3 = RefOf (F061)
                        Local4 = RefOf (G007)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   6,
                            F062,   7
                        }

                        Local3 = RefOf (F062)
                        Local4 = RefOf (G008)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, ByteAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   6,
                            F063,   8
                        }

                        Local3 = RefOf (F063)
                        Local4 = RefOf (G009)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   6,
                            F064,   9
                        }

                        Local3 = RefOf (F064)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, WordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   6,
                            F065,   31
                        }

                        Local3 = RefOf (F065)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   6,
                            F066,   32
                        }

                        Local3 = RefOf (F066)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   6,
                            F067,   33
                        }

                        Local3 = RefOf (F067)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   6,
                            F068,   63
                        }

                        Local3 = RefOf (F068)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   6,
                            F069,   64
                        }

                        Local3 = RefOf (F069)
                        Local4 = RefOf (G000)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   6,
                            F06A,   65
                        }

                        Local3 = RefOf (F06A)
                        Local4 = RefOf (G001)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, AnyAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   6,
                            F06B,   69
                        }

                        Local3 = RefOf (F06B)
                        Local4 = RefOf (G002)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   6,
                            F06C,   129
                        }

                        Local3 = RefOf (F06C)
                        Local4 = RefOf (G003)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, ByteAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   6,
                            F06D,   256
                        }

                        Local3 = RefOf (F06D)
                        Local4 = RefOf (G004)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   6,
                            F06E,   1023
                        }

                        Local3 = RefOf (F06E)
                        Local4 = RefOf (G005)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, WordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   6,
                            F06F,   1983
                        }

                        Local3 = RefOf (F06F)
                        Local4 = RefOf (G006)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x07)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, DWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   7,
                            F070,   1
                        }

                        Local3 = RefOf (F070)
                        Local4 = RefOf (G007)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   7,
                            F071,   6
                        }

                        Local3 = RefOf (F071)
                        Local4 = RefOf (G008)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, QWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   7,
                            F072,   7
                        }

                        Local3 = RefOf (F072)
                        Local4 = RefOf (G009)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   7,
                            F073,   8
                        }

                        Local3 = RefOf (F073)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, AnyAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   7,
                            F074,   9
                        }

                        Local3 = RefOf (F074)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   7,
                            F075,   31
                        }

                        Local3 = RefOf (F075)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, ByteAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   7,
                            F076,   32
                        }

                        Local3 = RefOf (F076)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x21)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   7,
                            F077,   33
                        }

                        Local3 = RefOf (F077)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   7,
                            F078,   63
                        }

                        Local3 = RefOf (F078)
                        Local4 = RefOf (G000)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   7,
                            F079,   64
                        }

                        Local3 = RefOf (F079)
                        Local4 = RefOf (G001)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, DWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   7,
                            F07A,   65
                        }

                        Local3 = RefOf (F07A)
                        Local4 = RefOf (G002)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   7,
                            F07B,   69
                        }

                        Local3 = RefOf (F07B)
                        Local4 = RefOf (G003)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, QWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   7,
                            F07C,   129
                        }

                        Local3 = RefOf (F07C)
                        Local4 = RefOf (G004)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   7,
                            F07D,   256
                        }

                        Local3 = RefOf (F07D)
                        Local4 = RefOf (G005)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, AnyAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   7,
                            F07E,   1023
                        }

                        Local3 = RefOf (F07E)
                        Local4 = RefOf (G006)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   7,
                            F07F,   1983
                        }

                        Local3 = RefOf (F07F)
                        Local4 = RefOf (G007)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x08)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x01),
                            F080,   1
                        }

                        Local3 = RefOf (F080)
                        Local4 = RefOf (G008)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, ByteAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x01),
                            F081,   6
                        }

                        Local3 = RefOf (F081)
                        Local4 = RefOf (G009)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x01),
                            F082,   7
                        }

                        Local3 = RefOf (F082)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, WordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x01),
                            F083,   8
                        }

                        Local3 = RefOf (F083)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x01),
                            F084,   9
                        }

                        Local3 = RefOf (F084)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x01),
                            F085,   31
                        }

                        Local3 = RefOf (F085)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x20)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x01),
                            F086,   32
                        }

                        Local3 = RefOf (F086)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x01),
                            F087,   33
                        }

                        Local3 = RefOf (F087)
                        Local4 = RefOf (G000)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x01),
                            F088,   63
                        }

                        Local3 = RefOf (F088)
                        Local4 = RefOf (G001)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, AnyAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x01),
                            F089,   64
                        }

                        Local3 = RefOf (F089)
                        Local4 = RefOf (G002)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x01),
                            F08A,   65
                        }

                        Local3 = RefOf (F08A)
                        Local4 = RefOf (G003)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, ByteAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x01),
                            F08B,   69
                        }

                        Local3 = RefOf (F08B)
                        Local4 = RefOf (G004)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x01),
                            F08C,   129
                        }

                        Local3 = RefOf (F08C)
                        Local4 = RefOf (G005)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, WordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x01),
                            F08D,   256
                        }

                        Local3 = RefOf (F08D)
                        Local4 = RefOf (G006)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x01),
                            F08E,   1023
                        }

                        Local3 = RefOf (F08E)
                        Local4 = RefOf (G007)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, DWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x01),
                            F08F,   1983
                        }

                        Local3 = RefOf (F08F)
                        Local4 = RefOf (G008)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x09)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, QWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   9,
                            F090,   1
                        }

                        Local3 = RefOf (F090)
                        Local4 = RefOf (G009)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   9,
                            F091,   6
                        }

                        Local3 = RefOf (F091)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, AnyAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   9,
                            F092,   7
                        }

                        Local3 = RefOf (F092)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   9,
                            F093,   8
                        }

                        Local3 = RefOf (F093)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, ByteAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   9,
                            F094,   9
                        }

                        Local3 = RefOf (F094)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   9,
                            F095,   31
                        }

                        Local3 = RefOf (F095)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   9,
                            F096,   32
                        }

                        Local3 = RefOf (F096)
                        Local4 = RefOf (G000)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   9,
                            F097,   33
                        }

                        Local3 = RefOf (F097)
                        Local4 = RefOf (G001)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, DWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   9,
                            F098,   63
                        }

                        Local3 = RefOf (F098)
                        Local4 = RefOf (G002)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   9,
                            F099,   64
                        }

                        Local3 = RefOf (F099)
                        Local4 = RefOf (G003)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, QWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   9,
                            F09A,   65
                        }

                        Local3 = RefOf (F09A)
                        Local4 = RefOf (G004)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   9,
                            F09B,   69
                        }

                        Local3 = RefOf (F09B)
                        Local4 = RefOf (G005)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, AnyAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   9,
                            F09C,   129
                        }

                        Local3 = RefOf (F09C)
                        Local4 = RefOf (G006)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   9,
                            F09D,   256
                        }

                        Local3 = RefOf (F09D)
                        Local4 = RefOf (G007)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, ByteAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   9,
                            F09E,   1023
                        }

                        Local3 = RefOf (F09E)
                        Local4 = RefOf (G008)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   9,
                            F09F,   1983
                        }

                        Local3 = RefOf (F09F)
                        Local4 = RefOf (G009)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x1F)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A0,   1
                        }

                        Local3 = RefOf (F0A0)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, WordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0A1,   6
                        }

                        Local3 = RefOf (F0A1)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A2,   7
                        }

                        Local3 = RefOf (F0A2)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0A3,   8
                        }

                        Local3 = RefOf (F0A3)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x09)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A4,   9
                        }

                        Local3 = RefOf (F0A4)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0A5,   31
                        }

                        Local3 = RefOf (F0A5)
                        Local4 = RefOf (G000)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A6,   32
                        }

                        Local3 = RefOf (F0A6)
                        Local4 = RefOf (G001)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, AnyAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0A7,   33
                        }

                        Local3 = RefOf (F0A7)
                        Local4 = RefOf (G002)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A8,   63
                        }

                        Local3 = RefOf (F0A8)
                        Local4 = RefOf (G003)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, ByteAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0A9,   64
                        }

                        Local3 = RefOf (F0A9)
                        Local4 = RefOf (G004)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x03),
                                ,   7,
                            F0AA,   65
                        }

                        Local3 = RefOf (F0AA)
                        Local4 = RefOf (G005)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, WordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0AB,   69
                        }

                        Local3 = RefOf (F0AB)
                        Local4 = RefOf (G006)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x03),
                                ,   7,
                            F0AC,   129
                        }

                        Local3 = RefOf (F0AC)
                        Local4 = RefOf (G007)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, DWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0AD,   256
                        }

                        Local3 = RefOf (F0AD)
                        Local4 = RefOf (G008)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x03),
                                ,   7,
                            F0AE,   1023
                        }

                        Local3 = RefOf (F0AE)
                        Local4 = RefOf (G009)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, QWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0AF,   1983
                        }

                        Local3 = RefOf (F0AF)
                        Local4 = RefOf (G00A)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x20)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, AnyAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x04),
                            F0B0,   1
                        }

                        Local3 = RefOf (F0B0)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x04),
                            F0B1,   6
                        }

                        Local3 = RefOf (F0B1)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, ByteAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x04),
                            F0B2,   7
                        }

                        Local3 = RefOf (F0B2)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x08)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x04),
                            F0B3,   8
                        }

                        Local3 = RefOf (F0B3)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x04),
                            F0B4,   9
                        }

                        Local3 = RefOf (F0B4)
                        Local4 = RefOf (G000)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x04),
                            F0B5,   31
                        }

                        Local3 = RefOf (F0B5)
                        Local4 = RefOf (G001)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, DWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x04),
                            F0B6,   32
                        }

                        Local3 = RefOf (F0B6)
                        Local4 = RefOf (G002)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x04),
                            F0B7,   33
                        }

                        Local3 = RefOf (F0B7)
                        Local4 = RefOf (G003)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, QWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x04),
                            F0B8,   63
                        }

                        Local3 = RefOf (F0B8)
                        Local4 = RefOf (G004)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x04),
                            F0B9,   64
                        }

                        Local3 = RefOf (F0B9)
                        Local4 = RefOf (G005)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, AnyAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x04),
                            F0BA,   65
                        }

                        Local3 = RefOf (F0BA)
                        Local4 = RefOf (G006)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x04),
                            F0BB,   69
                        }

                        Local3 = RefOf (F0BB)
                        Local4 = RefOf (G007)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, ByteAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x04),
                            F0BC,   129
                        }

                        Local3 = RefOf (F0BC)
                        Local4 = RefOf (G008)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x04),
                            F0BD,   256
                        }

                        Local3 = RefOf (F0BD)
                        Local4 = RefOf (G009)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, WordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x04),
                            F0BE,   1023
                        }

                        Local3 = RefOf (F0BE)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x04),
                            F0BF,   1983
                        }

                        Local3 = RefOf (F0BF)
                        Local4 = RefOf (G00B)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x21)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   33,
                            F0C0,   1
                        }

                        Local3 = RefOf (F0C0)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   33,
                            F0C1,   6
                        }

                        Local3 = RefOf (F0C1)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x07)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   33,
                            F0C2,   7
                        }

                        Local3 = RefOf (F0C2)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   33,
                            F0C3,   8
                        }

                        Local3 = RefOf (F0C3)
                        Local4 = RefOf (G000)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   33,
                            F0C4,   9
                        }

                        Local3 = RefOf (F0C4)
                        Local4 = RefOf (G001)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, AnyAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   33,
                            F0C5,   31
                        }

                        Local3 = RefOf (F0C5)
                        Local4 = RefOf (G002)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   33,
                            F0C6,   32
                        }

                        Local3 = RefOf (F0C6)
                        Local4 = RefOf (G003)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, ByteAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   33,
                            F0C7,   33
                        }

                        Local3 = RefOf (F0C7)
                        Local4 = RefOf (G004)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   33,
                            F0C8,   63
                        }

                        Local3 = RefOf (F0C8)
                        Local4 = RefOf (G005)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, WordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   33,
                            F0C9,   64
                        }

                        Local3 = RefOf (F0C9)
                        Local4 = RefOf (G006)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   33,
                            F0CA,   65
                        }

                        Local3 = RefOf (F0CA)
                        Local4 = RefOf (G007)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, DWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   33,
                            F0CB,   69
                        }

                        Local3 = RefOf (F0CB)
                        Local4 = RefOf (G008)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   33,
                            F0CC,   129
                        }

                        Local3 = RefOf (F0CC)
                        Local4 = RefOf (G009)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, QWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   33,
                            F0CD,   256
                        }

                        Local3 = RefOf (F0CD)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   33,
                            F0CE,   1023
                        }

                        Local3 = RefOf (F0CE)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, AnyAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   33,
                            F0CF,   1983
                        }

                        Local3 = RefOf (F0CF)
                        Local4 = RefOf (G00C)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x3F)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   63,
                            F0D0,   1
                        }

                        Local3 = RefOf (F0D0)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x06)
                    {
                        /* November 2011: Changed to DWordAcc from ByteAcc to enable */
                        /* correct operation ("Expected" buffer assumes DWordAcc) */
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   63,
                            F0D1,   6
                        }

                        Local3 = RefOf (F0D1)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, DWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   63,
                            F0D2,   7
                        }

                        Local3 = RefOf (F0D2)
                        Local4 = RefOf (G000)
                    }
                    Case (0x08)
                    {
                        /* November 2011: Changed to DWordAcc from WordAcc to enable */
                        /* correct operation ("Expected" buffer assumes DWordAcc) */
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   63,
                            F0D3,   8
                        }

                        Local3 = RefOf (F0D3)
                        Local4 = RefOf (G001)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, DWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   63,
                            F0D4,   9
                        }

                        Local3 = RefOf (F0D4)
                        Local4 = RefOf (G002)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   63,
                            F0D5,   31
                        }

                        Local3 = RefOf (F0D5)
                        Local4 = RefOf (G003)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, QWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   63,
                            F0D6,   32
                        }

                        Local3 = RefOf (F0D6)
                        Local4 = RefOf (G004)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   63,
                            F0D7,   33
                        }

                        Local3 = RefOf (F0D7)
                        Local4 = RefOf (G005)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, AnyAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   63,
                            F0D8,   63
                        }

                        Local3 = RefOf (F0D8)
                        Local4 = RefOf (G006)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   63,
                            F0D9,   64
                        }

                        Local3 = RefOf (F0D9)
                        Local4 = RefOf (G007)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, ByteAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   63,
                            F0DA,   65
                        }

                        Local3 = RefOf (F0DA)
                        Local4 = RefOf (G008)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   63,
                            F0DB,   69
                        }

                        Local3 = RefOf (F0DB)
                        Local4 = RefOf (G009)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, WordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   63,
                            F0DC,   129
                        }

                        Local3 = RefOf (F0DC)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   63,
                            F0DD,   256
                        }

                        Local3 = RefOf (F0DD)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, DWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                                ,   63,
                            F0DE,   1023
                        }

                        Local3 = RefOf (F0DE)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   63,
                            F0DF,   1983
                        }

                        Local3 = RefOf (F0DF)
                        Local4 = RefOf (G00D)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x40)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                            F0E0,   1
                        }

                        Local3 = RefOf (F0E0)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x08),
                            F0E1,   6
                        }

                        Local3 = RefOf (F0E1)
                        Local4 = RefOf (G000)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                            F0E2,   7
                        }

                        Local3 = RefOf (F0E2)
                        Local4 = RefOf (G001)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, AnyAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x08),
                            F0E3,   8
                        }

                        Local3 = RefOf (F0E3)
                        Local4 = RefOf (G002)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                            F0E4,   9
                        }

                        Local3 = RefOf (F0E4)
                        Local4 = RefOf (G003)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, ByteAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x08),
                            F0E5,   31
                        }

                        Local3 = RefOf (F0E5)
                        Local4 = RefOf (G004)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                            F0E6,   32
                        }

                        Local3 = RefOf (F0E6)
                        Local4 = RefOf (G005)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, WordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x08),
                            F0E7,   33
                        }

                        Local3 = RefOf (F0E7)
                        Local4 = RefOf (G006)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                            F0E8,   63
                        }

                        Local3 = RefOf (F0E8)
                        Local4 = RefOf (G007)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, DWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x08),
                            F0E9,   64
                        }

                        Local3 = RefOf (F0E9)
                        Local4 = RefOf (G008)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                            F0EA,   65
                        }

                        Local3 = RefOf (F0EA)
                        Local4 = RefOf (G009)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, QWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x08),
                            F0EB,   69
                        }

                        Local3 = RefOf (F0EB)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                            F0EC,   129
                        }

                        Local3 = RefOf (F0EC)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, AnyAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x08),
                            F0ED,   256
                        }

                        Local3 = RefOf (F0ED)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                            F0EE,   1023
                        }

                        Local3 = RefOf (F0EE)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, ByteAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x08),
                            F0EF,   1983
                        }

                        Local3 = RefOf (F0EF)
                        Local4 = RefOf (G00E)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x41)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0F0,   1
                        }

                        Local3 = RefOf (F0F0)
                        Local4 = RefOf (G000)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F1,   6
                        }

                        Local3 = RefOf (F0F1)
                        Local4 = RefOf (G001)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, DWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0F2,   7
                        }

                        Local3 = RefOf (F0F2)
                        Local4 = RefOf (G002)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F3,   8
                        }

                        Local3 = RefOf (F0F3)
                        Local4 = RefOf (G003)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, QWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0F4,   9
                        }

                        Local3 = RefOf (F0F4)
                        Local4 = RefOf (G004)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F5,   31
                        }

                        Local3 = RefOf (F0F5)
                        Local4 = RefOf (G005)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, AnyAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0F6,   32
                        }

                        Local3 = RefOf (F0F6)
                        Local4 = RefOf (G006)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F7,   33
                        }

                        Local3 = RefOf (F0F7)
                        Local4 = RefOf (G007)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, ByteAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0F8,   63
                        }

                        Local3 = RefOf (F0F8)
                        Local4 = RefOf (G008)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F9,   64
                        }

                        Local3 = RefOf (F0F9)
                        Local4 = RefOf (G009)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, WordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0FA,   65
                        }

                        Local3 = RefOf (F0FA)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                                ,   1,
                            F0FB,   69
                        }

                        Local3 = RefOf (F0FB)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, DWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0FC,   129
                        }

                        Local3 = RefOf (F0FC)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                                ,   1,
                            F0FD,   256
                        }

                        Local3 = RefOf (F0FD)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, QWordAcc, NoLock, WriteAsZeros)
                        {
                            AccessAs (DWordAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0FE,   1023
                        }

                        Local3 = RefOf (F0FE)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                                ,   1,
                            F0FF,   1983
                        }

                        Local3 = RefOf (F0FF)
                        Local4 = RefOf (G000)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Default
            {
                ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                Return (Zero)
            }

        }

        FCP0 [0x00] = 0x02
        FCP0 [0x01] = RefOf (BNK0)
        FCP0 [0x02] = Local2
        M72D (Arg0, Local3, Arg2, Arg3, Arg4, Arg5, Local4)
        FCP0 [0x00] = 0x00
    }

    /* Create BankField Unit */
    /* (QWordAcc, NoLock, Preserve) */
    Method (M7D3, 6, Serialized)
    {
        OperationRegion (OPRB, SystemIO, 0x00, 0x09)
        OperationRegion (OPR0, SystemIO, 0x0B, 0x0100)
        Field (OPRB, ByteAcc, NoLock, Preserve)
        {
            BNK0,   8
        }

        BankField (OPR0, BNK0, 0x00, ByteAcc, NoLock, Preserve)
        {
            G000,   2048
        }

        BankField (OPR0, BNK0, 0x01, ByteAcc, NoLock, Preserve)
        {
            G001,   2048
        }

        BankField (OPR0, BNK0, 0x02, ByteAcc, NoLock, Preserve)
        {
            G002,   2048
        }

        BankField (OPR0, BNK0, 0x03, ByteAcc, NoLock, Preserve)
        {
            G003,   2048
        }

        BankField (OPR0, BNK0, 0x04, ByteAcc, NoLock, Preserve)
        {
            G004,   2048
        }

        BankField (OPR0, BNK0, 0x05, ByteAcc, NoLock, Preserve)
        {
            G005,   2048
        }

        BankField (OPR0, BNK0, 0x06, ByteAcc, NoLock, Preserve)
        {
            G006,   2048
        }

        BankField (OPR0, BNK0, 0x07, ByteAcc, NoLock, Preserve)
        {
            G007,   2048
        }

        BankField (OPR0, BNK0, 0x08, ByteAcc, NoLock, Preserve)
        {
            G008,   2048
        }

        BankField (OPR0, BNK0, 0x09, ByteAcc, NoLock, Preserve)
        {
            G009,   2048
        }

        BankField (OPR0, BNK0, 0x3F, ByteAcc, NoLock, Preserve)
        {
            G00A,   2048
        }

        BankField (OPR0, BNK0, 0x40, ByteAcc, NoLock, Preserve)
        {
            G00B,   2048
        }

        BankField (OPR0, BNK0, 0x7F, ByteAcc, NoLock, Preserve)
        {
            G00C,   2048
        }

        BankField (OPR0, BNK0, 0x80, ByteAcc, NoLock, Preserve)
        {
            G00D,   2048
        }

        BankField (OPR0, BNK0, 0xFF, ByteAcc, NoLock, Preserve)
        {
            G00E,   2048
        }

        Concatenate (Arg0, "-m7d3", Arg0)
        Switch (ToInteger (Arg2))
        {
            Case (0x00)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F000,   1
                        }

                        Local3 = RefOf (F000)
                        Local4 = RefOf (G000)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x00),
                            F001,   6
                        }

                        Local3 = RefOf (F001)
                        Local4 = RefOf (G001)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F002,   7
                        }

                        Local3 = RefOf (F002)
                        Local4 = RefOf (G002)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x00),
                            F003,   8
                        }

                        Local3 = RefOf (F003)
                        Local4 = RefOf (G003)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F004,   9
                        }

                        Local3 = RefOf (F004)
                        Local4 = RefOf (G004)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x00),
                            F005,   31
                        }

                        Local3 = RefOf (F005)
                        Local4 = RefOf (G005)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F006,   32
                        }

                        Local3 = RefOf (F006)
                        Local4 = RefOf (G006)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x00),
                            F007,   33
                        }

                        Local3 = RefOf (F007)
                        Local4 = RefOf (G007)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F008,   63
                        }

                        Local3 = RefOf (F008)
                        Local4 = RefOf (G008)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x00),
                            F009,   64
                        }

                        Local3 = RefOf (F009)
                        Local4 = RefOf (G009)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F00A,   65
                        }

                        Local3 = RefOf (F00A)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x00),
                            F00B,   69
                        }

                        Local3 = RefOf (F00B)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F00C,   129
                        }

                        Local3 = RefOf (F00C)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x00),
                            F00D,   256
                        }

                        Local3 = RefOf (F00D)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F00E,   1023
                        }

                        Local3 = RefOf (F00E)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x00),
                            F00F,   1983
                        }

                        Local3 = RefOf (F00F)
                        Local4 = RefOf (G000)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x01)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   1,
                            F010,   1
                        }

                        Local3 = RefOf (F010)
                        Local4 = RefOf (G001)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, QWordAcc, NoLock, Preserve)
                        {
                                ,   1,
                            F011,   6
                        }

                        Local3 = RefOf (F011)
                        Local4 = RefOf (G002)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   1,
                            F012,   7
                        }

                        Local3 = RefOf (F012)
                        Local4 = RefOf (G003)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, QWordAcc, NoLock, Preserve)
                        {
                                ,   1,
                            F013,   8
                        }

                        Local3 = RefOf (F013)
                        Local4 = RefOf (G004)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   1,
                            F014,   9
                        }

                        Local3 = RefOf (F014)
                        Local4 = RefOf (G005)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, QWordAcc, NoLock, Preserve)
                        {
                                ,   1,
                            F015,   31
                        }

                        Local3 = RefOf (F015)
                        Local4 = RefOf (G006)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   1,
                            F016,   32
                        }

                        Local3 = RefOf (F016)
                        Local4 = RefOf (G007)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, QWordAcc, NoLock, Preserve)
                        {
                                ,   1,
                            F017,   33
                        }

                        Local3 = RefOf (F017)
                        Local4 = RefOf (G008)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   1,
                            F018,   63
                        }

                        Local3 = RefOf (F018)
                        Local4 = RefOf (G009)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, QWordAcc, NoLock, Preserve)
                        {
                                ,   1,
                            F019,   64
                        }

                        Local3 = RefOf (F019)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   1,
                            F01A,   65
                        }

                        Local3 = RefOf (F01A)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, QWordAcc, NoLock, Preserve)
                        {
                                ,   1,
                            F01B,   69
                        }

                        Local3 = RefOf (F01B)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   1,
                            F01C,   129
                        }

                        Local3 = RefOf (F01C)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, QWordAcc, NoLock, Preserve)
                        {
                                ,   1,
                            F01D,   256
                        }

                        Local3 = RefOf (F01D)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   1,
                            F01E,   1023
                        }

                        Local3 = RefOf (F01E)
                        Local4 = RefOf (G000)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, QWordAcc, NoLock, Preserve)
                        {
                                ,   1,
                            F01F,   1983
                        }

                        Local3 = RefOf (F01F)
                        Local4 = RefOf (G001)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x02)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, QWordAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F020,   1
                        }

                        Local3 = RefOf (F020)
                        Local4 = RefOf (G002)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   2,
                            F021,   6
                        }

                        Local3 = RefOf (F021)
                        Local4 = RefOf (G003)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, QWordAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F022,   7
                        }

                        Local3 = RefOf (F022)
                        Local4 = RefOf (G004)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   2,
                            F023,   8
                        }

                        Local3 = RefOf (F023)
                        Local4 = RefOf (G005)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, QWordAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F024,   9
                        }

                        Local3 = RefOf (F024)
                        Local4 = RefOf (G006)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   2,
                            F025,   31
                        }

                        Local3 = RefOf (F025)
                        Local4 = RefOf (G007)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, QWordAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F026,   32
                        }

                        Local3 = RefOf (F026)
                        Local4 = RefOf (G008)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   2,
                            F027,   33
                        }

                        Local3 = RefOf (F027)
                        Local4 = RefOf (G009)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, QWordAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F028,   63
                        }

                        Local3 = RefOf (F028)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   2,
                            F029,   64
                        }

                        Local3 = RefOf (F029)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, QWordAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F02A,   65
                        }

                        Local3 = RefOf (F02A)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   2,
                            F02B,   69
                        }

                        Local3 = RefOf (F02B)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x81)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, QWordAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F02C,   129
                        }

                        Local3 = RefOf (F02C)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   2,
                            F02D,   256
                        }

                        Local3 = RefOf (F02D)
                        Local4 = RefOf (G000)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, QWordAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F02E,   1023
                        }

                        Local3 = RefOf (F02E)
                        Local4 = RefOf (G001)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   2,
                            F02F,   1983
                        }

                        Local3 = RefOf (F02F)
                        Local4 = RefOf (G002)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x03)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   3,
                            F030,   1
                        }

                        Local3 = RefOf (F030)
                        Local4 = RefOf (G003)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, QWordAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F031,   6
                        }

                        Local3 = RefOf (F031)
                        Local4 = RefOf (G004)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   3,
                            F032,   7
                        }

                        Local3 = RefOf (F032)
                        Local4 = RefOf (G005)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, QWordAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F033,   8
                        }

                        Local3 = RefOf (F033)
                        Local4 = RefOf (G006)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   3,
                            F034,   9
                        }

                        Local3 = RefOf (F034)
                        Local4 = RefOf (G007)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, QWordAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F035,   31
                        }

                        Local3 = RefOf (F035)
                        Local4 = RefOf (G008)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   3,
                            F036,   32
                        }

                        Local3 = RefOf (F036)
                        Local4 = RefOf (G009)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, QWordAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F037,   33
                        }

                        Local3 = RefOf (F037)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   3,
                            F038,   63
                        }

                        Local3 = RefOf (F038)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, QWordAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F039,   64
                        }

                        Local3 = RefOf (F039)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   3,
                            F03A,   65
                        }

                        Local3 = RefOf (F03A)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x45)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, QWordAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F03B,   69
                        }

                        Local3 = RefOf (F03B)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   3,
                            F03C,   129
                        }

                        Local3 = RefOf (F03C)
                        Local4 = RefOf (G000)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, QWordAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F03D,   256
                        }

                        Local3 = RefOf (F03D)
                        Local4 = RefOf (G001)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   3,
                            F03E,   1023
                        }

                        Local3 = RefOf (F03E)
                        Local4 = RefOf (G002)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, QWordAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F03F,   1983
                        }

                        Local3 = RefOf (F03F)
                        Local4 = RefOf (G003)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x04)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, QWordAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F040,   1
                        }

                        Local3 = RefOf (F040)
                        Local4 = RefOf (G004)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   4,
                            F041,   6
                        }

                        Local3 = RefOf (F041)
                        Local4 = RefOf (G005)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, QWordAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F042,   7
                        }

                        Local3 = RefOf (F042)
                        Local4 = RefOf (G006)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   4,
                            F043,   8
                        }

                        Local3 = RefOf (F043)
                        Local4 = RefOf (G007)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, QWordAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F044,   9
                        }

                        Local3 = RefOf (F044)
                        Local4 = RefOf (G008)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   4,
                            F045,   31
                        }

                        Local3 = RefOf (F045)
                        Local4 = RefOf (G009)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, QWordAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F046,   32
                        }

                        Local3 = RefOf (F046)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   4,
                            F047,   33
                        }

                        Local3 = RefOf (F047)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, QWordAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F048,   63
                        }

                        Local3 = RefOf (F048)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   4,
                            F049,   64
                        }

                        Local3 = RefOf (F049)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x41)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, QWordAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F04A,   65
                        }

                        Local3 = RefOf (F04A)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   4,
                            F04B,   69
                        }

                        Local3 = RefOf (F04B)
                        Local4 = RefOf (G000)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, QWordAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F04C,   129
                        }

                        Local3 = RefOf (F04C)
                        Local4 = RefOf (G001)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   4,
                            F04D,   256
                        }

                        Local3 = RefOf (F04D)
                        Local4 = RefOf (G002)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, QWordAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F04E,   1023
                        }

                        Local3 = RefOf (F04E)
                        Local4 = RefOf (G003)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   4,
                            F04F,   1983
                        }

                        Local3 = RefOf (F04F)
                        Local4 = RefOf (G004)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x05)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   5,
                            F050,   1
                        }

                        Local3 = RefOf (F050)
                        Local4 = RefOf (G005)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, QWordAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F051,   6
                        }

                        Local3 = RefOf (F051)
                        Local4 = RefOf (G006)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   5,
                            F052,   7
                        }

                        Local3 = RefOf (F052)
                        Local4 = RefOf (G007)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, QWordAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F053,   8
                        }

                        Local3 = RefOf (F053)
                        Local4 = RefOf (G008)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   5,
                            F054,   9
                        }

                        Local3 = RefOf (F054)
                        Local4 = RefOf (G009)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, QWordAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F055,   31
                        }

                        Local3 = RefOf (F055)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   5,
                            F056,   32
                        }

                        Local3 = RefOf (F056)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, QWordAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F057,   33
                        }

                        Local3 = RefOf (F057)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   5,
                            F058,   63
                        }

                        Local3 = RefOf (F058)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x40)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, QWordAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F059,   64
                        }

                        Local3 = RefOf (F059)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   5,
                            F05A,   65
                        }

                        Local3 = RefOf (F05A)
                        Local4 = RefOf (G000)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, QWordAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F05B,   69
                        }

                        Local3 = RefOf (F05B)
                        Local4 = RefOf (G001)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   5,
                            F05C,   129
                        }

                        Local3 = RefOf (F05C)
                        Local4 = RefOf (G002)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, QWordAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F05D,   256
                        }

                        Local3 = RefOf (F05D)
                        Local4 = RefOf (G003)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   5,
                            F05E,   1023
                        }

                        Local3 = RefOf (F05E)
                        Local4 = RefOf (G004)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, QWordAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F05F,   1983
                        }

                        Local3 = RefOf (F05F)
                        Local4 = RefOf (G005)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x06)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, QWordAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F060,   1
                        }

                        Local3 = RefOf (F060)
                        Local4 = RefOf (G006)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   6,
                            F061,   6
                        }

                        Local3 = RefOf (F061)
                        Local4 = RefOf (G007)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, QWordAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F062,   7
                        }

                        Local3 = RefOf (F062)
                        Local4 = RefOf (G008)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   6,
                            F063,   8
                        }

                        Local3 = RefOf (F063)
                        Local4 = RefOf (G009)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, QWordAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F064,   9
                        }

                        Local3 = RefOf (F064)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   6,
                            F065,   31
                        }

                        Local3 = RefOf (F065)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, QWordAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F066,   32
                        }

                        Local3 = RefOf (F066)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   6,
                            F067,   33
                        }

                        Local3 = RefOf (F067)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, QWordAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F068,   63
                        }

                        Local3 = RefOf (F068)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   6,
                            F069,   64
                        }

                        Local3 = RefOf (F069)
                        Local4 = RefOf (G000)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, QWordAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F06A,   65
                        }

                        Local3 = RefOf (F06A)
                        Local4 = RefOf (G001)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   6,
                            F06B,   69
                        }

                        Local3 = RefOf (F06B)
                        Local4 = RefOf (G002)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, QWordAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F06C,   129
                        }

                        Local3 = RefOf (F06C)
                        Local4 = RefOf (G003)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   6,
                            F06D,   256
                        }

                        Local3 = RefOf (F06D)
                        Local4 = RefOf (G004)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, QWordAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F06E,   1023
                        }

                        Local3 = RefOf (F06E)
                        Local4 = RefOf (G005)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   6,
                            F06F,   1983
                        }

                        Local3 = RefOf (F06F)
                        Local4 = RefOf (G006)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x07)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   7,
                            F070,   1
                        }

                        Local3 = RefOf (F070)
                        Local4 = RefOf (G007)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, QWordAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F071,   6
                        }

                        Local3 = RefOf (F071)
                        Local4 = RefOf (G008)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   7,
                            F072,   7
                        }

                        Local3 = RefOf (F072)
                        Local4 = RefOf (G009)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, QWordAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F073,   8
                        }

                        Local3 = RefOf (F073)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   7,
                            F074,   9
                        }

                        Local3 = RefOf (F074)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, QWordAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F075,   31
                        }

                        Local3 = RefOf (F075)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   7,
                            F076,   32
                        }

                        Local3 = RefOf (F076)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x21)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, QWordAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F077,   33
                        }

                        Local3 = RefOf (F077)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   7,
                            F078,   63
                        }

                        Local3 = RefOf (F078)
                        Local4 = RefOf (G000)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, QWordAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F079,   64
                        }

                        Local3 = RefOf (F079)
                        Local4 = RefOf (G001)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   7,
                            F07A,   65
                        }

                        Local3 = RefOf (F07A)
                        Local4 = RefOf (G002)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, QWordAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F07B,   69
                        }

                        Local3 = RefOf (F07B)
                        Local4 = RefOf (G003)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   7,
                            F07C,   129
                        }

                        Local3 = RefOf (F07C)
                        Local4 = RefOf (G004)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, QWordAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F07D,   256
                        }

                        Local3 = RefOf (F07D)
                        Local4 = RefOf (G005)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   7,
                            F07E,   1023
                        }

                        Local3 = RefOf (F07E)
                        Local4 = RefOf (G006)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, QWordAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F07F,   1983
                        }

                        Local3 = RefOf (F07F)
                        Local4 = RefOf (G007)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x08)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F080,   1
                        }

                        Local3 = RefOf (F080)
                        Local4 = RefOf (G008)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x01),
                            F081,   6
                        }

                        Local3 = RefOf (F081)
                        Local4 = RefOf (G009)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F082,   7
                        }

                        Local3 = RefOf (F082)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x01),
                            F083,   8
                        }

                        Local3 = RefOf (F083)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F084,   9
                        }

                        Local3 = RefOf (F084)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x01),
                            F085,   31
                        }

                        Local3 = RefOf (F085)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x20)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F086,   32
                        }

                        Local3 = RefOf (F086)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x01),
                            F087,   33
                        }

                        Local3 = RefOf (F087)
                        Local4 = RefOf (G000)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F088,   63
                        }

                        Local3 = RefOf (F088)
                        Local4 = RefOf (G001)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x01),
                            F089,   64
                        }

                        Local3 = RefOf (F089)
                        Local4 = RefOf (G002)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F08A,   65
                        }

                        Local3 = RefOf (F08A)
                        Local4 = RefOf (G003)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x01),
                            F08B,   69
                        }

                        Local3 = RefOf (F08B)
                        Local4 = RefOf (G004)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F08C,   129
                        }

                        Local3 = RefOf (F08C)
                        Local4 = RefOf (G005)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x01),
                            F08D,   256
                        }

                        Local3 = RefOf (F08D)
                        Local4 = RefOf (G006)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F08E,   1023
                        }

                        Local3 = RefOf (F08E)
                        Local4 = RefOf (G007)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x01),
                            F08F,   1983
                        }

                        Local3 = RefOf (F08F)
                        Local4 = RefOf (G008)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x09)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   9,
                            F090,   1
                        }

                        Local3 = RefOf (F090)
                        Local4 = RefOf (G009)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, QWordAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F091,   6
                        }

                        Local3 = RefOf (F091)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   9,
                            F092,   7
                        }

                        Local3 = RefOf (F092)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, QWordAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F093,   8
                        }

                        Local3 = RefOf (F093)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   9,
                            F094,   9
                        }

                        Local3 = RefOf (F094)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, QWordAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F095,   31
                        }

                        Local3 = RefOf (F095)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   9,
                            F096,   32
                        }

                        Local3 = RefOf (F096)
                        Local4 = RefOf (G000)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, QWordAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F097,   33
                        }

                        Local3 = RefOf (F097)
                        Local4 = RefOf (G001)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   9,
                            F098,   63
                        }

                        Local3 = RefOf (F098)
                        Local4 = RefOf (G002)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, QWordAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F099,   64
                        }

                        Local3 = RefOf (F099)
                        Local4 = RefOf (G003)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   9,
                            F09A,   65
                        }

                        Local3 = RefOf (F09A)
                        Local4 = RefOf (G004)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, QWordAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F09B,   69
                        }

                        Local3 = RefOf (F09B)
                        Local4 = RefOf (G005)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   9,
                            F09C,   129
                        }

                        Local3 = RefOf (F09C)
                        Local4 = RefOf (G006)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, QWordAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F09D,   256
                        }

                        Local3 = RefOf (F09D)
                        Local4 = RefOf (G007)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   9,
                            F09E,   1023
                        }

                        Local3 = RefOf (F09E)
                        Local4 = RefOf (G008)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, QWordAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F09F,   1983
                        }

                        Local3 = RefOf (F09F)
                        Local4 = RefOf (G009)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x1F)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A0,   1
                        }

                        Local3 = RefOf (F0A0)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0A1,   6
                        }

                        Local3 = RefOf (F0A1)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A2,   7
                        }

                        Local3 = RefOf (F0A2)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0A3,   8
                        }

                        Local3 = RefOf (F0A3)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x09)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A4,   9
                        }

                        Local3 = RefOf (F0A4)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0A5,   31
                        }

                        Local3 = RefOf (F0A5)
                        Local4 = RefOf (G000)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A6,   32
                        }

                        Local3 = RefOf (F0A6)
                        Local4 = RefOf (G001)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0A7,   33
                        }

                        Local3 = RefOf (F0A7)
                        Local4 = RefOf (G002)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A8,   63
                        }

                        Local3 = RefOf (F0A8)
                        Local4 = RefOf (G003)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0A9,   64
                        }

                        Local3 = RefOf (F0A9)
                        Local4 = RefOf (G004)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0AA,   65
                        }

                        Local3 = RefOf (F0AA)
                        Local4 = RefOf (G005)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0AB,   69
                        }

                        Local3 = RefOf (F0AB)
                        Local4 = RefOf (G006)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0AC,   129
                        }

                        Local3 = RefOf (F0AC)
                        Local4 = RefOf (G007)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0AD,   256
                        }

                        Local3 = RefOf (F0AD)
                        Local4 = RefOf (G008)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0AE,   1023
                        }

                        Local3 = RefOf (F0AE)
                        Local4 = RefOf (G009)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0AF,   1983
                        }

                        Local3 = RefOf (F0AF)
                        Local4 = RefOf (G00A)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x20)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x04),
                            F0B0,   1
                        }

                        Local3 = RefOf (F0B0)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0B1,   6
                        }

                        Local3 = RefOf (F0B1)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x04),
                            F0B2,   7
                        }

                        Local3 = RefOf (F0B2)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x08)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0B3,   8
                        }

                        Local3 = RefOf (F0B3)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x04),
                            F0B4,   9
                        }

                        Local3 = RefOf (F0B4)
                        Local4 = RefOf (G000)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0B5,   31
                        }

                        Local3 = RefOf (F0B5)
                        Local4 = RefOf (G001)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x04),
                            F0B6,   32
                        }

                        Local3 = RefOf (F0B6)
                        Local4 = RefOf (G002)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0B7,   33
                        }

                        Local3 = RefOf (F0B7)
                        Local4 = RefOf (G003)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x04),
                            F0B8,   63
                        }

                        Local3 = RefOf (F0B8)
                        Local4 = RefOf (G004)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0B9,   64
                        }

                        Local3 = RefOf (F0B9)
                        Local4 = RefOf (G005)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x04),
                            F0BA,   65
                        }

                        Local3 = RefOf (F0BA)
                        Local4 = RefOf (G006)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0BB,   69
                        }

                        Local3 = RefOf (F0BB)
                        Local4 = RefOf (G007)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x04),
                            F0BC,   129
                        }

                        Local3 = RefOf (F0BC)
                        Local4 = RefOf (G008)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0BD,   256
                        }

                        Local3 = RefOf (F0BD)
                        Local4 = RefOf (G009)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x04),
                            F0BE,   1023
                        }

                        Local3 = RefOf (F0BE)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0BF,   1983
                        }

                        Local3 = RefOf (F0BF)
                        Local4 = RefOf (G00B)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x21)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, QWordAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0C0,   1
                        }

                        Local3 = RefOf (F0C0)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   33,
                            F0C1,   6
                        }

                        Local3 = RefOf (F0C1)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x07)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, QWordAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0C2,   7
                        }

                        Local3 = RefOf (F0C2)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   33,
                            F0C3,   8
                        }

                        Local3 = RefOf (F0C3)
                        Local4 = RefOf (G000)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, QWordAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0C4,   9
                        }

                        Local3 = RefOf (F0C4)
                        Local4 = RefOf (G001)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   33,
                            F0C5,   31
                        }

                        Local3 = RefOf (F0C5)
                        Local4 = RefOf (G002)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, QWordAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0C6,   32
                        }

                        Local3 = RefOf (F0C6)
                        Local4 = RefOf (G003)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   33,
                            F0C7,   33
                        }

                        Local3 = RefOf (F0C7)
                        Local4 = RefOf (G004)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, QWordAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0C8,   63
                        }

                        Local3 = RefOf (F0C8)
                        Local4 = RefOf (G005)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   33,
                            F0C9,   64
                        }

                        Local3 = RefOf (F0C9)
                        Local4 = RefOf (G006)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, QWordAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0CA,   65
                        }

                        Local3 = RefOf (F0CA)
                        Local4 = RefOf (G007)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   33,
                            F0CB,   69
                        }

                        Local3 = RefOf (F0CB)
                        Local4 = RefOf (G008)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, QWordAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0CC,   129
                        }

                        Local3 = RefOf (F0CC)
                        Local4 = RefOf (G009)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   33,
                            F0CD,   256
                        }

                        Local3 = RefOf (F0CD)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, QWordAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0CE,   1023
                        }

                        Local3 = RefOf (F0CE)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   33,
                            F0CF,   1983
                        }

                        Local3 = RefOf (F0CF)
                        Local4 = RefOf (G00C)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x3F)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   63,
                            F0D0,   1
                        }

                        Local3 = RefOf (F0D0)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x06)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, ByteAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0D1,   6
                        }

                        Local3 = RefOf (F0D1)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   63,
                            F0D2,   7
                        }

                        Local3 = RefOf (F0D2)
                        Local4 = RefOf (G000)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, WordAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0D3,   8
                        }

                        Local3 = RefOf (F0D3)
                        Local4 = RefOf (G001)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   63,
                            F0D4,   9
                        }

                        Local3 = RefOf (F0D4)
                        Local4 = RefOf (G002)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, DWordAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0D5,   31
                        }

                        Local3 = RefOf (F0D5)
                        Local4 = RefOf (G003)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   63,
                            F0D6,   32
                        }

                        Local3 = RefOf (F0D6)
                        Local4 = RefOf (G004)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, QWordAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0D7,   33
                        }

                        Local3 = RefOf (F0D7)
                        Local4 = RefOf (G005)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   63,
                            F0D8,   63
                        }

                        Local3 = RefOf (F0D8)
                        Local4 = RefOf (G006)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, QWordAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0D9,   64
                        }

                        Local3 = RefOf (F0D9)
                        Local4 = RefOf (G007)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   63,
                            F0DA,   65
                        }

                        Local3 = RefOf (F0DA)
                        Local4 = RefOf (G008)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, QWordAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0DB,   69
                        }

                        Local3 = RefOf (F0DB)
                        Local4 = RefOf (G009)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   63,
                            F0DC,   129
                        }

                        Local3 = RefOf (F0DC)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, QWordAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0DD,   256
                        }

                        Local3 = RefOf (F0DD)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                                ,   63,
                            F0DE,   1023
                        }

                        Local3 = RefOf (F0DE)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, QWordAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0DF,   1983
                        }

                        Local3 = RefOf (F0DF)
                        Local4 = RefOf (G00D)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x40)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0E0,   1
                        }

                        Local3 = RefOf (F0E0)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x08),
                            F0E1,   6
                        }

                        Local3 = RefOf (F0E1)
                        Local4 = RefOf (G000)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0E2,   7
                        }

                        Local3 = RefOf (F0E2)
                        Local4 = RefOf (G001)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x08),
                            F0E3,   8
                        }

                        Local3 = RefOf (F0E3)
                        Local4 = RefOf (G002)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0E4,   9
                        }

                        Local3 = RefOf (F0E4)
                        Local4 = RefOf (G003)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x08),
                            F0E5,   31
                        }

                        Local3 = RefOf (F0E5)
                        Local4 = RefOf (G004)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0E6,   32
                        }

                        Local3 = RefOf (F0E6)
                        Local4 = RefOf (G005)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x08),
                            F0E7,   33
                        }

                        Local3 = RefOf (F0E7)
                        Local4 = RefOf (G006)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0E8,   63
                        }

                        Local3 = RefOf (F0E8)
                        Local4 = RefOf (G007)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x08),
                            F0E9,   64
                        }

                        Local3 = RefOf (F0E9)
                        Local4 = RefOf (G008)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0EA,   65
                        }

                        Local3 = RefOf (F0EA)
                        Local4 = RefOf (G009)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x08),
                            F0EB,   69
                        }

                        Local3 = RefOf (F0EB)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0EC,   129
                        }

                        Local3 = RefOf (F0EC)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x08),
                            F0ED,   256
                        }

                        Local3 = RefOf (F0ED)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0EE,   1023
                        }

                        Local3 = RefOf (F0EE)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x08),
                            F0EF,   1983
                        }

                        Local3 = RefOf (F0EF)
                        Local4 = RefOf (G00E)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x41)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0F0,   1
                        }

                        Local3 = RefOf (F0F0)
                        Local4 = RefOf (G000)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F1,   6
                        }

                        Local3 = RefOf (F0F1)
                        Local4 = RefOf (G001)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0F2,   7
                        }

                        Local3 = RefOf (F0F2)
                        Local4 = RefOf (G002)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F3,   8
                        }

                        Local3 = RefOf (F0F3)
                        Local4 = RefOf (G003)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0F4,   9
                        }

                        Local3 = RefOf (F0F4)
                        Local4 = RefOf (G004)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F5,   31
                        }

                        Local3 = RefOf (F0F5)
                        Local4 = RefOf (G005)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0F6,   32
                        }

                        Local3 = RefOf (F0F6)
                        Local4 = RefOf (G006)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F7,   33
                        }

                        Local3 = RefOf (F0F7)
                        Local4 = RefOf (G007)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0F8,   63
                        }

                        Local3 = RefOf (F0F8)
                        Local4 = RefOf (G008)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F9,   64
                        }

                        Local3 = RefOf (F0F9)
                        Local4 = RefOf (G009)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0FA,   65
                        }

                        Local3 = RefOf (F0FA)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0FB,   69
                        }

                        Local3 = RefOf (F0FB)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0FC,   129
                        }

                        Local3 = RefOf (F0FC)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0FD,   256
                        }

                        Local3 = RefOf (F0FD)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (QWordAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0FE,   1023
                        }

                        Local3 = RefOf (F0FE)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0FF,   1983
                        }

                        Local3 = RefOf (F0FF)
                        Local4 = RefOf (G000)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Default
            {
                ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                Return (Zero)
            }

        }

        FCP0 [0x00] = 0x02
        FCP0 [0x01] = RefOf (BNK0)
        FCP0 [0x02] = Local2
        M72D (Arg0, Local3, Arg2, Arg3, Arg4, Arg5, Local4)
        FCP0 [0x00] = 0x00
    }

    /* Create BankField Unit */
    /* (AnyAcc, Lock, Preserve) */
    Method (M7D4, 6, Serialized)
    {
        OperationRegion (OPRB, SystemIO, 0x00, 0x09)
        OperationRegion (OPR0, SystemIO, 0x0B, 0x0100)
        Field (OPRB, ByteAcc, NoLock, Preserve)
        {
            BNK0,   8
        }

        BankField (OPR0, BNK0, 0x00, ByteAcc, NoLock, Preserve)
        {
            G000,   2048
        }

        BankField (OPR0, BNK0, 0x01, ByteAcc, NoLock, Preserve)
        {
            G001,   2048
        }

        BankField (OPR0, BNK0, 0x02, ByteAcc, NoLock, Preserve)
        {
            G002,   2048
        }

        BankField (OPR0, BNK0, 0x03, ByteAcc, NoLock, Preserve)
        {
            G003,   2048
        }

        BankField (OPR0, BNK0, 0x04, ByteAcc, NoLock, Preserve)
        {
            G004,   2048
        }

        BankField (OPR0, BNK0, 0x05, ByteAcc, NoLock, Preserve)
        {
            G005,   2048
        }

        BankField (OPR0, BNK0, 0x06, ByteAcc, NoLock, Preserve)
        {
            G006,   2048
        }

        BankField (OPR0, BNK0, 0x07, ByteAcc, NoLock, Preserve)
        {
            G007,   2048
        }

        BankField (OPR0, BNK0, 0x08, ByteAcc, NoLock, Preserve)
        {
            G008,   2048
        }

        BankField (OPR0, BNK0, 0x09, ByteAcc, NoLock, Preserve)
        {
            G009,   2048
        }

        BankField (OPR0, BNK0, 0x3F, ByteAcc, NoLock, Preserve)
        {
            G00A,   2048
        }

        BankField (OPR0, BNK0, 0x40, ByteAcc, NoLock, Preserve)
        {
            G00B,   2048
        }

        BankField (OPR0, BNK0, 0x7F, ByteAcc, NoLock, Preserve)
        {
            G00C,   2048
        }

        BankField (OPR0, BNK0, 0x80, ByteAcc, NoLock, Preserve)
        {
            G00D,   2048
        }

        BankField (OPR0, BNK0, 0xFF, ByteAcc, NoLock, Preserve)
        {
            G00E,   2048
        }

        Concatenate (Arg0, "-m7d4", Arg0)
        Switch (ToInteger (Arg2))
        {
            Case (0x00)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                            F000,   1
                        }

                        Local3 = RefOf (F000)
                        Local4 = RefOf (G000)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, WordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x00),
                            F001,   6
                        }

                        Local3 = RefOf (F001)
                        Local4 = RefOf (G001)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                            F002,   7
                        }

                        Local3 = RefOf (F002)
                        Local4 = RefOf (G002)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, DWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x00),
                            F003,   8
                        }

                        Local3 = RefOf (F003)
                        Local4 = RefOf (G003)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                            F004,   9
                        }

                        Local3 = RefOf (F004)
                        Local4 = RefOf (G004)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, QWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x00),
                            F005,   31
                        }

                        Local3 = RefOf (F005)
                        Local4 = RefOf (G005)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                            F006,   32
                        }

                        Local3 = RefOf (F006)
                        Local4 = RefOf (G006)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, AnyAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x00),
                            F007,   33
                        }

                        Local3 = RefOf (F007)
                        Local4 = RefOf (G007)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                            F008,   63
                        }

                        Local3 = RefOf (F008)
                        Local4 = RefOf (G008)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, ByteAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x00),
                            F009,   64
                        }

                        Local3 = RefOf (F009)
                        Local4 = RefOf (G009)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                            F00A,   65
                        }

                        Local3 = RefOf (F00A)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, WordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x00),
                            F00B,   69
                        }

                        Local3 = RefOf (F00B)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                            F00C,   129
                        }

                        Local3 = RefOf (F00C)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x00),
                            F00D,   256
                        }

                        Local3 = RefOf (F00D)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                            F00E,   1023
                        }

                        Local3 = RefOf (F00E)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x00),
                            F00F,   1983
                        }

                        Local3 = RefOf (F00F)
                        Local4 = RefOf (G000)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x01)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, AnyAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   1,
                            F010,   1
                        }

                        Local3 = RefOf (F010)
                        Local4 = RefOf (G001)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, AnyAcc, Lock, Preserve)
                        {
                                ,   1,
                            F011,   6
                        }

                        Local3 = RefOf (F011)
                        Local4 = RefOf (G002)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, AnyAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   1,
                            F012,   7
                        }

                        Local3 = RefOf (F012)
                        Local4 = RefOf (G003)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, ByteAcc, Lock, Preserve)
                        {
                                ,   1,
                            F013,   8
                        }

                        Local3 = RefOf (F013)
                        Local4 = RefOf (G004)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, WordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   1,
                            F014,   9
                        }

                        Local3 = RefOf (F014)
                        Local4 = RefOf (G005)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, AnyAcc, Lock, Preserve)
                        {
                                ,   1,
                            F015,   31
                        }

                        Local3 = RefOf (F015)
                        Local4 = RefOf (G006)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, DWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   1,
                            F016,   32
                        }

                        Local3 = RefOf (F016)
                        Local4 = RefOf (G007)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, AnyAcc, Lock, Preserve)
                        {
                                ,   1,
                            F017,   33
                        }

                        Local3 = RefOf (F017)
                        Local4 = RefOf (G008)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, QWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   1,
                            F018,   63
                        }

                        Local3 = RefOf (F018)
                        Local4 = RefOf (G009)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, AnyAcc, Lock, Preserve)
                        {
                                ,   1,
                            F019,   64
                        }

                        Local3 = RefOf (F019)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, AnyAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   1,
                            F01A,   65
                        }

                        Local3 = RefOf (F01A)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, AnyAcc, Lock, Preserve)
                        {
                                ,   1,
                            F01B,   69
                        }

                        Local3 = RefOf (F01B)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, ByteAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   1,
                            F01C,   129
                        }

                        Local3 = RefOf (F01C)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, AnyAcc, Lock, Preserve)
                        {
                                ,   1,
                            F01D,   256
                        }

                        Local3 = RefOf (F01D)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   1,
                            F01E,   1023
                        }

                        Local3 = RefOf (F01E)
                        Local4 = RefOf (G000)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, AnyAcc, Lock, Preserve)
                        {
                                ,   1,
                            F01F,   1983
                        }

                        Local3 = RefOf (F01F)
                        Local4 = RefOf (G001)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x02)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, AnyAcc, Lock, Preserve)
                        {
                                ,   2,
                            F020,   1
                        }

                        Local3 = RefOf (F020)
                        Local4 = RefOf (G002)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, DWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   2,
                            F021,   6
                        }

                        Local3 = RefOf (F021)
                        Local4 = RefOf (G003)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, AnyAcc, Lock, Preserve)
                        {
                                ,   2,
                            F022,   7
                        }

                        Local3 = RefOf (F022)
                        Local4 = RefOf (G004)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, QWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   2,
                            F023,   8
                        }

                        Local3 = RefOf (F023)
                        Local4 = RefOf (G005)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, AnyAcc, Lock, Preserve)
                        {
                                ,   2,
                            F024,   9
                        }

                        Local3 = RefOf (F024)
                        Local4 = RefOf (G006)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, AnyAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   2,
                            F025,   31
                        }

                        Local3 = RefOf (F025)
                        Local4 = RefOf (G007)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, AnyAcc, Lock, Preserve)
                        {
                                ,   2,
                            F026,   32
                        }

                        Local3 = RefOf (F026)
                        Local4 = RefOf (G008)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, ByteAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   2,
                            F027,   33
                        }

                        Local3 = RefOf (F027)
                        Local4 = RefOf (G009)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, AnyAcc, Lock, Preserve)
                        {
                                ,   2,
                            F028,   63
                        }

                        Local3 = RefOf (F028)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, WordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   2,
                            F029,   64
                        }

                        Local3 = RefOf (F029)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, AnyAcc, Lock, Preserve)
                        {
                                ,   2,
                            F02A,   65
                        }

                        Local3 = RefOf (F02A)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   2,
                            F02B,   69
                        }

                        Local3 = RefOf (F02B)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x81)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, AnyAcc, Lock, Preserve)
                        {
                                ,   2,
                            F02C,   129
                        }

                        Local3 = RefOf (F02C)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   2,
                            F02D,   256
                        }

                        Local3 = RefOf (F02D)
                        Local4 = RefOf (G000)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, AnyAcc, Lock, Preserve)
                        {
                                ,   2,
                            F02E,   1023
                        }

                        Local3 = RefOf (F02E)
                        Local4 = RefOf (G001)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, AnyAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   2,
                            F02F,   1983
                        }

                        Local3 = RefOf (F02F)
                        Local4 = RefOf (G002)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x03)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, ByteAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   3,
                            F030,   1
                        }

                        Local3 = RefOf (F030)
                        Local4 = RefOf (G003)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, AnyAcc, Lock, Preserve)
                        {
                                ,   3,
                            F031,   6
                        }

                        Local3 = RefOf (F031)
                        Local4 = RefOf (G004)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, WordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   3,
                            F032,   7
                        }

                        Local3 = RefOf (F032)
                        Local4 = RefOf (G005)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, AnyAcc, Lock, Preserve)
                        {
                                ,   3,
                            F033,   8
                        }

                        Local3 = RefOf (F033)
                        Local4 = RefOf (G006)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, DWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   3,
                            F034,   9
                        }

                        Local3 = RefOf (F034)
                        Local4 = RefOf (G007)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, AnyAcc, Lock, Preserve)
                        {
                                ,   3,
                            F035,   31
                        }

                        Local3 = RefOf (F035)
                        Local4 = RefOf (G008)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, QWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   3,
                            F036,   32
                        }

                        Local3 = RefOf (F036)
                        Local4 = RefOf (G009)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, AnyAcc, Lock, Preserve)
                        {
                                ,   3,
                            F037,   33
                        }

                        Local3 = RefOf (F037)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, AnyAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   3,
                            F038,   63
                        }

                        Local3 = RefOf (F038)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, AnyAcc, Lock, Preserve)
                        {
                                ,   3,
                            F039,   64
                        }

                        Local3 = RefOf (F039)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, ByteAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   3,
                            F03A,   65
                        }

                        Local3 = RefOf (F03A)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x45)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, AnyAcc, Lock, Preserve)
                        {
                                ,   3,
                            F03B,   69
                        }

                        Local3 = RefOf (F03B)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   3,
                            F03C,   129
                        }

                        Local3 = RefOf (F03C)
                        Local4 = RefOf (G000)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, AnyAcc, Lock, Preserve)
                        {
                                ,   3,
                            F03D,   256
                        }

                        Local3 = RefOf (F03D)
                        Local4 = RefOf (G001)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, DWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   3,
                            F03E,   1023
                        }

                        Local3 = RefOf (F03E)
                        Local4 = RefOf (G002)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, AnyAcc, Lock, Preserve)
                        {
                                ,   3,
                            F03F,   1983
                        }

                        Local3 = RefOf (F03F)
                        Local4 = RefOf (G003)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x04)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, AnyAcc, Lock, Preserve)
                        {
                                ,   4,
                            F040,   1
                        }

                        Local3 = RefOf (F040)
                        Local4 = RefOf (G004)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, QWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   4,
                            F041,   6
                        }

                        Local3 = RefOf (F041)
                        Local4 = RefOf (G005)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, AnyAcc, Lock, Preserve)
                        {
                                ,   4,
                            F042,   7
                        }

                        Local3 = RefOf (F042)
                        Local4 = RefOf (G006)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, AnyAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   4,
                            F043,   8
                        }

                        Local3 = RefOf (F043)
                        Local4 = RefOf (G007)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, AnyAcc, Lock, Preserve)
                        {
                                ,   4,
                            F044,   9
                        }

                        Local3 = RefOf (F044)
                        Local4 = RefOf (G008)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, ByteAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   4,
                            F045,   31
                        }

                        Local3 = RefOf (F045)
                        Local4 = RefOf (G009)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, AnyAcc, Lock, Preserve)
                        {
                                ,   4,
                            F046,   32
                        }

                        Local3 = RefOf (F046)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, WordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   4,
                            F047,   33
                        }

                        Local3 = RefOf (F047)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, AnyAcc, Lock, Preserve)
                        {
                                ,   4,
                            F048,   63
                        }

                        Local3 = RefOf (F048)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   4,
                            F049,   64
                        }

                        Local3 = RefOf (F049)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x41)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, AnyAcc, Lock, Preserve)
                        {
                                ,   4,
                            F04A,   65
                        }

                        Local3 = RefOf (F04A)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   4,
                            F04B,   69
                        }

                        Local3 = RefOf (F04B)
                        Local4 = RefOf (G000)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, AnyAcc, Lock, Preserve)
                        {
                                ,   4,
                            F04C,   129
                        }

                        Local3 = RefOf (F04C)
                        Local4 = RefOf (G001)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, AnyAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   4,
                            F04D,   256
                        }

                        Local3 = RefOf (F04D)
                        Local4 = RefOf (G002)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, AnyAcc, Lock, Preserve)
                        {
                                ,   4,
                            F04E,   1023
                        }

                        Local3 = RefOf (F04E)
                        Local4 = RefOf (G003)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, ByteAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   4,
                            F04F,   1983
                        }

                        Local3 = RefOf (F04F)
                        Local4 = RefOf (G004)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x05)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, WordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   5,
                            F050,   1
                        }

                        Local3 = RefOf (F050)
                        Local4 = RefOf (G005)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, AnyAcc, Lock, Preserve)
                        {
                                ,   5,
                            F051,   6
                        }

                        Local3 = RefOf (F051)
                        Local4 = RefOf (G006)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, DWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   5,
                            F052,   7
                        }

                        Local3 = RefOf (F052)
                        Local4 = RefOf (G007)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, AnyAcc, Lock, Preserve)
                        {
                                ,   5,
                            F053,   8
                        }

                        Local3 = RefOf (F053)
                        Local4 = RefOf (G008)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, QWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   5,
                            F054,   9
                        }

                        Local3 = RefOf (F054)
                        Local4 = RefOf (G009)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, AnyAcc, Lock, Preserve)
                        {
                                ,   5,
                            F055,   31
                        }

                        Local3 = RefOf (F055)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, AnyAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   5,
                            F056,   32
                        }

                        Local3 = RefOf (F056)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, AnyAcc, Lock, Preserve)
                        {
                                ,   5,
                            F057,   33
                        }

                        Local3 = RefOf (F057)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, ByteAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   5,
                            F058,   63
                        }

                        Local3 = RefOf (F058)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x40)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, AnyAcc, Lock, Preserve)
                        {
                                ,   5,
                            F059,   64
                        }

                        Local3 = RefOf (F059)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   5,
                            F05A,   65
                        }

                        Local3 = RefOf (F05A)
                        Local4 = RefOf (G000)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, AnyAcc, Lock, Preserve)
                        {
                                ,   5,
                            F05B,   69
                        }

                        Local3 = RefOf (F05B)
                        Local4 = RefOf (G001)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, DWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   5,
                            F05C,   129
                        }

                        Local3 = RefOf (F05C)
                        Local4 = RefOf (G002)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, AnyAcc, Lock, Preserve)
                        {
                                ,   5,
                            F05D,   256
                        }

                        Local3 = RefOf (F05D)
                        Local4 = RefOf (G003)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, QWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   5,
                            F05E,   1023
                        }

                        Local3 = RefOf (F05E)
                        Local4 = RefOf (G004)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, AnyAcc, Lock, Preserve)
                        {
                                ,   5,
                            F05F,   1983
                        }

                        Local3 = RefOf (F05F)
                        Local4 = RefOf (G005)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x06)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, AnyAcc, Lock, Preserve)
                        {
                                ,   6,
                            F060,   1
                        }

                        Local3 = RefOf (F060)
                        Local4 = RefOf (G006)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, AnyAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   6,
                            F061,   6
                        }

                        Local3 = RefOf (F061)
                        Local4 = RefOf (G007)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, AnyAcc, Lock, Preserve)
                        {
                                ,   6,
                            F062,   7
                        }

                        Local3 = RefOf (F062)
                        Local4 = RefOf (G008)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, ByteAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   6,
                            F063,   8
                        }

                        Local3 = RefOf (F063)
                        Local4 = RefOf (G009)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, AnyAcc, Lock, Preserve)
                        {
                                ,   6,
                            F064,   9
                        }

                        Local3 = RefOf (F064)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, WordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   6,
                            F065,   31
                        }

                        Local3 = RefOf (F065)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, AnyAcc, Lock, Preserve)
                        {
                                ,   6,
                            F066,   32
                        }

                        Local3 = RefOf (F066)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   6,
                            F067,   33
                        }

                        Local3 = RefOf (F067)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, AnyAcc, Lock, Preserve)
                        {
                                ,   6,
                            F068,   63
                        }

                        Local3 = RefOf (F068)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   6,
                            F069,   64
                        }

                        Local3 = RefOf (F069)
                        Local4 = RefOf (G000)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, AnyAcc, Lock, Preserve)
                        {
                                ,   6,
                            F06A,   65
                        }

                        Local3 = RefOf (F06A)
                        Local4 = RefOf (G001)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, AnyAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   6,
                            F06B,   69
                        }

                        Local3 = RefOf (F06B)
                        Local4 = RefOf (G002)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, AnyAcc, Lock, Preserve)
                        {
                                ,   6,
                            F06C,   129
                        }

                        Local3 = RefOf (F06C)
                        Local4 = RefOf (G003)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, ByteAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   6,
                            F06D,   256
                        }

                        Local3 = RefOf (F06D)
                        Local4 = RefOf (G004)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, AnyAcc, Lock, Preserve)
                        {
                                ,   6,
                            F06E,   1023
                        }

                        Local3 = RefOf (F06E)
                        Local4 = RefOf (G005)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, WordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   6,
                            F06F,   1983
                        }

                        Local3 = RefOf (F06F)
                        Local4 = RefOf (G006)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x07)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, DWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   7,
                            F070,   1
                        }

                        Local3 = RefOf (F070)
                        Local4 = RefOf (G007)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, AnyAcc, Lock, Preserve)
                        {
                                ,   7,
                            F071,   6
                        }

                        Local3 = RefOf (F071)
                        Local4 = RefOf (G008)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, QWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   7,
                            F072,   7
                        }

                        Local3 = RefOf (F072)
                        Local4 = RefOf (G009)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, AnyAcc, Lock, Preserve)
                        {
                                ,   7,
                            F073,   8
                        }

                        Local3 = RefOf (F073)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, AnyAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   7,
                            F074,   9
                        }

                        Local3 = RefOf (F074)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, AnyAcc, Lock, Preserve)
                        {
                                ,   7,
                            F075,   31
                        }

                        Local3 = RefOf (F075)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, ByteAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   7,
                            F076,   32
                        }

                        Local3 = RefOf (F076)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x21)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, AnyAcc, Lock, Preserve)
                        {
                                ,   7,
                            F077,   33
                        }

                        Local3 = RefOf (F077)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   7,
                            F078,   63
                        }

                        Local3 = RefOf (F078)
                        Local4 = RefOf (G000)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, AnyAcc, Lock, Preserve)
                        {
                                ,   7,
                            F079,   64
                        }

                        Local3 = RefOf (F079)
                        Local4 = RefOf (G001)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, DWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   7,
                            F07A,   65
                        }

                        Local3 = RefOf (F07A)
                        Local4 = RefOf (G002)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, AnyAcc, Lock, Preserve)
                        {
                                ,   7,
                            F07B,   69
                        }

                        Local3 = RefOf (F07B)
                        Local4 = RefOf (G003)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, QWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   7,
                            F07C,   129
                        }

                        Local3 = RefOf (F07C)
                        Local4 = RefOf (G004)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, AnyAcc, Lock, Preserve)
                        {
                                ,   7,
                            F07D,   256
                        }

                        Local3 = RefOf (F07D)
                        Local4 = RefOf (G005)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, AnyAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   7,
                            F07E,   1023
                        }

                        Local3 = RefOf (F07E)
                        Local4 = RefOf (G006)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, AnyAcc, Lock, Preserve)
                        {
                                ,   7,
                            F07F,   1983
                        }

                        Local3 = RefOf (F07F)
                        Local4 = RefOf (G007)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x08)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x01),
                            F080,   1
                        }

                        Local3 = RefOf (F080)
                        Local4 = RefOf (G008)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, ByteAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x01),
                            F081,   6
                        }

                        Local3 = RefOf (F081)
                        Local4 = RefOf (G009)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x01),
                            F082,   7
                        }

                        Local3 = RefOf (F082)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, WordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x01),
                            F083,   8
                        }

                        Local3 = RefOf (F083)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x01),
                            F084,   9
                        }

                        Local3 = RefOf (F084)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x01),
                            F085,   31
                        }

                        Local3 = RefOf (F085)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x20)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x01),
                            F086,   32
                        }

                        Local3 = RefOf (F086)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x01),
                            F087,   33
                        }

                        Local3 = RefOf (F087)
                        Local4 = RefOf (G000)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x01),
                            F088,   63
                        }

                        Local3 = RefOf (F088)
                        Local4 = RefOf (G001)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, AnyAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x01),
                            F089,   64
                        }

                        Local3 = RefOf (F089)
                        Local4 = RefOf (G002)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x01),
                            F08A,   65
                        }

                        Local3 = RefOf (F08A)
                        Local4 = RefOf (G003)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, ByteAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x01),
                            F08B,   69
                        }

                        Local3 = RefOf (F08B)
                        Local4 = RefOf (G004)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x01),
                            F08C,   129
                        }

                        Local3 = RefOf (F08C)
                        Local4 = RefOf (G005)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, WordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x01),
                            F08D,   256
                        }

                        Local3 = RefOf (F08D)
                        Local4 = RefOf (G006)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x01),
                            F08E,   1023
                        }

                        Local3 = RefOf (F08E)
                        Local4 = RefOf (G007)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, DWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x01),
                            F08F,   1983
                        }

                        Local3 = RefOf (F08F)
                        Local4 = RefOf (G008)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x09)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, QWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   9,
                            F090,   1
                        }

                        Local3 = RefOf (F090)
                        Local4 = RefOf (G009)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, AnyAcc, Lock, Preserve)
                        {
                                ,   9,
                            F091,   6
                        }

                        Local3 = RefOf (F091)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, AnyAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   9,
                            F092,   7
                        }

                        Local3 = RefOf (F092)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, AnyAcc, Lock, Preserve)
                        {
                                ,   9,
                            F093,   8
                        }

                        Local3 = RefOf (F093)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, ByteAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   9,
                            F094,   9
                        }

                        Local3 = RefOf (F094)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, AnyAcc, Lock, Preserve)
                        {
                                ,   9,
                            F095,   31
                        }

                        Local3 = RefOf (F095)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   9,
                            F096,   32
                        }

                        Local3 = RefOf (F096)
                        Local4 = RefOf (G000)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, AnyAcc, Lock, Preserve)
                        {
                                ,   9,
                            F097,   33
                        }

                        Local3 = RefOf (F097)
                        Local4 = RefOf (G001)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, DWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   9,
                            F098,   63
                        }

                        Local3 = RefOf (F098)
                        Local4 = RefOf (G002)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, AnyAcc, Lock, Preserve)
                        {
                                ,   9,
                            F099,   64
                        }

                        Local3 = RefOf (F099)
                        Local4 = RefOf (G003)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, QWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   9,
                            F09A,   65
                        }

                        Local3 = RefOf (F09A)
                        Local4 = RefOf (G004)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, AnyAcc, Lock, Preserve)
                        {
                                ,   9,
                            F09B,   69
                        }

                        Local3 = RefOf (F09B)
                        Local4 = RefOf (G005)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, AnyAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   9,
                            F09C,   129
                        }

                        Local3 = RefOf (F09C)
                        Local4 = RefOf (G006)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, AnyAcc, Lock, Preserve)
                        {
                                ,   9,
                            F09D,   256
                        }

                        Local3 = RefOf (F09D)
                        Local4 = RefOf (G007)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, ByteAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   9,
                            F09E,   1023
                        }

                        Local3 = RefOf (F09E)
                        Local4 = RefOf (G008)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, AnyAcc, Lock, Preserve)
                        {
                                ,   9,
                            F09F,   1983
                        }

                        Local3 = RefOf (F09F)
                        Local4 = RefOf (G009)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x1F)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A0,   1
                        }

                        Local3 = RefOf (F0A0)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, WordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0A1,   6
                        }

                        Local3 = RefOf (F0A1)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A2,   7
                        }

                        Local3 = RefOf (F0A2)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0A3,   8
                        }

                        Local3 = RefOf (F0A3)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x09)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A4,   9
                        }

                        Local3 = RefOf (F0A4)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0A5,   31
                        }

                        Local3 = RefOf (F0A5)
                        Local4 = RefOf (G000)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A6,   32
                        }

                        Local3 = RefOf (F0A6)
                        Local4 = RefOf (G001)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, AnyAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0A7,   33
                        }

                        Local3 = RefOf (F0A7)
                        Local4 = RefOf (G002)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A8,   63
                        }

                        Local3 = RefOf (F0A8)
                        Local4 = RefOf (G003)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, ByteAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0A9,   64
                        }

                        Local3 = RefOf (F0A9)
                        Local4 = RefOf (G004)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0AA,   65
                        }

                        Local3 = RefOf (F0AA)
                        Local4 = RefOf (G005)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, WordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0AB,   69
                        }

                        Local3 = RefOf (F0AB)
                        Local4 = RefOf (G006)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0AC,   129
                        }

                        Local3 = RefOf (F0AC)
                        Local4 = RefOf (G007)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, DWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0AD,   256
                        }

                        Local3 = RefOf (F0AD)
                        Local4 = RefOf (G008)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0AE,   1023
                        }

                        Local3 = RefOf (F0AE)
                        Local4 = RefOf (G009)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, QWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x03),
                                ,   7,
                            F0AF,   1983
                        }

                        Local3 = RefOf (F0AF)
                        Local4 = RefOf (G00A)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x20)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, AnyAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x04),
                            F0B0,   1
                        }

                        Local3 = RefOf (F0B0)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x04),
                            F0B1,   6
                        }

                        Local3 = RefOf (F0B1)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, ByteAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x04),
                            F0B2,   7
                        }

                        Local3 = RefOf (F0B2)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x08)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x04),
                            F0B3,   8
                        }

                        Local3 = RefOf (F0B3)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x04),
                            F0B4,   9
                        }

                        Local3 = RefOf (F0B4)
                        Local4 = RefOf (G000)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x04),
                            F0B5,   31
                        }

                        Local3 = RefOf (F0B5)
                        Local4 = RefOf (G001)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, DWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x04),
                            F0B6,   32
                        }

                        Local3 = RefOf (F0B6)
                        Local4 = RefOf (G002)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x04),
                            F0B7,   33
                        }

                        Local3 = RefOf (F0B7)
                        Local4 = RefOf (G003)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, QWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x04),
                            F0B8,   63
                        }

                        Local3 = RefOf (F0B8)
                        Local4 = RefOf (G004)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x04),
                            F0B9,   64
                        }

                        Local3 = RefOf (F0B9)
                        Local4 = RefOf (G005)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, AnyAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x04),
                            F0BA,   65
                        }

                        Local3 = RefOf (F0BA)
                        Local4 = RefOf (G006)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x04),
                            F0BB,   69
                        }

                        Local3 = RefOf (F0BB)
                        Local4 = RefOf (G007)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, ByteAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x04),
                            F0BC,   129
                        }

                        Local3 = RefOf (F0BC)
                        Local4 = RefOf (G008)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x04),
                            F0BD,   256
                        }

                        Local3 = RefOf (F0BD)
                        Local4 = RefOf (G009)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, WordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x04),
                            F0BE,   1023
                        }

                        Local3 = RefOf (F0BE)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x04),
                            F0BF,   1983
                        }

                        Local3 = RefOf (F0BF)
                        Local4 = RefOf (G00B)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x21)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, AnyAcc, Lock, Preserve)
                        {
                                ,   33,
                            F0C0,   1
                        }

                        Local3 = RefOf (F0C0)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, DWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   33,
                            F0C1,   6
                        }

                        Local3 = RefOf (F0C1)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x07)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, AnyAcc, Lock, Preserve)
                        {
                                ,   33,
                            F0C2,   7
                        }

                        Local3 = RefOf (F0C2)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   33,
                            F0C3,   8
                        }

                        Local3 = RefOf (F0C3)
                        Local4 = RefOf (G000)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, AnyAcc, Lock, Preserve)
                        {
                                ,   33,
                            F0C4,   9
                        }

                        Local3 = RefOf (F0C4)
                        Local4 = RefOf (G001)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, AnyAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   33,
                            F0C5,   31
                        }

                        Local3 = RefOf (F0C5)
                        Local4 = RefOf (G002)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, AnyAcc, Lock, Preserve)
                        {
                                ,   33,
                            F0C6,   32
                        }

                        Local3 = RefOf (F0C6)
                        Local4 = RefOf (G003)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, ByteAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   33,
                            F0C7,   33
                        }

                        Local3 = RefOf (F0C7)
                        Local4 = RefOf (G004)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, AnyAcc, Lock, Preserve)
                        {
                                ,   33,
                            F0C8,   63
                        }

                        Local3 = RefOf (F0C8)
                        Local4 = RefOf (G005)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, WordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   33,
                            F0C9,   64
                        }

                        Local3 = RefOf (F0C9)
                        Local4 = RefOf (G006)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, AnyAcc, Lock, Preserve)
                        {
                                ,   33,
                            F0CA,   65
                        }

                        Local3 = RefOf (F0CA)
                        Local4 = RefOf (G007)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, DWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   33,
                            F0CB,   69
                        }

                        Local3 = RefOf (F0CB)
                        Local4 = RefOf (G008)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, AnyAcc, Lock, Preserve)
                        {
                                ,   33,
                            F0CC,   129
                        }

                        Local3 = RefOf (F0CC)
                        Local4 = RefOf (G009)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, QWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   33,
                            F0CD,   256
                        }

                        Local3 = RefOf (F0CD)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, AnyAcc, Lock, Preserve)
                        {
                                ,   33,
                            F0CE,   1023
                        }

                        Local3 = RefOf (F0CE)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, AnyAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   33,
                            F0CF,   1983
                        }

                        Local3 = RefOf (F0CF)
                        Local4 = RefOf (G00C)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x3F)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, ByteAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   63,
                            F0D0,   1
                        }

                        Local3 = RefOf (F0D0)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x06)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, AnyAcc, Lock, Preserve)
                        {
                                ,   63,
                            F0D1,   6
                        }

                        Local3 = RefOf (F0D1)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   63,
                            F0D2,   7
                        }

                        Local3 = RefOf (F0D2)
                        Local4 = RefOf (G000)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, AnyAcc, Lock, Preserve)
                        {
                                ,   63,
                            F0D3,   8
                        }

                        Local3 = RefOf (F0D3)
                        Local4 = RefOf (G001)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, DWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   63,
                            F0D4,   9
                        }

                        Local3 = RefOf (F0D4)
                        Local4 = RefOf (G002)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, AnyAcc, Lock, Preserve)
                        {
                                ,   63,
                            F0D5,   31
                        }

                        Local3 = RefOf (F0D5)
                        Local4 = RefOf (G003)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, QWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   63,
                            F0D6,   32
                        }

                        Local3 = RefOf (F0D6)
                        Local4 = RefOf (G004)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, AnyAcc, Lock, Preserve)
                        {
                                ,   63,
                            F0D7,   33
                        }

                        Local3 = RefOf (F0D7)
                        Local4 = RefOf (G005)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, AnyAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   63,
                            F0D8,   63
                        }

                        Local3 = RefOf (F0D8)
                        Local4 = RefOf (G006)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, AnyAcc, Lock, Preserve)
                        {
                                ,   63,
                            F0D9,   64
                        }

                        Local3 = RefOf (F0D9)
                        Local4 = RefOf (G007)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, ByteAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   63,
                            F0DA,   65
                        }

                        Local3 = RefOf (F0DA)
                        Local4 = RefOf (G008)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, AnyAcc, Lock, Preserve)
                        {
                                ,   63,
                            F0DB,   69
                        }

                        Local3 = RefOf (F0DB)
                        Local4 = RefOf (G009)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, WordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   63,
                            F0DC,   129
                        }

                        Local3 = RefOf (F0DC)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, AnyAcc, Lock, Preserve)
                        {
                                ,   63,
                            F0DD,   256
                        }

                        Local3 = RefOf (F0DD)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, DWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                                ,   63,
                            F0DE,   1023
                        }

                        Local3 = RefOf (F0DE)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, AnyAcc, Lock, Preserve)
                        {
                                ,   63,
                            F0DF,   1983
                        }

                        Local3 = RefOf (F0DF)
                        Local4 = RefOf (G00D)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x40)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                            F0E0,   1
                        }

                        Local3 = RefOf (F0E0)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, QWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x08),
                            F0E1,   6
                        }

                        Local3 = RefOf (F0E1)
                        Local4 = RefOf (G000)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                            F0E2,   7
                        }

                        Local3 = RefOf (F0E2)
                        Local4 = RefOf (G001)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, AnyAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x08),
                            F0E3,   8
                        }

                        Local3 = RefOf (F0E3)
                        Local4 = RefOf (G002)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                            F0E4,   9
                        }

                        Local3 = RefOf (F0E4)
                        Local4 = RefOf (G003)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, ByteAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x08),
                            F0E5,   31
                        }

                        Local3 = RefOf (F0E5)
                        Local4 = RefOf (G004)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                            F0E6,   32
                        }

                        Local3 = RefOf (F0E6)
                        Local4 = RefOf (G005)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, WordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x08),
                            F0E7,   33
                        }

                        Local3 = RefOf (F0E7)
                        Local4 = RefOf (G006)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                            F0E8,   63
                        }

                        Local3 = RefOf (F0E8)
                        Local4 = RefOf (G007)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, DWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x08),
                            F0E9,   64
                        }

                        Local3 = RefOf (F0E9)
                        Local4 = RefOf (G008)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                            F0EA,   65
                        }

                        Local3 = RefOf (F0EA)
                        Local4 = RefOf (G009)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, QWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x08),
                            F0EB,   69
                        }

                        Local3 = RefOf (F0EB)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                            F0EC,   129
                        }

                        Local3 = RefOf (F0EC)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, AnyAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x08),
                            F0ED,   256
                        }

                        Local3 = RefOf (F0ED)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                            F0EE,   1023
                        }

                        Local3 = RefOf (F0EE)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, ByteAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x08),
                            F0EF,   1983
                        }

                        Local3 = RefOf (F0EF)
                        Local4 = RefOf (G00E)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Case (0x41)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, WordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0F0,   1
                        }

                        Local3 = RefOf (F0F0)
                        Local4 = RefOf (G000)
                    }
                    Case (0x06)
                    {
                        Local2 = 0x01
                        BankField (OPR0, BNK0, 0x01, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F1,   6
                        }

                        Local3 = RefOf (F0F1)
                        Local4 = RefOf (G001)
                    }
                    Case (0x07)
                    {
                        Local2 = 0x02
                        BankField (OPR0, BNK0, 0x02, DWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0F2,   7
                        }

                        Local3 = RefOf (F0F2)
                        Local4 = RefOf (G002)
                    }
                    Case (0x08)
                    {
                        Local2 = 0x03
                        BankField (OPR0, BNK0, 0x03, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F3,   8
                        }

                        Local3 = RefOf (F0F3)
                        Local4 = RefOf (G003)
                    }
                    Case (0x09)
                    {
                        Local2 = 0x04
                        BankField (OPR0, BNK0, 0x04, QWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0F4,   9
                        }

                        Local3 = RefOf (F0F4)
                        Local4 = RefOf (G004)
                    }
                    Case (0x1F)
                    {
                        Local2 = 0x05
                        BankField (OPR0, BNK0, 0x05, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F5,   31
                        }

                        Local3 = RefOf (F0F5)
                        Local4 = RefOf (G005)
                    }
                    Case (0x20)
                    {
                        Local2 = 0x06
                        BankField (OPR0, BNK0, 0x06, AnyAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0F6,   32
                        }

                        Local3 = RefOf (F0F6)
                        Local4 = RefOf (G006)
                    }
                    Case (0x21)
                    {
                        Local2 = 0x07
                        BankField (OPR0, BNK0, 0x07, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F7,   33
                        }

                        Local3 = RefOf (F0F7)
                        Local4 = RefOf (G007)
                    }
                    Case (0x3F)
                    {
                        Local2 = 0x08
                        BankField (OPR0, BNK0, 0x08, ByteAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0F8,   63
                        }

                        Local3 = RefOf (F0F8)
                        Local4 = RefOf (G008)
                    }
                    Case (0x40)
                    {
                        Local2 = 0x09
                        BankField (OPR0, BNK0, 0x09, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F9,   64
                        }

                        Local3 = RefOf (F0F9)
                        Local4 = RefOf (G009)
                    }
                    Case (0x41)
                    {
                        Local2 = 0x3F
                        BankField (OPR0, BNK0, 0x3F, WordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0FA,   65
                        }

                        Local3 = RefOf (F0FA)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x45)
                    {
                        Local2 = 0x40
                        BankField (OPR0, BNK0, 0x40, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0FB,   69
                        }

                        Local3 = RefOf (F0FB)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x81)
                    {
                        Local2 = 0x7F
                        BankField (OPR0, BNK0, 0x7F, DWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0FC,   129
                        }

                        Local3 = RefOf (F0FC)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x0100)
                    {
                        Local2 = 0x80
                        BankField (OPR0, BNK0, 0x80, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0FD,   256
                        }

                        Local3 = RefOf (F0FD)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x03FF)
                    {
                        Local2 = 0xFF
                        BankField (OPR0, BNK0, 0xFF, QWordAcc, Lock, Preserve)
                        {
                            AccessAs (AnyAcc, 0x00),
                            Offset (0x08),
                                ,   1,
                            F0FE,   1023
                        }

                        Local3 = RefOf (F0FE)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x07BF)
                    {
                        Local2 = 0x00
                        BankField (OPR0, BNK0, 0x00, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0FF,   1983
                        }

                        Local3 = RefOf (F0FF)
                        Local4 = RefOf (G000)
                    }
                    Default
                    {
                        ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Default
            {
                ERR (Arg0, Z145, __LINE__, 0x00, 0x00, Arg2, Arg3)
                Return (Zero)
            }

        }

        FCP0 [0x00] = 0x02
        FCP0 [0x01] = RefOf (BNK0)
        FCP0 [0x02] = Local2
        M72D (Arg0, Local3, Arg2, Arg3, Arg4, Arg5, Local4)
        FCP0 [0x00] = 0x00
    }

    /* Splitting of BankFields */
    /* m7c6(CallChain) */
    Method (M7C6, 1, Serialized)
    {
        OperationRegion (OPR0, SystemIO, 0x03E8, 0x0101)
        Debug = "TEST: m7c6, Check Splitting of BankFields"
        Concatenate (Arg0, "-m7c6", Arg0)
        M7E0 (Arg0, OPR0, 0x04)
        M7E1 (Arg0, OPR0, 0x0400)
        M7E2 (Arg0, OPR0, 0x4000)
        M7E3 (Arg0, OPR0, 0xF000)
        M7E4 (Arg0, OPR0, 0xF004)
        M7E5 (Arg0, OPR0, 0xF400)
        M7E6 (Arg0, OPR0, 0xFF00)
        M7E7 (Arg0, OPR0, 0xFFF0)
        M7E8 (Arg0, OPR0, 0xFFFF)
        M7E9 (Arg0, OPR0, 0x04)
    }

    /* Create BankFields that spans the same bits */
    /* and check possible inconsistence, 0-bit offset. */
    /* m7e0(CallChain, OpRegion, BankNum) */
    Method (M7E0, 3, Serialized)
    {
        OperationRegion (OPRM, 0xFF, 0x0100, 0x08)
        OperationRegion (OPRN, SystemIO, 0x10, 0x02)
        Field (OPRN, ByteAcc, NoLock, Preserve)
        {
            BNK0,   16
        }

        Concatenate (Arg0, "-m7e0", Arg0)
        CopyObject (Arg1, OPRM) /* \M7E0.OPRM */
        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
            Offset (0x00),
            BF00,   3
        }

        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
            Offset (0x00),
            BF10,   1,
            BF11,   1,
            BF12,   1
        }

        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
            Offset (0x00),
            BF20,   1,
            BF21,   2
        }

        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
            Offset (0x00),
            BF30,   2,
            BF31,   1
        }

        Local0 = 0x08
        Local1 = Package (0x07)
            {
                BF10,
                BF11,
                BF12,
                BF20,
                BF21,
                BF30,
                BF31
            }
        While (Local0)
        {
            Local0--
            BF00 = Local0
            If (Y118){}
            Else
            {
                Local1 [0x00] = BF10 /* \M7E0.BF10 */
                Local1 [0x01] = BF11 /* \M7E0.BF11 */
                Local1 [0x02] = BF12 /* \M7E0.BF12 */
                Local1 [0x03] = BF20 /* \M7E0.BF20 */
                Local1 [0x04] = BF21 /* \M7E0.BF21 */
                Local1 [0x05] = BF30 /* \M7E0.BF30 */
                Local1 [0x06] = BF31 /* \M7E0.BF31 */
            }

            M72A (Arg0, Local0, Local1)
        }
    }

    /* Create BankFields that spans the same bits */
    /* and check possible inconsistence, 1-bit offset. */
    /* m7e1(CallChain, OpRegion, BankNum) */
    Method (M7E1, 3, Serialized)
    {
        OperationRegion (OPRM, 0xFF, 0x00, 0x08)
        OperationRegion (OPRN, SystemIO, 0x10, 0x02)
        Field (OPRN, ByteAcc, NoLock, Preserve)
        {
            BNK0,   16
        }

        Concatenate (Arg0, "-m7e1", Arg0)
        CopyObject (Arg1, OPRM) /* \M7E1.OPRM */
        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
                ,   1,
            BF00,   3
        }

        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
                ,   1,
            BF10,   1,
            BF11,   1,
            BF12,   1
        }

        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
                ,   1,
            BF20,   1,
            BF21,   2
        }

        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
                ,   1,
            BF30,   2,
            BF31,   1
        }

        Local0 = 0x08
        Local1 = Package (0x07)
            {
                BF10,
                BF11,
                BF12,
                BF20,
                BF21,
                BF30,
                BF31
            }
        While (Local0)
        {
            Local0--
            BF00 = Local0
            If (Y118){}
            Else
            {
                Local1 [0x00] = BF10 /* \M7E1.BF10 */
                Local1 [0x01] = BF11 /* \M7E1.BF11 */
                Local1 [0x02] = BF12 /* \M7E1.BF12 */
                Local1 [0x03] = BF20 /* \M7E1.BF20 */
                Local1 [0x04] = BF21 /* \M7E1.BF21 */
                Local1 [0x05] = BF30 /* \M7E1.BF30 */
                Local1 [0x06] = BF31 /* \M7E1.BF31 */
            }

            M72A (Arg0, Local0, Local1)
        }
    }

    /* Create BankFields that spans the same bits */
    /* and check possible inconsistence, 2-bit offset. */
    /* m7e2(CallChain, OpRegion, BankNum) */
    Method (M7E2, 3, Serialized)
    {
        OperationRegion (OPRM, 0xFF, 0x00, 0x08)
        OperationRegion (OPRN, SystemIO, 0x10, 0x02)
        Field (OPRN, ByteAcc, NoLock, Preserve)
        {
            BNK0,   16
        }

        Concatenate (Arg0, "-m7e2", Arg0)
        CopyObject (Arg1, OPRM) /* \M7E2.OPRM */
        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
                ,   2,
            BF00,   3
        }

        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
                ,   2,
            BF10,   1,
            BF11,   1,
            BF12,   1
        }

        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
                ,   2,
            BF20,   1,
            BF21,   2
        }

        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
                ,   2,
            BF30,   2,
            BF31,   1
        }

        Local0 = 0x08
        Local1 = Package (0x07)
            {
                BF10,
                BF11,
                BF12,
                BF20,
                BF21,
                BF30,
                BF31
            }
        While (Local0)
        {
            Local0--
            BF00 = Local0
            If (Y118){}
            Else
            {
                Local1 [0x00] = BF10 /* \M7E2.BF10 */
                Local1 [0x01] = BF11 /* \M7E2.BF11 */
                Local1 [0x02] = BF12 /* \M7E2.BF12 */
                Local1 [0x03] = BF20 /* \M7E2.BF20 */
                Local1 [0x04] = BF21 /* \M7E2.BF21 */
                Local1 [0x05] = BF30 /* \M7E2.BF30 */
                Local1 [0x06] = BF31 /* \M7E2.BF31 */
            }

            M72A (Arg0, Local0, Local1)
        }
    }

    /* Create BankFields that spans the same bits */
    /* and check possible inconsistence, 3-bit offset. */
    /* m7e3(CallChain, OpRegion, BankNum) */
    Method (M7E3, 3, Serialized)
    {
        OperationRegion (OPRM, 0xFF, 0x00, 0x08)
        OperationRegion (OPRN, SystemIO, 0x10, 0x02)
        Field (OPRN, ByteAcc, NoLock, Preserve)
        {
            BNK0,   16
        }

        Concatenate (Arg0, "-m7e3", Arg0)
        CopyObject (Arg1, OPRM) /* \M7E3.OPRM */
        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
                ,   3,
            BF00,   3
        }

        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
                ,   3,
            BF10,   1,
            BF11,   1,
            BF12,   1
        }

        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
                ,   3,
            BF20,   1,
            BF21,   2
        }

        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
                ,   3,
            BF30,   2,
            BF31,   1
        }

        Local0 = 0x08
        Local1 = Package (0x07)
            {
                BF10,
                BF11,
                BF12,
                BF20,
                BF21,
                BF30,
                BF31
            }
        While (Local0)
        {
            Local0--
            BF00 = Local0
            If (Y118){}
            Else
            {
                Local1 [0x00] = BF10 /* \M7E3.BF10 */
                Local1 [0x01] = BF11 /* \M7E3.BF11 */
                Local1 [0x02] = BF12 /* \M7E3.BF12 */
                Local1 [0x03] = BF20 /* \M7E3.BF20 */
                Local1 [0x04] = BF21 /* \M7E3.BF21 */
                Local1 [0x05] = BF30 /* \M7E3.BF30 */
                Local1 [0x06] = BF31 /* \M7E3.BF31 */
            }

            M72A (Arg0, Local0, Local1)
        }
    }

    /* Create BankFields that spans the same bits */
    /* and check possible inconsistence, 4-bit offset. */
    /* m7e4(CallChain, OpRegion, BankNum) */
    Method (M7E4, 3, Serialized)
    {
        OperationRegion (OPRM, 0xFF, 0x00, 0x08)
        OperationRegion (OPRN, SystemIO, 0x10, 0x02)
        Field (OPRN, ByteAcc, NoLock, Preserve)
        {
            BNK0,   16
        }

        Concatenate (Arg0, "-m7e4", Arg0)
        CopyObject (Arg1, OPRM) /* \M7E4.OPRM */
        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
                ,   4,
            BF00,   3
        }

        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
                ,   4,
            BF10,   1,
            BF11,   1,
            BF12,   1
        }

        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
                ,   4,
            BF20,   1,
            BF21,   2
        }

        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
                ,   4,
            BF30,   2,
            BF31,   1
        }

        Local0 = 0x08
        Local1 = Package (0x07)
            {
                BF10,
                BF11,
                BF12,
                BF20,
                BF21,
                BF30,
                BF31
            }
        While (Local0)
        {
            Local0--
            BF00 = Local0
            If (Y118){}
            Else
            {
                Local1 [0x00] = BF10 /* \M7E4.BF10 */
                Local1 [0x01] = BF11 /* \M7E4.BF11 */
                Local1 [0x02] = BF12 /* \M7E4.BF12 */
                Local1 [0x03] = BF20 /* \M7E4.BF20 */
                Local1 [0x04] = BF21 /* \M7E4.BF21 */
                Local1 [0x05] = BF30 /* \M7E4.BF30 */
                Local1 [0x06] = BF31 /* \M7E4.BF31 */
            }

            M72A (Arg0, Local0, Local1)
        }
    }

    /* Create BankFields that spans the same bits */
    /* and check possible inconsistence, 5-bit offset. */
    /* m7e5(CallChain, OpRegion, BankNum) */
    Method (M7E5, 3, Serialized)
    {
        OperationRegion (OPRM, 0xFF, 0x00, 0x08)
        OperationRegion (OPRN, SystemIO, 0x10, 0x02)
        Field (OPRN, ByteAcc, NoLock, Preserve)
        {
            BNK0,   16
        }

        Concatenate (Arg0, "-m7e5", Arg0)
        CopyObject (Arg1, OPRM) /* \M7E5.OPRM */
        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
                ,   5,
            BF00,   3
        }

        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
                ,   5,
            BF10,   1,
            BF11,   1,
            BF12,   1
        }

        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
                ,   5,
            BF20,   1,
            BF21,   2
        }

        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
                ,   5,
            BF30,   2,
            BF31,   1
        }

        Local0 = 0x08
        Local1 = Package (0x07)
            {
                BF10,
                BF11,
                BF12,
                BF20,
                BF21,
                BF30,
                BF31
            }
        While (Local0)
        {
            Local0--
            BF00 = Local0
            If (Y118){}
            Else
            {
                Local1 [0x00] = BF10 /* \M7E5.BF10 */
                Local1 [0x01] = BF11 /* \M7E5.BF11 */
                Local1 [0x02] = BF12 /* \M7E5.BF12 */
                Local1 [0x03] = BF20 /* \M7E5.BF20 */
                Local1 [0x04] = BF21 /* \M7E5.BF21 */
                Local1 [0x05] = BF30 /* \M7E5.BF30 */
                Local1 [0x06] = BF31 /* \M7E5.BF31 */
            }

            M72A (Arg0, Local0, Local1)
        }
    }

    /* Create BankFields that spans the same bits */
    /* and check possible inconsistence, 6-bit offset. */
    /* m7e6(CallChain, OpRegion, BankNum) */
    Method (M7E6, 3, Serialized)
    {
        OperationRegion (OPRM, 0xFF, 0x00, 0x08)
        OperationRegion (OPRN, SystemIO, 0x10, 0x02)
        Field (OPRN, ByteAcc, NoLock, Preserve)
        {
            BNK0,   16
        }

        Concatenate (Arg0, "-m7e6", Arg0)
        CopyObject (Arg1, OPRM) /* \M7E6.OPRM */
        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
                ,   6,
            BF00,   3
        }

        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
                ,   6,
            BF10,   1,
            BF11,   1,
            BF12,   1
        }

        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
                ,   6,
            BF20,   1,
            BF21,   2
        }

        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
                ,   6,
            BF30,   2,
            BF31,   1
        }

        Local0 = 0x08
        Local1 = Package (0x07)
            {
                BF10,
                BF11,
                BF12,
                BF20,
                BF21,
                BF30,
                BF31
            }
        While (Local0)
        {
            Local0--
            BF00 = Local0
            If (Y118){}
            Else
            {
                Local1 [0x00] = BF10 /* \M7E6.BF10 */
                Local1 [0x01] = BF11 /* \M7E6.BF11 */
                Local1 [0x02] = BF12 /* \M7E6.BF12 */
                Local1 [0x03] = BF20 /* \M7E6.BF20 */
                Local1 [0x04] = BF21 /* \M7E6.BF21 */
                Local1 [0x05] = BF30 /* \M7E6.BF30 */
                Local1 [0x06] = BF31 /* \M7E6.BF31 */
            }

            M72A (Arg0, Local0, Local1)
        }
    }

    /* Create BankFields that spans the same bits */
    /* and check possible inconsistence, 7-bit offset. */
    /* m7e7(CallChain, OpRegion, BankNum) */
    Method (M7E7, 3, Serialized)
    {
        OperationRegion (OPRM, 0xFF, 0x00, 0x08)
        OperationRegion (OPRN, SystemIO, 0x10, 0x02)
        Field (OPRN, ByteAcc, NoLock, Preserve)
        {
            BNK0,   16
        }

        Concatenate (Arg0, "-m7e7", Arg0)
        CopyObject (Arg1, OPRM) /* \M7E7.OPRM */
        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
                ,   7,
            BF00,   3
        }

        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
                ,   7,
            BF10,   1,
            BF11,   1,
            BF12,   1
        }

        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
                ,   7,
            BF20,   1,
            BF21,   2
        }

        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
                ,   7,
            BF30,   2,
            BF31,   1
        }

        Local0 = 0x08
        Local1 = Package (0x07)
            {
                BF10,
                BF11,
                BF12,
                BF20,
                BF21,
                BF30,
                BF31
            }
        While (Local0)
        {
            Local0--
            BF00 = Local0
            If (Y118){}
            Else
            {
                Local1 [0x00] = BF10 /* \M7E7.BF10 */
                Local1 [0x01] = BF11 /* \M7E7.BF11 */
                Local1 [0x02] = BF12 /* \M7E7.BF12 */
                Local1 [0x03] = BF20 /* \M7E7.BF20 */
                Local1 [0x04] = BF21 /* \M7E7.BF21 */
                Local1 [0x05] = BF30 /* \M7E7.BF30 */
                Local1 [0x06] = BF31 /* \M7E7.BF31 */
            }

            M72A (Arg0, Local0, Local1)
        }
    }

    /* Create BankFields that spans the same bits */
    /* and check possible inconsistence, 8-bit offset. */
    /* m7e8(CallChain, OpRegion, BankNum) */
    Method (M7E8, 3, Serialized)
    {
        OperationRegion (OPRM, 0xFF, 0x00, 0x08)
        OperationRegion (OPRN, SystemIO, 0x10, 0x02)
        Field (OPRN, ByteAcc, NoLock, Preserve)
        {
            BNK0,   16
        }

        Concatenate (Arg0, "-m7e8", Arg0)
        CopyObject (Arg1, OPRM) /* \M7E8.OPRM */
        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
            Offset (0x01),
            BF00,   3
        }

        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
            Offset (0x01),
            BF10,   1,
            BF11,   1,
            BF12,   1
        }

        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
            Offset (0x01),
            BF20,   1,
            BF21,   2
        }

        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
            Offset (0x01),
            BF30,   2,
            BF31,   1
        }

        Local0 = 0x08
        Local1 = Package (0x07)
            {
                BF10,
                BF11,
                BF12,
                BF20,
                BF21,
                BF30,
                BF31
            }
        While (Local0)
        {
            Local0--
            BF00 = Local0
            If (Y118){}
            Else
            {
                Local1 [0x00] = BF10 /* \M7E8.BF10 */
                Local1 [0x01] = BF11 /* \M7E8.BF11 */
                Local1 [0x02] = BF12 /* \M7E8.BF12 */
                Local1 [0x03] = BF20 /* \M7E8.BF20 */
                Local1 [0x04] = BF21 /* \M7E8.BF21 */
                Local1 [0x05] = BF30 /* \M7E8.BF30 */
                Local1 [0x06] = BF31 /* \M7E8.BF31 */
            }

            M72A (Arg0, Local0, Local1)
        }
    }

    /* Create BankFields that spans the same bits */
    /* and check possible inconsistence, 2046-bit offset. */
    /* m7e9(CallChain, OpRegion, BankNum) */
    Method (M7E9, 3, Serialized)
    {
        OperationRegion (OPRM, 0xFF, 0x00, 0x0101)
        OperationRegion (OPRN, SystemIO, 0x10, 0x02)
        Field (OPRN, ByteAcc, NoLock, Preserve)
        {
            BNK0,   16
        }

        Concatenate (Arg0, "-m7e9", Arg0)
        CopyObject (Arg1, OPRM) /* \M7E9.OPRM */
        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
                ,   2046,
            BF00,   3
        }

        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
                ,   2046,
            BF10,   1,
            BF11,   1,
            BF12,   1
        }

        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
                ,   2046,
            BF20,   1,
            BF21,   2
        }

        BankField (OPRM, BNK0, Arg2, ByteAcc, NoLock, Preserve)
        {
                ,   2046,
            BF30,   2,
            BF31,   1
        }

        Local0 = 0x08
        Local1 = Package (0x07)
            {
                BF10,
                BF11,
                BF12,
                BF20,
                BF21,
                BF30,
                BF31
            }
        While (Local0)
        {
            Local0--
            BF00 = Local0
            If (Y118){}
            Else
            {
                Local1 [0x00] = BF10 /* \M7E9.BF10 */
                Local1 [0x01] = BF11 /* \M7E9.BF11 */
                Local1 [0x02] = BF12 /* \M7E9.BF12 */
                Local1 [0x03] = BF20 /* \M7E9.BF20 */
                Local1 [0x04] = BF21 /* \M7E9.BF21 */
                Local1 [0x05] = BF30 /* \M7E9.BF30 */
                Local1 [0x06] = BF31 /* \M7E9.BF31 */
            }

            M72A (Arg0, Local0, Local1)
        }
    }

    /* Check non-constant Bank value */

    Method (M7C7, 1, Serialized)
    {
        Field (OPRI, ByteAcc, NoLock, Preserve)
        {
            BNK0,   8
        }

        Name (BVAL, 0x02)
        Method (CHCK, 3, NotSerialized)
        {
            Local0 = RefOf (Arg1)
            /* Write */

            BNK0 = 0xFF
            M7BF (Arg0, BNK0, 0xFF, (Arg2 + 0x00))
            DerefOf (Local0) = 0x67
            M7BF (Arg0, BNK0, 0x02, (Arg2 + 0x01))
            /* Read */

            BNK0 = 0xFF
            M7BF (Arg0, BNK0, 0xFF, (Arg2 + 0x02))
            Local1 = DerefOf (Arg1)
            M7BF (Arg0, Local1, 0x67, (Arg2 + 0x03))
            M7BF (Arg0, BNK0, 0x02, (Arg2 + 0x04))
        }

        /* ArgX */

        Method (M000, 2, Serialized)
        {
            BankField (OPRJ, BNK0, Arg1, ByteAcc, NoLock, Preserve)
            {
                Offset (0x08),
                BF00,   8
            }

            CHCK (Arg0, RefOf (BF00), 0x5F)
        }

        /* Named */

        Method (M001, 1, Serialized)
        {
            BankField (OPRJ, BNK0, BVAL, ByteAcc, NoLock, Preserve)
            {
                Offset (0x08),
                BF00,   8
            }

            CHCK (Arg0, RefOf (BF00), 0x64)
        }

        /* LocalX */

        Method (M002, 1, Serialized)
        {
            Local0 = BVAL /* \M7C7.BVAL */
            BankField (OPRJ, BNK0, Local0, ByteAcc, NoLock, Preserve)
            {
                Offset (0x08),
                BF00,   8
            }

            CHCK (Arg0, RefOf (BF00), 0x69)
        }

        /* Expression */

        Method (M003, 1, Serialized)
        {
            Local0 = 0x01
            BankField (OPRJ, BNK0, (Local0 + 0x01), ByteAcc, NoLock, Preserve)
            {
                Offset (0x08),
                BF00,   8
            }

            CHCK (Arg0, RefOf (BF00), 0x6E)
        }

        Concatenate (Arg0, "-m7c7", Arg0)
        M000 (Arg0, 0x02)
        M001 (Arg0)
        M002 (Arg0)
        M003 (Arg0)
    }

    /* Check non-Integer Bank value */

    Method (M7C8, 1, Serialized)
    {
        Field (OPRI, ByteAcc, NoLock, Preserve)
        {
            BNK0,   8
        }

        Name (VAL0, 0x02)
        Name (VALB, Buffer (0x01)
        {
             0x02                                             // .
        })
        Name (VALS, "2")
        BankField (OPRJ, BNK0, 0x02, ByteAcc, NoLock, Preserve)
        {
            Offset (0x08),
            BF00,   32
        }

        /* */
        /* BUG: ToInteger should not be necessary. The buffer and string */
        /* arguments should be implicitly converted to integers. */
        /* */
        BankField (OPRJ, BNK0, ToInteger (VALB), ByteAcc, NoLock, Preserve)
        {
            Offset (0x08),
            BF01,   32
        }

        BankField (OPRJ, BNK0, ToInteger (VALS), ByteAcc, NoLock, Preserve)
        {
            Offset (0x08),
            BF02,   32
        }

        Name (I000, 0x12345678)
        Method (M000, 3, Serialized)
        {
            Local0 = 0x01
            BankField (OPRJ, BNK0, Arg1, ByteAcc, NoLock, Preserve)
            {
                Offset (0x08),
                BF03,   32
            }

            If ((BF03 != I000))
            {
                ERR (Arg0, Z145, __LINE__, 0x00, 0x00, BF03, I000)
            }
        }

        Concatenate (Arg0, "-m7c8", Arg0)
        BF00 = I000 /* \M7C8.I000 */
        If ((BF00 != I000))
        {
            ERR (Arg0, Z145, __LINE__, 0x00, 0x00, BF00, I000)
        }

        If ((BF01 != I000))
        {
            ERR (Arg0, Z145, __LINE__, 0x00, 0x00, BF00, I000)
        }

        If ((BF02 != I000))
        {
            ERR (Arg0, Z145, __LINE__, 0x00, 0x00, BF00, I000)
        }

        /* */
        /* BUG: ToInteger should not be necessary. The buffer and string */
        /* arguments should be implicitly converted to integers. */
        /* */
        M000 (Arg0, VAL0, 0x76)
        M000 (Arg0, ToInteger (VALB), 0x77)
        M000 (Arg0, ToInteger (VALS), 0x78)
    }

    /* Run-method */

    Method (BFC0, 0, Serialized)
    {
        /* Simple BankField test */

        SRMT ("m7c0")
        M7C0 (__METHOD__)
        /* Check BankField access: ByteAcc, NoLock, Preserve */

        SRMT ("m7c1")
        If (Y192)
        {
            M7C1 (__METHOD__)
        }
        Else
        {
            BLCK ()
        }

        /* Check BankField access: WordAcc, NoLock, WriteAsOnes */

        SRMT ("m7c2")
        If (Y192)
        {
            M7C2 (__METHOD__)
        }
        Else
        {
            BLCK ()
        }

        /* Check BankField access: DWordAcc, NoLock, WriteAsZeros */

        SRMT ("m7c3")
        If (Y192)
        {
            M7C3 (__METHOD__)
        }
        Else
        {
            BLCK ()
        }

        /* Check BankField access: QWordAcc, NoLock, Preserve */

        SRMT ("m7c4")
        If (Y192)
        {
            M7C4 (__METHOD__)
        }
        Else
        {
            BLCK ()
        }

        /* Check BankField access: AnyAcc, Lock, Preserve */

        SRMT ("m7c5")
        If (Y192)
        {
            M7C5 (__METHOD__)
        }
        Else
        {
            BLCK ()
        }

        /* Splitting of BankFields */

        SRMT ("m7c6")
        If (Y192)
        {
            M7C6 (__METHOD__)
        }
        Else
        {
            BLCK ()
        }

        /* Non-constant Bank value */

        SRMT ("m7c7")
        If (Y178)
        {
            M7C7 (__METHOD__)
        }
        Else
        {
            BLCK ()
        }

        /* Non-Integer Bank value */

        SRMT ("m7c8")
        If (Y178)
        {
            M7C8 (__METHOD__)
        }
        Else
        {
            BLCK ()
        }
    }
