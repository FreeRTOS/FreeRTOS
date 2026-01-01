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
     * IndexField objects definition and processing
     */
    /*
     * On testing following issues should be covered:
     * - Operation Regions of different Region Space types application
     *   for index/data fields in IndexField objects definition,
     * - application of any allowed AccessType Keywords,
     * - application of any allowed LockRule Keywords,
     * - application of any allowed UpdateRule Keywords,
     * - application of the Offset macros in the FieldUnitList,
     * - application of the AccessAs macros in the FieldUnitList,
     * - on writing taking into account the Access Type in accord with
     the Update Rule,
     * - AccessAs macros influence on the remaining Field Units within the list,
     * - access to IndexField objects in accord with the index/data-style
     *   representation,
     * - access to IndexField objects located on boundary of AccessType Unit,
     * - integer/buffer representation of the Unit contents as depends on its
     *   Length and DSDT ComplianceRevision (32/64-bit Integer),
     * - Data Type Conversion Rules on storing to IndexFields.
     *
     * Can not be tested following issues:
     * - exact use of given Access Type alignment on Access to Unit data,
     * - exact functioning of data exchange based on IndexField functionality,
     * - exact use of specific Conversion Rules on storing of Buffers or Strings.
     */
    Name (Z144, 0x90)
    OperationRegion (OPRK, SystemMemory, 0x0200, 0x10)
    Field (OPRK, ByteAcc, NoLock, Preserve)
    {
        FK32,   32
    }

    Field (OPRK, ByteAcc, NoLock, Preserve)
    {
        FK64,   64
    }

    Field (OPRK, ByteAcc, NoLock, Preserve)
    {
        FK28,   128
    }

    Method (M770, 1, Serialized)
    {
        Field (OPRK, ByteAcc, NoLock, Preserve)
        {
            IDX0,   8,
            DTA0,   8
        }

        IndexField (IDX0, DTA0, ByteAcc, NoLock, Preserve)
        {
            Offset (0x1A),
            REG0,   8,
            Offset (0x5B),
            REG1,   8,
            Offset (0x9C),
            REG2,   8,
            Offset (0xED),
            REG3,   8
        }

        Name (I000, 0x1122)
        Concatenate (Arg0, "-m770", Arg0)
        Debug = "TEST: m770, initial IndexFields check"
        /* Check object types */

        Local0 = ObjectType (REG0)
        Local1 = C00D /* \C00D */
        If ((Local0 != Local1))
        {
            ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Local0, Local1)
        }

        Local0 = ObjectType (REG1)
        Local1 = C00D /* \C00D */
        If ((Local0 != Local1))
        {
            ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Local0, Local1)
        }

        Local0 = ObjectType (REG2)
        Local1 = C00D /* \C00D */
        If ((Local1 != Local0))
        {
            ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Local0, Local1)
        }

        Local0 = ObjectType (REG3)
        Local1 = C00D /* \C00D */
        If ((Local1 != Local0))
        {
            ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Local0, Local1)
        }

        /* Check actual writes to the IndexField(s). */
        /* Uses fk32 overlay to check what exactly was written to the */
        /* Index/Data register pair. */
        FK32 = I000 /* \M770.I000 */
        REG0 = 0xF1
        Local0 = FK32 /* \FK32 */
        Local1 = 0xF11A
        If ((Local1 != Local0))
        {
            ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Local0, Local1)
        }

        FK32 = I000 /* \M770.I000 */
        REG1 = 0xD2
        Local0 = FK32 /* \FK32 */
        Local1 = 0xD25B
        If ((Local1 != Local0))
        {
            ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Local0, Local1)
        }

        FK32 = I000 /* \M770.I000 */
        REG2 = 0x93
        Local0 = FK32 /* \FK32 */
        Local1 = 0x939C
        If ((Local1 != Local0))
        {
            ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Local0, Local1)
        }

        FK32 = I000 /* \M770.I000 */
        REG3 = 0x54
        Local0 = FK32 /* \FK32 */
        Local1 = 0x54ED
        If ((Local1 != Local0))
        {
            ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Local0, Local1)
        }
    }

    /* Access to 1-bit IndexFields, ByteAcc */

    Method (M771, 1, Serialized)
    {
        Concatenate (Arg0, "-m771", Arg0)
        Debug = "TEST: m771, Check Access to 1-bit IndexFields, ByteAcc"
        Field (OPRK, ByteAcc, NoLock, WriteAsZeros)
        {
            IDX0,   16,
            DTA0,   16
        }

        IndexField (IDX0, DTA0, ByteAcc, NoLock, WriteAsZeros)
        {
            IDF0,   1,
                ,   6,
            IDF1,   1,
            IDF2,   1,
                ,   6,
            IDF3,   1,
            IDF4,   1,
                ,   6,
            IDF5,   1,
            IDF6,   1,
                ,   6,
            IDF7,   1
        }

        M77E (Arg0, 0x01, RefOf (IDF0), RefOf (FK32), 0xFFFFFFFF, 0x00010000, 0x00)
        M77E (Arg0, 0x01, RefOf (IDF1), RefOf (FK32), 0xFFFFFFFF, 0x00800000, 0x01)
        M77E (Arg0, 0x01, RefOf (IDF2), RefOf (FK32), 0xFFFFFFFF, 0x00010001, 0x02)
        M77E (Arg0, 0x01, RefOf (IDF3), RefOf (FK32), 0xFFFFFFFF, 0x00800001, 0x03)
        M77E (Arg0, 0x01, RefOf (IDF4), RefOf (FK32), 0xFFFFFFFF, 0x00010002, 0x04)
        M77E (Arg0, 0x01, RefOf (IDF5), RefOf (FK32), 0xFFFFFFFF, 0x00800002, 0x05)
        M77E (Arg0, 0x01, RefOf (IDF6), RefOf (FK32), 0xFFFFFFFF, 0x00010003, 0x06)
        M77E (Arg0, 0x01, RefOf (IDF7), RefOf (FK32), 0xFFFFFFFF, 0x00800003, 0x07)
    }

    /* Access to 1-bit IndexFields, WordAcc */

    Method (M772, 1, Serialized)
    {
        Concatenate (Arg0, "-m772", Arg0)
        Debug = "TEST: m772, Check Access to 1-bit IndexFields, WordAcc"
        Field (OPRK, ByteAcc, NoLock, WriteAsZeros)
        {
            IDX0,   16,
            DTA0,   16
        }

        IndexField (IDX0, DTA0, WordAcc, NoLock, WriteAsZeros)
        {
            IDF0,   1,
                ,   6,
            IDF1,   1,
            IDF2,   1,
                ,   6,
            IDF3,   1,
            IDF4,   1,
                ,   6,
            IDF5,   1,
            IDF6,   1,
                ,   6,
            IDF7,   1
        }

        M77E (Arg0, 0x01, RefOf (IDF0), RefOf (FK32), 0xFFFFFFFF, 0x00010000, 0x00)
        M77E (Arg0, 0x01, RefOf (IDF1), RefOf (FK32), 0xFFFFFFFF, 0x00800000, 0x01)
        M77E (Arg0, 0x01, RefOf (IDF2), RefOf (FK32), 0xFFFFFFFF, 0x01000000, 0x02)
        M77E (Arg0, 0x01, RefOf (IDF3), RefOf (FK32), 0xFFFFFFFF, 0x80000000, 0x03)
        M77E (Arg0, 0x01, RefOf (IDF4), RefOf (FK32), 0xFFFFFFFF, 0x00010002, 0x04)
        M77E (Arg0, 0x01, RefOf (IDF5), RefOf (FK32), 0xFFFFFFFF, 0x00800002, 0x05)
        M77E (Arg0, 0x01, RefOf (IDF6), RefOf (FK32), 0xFFFFFFFF, 0x01000002, 0x06)
        M77E (Arg0, 0x01, RefOf (IDF7), RefOf (FK32), 0xFFFFFFFF, 0x80000002, 0x07)
    }

    /* Access to 1-bit IndexFields, DWordAcc */

    Method (M773, 1, Serialized)
    {
        Concatenate (Arg0, "-m773", Arg0)
        Debug = "TEST: m773, Check Access to 1-bit IndexFields, DWordAcc"
        Field (OPRK, ByteAcc, NoLock, WriteAsZeros)
        {
            IDX0,   32,
            DTA0,   32
        }

        IndexField (IDX0, DTA0, DWordAcc, NoLock, WriteAsZeros)
        {
            IDF0,   1,
                ,   14,
            IDF1,   1,
            IDF2,   1,
                ,   14,
            IDF3,   1,
            IDF4,   1,
                ,   14,
            IDF5,   1,
            IDF6,   1,
                ,   14,
            IDF7,   1
        }

        If (F64)
        {
            Local0 = 0xFFFFFFFFFFFFFFFF
        }
        Else
        {
            Local0 = Buffer (0x08)
                {
                     0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF   // ........
                }
        }

        M77E (Arg0, 0x01, RefOf (IDF0), RefOf (FK64), Local0, Buffer (0x08)
            {
                 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00   // ........
            }, 0x00)
        M77E (Arg0, 0x01, RefOf (IDF1), RefOf (FK64), Local0, Buffer (0x08)
            {
                 0x00, 0x00, 0x00, 0x00, 0x00, 0x80, 0x00, 0x00   // ........
            }, 0x01)
        M77E (Arg0, 0x01, RefOf (IDF2), RefOf (FK64), Local0, Buffer (0x08)
            {
                 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00   // ........
            }, 0x02)
        M77E (Arg0, 0x01, RefOf (IDF3), RefOf (FK64), Local0, Buffer (0x08)
            {
                 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80   // ........
            }, 0x03)
        M77E (Arg0, 0x01, RefOf (IDF4), RefOf (FK64), Local0, Buffer (0x08)
            {
                 0x04, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00   // ........
            }, 0x04)
        M77E (Arg0, 0x01, RefOf (IDF5), RefOf (FK64), Local0, Buffer (0x08)
            {
                 0x04, 0x00, 0x00, 0x00, 0x00, 0x80, 0x00, 0x00   // ........
            }, 0x05)
        M77E (Arg0, 0x01, RefOf (IDF6), RefOf (FK64), Local0, Buffer (0x08)
            {
                 0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00   // ........
            }, 0x06)
        M77E (Arg0, 0x01, RefOf (IDF7), RefOf (FK64), Local0, Buffer (0x08)
            {
                 0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80   // ........
            }, 0x07)
    }

    /* Access to 1-bit IndexFields, QWordAcc */

    Method (M774, 1, Serialized)
    {
        Concatenate (Arg0, "-m774", Arg0)
        Debug = "TEST: m774, Check Access to 1-bit IndexFields, QWordAcc"
        Field (OPRK, ByteAcc, NoLock, WriteAsZeros)
        {
            IDX0,   64,
            DTA0,   64
        }

        IndexField (IDX0, DTA0, QWordAcc, NoLock, WriteAsZeros)
        {
            IDF0,   1,
                ,   30,
            IDF1,   1,
            IDF2,   1,
                ,   30,
            IDF3,   1,
            IDF4,   1,
                ,   30,
            IDF5,   1,
            IDF6,   1,
                ,   30,
            IDF7,   1
        }

        Local0 = Buffer (0x10)
            {
                /* 0000 */  0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,  // ........
                /* 0008 */  0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF   // ........
            }
        M77E (Arg0, 0x01, RefOf (IDF0), RefOf (FK28), Local0, Buffer (0x10)
            {
                /* 0000 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // ........
            }, 0x00)
        M77E (Arg0, 0x01, RefOf (IDF1), RefOf (FK28), Local0, Buffer (0x10)
            {
                /* 0000 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x00, 0x00, 0x00, 0x80, 0x00, 0x00, 0x00, 0x00   // ........
            }, 0x01)
        M77E (Arg0, 0x01, RefOf (IDF2), RefOf (FK28), Local0, Buffer (0x10)
            {
                /* 0000 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00   // ........
            }, 0x02)
        M77E (Arg0, 0x01, RefOf (IDF3), RefOf (FK28), Local0, Buffer (0x10)
            {
                /* 0000 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80   // ........
            }, 0x03)
        M77E (Arg0, 0x01, RefOf (IDF4), RefOf (FK28), Local0, Buffer (0x10)
            {
                /* 0000 */  0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00   // ........
            }, 0x04)
        M77E (Arg0, 0x01, RefOf (IDF5), RefOf (FK28), Local0, Buffer (0x10)
            {
                /* 0000 */  0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x00, 0x00, 0x00, 0x80, 0x00, 0x00, 0x00, 0x00   // ........
            }, 0x05)
        M77E (Arg0, 0x01, RefOf (IDF6), RefOf (FK28), Local0, Buffer (0x10)
            {
                /* 0000 */  0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00   // ........
            }, 0x06)
        M77E (Arg0, 0x01, RefOf (IDF7), RefOf (FK28), Local0, Buffer (0x10)
            {
                /* 0000 */  0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,  // ........
                /* 0008 */  0x00, 0x00, 0x00, 0x80, 0x00, 0x00, 0x00, 0x80   // ........
            }, 0x07)
    }

    /* Store to the IndexField and check Index/Data common Region Field */
    /*m77e(CallChain, Source, IndexField, Common, Filler, BenchMark, ErrNum) */
    Method (M77E, 7, NotSerialized)
    {
        Concatenate (Arg0, "-m77e", Arg0)
        Local0 = RefOf (Arg2)
        Local1 = RefOf (Arg3)
        /* Fill Index/Data common Region Field */

        DerefOf (Local1) = Arg4
        /* Store to the IndexField */

        DerefOf (Local0) = Arg1
        /* Retrieve Index/Data common Region Field */

        Local2 = DerefOf (Arg3)
        If ((ObjectType (Arg4) == 0x01))
        {
            ToInteger (Arg5, Arg5)
        }

        If ((Arg5 != Local2))
        {
            ERR (Arg0, Z144, __LINE__, Z144, Arg6, Local2, Arg5)
        }

        /* Fill then immediately read */
        /* Fill Index/Data common Region Field */
        DerefOf (Local1) = Arg4
        /* Read from the IndexField */

        Local2 = DerefOf (Arg2)
        If ((Arg1 != Local2))
        {
            ERR (Arg0, Z144, __LINE__, Z144, Arg6, Local2, Arg1)
        }
        /*
     * November 2011:
     * This code does not make sense. It fills the region overlay and then
     * reads the IndexField, and expects the resulting data to match the
     * compare value (BenchMark). Commented out.
     */
    /*
     // Retrieve Index/Data common Region Field
     Store(Derefof(arg3), Local2)
     if (LNotEqual(arg5, Local2)) {
     err(arg0, z144, __LINE__, z144, arg6, Local2, arg5)
     }
     */
    }

    /* Splitting of IndexFields */
    /* m775(CallChain) */
    Method (M775, 1, Serialized)
    {
        OperationRegion (OPR0, SystemMemory, 0x03E8, 0x08)
        Debug = "TEST: m775, Check Splitting of IndexFields"
        Concatenate (Arg0, "-m775", Arg0)
        M780 (Arg0, OPR0)
        M781 (Arg0, OPR0)
        M782 (Arg0, OPR0)
        M783 (Arg0, OPR0)
        M784 (Arg0, OPR0)
        M785 (Arg0, OPR0)
        M786 (Arg0, OPR0)
        M787 (Arg0, OPR0)
        M788 (Arg0, OPR0)
        M789 (Arg0, OPR0)
    }

    /* Create IndexFields that spans the same bits */
    /* and check possible inconsistence, 0-bit offset. */
    /* m780(CallChain, OpRegion) */
    Method (M780, 2, Serialized)
    {
        OperationRegion (OPRM, 0xFF, 0x0100, 0x08)
        Concatenate (Arg0, "-m780", Arg0)
        CopyObject (Arg1, OPRM) /* \M780.OPRM */
        Field (OPRM, ByteAcc, NoLock, Preserve)
        {
            IDX0,   16,
            DAT0,   16
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
            Offset (0x00),
            IF00,   3
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
            Offset (0x00),
            IF10,   1,
            IF11,   1,
            IF12,   1
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
            Offset (0x00),
            IF20,   1,
            IF21,   2
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
            Offset (0x00),
            IF30,   2,
            IF31,   1
        }

        Local0 = 0x08
        Local1 = Package (0x07)
            {
                IF10,
                IF11,
                IF12,
                IF20,
                IF21,
                IF30,
                IF31
            }
        While (Local0)
        {
            Local0--
            IF00 = Local0
            If (Y118){}
            Else
            {
                Local1 [0x00] = IF10 /* \M780.IF10 */
                Local1 [0x01] = IF11 /* \M780.IF11 */
                Local1 [0x02] = IF12 /* \M780.IF12 */
                Local1 [0x03] = IF20 /* \M780.IF20 */
                Local1 [0x04] = IF21 /* \M780.IF21 */
                Local1 [0x05] = IF30 /* \M780.IF30 */
                Local1 [0x06] = IF31 /* \M780.IF31 */
            }

            M72A (Arg0, Local0, Local1)
        }
    }

    /* Create IndexFields that spans the same bits */
    /* and check possible inconsistence, 1-bit offset. */
    /* m781(CallChain, OpRegion) */
    Method (M781, 2, Serialized)
    {
        OperationRegion (OPRM, 0xFF, 0x00, 0x08)
        Concatenate (Arg0, "-m781", Arg0)
        CopyObject (Arg1, OPRM) /* \M781.OPRM */
        Field (OPRM, WordAcc, NoLock, Preserve)
        {
            IDX0,   16,
            DAT0,   16
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
                ,   1,
            IF00,   3
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
                ,   1,
            IF10,   1,
            IF11,   1,
            IF12,   1
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
                ,   1,
            IF20,   1,
            IF21,   2
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
                ,   1,
            IF30,   2,
            IF31,   1
        }

        Local0 = 0x08
        Local1 = Package (0x07)
            {
                IF10,
                IF11,
                IF12,
                IF20,
                IF21,
                IF30,
                IF31
            }
        While (Local0)
        {
            Local0--
            IF00 = Local0
            If (Y118){}
            Else
            {
                Local1 [0x00] = IF10 /* \M781.IF10 */
                Local1 [0x01] = IF11 /* \M781.IF11 */
                Local1 [0x02] = IF12 /* \M781.IF12 */
                Local1 [0x03] = IF20 /* \M781.IF20 */
                Local1 [0x04] = IF21 /* \M781.IF21 */
                Local1 [0x05] = IF30 /* \M781.IF30 */
                Local1 [0x06] = IF31 /* \M781.IF31 */
            }

            M72A (Arg0, Local0, Local1)
        }
    }

    /* Create IndexFields that spans the same bits */
    /* and check possible inconsistence, 2-bit offset. */
    /* m782(CallChain, OpRegion) */
    Method (M782, 2, Serialized)
    {
        OperationRegion (OPRM, 0xFF, 0x00, 0x08)
        Concatenate (Arg0, "-m782", Arg0)
        CopyObject (Arg1, OPRM) /* \M782.OPRM */
        Field (OPRM, DWordAcc, NoLock, Preserve)
        {
            IDX0,   32,
            DAT0,   32
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
                ,   2,
            IF00,   3
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
                ,   2,
            IF10,   1,
            IF11,   1,
            IF12,   1
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
                ,   2,
            IF20,   1,
            IF21,   2
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
                ,   2,
            IF30,   2,
            IF31,   1
        }

        Local0 = 0x08
        Local1 = Package (0x07)
            {
                IF10,
                IF11,
                IF12,
                IF20,
                IF21,
                IF30,
                IF31
            }
        While (Local0)
        {
            Local0--
            IF00 = Local0
            If (Y118){}
            Else
            {
                Local1 [0x00] = IF10 /* \M782.IF10 */
                Local1 [0x01] = IF11 /* \M782.IF11 */
                Local1 [0x02] = IF12 /* \M782.IF12 */
                Local1 [0x03] = IF20 /* \M782.IF20 */
                Local1 [0x04] = IF21 /* \M782.IF21 */
                Local1 [0x05] = IF30 /* \M782.IF30 */
                Local1 [0x06] = IF31 /* \M782.IF31 */
            }

            M72A (Arg0, Local0, Local1)
        }
    }

    /* Create IndexFields that spans the same bits */
    /* and check possible inconsistence, 3-bit offset. */
    /* m783(CallChain, OpRegion) */
    Method (M783, 2, Serialized)
    {
        OperationRegion (OPRM, 0xFF, 0x00, 0x08)
        Concatenate (Arg0, "-m783", Arg0)
        CopyObject (Arg1, OPRM) /* \M783.OPRM */
        Field (OPRM, ByteAcc, NoLock, WriteAsOnes)
        {
            IDX0,   16,
            DAT0,   16
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
                ,   3,
            IF00,   3
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
                ,   3,
            IF10,   1,
            IF11,   1,
            IF12,   1
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
                ,   3,
            IF20,   1,
            IF21,   2
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
                ,   3,
            IF30,   2,
            IF31,   1
        }

        Local0 = 0x08
        Local1 = Package (0x07)
            {
                IF10,
                IF11,
                IF12,
                IF20,
                IF21,
                IF30,
                IF31
            }
        While (Local0)
        {
            Local0--
            IF00 = Local0
            If (Y118){}
            Else
            {
                Local1 [0x00] = IF10 /* \M783.IF10 */
                Local1 [0x01] = IF11 /* \M783.IF11 */
                Local1 [0x02] = IF12 /* \M783.IF12 */
                Local1 [0x03] = IF20 /* \M783.IF20 */
                Local1 [0x04] = IF21 /* \M783.IF21 */
                Local1 [0x05] = IF30 /* \M783.IF30 */
                Local1 [0x06] = IF31 /* \M783.IF31 */
            }

            M72A (Arg0, Local0, Local1)
        }
    }

    /* Create IndexFields that spans the same bits */
    /* and check possible inconsistence, 4-bit offset. */
    /* m784(CallChain, OpRegion) */
    Method (M784, 2, Serialized)
    {
        OperationRegion (OPRM, 0xFF, 0x00, 0x08)
        Concatenate (Arg0, "-m784", Arg0)
        CopyObject (Arg1, OPRM) /* \M784.OPRM */
        Field (OPRM, WordAcc, NoLock, WriteAsOnes)
        {
            IDX0,   16,
            DAT0,   16
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
                ,   4,
            IF00,   3
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
                ,   4,
            IF10,   1,
            IF11,   1,
            IF12,   1
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
                ,   4,
            IF20,   1,
            IF21,   2
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
                ,   4,
            IF30,   2,
            IF31,   1
        }

        Local0 = 0x08
        Local1 = Package (0x07)
            {
                IF10,
                IF11,
                IF12,
                IF20,
                IF21,
                IF30,
                IF31
            }
        While (Local0)
        {
            Local0--
            IF00 = Local0
            If (Y118){}
            Else
            {
                Local1 [0x00] = IF10 /* \M784.IF10 */
                Local1 [0x01] = IF11 /* \M784.IF11 */
                Local1 [0x02] = IF12 /* \M784.IF12 */
                Local1 [0x03] = IF20 /* \M784.IF20 */
                Local1 [0x04] = IF21 /* \M784.IF21 */
                Local1 [0x05] = IF30 /* \M784.IF30 */
                Local1 [0x06] = IF31 /* \M784.IF31 */
            }

            M72A (Arg0, Local0, Local1)
        }
    }

    /* Create IndexFields that spans the same bits */
    /* and check possible inconsistence, 5-bit offset. */
    /* m785(CallChain, OpRegion) */
    Method (M785, 2, Serialized)
    {
        OperationRegion (OPRM, 0xFF, 0x00, 0x08)
        Concatenate (Arg0, "-m785", Arg0)
        CopyObject (Arg1, OPRM) /* \M785.OPRM */
        Field (OPRM, DWordAcc, NoLock, WriteAsOnes)
        {
            IDX0,   32,
            DAT0,   32
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
                ,   5,
            IF00,   3
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
                ,   5,
            IF10,   1,
            IF11,   1,
            IF12,   1
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
                ,   5,
            IF20,   1,
            IF21,   2
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
                ,   5,
            IF30,   2,
            IF31,   1
        }

        Local0 = 0x08
        Local1 = Package (0x07)
            {
                IF10,
                IF11,
                IF12,
                IF20,
                IF21,
                IF30,
                IF31
            }
        While (Local0)
        {
            Local0--
            IF00 = Local0
            If (Y118){}
            Else
            {
                Local1 [0x00] = IF10 /* \M785.IF10 */
                Local1 [0x01] = IF11 /* \M785.IF11 */
                Local1 [0x02] = IF12 /* \M785.IF12 */
                Local1 [0x03] = IF20 /* \M785.IF20 */
                Local1 [0x04] = IF21 /* \M785.IF21 */
                Local1 [0x05] = IF30 /* \M785.IF30 */
                Local1 [0x06] = IF31 /* \M785.IF31 */
            }

            M72A (Arg0, Local0, Local1)
        }
    }

    /* Create IndexFields that spans the same bits */
    /* and check possible inconsistence, 6-bit offset. */
    /* m786(CallChain, OpRegion) */
    Method (M786, 2, Serialized)
    {
        OperationRegion (OPRM, 0xFF, 0x00, 0x08)
        Concatenate (Arg0, "-m786", Arg0)
        CopyObject (Arg1, OPRM) /* \M786.OPRM */
        Field (OPRM, ByteAcc, NoLock, WriteAsZeros)
        {
            IDX0,   16,
            DAT0,   16
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
                ,   6,
            IF00,   3
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
                ,   6,
            IF10,   1,
            IF11,   1,
            IF12,   1
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
                ,   6,
            IF20,   1,
            IF21,   2
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
                ,   6,
            IF30,   2,
            IF31,   1
        }

        Local0 = 0x08
        Local1 = Package (0x07)
            {
                IF10,
                IF11,
                IF12,
                IF20,
                IF21,
                IF30,
                IF31
            }
        While (Local0)
        {
            Local0--
            IF00 = Local0
            If (Y118){}
            Else
            {
                Local1 [0x00] = IF10 /* \M786.IF10 */
                Local1 [0x01] = IF11 /* \M786.IF11 */
                Local1 [0x02] = IF12 /* \M786.IF12 */
                Local1 [0x03] = IF20 /* \M786.IF20 */
                Local1 [0x04] = IF21 /* \M786.IF21 */
                Local1 [0x05] = IF30 /* \M786.IF30 */
                Local1 [0x06] = IF31 /* \M786.IF31 */
            }

            M72A (Arg0, Local0, Local1)
        }
    }

    /* Create IndexFields that spans the same bits */
    /* and check possible inconsistence, 7-bit offset. */
    /* m787(CallChain, OpRegion) */
    Method (M787, 2, Serialized)
    {
        OperationRegion (OPRM, 0xFF, 0x00, 0x08)
        Concatenate (Arg0, "-m787", Arg0)
        CopyObject (Arg1, OPRM) /* \M787.OPRM */
        Field (OPRM, WordAcc, NoLock, WriteAsZeros)
        {
            IDX0,   16,
            DAT0,   16
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
                ,   7,
            IF00,   3
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
                ,   7,
            IF10,   1,
            IF11,   1,
            IF12,   1
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
                ,   7,
            IF20,   1,
            IF21,   2
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
                ,   7,
            IF30,   2,
            IF31,   1
        }

        Local0 = 0x08
        Local1 = Package (0x07)
            {
                IF10,
                IF11,
                IF12,
                IF20,
                IF21,
                IF30,
                IF31
            }
        While (Local0)
        {
            Local0--
            IF00 = Local0
            If (Y118){}
            Else
            {
                Local1 [0x00] = IF10 /* \M787.IF10 */
                Local1 [0x01] = IF11 /* \M787.IF11 */
                Local1 [0x02] = IF12 /* \M787.IF12 */
                Local1 [0x03] = IF20 /* \M787.IF20 */
                Local1 [0x04] = IF21 /* \M787.IF21 */
                Local1 [0x05] = IF30 /* \M787.IF30 */
                Local1 [0x06] = IF31 /* \M787.IF31 */
            }

            M72A (Arg0, Local0, Local1)
        }
    }

    /* Create IndexFields that spans the same bits */
    /* and check possible inconsistence, 8-bit offset. */
    /* m788(CallChain, OpRegion) */
    Method (M788, 2, Serialized)
    {
        OperationRegion (OPRM, 0xFF, 0x00, 0x08)
        Concatenate (Arg0, "-m788", Arg0)
        CopyObject (Arg1, OPRM) /* \M788.OPRM */
        Field (OPRM, DWordAcc, NoLock, WriteAsZeros)
        {
            IDX0,   32,
            DAT0,   32
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
            Offset (0x01),
            IF00,   3
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
            Offset (0x01),
            IF10,   1,
            IF11,   1,
            IF12,   1
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
            Offset (0x01),
            IF20,   1,
            IF21,   2
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
            Offset (0x01),
            IF30,   2,
            IF31,   1
        }

        Local0 = 0x08
        Local1 = Package (0x07)
            {
                IF10,
                IF11,
                IF12,
                IF20,
                IF21,
                IF30,
                IF31
            }
        While (Local0)
        {
            Local0--
            IF00 = Local0
            If (Y118){}
            Else
            {
                Local1 [0x00] = IF10 /* \M788.IF10 */
                Local1 [0x01] = IF11 /* \M788.IF11 */
                Local1 [0x02] = IF12 /* \M788.IF12 */
                Local1 [0x03] = IF20 /* \M788.IF20 */
                Local1 [0x04] = IF21 /* \M788.IF21 */
                Local1 [0x05] = IF30 /* \M788.IF30 */
                Local1 [0x06] = IF31 /* \M788.IF31 */
            }

            M72A (Arg0, Local0, Local1)
        }
    }

    /* Create IndexFields that spans the same bits */
    /* and check possible inconsistence, 2046-bit offset. */
    /* m789(CallChain, OpRegion) */
    Method (M789, 2, Serialized)
    {
        OperationRegion (OPRM, 0xFF, 0x00, 0x08)
        Concatenate (Arg0, "-m789", Arg0)
        CopyObject (Arg1, OPRM) /* \M789.OPRM */
        Field (OPRM, WordAcc, NoLock, Preserve)
        {
            IDX0,   16,
            DAT0,   16
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
                ,   2046,
            IF00,   3
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
                ,   2046,
            IF10,   1,
            IF11,   1,
            IF12,   1
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
                ,   2046,
            IF20,   1,
            IF21,   2
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
                ,   2046,
            IF30,   2,
            IF31,   1
        }

        Local0 = 0x08
        Local1 = Package (0x07)
            {
                IF10,
                IF11,
                IF12,
                IF20,
                IF21,
                IF30,
                IF31
            }
        While (Local0)
        {
            Local0--
            IF00 = Local0
            If (Y118){}
            Else
            {
                Local1 [0x00] = IF10 /* \M789.IF10 */
                Local1 [0x01] = IF11 /* \M789.IF11 */
                Local1 [0x02] = IF12 /* \M789.IF12 */
                Local1 [0x03] = IF20 /* \M789.IF20 */
                Local1 [0x04] = IF21 /* \M789.IF21 */
                Local1 [0x05] = IF30 /* \M789.IF30 */
                Local1 [0x06] = IF31 /* \M789.IF31 */
            }

            M72A (Arg0, Local0, Local1)
        }
    }

    /* Testing parameters Packages */
    /* Layout see in regionfield.asl */
    /* (ByteAcc, NoLock, Preserve) */
    Name (PP10, Package (0x05)
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
            "m790"
        }
    })
    /* (WordAcc, NoLock, WriteAsOnes) */

    Name (PP11, Package (0x05)
    {
        0x00,
        0x08,
        0x08,
        0x08,
        Package (0x06)
        {
            0x01,
            0x00,
            0x02,
            0x01,
            0x01,
            "m791"
        }
    })
    /* (DWordAcc, NoLock, WriteAsZeros) */

    Name (PP12, Package (0x05)
    {
        0x08,
        0x08,
        0x00,
        0x08,
        Package (0x06)
        {
            0x02,
            0x01,
            0x03,
            0x02,
            0x01,
            "m792"
        }
    })
    /* (QWordAcc, NoLock, Preserve) */

    Name (PP13, Package (0x05)
    {
        0x08,
        0x04,
        0x08,
        0x08,
        Package (0x06)
        {
            0x01,
            0x02,
            0x04,
            0x00,
            0x01,
            "m793"
        }
    })
    /* (AnyAcc, Lock, Preserve) */

    Name (PP14, Package (0x05)
    {
        0x0C,
        0x04,
        0x08,
        0x08,
        Package (0x06)
        {
            0x01,
            0x00,
            0x00,
            0x00,
            0x00,
            "m794"
        }
    })
    /* Check IndexField access: ByteAcc, NoLock, Preserve */
    /* m776(CallChain) */
    Method (M776, 1, NotSerialized)
    {
        Concatenate (Arg0, "-m776", Arg0)
        Debug = "TEST: m776, Check IndexFields specified as (ByteAcc, NoLock, Preserve)"
        M72F (Arg0, 0x01, "pp10", PP10)
    }

    /* Check IndexField access: WordAcc, NoLock, WriteAsOnes */
    /* m777(CallChain) */
    Method (M777, 1, NotSerialized)
    {
        Concatenate (Arg0, "-m777", Arg0)
        Debug = "TEST: m777, Check IndexFields specified as (WordAcc, NoLock, WriteAsOnes)"
        M72F (Arg0, 0x01, "pp11", PP11)
    }

    /* Check IndexField access: DWordAcc, NoLock, WriteAsZeros */
    /* m778(CallChain) */
    Method (M778, 1, NotSerialized)
    {
        Concatenate (Arg0, "-m778", Arg0)
        Debug = "TEST: m778, Check IndexFields specified as (DWordAcc, NoLock, WriteAsZeros)"
        M72F (Arg0, 0x01, "pp12", PP12)
    }

    /* Check IndexField access: QWordAcc, NoLock, Preserve */
    /* m779(CallChain) */
    Method (M779, 1, NotSerialized)
    {
        Concatenate (Arg0, "-m779", Arg0)
        Debug = "TEST: m779, Check IndexFields specified as (QWordAcc, NoLock, Preserve)"
        M72F (Arg0, 0x01, "pp13", PP13)
    }

    /* Check IndexField access: AnyAcc, Lock, Preserve */
    /* m77a(CallChain) */
    Method (M77A, 1, NotSerialized)
    {
        Concatenate (Arg0, "-m77a", Arg0)
        Debug = "TEST: m77a, Check IndexFields specified as (AnyAcc, Lock, Preserve)"
        M72F (Arg0, 0x01, "pp14", PP14)
    }

    /* Create IndexField Unit */
    /* (ByteAcc, NoLock, Preserve) */
    Method (M790, 6, Serialized)
    {
        OperationRegion (OPR0, SystemMemory, 0x0BB8, 0x87)
        /*
         * Consider different attributes of index/data fields
         * taking into account the following restrictions:
         * - the fields spanning the same access unit interfere,
         * - the fields exceeding 64 bits cause AE_BUFFER_OVERFLOW,
         * - index field exceeding 32 bits unexpectedly cause
         *   AE_BUFFER_OVERFLOW too,
         * - data field exceeding IndexField's Access Width
         *   causes overwriting of next memory bytes.
         */
        Field (OPR0, ByteAcc, NoLock, Preserve)
        {
            IDX0,   8,
            DAT0,   8
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
            G000,   2048
        }

        Field (OPR0, ByteAcc, NoLock, WriteAsOnes)
        {
            Offset (0x03),
            IDX1,   8,
            DAT1,   8
        }

        IndexField (IDX1, DAT1, ByteAcc, NoLock, Preserve)
        {
            G001,   2048
        }

        Field (OPR0, ByteAcc, NoLock, WriteAsZeros)
        {
            Offset (0x07),
            IDX2,   16,
            DAT2,   8
        }

        IndexField (IDX2, DAT2, ByteAcc, NoLock, Preserve)
        {
            G002,   2048
        }

        Field (OPR0, WordAcc, NoLock, Preserve)
        {
            Offset (0x0B),
            IDX3,   8,
            DAT3,   8
        }

        IndexField (IDX3, DAT3, ByteAcc, NoLock, Preserve)
        {
            G003,   2048
        }

        Field (OPR0, WordAcc, NoLock, WriteAsOnes)
        {
            Offset (0x0E),
            IDX4,   16,
            DAT4,   8
        }

        IndexField (IDX4, DAT4, ByteAcc, NoLock, Preserve)
        {
            G004,   2048
        }

        Field (OPR0, WordAcc, NoLock, WriteAsZeros)
        {
            Offset (0x12),
            IDX5,   32,
            DAT5,   8
        }

        IndexField (IDX5, DAT5, ByteAcc, NoLock, Preserve)
        {
            G005,   2048
        }

        Field (OPR0, DWordAcc, NoLock, Preserve)
        {
            Offset (0x1A),
            IDX6,   8,
            Offset (0x1C),
            DAT6,   8
        }

        IndexField (IDX6, DAT6, ByteAcc, NoLock, Preserve)
        {
            G006,   2048
        }

        Field (OPR0, DWordAcc, NoLock, WriteAsOnes)
        {
            Offset (0x20),
            IDX7,   32,
            DAT7,   8
        }

        IndexField (IDX7, DAT7, ByteAcc, NoLock, Preserve)
        {
            G007,   2048
        }

        Field (OPR0, DWordAcc, NoLock, WriteAsZeros)
        {
            Offset (0x28),
            IDX8,   32,
            DAT8,   8
        }

        IndexField (IDX8, DAT8, ByteAcc, NoLock, Preserve)
        {
            G008,   2048
        }

        Field (OPR0, QWordAcc, NoLock, Preserve)
        {
            Offset (0x38),
            IDX9,   8,
            Offset (0x40),
            DAT9,   8
        }

        IndexField (IDX9, DAT9, ByteAcc, NoLock, Preserve)
        {
            G009,   2048
        }

        Field (OPR0, QWordAcc, NoLock, WriteAsOnes)
        {
            Offset (0x48),
            Offset (0x4C),
            /* Index field exceeding 32 bits causes AE_BUFFER_OVERFLOW */
            /* IDXA, 64, */
            /* Do not allow index/data interference */
            IDXA,   32,
            DATA,   8
        }

        IndexField (IDXA, DATA, ByteAcc, NoLock, Preserve)
        {
            G00A,   2048
        }

        Field (OPR0, QWordAcc, NoLock, WriteAsZeros)
        {
            Offset (0x58),
            IDXB,   32,
            Offset (0x60),
            DATB,   8
        }

        IndexField (IDXB, DATB, ByteAcc, NoLock, Preserve)
        {
            G00B,   2048
        }

        Field (OPR0, AnyAcc, NoLock, Preserve)
        {
            Offset (0x68),
            IDXC,   8,
            DATC,   8
        }

        IndexField (IDXC, DATC, ByteAcc, NoLock, Preserve)
        {
            G00C,   2048
        }

        Field (OPR0, AnyAcc, NoLock, WriteAsOnes)
        {
            Offset (0x6B),
            /* Index field exceeding 32 bits causes AE_BUFFER_OVERFLOW */
            /* IDXD, 64, */
            IDXD,   32,
            DATD,   8
        }

        IndexField (IDXD, DATD, ByteAcc, NoLock, Preserve)
        {
            G00D,   2048
        }

        Field (OPR0, AnyAcc, NoLock, WriteAsZeros)
        {
            Offset (0x7B),
            IDXE,   32,
            DATE,   8
        }

        IndexField (IDXE, DATE, ByteAcc, NoLock, Preserve)
        {
            G00E,   2048
        }

        Concatenate (Arg0, "-m790", Arg0)
        BreakPoint
        Switch (ToInteger (Arg2))
        {
            Case (0x00)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F000,   1
                        }

                        Local3 = RefOf (F000)
                        Local4 = RefOf (G000)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX1, DAT1, ByteAcc, NoLock, Preserve)
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
                        IndexField (IDX2, DAT2, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F002,   7
                        }

                        Local3 = RefOf (F002)
                        Local4 = RefOf (G002)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX3, DAT3, WordAcc, NoLock, Preserve)
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
                        IndexField (IDX4, DAT4, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F004,   9
                        }

                        Local3 = RefOf (F004)
                        Local4 = RefOf (G004)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX5, DAT5, DWordAcc, NoLock, Preserve)
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
                        IndexField (IDX6, DAT6, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F006,   32
                        }

                        Local3 = RefOf (F006)
                        Local4 = RefOf (G006)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX7, DAT7, QWordAcc, NoLock, Preserve)
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
                        IndexField (IDX8, DAT8, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F008,   63
                        }

                        Local3 = RefOf (F008)
                        Local4 = RefOf (G008)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX9, DAT9, AnyAcc, NoLock, Preserve)
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
                        IndexField (IDXA, DATA, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F00A,   65
                        }

                        Local3 = RefOf (F00A)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x45)
                    {
                        IndexField (IDXB, DATB, ByteAcc, NoLock, Preserve)
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
                        IndexField (IDXC, DATC, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F00C,   129
                        }

                        Local3 = RefOf (F00C)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDXD, DATD, WordAcc, NoLock, Preserve)
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
                        IndexField (IDXE, DATE, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F00E,   1023
                        }

                        Local3 = RefOf (F00E)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX0, DAT0, DWordAcc, NoLock, Preserve)
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
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX1, DAT1, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x00),
                                ,   1,
                            F010,   1
                        }

                        Local3 = RefOf (F010)
                        Local4 = RefOf (G001)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX2, DAT2, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F011,   6
                        }

                        Local3 = RefOf (F011)
                        Local4 = RefOf (G002)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX3, DAT3, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x00),
                                ,   1,
                            F012,   7
                        }

                        Local3 = RefOf (F012)
                        Local4 = RefOf (G003)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX4, DAT4, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F013,   8
                        }

                        Local3 = RefOf (F013)
                        Local4 = RefOf (G004)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX5, DAT5, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x00),
                                ,   1,
                            F014,   9
                        }

                        Local3 = RefOf (F014)
                        Local4 = RefOf (G005)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX6, DAT6, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F015,   31
                        }

                        Local3 = RefOf (F015)
                        Local4 = RefOf (G006)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX7, DAT7, WordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x00),
                                ,   1,
                            F016,   32
                        }

                        Local3 = RefOf (F016)
                        Local4 = RefOf (G007)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX8, DAT8, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F017,   33
                        }

                        Local3 = RefOf (F017)
                        Local4 = RefOf (G008)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX9, DAT9, DWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x00),
                                ,   1,
                            F018,   63
                        }

                        Local3 = RefOf (F018)
                        Local4 = RefOf (G009)
                    }
                    Case (0x40)
                    {
                        IndexField (IDXA, DATA, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F019,   64
                        }

                        Local3 = RefOf (F019)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x41)
                    {
                        IndexField (IDXB, DATB, QWordAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x00),
                                ,   1,
                            F01A,   65
                        }

                        Local3 = RefOf (F01A)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x45)
                    {
                        IndexField (IDXC, DATC, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F01B,   69
                        }

                        Local3 = RefOf (F01B)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x81)
                    {
                        IndexField (IDXD, DATD, AnyAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x00),
                                ,   1,
                            F01C,   129
                        }

                        Local3 = RefOf (F01C)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDXE, DATE, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F01D,   256
                        }

                        Local3 = RefOf (F01D)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
                        {
                            AccessAs (ByteAcc, 0x00),
                            Offset (0x00),
                                ,   1,
                            F01E,   1023
                        }

                        Local3 = RefOf (F01E)
                        Local4 = RefOf (G000)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX1, DAT1, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F01F,   1983
                        }

                        Local3 = RefOf (F01F)
                        Local4 = RefOf (G001)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX2, DAT2, ByteAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F020,   1
                        }

                        Local3 = RefOf (F020)
                        Local4 = RefOf (G002)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX3, DAT3, WordAcc, NoLock, Preserve)
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
                        IndexField (IDX4, DAT4, ByteAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F022,   7
                        }

                        Local3 = RefOf (F022)
                        Local4 = RefOf (G004)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX5, DAT5, DWordAcc, NoLock, Preserve)
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
                        IndexField (IDX6, DAT6, ByteAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F024,   9
                        }

                        Local3 = RefOf (F024)
                        Local4 = RefOf (G006)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX7, DAT7, QWordAcc, NoLock, Preserve)
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
                        IndexField (IDX8, DAT8, ByteAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F026,   32
                        }

                        Local3 = RefOf (F026)
                        Local4 = RefOf (G008)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX9, DAT9, AnyAcc, NoLock, Preserve)
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
                        IndexField (IDXA, DATA, ByteAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F028,   63
                        }

                        Local3 = RefOf (F028)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x40)
                    {
                        IndexField (IDXB, DATB, ByteAcc, NoLock, Preserve)
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
                        IndexField (IDXC, DATC, ByteAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F02A,   65
                        }

                        Local3 = RefOf (F02A)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x45)
                    {
                        IndexField (IDXD, DATD, WordAcc, NoLock, Preserve)
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
                        IndexField (IDXE, DATE, ByteAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F02C,   129
                        }

                        Local3 = RefOf (F02C)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX0, DAT0, DWordAcc, NoLock, Preserve)
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
                        IndexField (IDX1, DAT1, ByteAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F02E,   1023
                        }

                        Local3 = RefOf (F02E)
                        Local4 = RefOf (G001)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX2, DAT2, QWordAcc, NoLock, Preserve)
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
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX3, DAT3, AnyAcc, NoLock, Preserve)
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
                        IndexField (IDX4, DAT4, ByteAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F031,   6
                        }

                        Local3 = RefOf (F031)
                        Local4 = RefOf (G004)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX5, DAT5, ByteAcc, NoLock, Preserve)
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
                        IndexField (IDX6, DAT6, ByteAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F033,   8
                        }

                        Local3 = RefOf (F033)
                        Local4 = RefOf (G006)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX7, DAT7, WordAcc, NoLock, Preserve)
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
                        IndexField (IDX8, DAT8, ByteAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F035,   31
                        }

                        Local3 = RefOf (F035)
                        Local4 = RefOf (G008)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX9, DAT9, DWordAcc, NoLock, Preserve)
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
                        IndexField (IDXA, DATA, ByteAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F037,   33
                        }

                        Local3 = RefOf (F037)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDXB, DATB, QWordAcc, NoLock, Preserve)
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
                        IndexField (IDXC, DATC, ByteAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F039,   64
                        }

                        Local3 = RefOf (F039)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x41)
                    {
                        IndexField (IDXD, DATD, AnyAcc, NoLock, Preserve)
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
                        IndexField (IDXE, DATE, ByteAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F03B,   69
                        }

                        Local3 = RefOf (F03B)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
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
                        IndexField (IDX1, DAT1, ByteAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F03D,   256
                        }

                        Local3 = RefOf (F03D)
                        Local4 = RefOf (G001)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX2, DAT2, WordAcc, NoLock, Preserve)
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
                        IndexField (IDX3, DAT3, ByteAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F03F,   1983
                        }

                        Local3 = RefOf (F03F)
                        Local4 = RefOf (G003)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX4, DAT4, ByteAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F040,   1
                        }

                        Local3 = RefOf (F040)
                        Local4 = RefOf (G004)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX5, DAT5, DWordAcc, NoLock, Preserve)
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
                        IndexField (IDX6, DAT6, ByteAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F042,   7
                        }

                        Local3 = RefOf (F042)
                        Local4 = RefOf (G006)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX7, DAT7, QWordAcc, NoLock, Preserve)
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
                        IndexField (IDX8, DAT8, ByteAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F044,   9
                        }

                        Local3 = RefOf (F044)
                        Local4 = RefOf (G008)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX9, DAT9, AnyAcc, NoLock, Preserve)
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
                        IndexField (IDXA, DATA, ByteAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F046,   32
                        }

                        Local3 = RefOf (F046)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x21)
                    {
                        IndexField (IDXB, DATB, ByteAcc, NoLock, Preserve)
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
                        IndexField (IDXC, DATC, ByteAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F048,   63
                        }

                        Local3 = RefOf (F048)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x40)
                    {
                        IndexField (IDXD, DATD, WordAcc, NoLock, Preserve)
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
                        IndexField (IDXE, DATE, ByteAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F04A,   65
                        }

                        Local3 = RefOf (F04A)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX0, DAT0, DWordAcc, NoLock, Preserve)
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
                        IndexField (IDX1, DAT1, ByteAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F04C,   129
                        }

                        Local3 = RefOf (F04C)
                        Local4 = RefOf (G001)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX2, DAT2, QWordAcc, NoLock, Preserve)
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
                        IndexField (IDX3, DAT3, ByteAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F04E,   1023
                        }

                        Local3 = RefOf (F04E)
                        Local4 = RefOf (G003)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX4, DAT4, AnyAcc, NoLock, Preserve)
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
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX5, DAT5, ByteAcc, NoLock, Preserve)
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
                        IndexField (IDX6, DAT6, ByteAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F051,   6
                        }

                        Local3 = RefOf (F051)
                        Local4 = RefOf (G006)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX7, DAT7, WordAcc, NoLock, Preserve)
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
                        IndexField (IDX8, DAT8, ByteAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F053,   8
                        }

                        Local3 = RefOf (F053)
                        Local4 = RefOf (G008)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX9, DAT9, DWordAcc, NoLock, Preserve)
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
                        IndexField (IDXA, DATA, ByteAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F055,   31
                        }

                        Local3 = RefOf (F055)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x20)
                    {
                        IndexField (IDXB, DATB, QWordAcc, NoLock, Preserve)
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
                        IndexField (IDXC, DATC, ByteAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F057,   33
                        }

                        Local3 = RefOf (F057)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDXD, DATD, AnyAcc, NoLock, Preserve)
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
                        IndexField (IDXE, DATE, ByteAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F059,   64
                        }

                        Local3 = RefOf (F059)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
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
                        IndexField (IDX1, DAT1, ByteAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F05B,   69
                        }

                        Local3 = RefOf (F05B)
                        Local4 = RefOf (G001)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX2, DAT2, WordAcc, NoLock, Preserve)
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
                        IndexField (IDX3, DAT3, ByteAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F05D,   256
                        }

                        Local3 = RefOf (F05D)
                        Local4 = RefOf (G003)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX4, DAT4, WordAcc, NoLock, Preserve)
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
                        IndexField (IDX5, DAT5, ByteAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F05F,   1983
                        }

                        Local3 = RefOf (F05F)
                        Local4 = RefOf (G005)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX6, DAT6, ByteAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F060,   1
                        }

                        Local3 = RefOf (F060)
                        Local4 = RefOf (G006)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX7, DAT7, QWordAcc, NoLock, Preserve)
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
                        IndexField (IDX8, DAT8, ByteAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F062,   7
                        }

                        Local3 = RefOf (F062)
                        Local4 = RefOf (G008)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX9, DAT9, AnyAcc, NoLock, Preserve)
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
                        IndexField (IDXA, DATA, ByteAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F064,   9
                        }

                        Local3 = RefOf (F064)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDXB, DATB, ByteAcc, NoLock, Preserve)
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
                        IndexField (IDXC, DATC, ByteAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F066,   32
                        }

                        Local3 = RefOf (F066)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x21)
                    {
                        IndexField (IDXD, DATD, WordAcc, NoLock, Preserve)
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
                        IndexField (IDXE, DATE, ByteAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F068,   63
                        }

                        Local3 = RefOf (F068)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX0, DAT0, DWordAcc, NoLock, Preserve)
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
                        IndexField (IDX1, DAT1, ByteAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F06A,   65
                        }

                        Local3 = RefOf (F06A)
                        Local4 = RefOf (G001)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX2, DAT2, QWordAcc, NoLock, Preserve)
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
                        IndexField (IDX3, DAT3, ByteAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F06C,   129
                        }

                        Local3 = RefOf (F06C)
                        Local4 = RefOf (G003)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX4, DAT4, AnyAcc, NoLock, Preserve)
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
                        IndexField (IDX5, DAT5, ByteAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F06E,   1023
                        }

                        Local3 = RefOf (F06E)
                        Local4 = RefOf (G005)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX6, DAT6, ByteAcc, NoLock, Preserve)
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
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX7, DAT7, WordAcc, NoLock, Preserve)
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
                        IndexField (IDX8, DAT8, ByteAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F071,   6
                        }

                        Local3 = RefOf (F071)
                        Local4 = RefOf (G008)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX9, DAT9, DWordAcc, NoLock, Preserve)
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
                        IndexField (IDXA, DATA, ByteAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F073,   8
                        }

                        Local3 = RefOf (F073)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x09)
                    {
                        IndexField (IDXB, DATB, QWordAcc, NoLock, Preserve)
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
                        IndexField (IDXC, DATC, ByteAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F075,   31
                        }

                        Local3 = RefOf (F075)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x20)
                    {
                        IndexField (IDXD, DATD, AnyAcc, NoLock, Preserve)
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
                        IndexField (IDXE, DATE, ByteAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F077,   33
                        }

                        Local3 = RefOf (F077)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
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
                        IndexField (IDX1, DAT1, ByteAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F079,   64
                        }

                        Local3 = RefOf (F079)
                        Local4 = RefOf (G001)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX2, DAT2, WordAcc, NoLock, Preserve)
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
                        IndexField (IDX3, DAT3, ByteAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F07B,   69
                        }

                        Local3 = RefOf (F07B)
                        Local4 = RefOf (G003)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX4, DAT4, DWordAcc, NoLock, Preserve)
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
                        IndexField (IDX5, DAT5, ByteAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F07D,   256
                        }

                        Local3 = RefOf (F07D)
                        Local4 = RefOf (G005)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX6, DAT6, QWordAcc, NoLock, Preserve)
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
                        IndexField (IDX7, DAT7, ByteAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F07F,   1983
                        }

                        Local3 = RefOf (F07F)
                        Local4 = RefOf (G007)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX8, DAT8, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F080,   1
                        }

                        Local3 = RefOf (F080)
                        Local4 = RefOf (G008)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX9, DAT9, AnyAcc, NoLock, Preserve)
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
                        IndexField (IDXA, DATA, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F082,   7
                        }

                        Local3 = RefOf (F082)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x08)
                    {
                        IndexField (IDXB, DATB, ByteAcc, NoLock, Preserve)
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
                        IndexField (IDXC, DATC, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F084,   9
                        }

                        Local3 = RefOf (F084)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDXD, DATD, WordAcc, NoLock, Preserve)
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
                        IndexField (IDXE, DATE, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F086,   32
                        }

                        Local3 = RefOf (F086)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX0, DAT0, DWordAcc, NoLock, Preserve)
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
                        IndexField (IDX1, DAT1, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F088,   63
                        }

                        Local3 = RefOf (F088)
                        Local4 = RefOf (G001)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX2, DAT2, QWordAcc, NoLock, Preserve)
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
                        IndexField (IDX3, DAT3, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F08A,   65
                        }

                        Local3 = RefOf (F08A)
                        Local4 = RefOf (G003)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX4, DAT4, AnyAcc, NoLock, Preserve)
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
                        IndexField (IDX5, DAT5, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F08C,   129
                        }

                        Local3 = RefOf (F08C)
                        Local4 = RefOf (G005)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX6, DAT6, ByteAcc, NoLock, Preserve)
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
                        IndexField (IDX7, DAT7, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F08E,   1023
                        }

                        Local3 = RefOf (F08E)
                        Local4 = RefOf (G007)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX8, DAT8, WordAcc, NoLock, Preserve)
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
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX9, DAT9, QWordAcc, NoLock, Preserve)
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
                        IndexField (IDXA, DATA, ByteAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F091,   6
                        }

                        Local3 = RefOf (F091)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x07)
                    {
                        IndexField (IDXB, DATB, AnyAcc, NoLock, Preserve)
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
                        IndexField (IDXC, DATC, ByteAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F093,   8
                        }

                        Local3 = RefOf (F093)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x09)
                    {
                        IndexField (IDXD, DATD, ByteAcc, NoLock, Preserve)
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
                        IndexField (IDXE, DATE, ByteAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F095,   31
                        }

                        Local3 = RefOf (F095)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX0, DAT0, WordAcc, NoLock, Preserve)
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
                        IndexField (IDX1, DAT1, ByteAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F097,   33
                        }

                        Local3 = RefOf (F097)
                        Local4 = RefOf (G001)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX2, DAT2, DWordAcc, NoLock, Preserve)
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
                        IndexField (IDX3, DAT3, ByteAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F099,   64
                        }

                        Local3 = RefOf (F099)
                        Local4 = RefOf (G003)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX4, DAT4, QWordAcc, NoLock, Preserve)
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
                        IndexField (IDX5, DAT5, ByteAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F09B,   69
                        }

                        Local3 = RefOf (F09B)
                        Local4 = RefOf (G005)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX6, DAT6, AnyAcc, NoLock, Preserve)
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
                        IndexField (IDX7, DAT7, ByteAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F09D,   256
                        }

                        Local3 = RefOf (F09D)
                        Local4 = RefOf (G007)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX8, DAT8, ByteAcc, NoLock, Preserve)
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
                        IndexField (IDX9, DAT9, ByteAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F09F,   1983
                        }

                        Local3 = RefOf (F09F)
                        Local4 = RefOf (G009)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDXA, DATA, ByteAcc, NoLock, Preserve)
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
                        IndexField (IDXB, DATB, WordAcc, NoLock, Preserve)
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
                        IndexField (IDXC, DATC, ByteAcc, NoLock, Preserve)
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
                        IndexField (IDXD, DATD, DWordAcc, NoLock, Preserve)
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
                        IndexField (IDXE, DATE, ByteAcc, NoLock, Preserve)
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
                        IndexField (IDX0, DAT0, QWordAcc, NoLock, Preserve)
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
                        IndexField (IDX1, DAT1, ByteAcc, NoLock, Preserve)
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
                        IndexField (IDX2, DAT2, AnyAcc, NoLock, Preserve)
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
                        IndexField (IDX3, DAT3, ByteAcc, NoLock, Preserve)
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
                        IndexField (IDX4, DAT4, ByteAcc, NoLock, Preserve)
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
                        IndexField (IDX5, DAT5, ByteAcc, NoLock, Preserve)
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
                        IndexField (IDX6, DAT6, WordAcc, NoLock, Preserve)
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
                        IndexField (IDX7, DAT7, ByteAcc, NoLock, Preserve)
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
                        IndexField (IDX8, DAT8, DWordAcc, NoLock, Preserve)
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
                        IndexField (IDX9, DAT9, ByteAcc, NoLock, Preserve)
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
                        IndexField (IDXA, DATA, QWordAcc, NoLock, Preserve)
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
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDXB, DATB, AnyAcc, NoLock, Preserve)
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
                        IndexField (IDXC, DATC, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0B1,   6
                        }

                        Local3 = RefOf (F0B1)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x07)
                    {
                        IndexField (IDXD, DATD, ByteAcc, NoLock, Preserve)
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
                        IndexField (IDXE, DATE, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0B3,   8
                        }

                        Local3 = RefOf (F0B3)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX0, DAT0, WordAcc, NoLock, Preserve)
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
                        IndexField (IDX1, DAT1, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0B5,   31
                        }

                        Local3 = RefOf (F0B5)
                        Local4 = RefOf (G001)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX2, DAT2, DWordAcc, NoLock, Preserve)
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
                        IndexField (IDX3, DAT3, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0B7,   33
                        }

                        Local3 = RefOf (F0B7)
                        Local4 = RefOf (G003)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX4, DAT4, QWordAcc, NoLock, Preserve)
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
                        IndexField (IDX5, DAT5, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0B9,   64
                        }

                        Local3 = RefOf (F0B9)
                        Local4 = RefOf (G005)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX6, DAT6, AnyAcc, NoLock, Preserve)
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
                        IndexField (IDX7, DAT7, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0BB,   69
                        }

                        Local3 = RefOf (F0BB)
                        Local4 = RefOf (G007)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX8, DAT8, ByteAcc, NoLock, Preserve)
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
                        IndexField (IDX9, DAT9, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0BD,   256
                        }

                        Local3 = RefOf (F0BD)
                        Local4 = RefOf (G009)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDXA, DATA, WordAcc, NoLock, Preserve)
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
                        IndexField (IDXB, DATB, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0BF,   1983
                        }

                        Local3 = RefOf (F0BF)
                        Local4 = RefOf (G00B)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDXC, DATC, ByteAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0C0,   1
                        }

                        Local3 = RefOf (F0C0)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x06)
                    {
                        IndexField (IDXD, DATD, DWordAcc, NoLock, Preserve)
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
                        IndexField (IDXE, DATE, ByteAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0C2,   7
                        }

                        Local3 = RefOf (F0C2)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX0, DAT0, QWordAcc, NoLock, Preserve)
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
                        IndexField (IDX1, DAT1, ByteAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0C4,   9
                        }

                        Local3 = RefOf (F0C4)
                        Local4 = RefOf (G001)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX2, DAT2, AnyAcc, NoLock, Preserve)
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
                        IndexField (IDX3, DAT3, ByteAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0C6,   32
                        }

                        Local3 = RefOf (F0C6)
                        Local4 = RefOf (G003)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX4, DAT4, ByteAcc, NoLock, Preserve)
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
                        IndexField (IDX5, DAT5, ByteAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0C8,   63
                        }

                        Local3 = RefOf (F0C8)
                        Local4 = RefOf (G005)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX6, DAT6, WordAcc, NoLock, Preserve)
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
                        IndexField (IDX7, DAT7, ByteAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0CA,   65
                        }

                        Local3 = RefOf (F0CA)
                        Local4 = RefOf (G007)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX8, DAT8, DWordAcc, NoLock, Preserve)
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
                        IndexField (IDX9, DAT9, ByteAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0CC,   129
                        }

                        Local3 = RefOf (F0CC)
                        Local4 = RefOf (G009)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDXA, DATA, QWordAcc, NoLock, Preserve)
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
                        IndexField (IDXB, DATB, ByteAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0CE,   1023
                        }

                        Local3 = RefOf (F0CE)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDXC, DATC, AnyAcc, NoLock, Preserve)
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
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDXD, DATD, ByteAcc, NoLock, Preserve)
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
                        IndexField (IDXE, DATE, ByteAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0D1,   6
                        }

                        Local3 = RefOf (F0D1)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX0, DAT0, WordAcc, NoLock, Preserve)
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
                        IndexField (IDX1, DAT1, ByteAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0D3,   8
                        }

                        Local3 = RefOf (F0D3)
                        Local4 = RefOf (G001)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX2, DAT2, DWordAcc, NoLock, Preserve)
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
                        IndexField (IDX3, DAT3, ByteAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0D5,   31
                        }

                        Local3 = RefOf (F0D5)
                        Local4 = RefOf (G003)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX4, DAT4, QWordAcc, NoLock, Preserve)
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
                        IndexField (IDX5, DAT5, ByteAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0D7,   33
                        }

                        Local3 = RefOf (F0D7)
                        Local4 = RefOf (G005)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX6, DAT6, AnyAcc, NoLock, Preserve)
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
                        IndexField (IDX7, DAT7, ByteAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0D9,   64
                        }

                        Local3 = RefOf (F0D9)
                        Local4 = RefOf (G007)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX8, DAT8, ByteAcc, NoLock, Preserve)
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
                        IndexField (IDX9, DAT9, ByteAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0DB,   69
                        }

                        Local3 = RefOf (F0DB)
                        Local4 = RefOf (G009)
                    }
                    Case (0x81)
                    {
                        IndexField (IDXA, DATA, WordAcc, NoLock, Preserve)
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
                        IndexField (IDXB, DATB, ByteAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0DD,   256
                        }

                        Local3 = RefOf (F0DD)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDXC, DATC, DWordAcc, NoLock, Preserve)
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
                        IndexField (IDXD, DATD, ByteAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0DF,   1983
                        }

                        Local3 = RefOf (F0DF)
                        Local4 = RefOf (G00D)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDXE, DATE, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0E0,   1
                        }

                        Local3 = RefOf (F0E0)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX0, DAT0, QWordAcc, NoLock, Preserve)
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
                        IndexField (IDX1, DAT1, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0E2,   7
                        }

                        Local3 = RefOf (F0E2)
                        Local4 = RefOf (G001)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX2, DAT2, AnyAcc, NoLock, Preserve)
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
                        IndexField (IDX3, DAT3, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0E4,   9
                        }

                        Local3 = RefOf (F0E4)
                        Local4 = RefOf (G003)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX4, DAT4, ByteAcc, NoLock, Preserve)
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
                        IndexField (IDX5, DAT5, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0E6,   32
                        }

                        Local3 = RefOf (F0E6)
                        Local4 = RefOf (G005)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX6, DAT6, WordAcc, NoLock, Preserve)
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
                        IndexField (IDX7, DAT7, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0E8,   63
                        }

                        Local3 = RefOf (F0E8)
                        Local4 = RefOf (G007)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX8, DAT8, DWordAcc, NoLock, Preserve)
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
                        IndexField (IDX9, DAT9, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0EA,   65
                        }

                        Local3 = RefOf (F0EA)
                        Local4 = RefOf (G009)
                    }
                    Case (0x45)
                    {
                        IndexField (IDXA, DATA, QWordAcc, NoLock, Preserve)
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
                        IndexField (IDXB, DATB, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0EC,   129
                        }

                        Local3 = RefOf (F0EC)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDXC, DATC, AnyAcc, NoLock, Preserve)
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
                        IndexField (IDXD, DATD, ByteAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0EE,   1023
                        }

                        Local3 = RefOf (F0EE)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDXE, DATE, ByteAcc, NoLock, Preserve)
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
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX0, DAT0, WordAcc, NoLock, Preserve)
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
                        IndexField (IDX1, DAT1, ByteAcc, NoLock, Preserve)
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
                        IndexField (IDX2, DAT2, DWordAcc, NoLock, Preserve)
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
                        IndexField (IDX3, DAT3, ByteAcc, NoLock, Preserve)
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
                        IndexField (IDX4, DAT4, QWordAcc, NoLock, Preserve)
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
                        IndexField (IDX5, DAT5, ByteAcc, NoLock, Preserve)
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
                        IndexField (IDX6, DAT6, AnyAcc, NoLock, Preserve)
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
                        IndexField (IDX7, DAT7, ByteAcc, NoLock, Preserve)
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
                        IndexField (IDX8, DAT8, ByteAcc, NoLock, Preserve)
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
                        IndexField (IDX9, DAT9, ByteAcc, NoLock, Preserve)
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
                        IndexField (IDXA, DATA, WordAcc, NoLock, Preserve)
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
                        IndexField (IDXB, DATB, ByteAcc, NoLock, Preserve)
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
                        IndexField (IDXC, DATC, DWordAcc, NoLock, Preserve)
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
                        IndexField (IDXD, DATD, ByteAcc, NoLock, Preserve)
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
                        IndexField (IDXE, DATE, QWordAcc, NoLock, Preserve)
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
                        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
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
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Default
            {
                ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
                Return (Zero)
            }

        }

        M72D (Arg0, Local3, Arg2, Arg3, Arg4, Arg5, Local4)
    }

    /* Create IndexField Unit */
    /* (WordAcc, NoLock, WriteAsOnes) */
    Method (M791, 6, Serialized)
    {
        OperationRegion (OPR0, SystemMemory, 0x0FA0, 0x87)
        /*
         * Consider different attributes of index/data fields
         * taking into account the following restrictions:
         * - the fields spanning the same access unit interfere,
         * - the fields exceeding 64 bits cause AE_BUFFER_OVERFLOW,
         * - index field exceeding 32 bits unexpectedly cause
         *   AE_BUFFER_OVERFLOW too,
         * - data field exceeding IndexField's Access Width
         *   causes overwriting of next memory bytes.
         */
        Field (OPR0, ByteAcc, NoLock, Preserve)
        {
            IDX0,   8,
            DAT0,   16
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
            G000,   2048
        }

        Field (OPR0, ByteAcc, NoLock, WriteAsOnes)
        {
            Offset (0x03),
            IDX1,   8,
            DAT1,   16
        }

        IndexField (IDX1, DAT1, ByteAcc, NoLock, Preserve)
        {
            G001,   2048
        }

        Field (OPR0, ByteAcc, NoLock, WriteAsZeros)
        {
            Offset (0x07),
            IDX2,   16,
            DAT2,   16
        }

        IndexField (IDX2, DAT2, ByteAcc, NoLock, Preserve)
        {
            G002,   2048
        }

        Field (OPR0, WordAcc, NoLock, Preserve)
        {
            Offset (0x0B),
            IDX3,   8,
            DAT3,   16
        }

        IndexField (IDX3, DAT3, ByteAcc, NoLock, Preserve)
        {
            G003,   2048
        }

        Field (OPR0, WordAcc, NoLock, WriteAsOnes)
        {
            Offset (0x0E),
            IDX4,   16,
            DAT4,   16
        }

        IndexField (IDX4, DAT4, ByteAcc, NoLock, Preserve)
        {
            G004,   2048
        }

        Field (OPR0, WordAcc, NoLock, WriteAsZeros)
        {
            Offset (0x12),
            IDX5,   32,
            DAT5,   16
        }

        IndexField (IDX5, DAT5, ByteAcc, NoLock, Preserve)
        {
            G005,   2048
        }

        Field (OPR0, DWordAcc, NoLock, Preserve)
        {
            Offset (0x1A),
            IDX6,   8,
            Offset (0x1C),
            DAT6,   16
        }

        IndexField (IDX6, DAT6, ByteAcc, NoLock, Preserve)
        {
            G006,   2048
        }

        Field (OPR0, DWordAcc, NoLock, WriteAsOnes)
        {
            Offset (0x20),
            IDX7,   32,
            DAT7,   16
        }

        IndexField (IDX7, DAT7, ByteAcc, NoLock, Preserve)
        {
            G007,   2048
        }

        Field (OPR0, DWordAcc, NoLock, WriteAsZeros)
        {
            Offset (0x28),
            IDX8,   32,
            DAT8,   16
        }

        IndexField (IDX8, DAT8, ByteAcc, NoLock, Preserve)
        {
            G008,   2048
        }

        Field (OPR0, QWordAcc, NoLock, Preserve)
        {
            Offset (0x38),
            IDX9,   8,
            Offset (0x40),
            DAT9,   16
        }

        IndexField (IDX9, DAT9, ByteAcc, NoLock, Preserve)
        {
            G009,   2048
        }

        Field (OPR0, QWordAcc, NoLock, WriteAsOnes)
        {
            Offset (0x48),
            Offset (0x4C),
            /* Index field exceeding 32 bits causes AE_BUFFER_OVERFLOW */
            /* IDXA, 64, */
            /* Do not allow index/data interference */
            IDXA,   32,
            DATA,   16
        }

        IndexField (IDXA, DATA, ByteAcc, NoLock, Preserve)
        {
            G00A,   2048
        }

        Field (OPR0, QWordAcc, NoLock, WriteAsZeros)
        {
            Offset (0x58),
            IDXB,   32,
            Offset (0x60),
            DATB,   16
        }

        IndexField (IDXB, DATB, ByteAcc, NoLock, Preserve)
        {
            G00B,   2048
        }

        Field (OPR0, AnyAcc, NoLock, Preserve)
        {
            Offset (0x68),
            IDXC,   8,
            DATC,   16
        }

        IndexField (IDXC, DATC, ByteAcc, NoLock, Preserve)
        {
            G00C,   2048
        }

        Field (OPR0, AnyAcc, NoLock, WriteAsOnes)
        {
            Offset (0x6B),
            /* Index field exceeding 32 bits causes AE_BUFFER_OVERFLOW */
            /* IDXD, 64, */
            IDXD,   32,
            DATD,   16
        }

        IndexField (IDXD, DATD, ByteAcc, NoLock, Preserve)
        {
            G00D,   2048
        }

        Field (OPR0, AnyAcc, NoLock, WriteAsZeros)
        {
            Offset (0x7B),
            IDXE,   32,
            DATE,   16
        }

        IndexField (IDXE, DATE, ByteAcc, NoLock, Preserve)
        {
            G00E,   2048
        }

        Concatenate (Arg0, "-m791", Arg0)
        Switch (ToInteger (Arg2))
        {
            Case (0x00)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        IndexField (IDX0, DAT0, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                            F000,   1
                        }

                        Local3 = RefOf (F000)
                        Local4 = RefOf (G000)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX1, DAT1, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                            F001,   6
                        }

                        Local3 = RefOf (F001)
                        Local4 = RefOf (G001)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX2, DAT2, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                            F002,   7
                        }

                        Local3 = RefOf (F002)
                        Local4 = RefOf (G002)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX3, DAT3, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                            F003,   8
                        }

                        Local3 = RefOf (F003)
                        Local4 = RefOf (G003)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX4, DAT4, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                            F004,   9
                        }

                        Local3 = RefOf (F004)
                        Local4 = RefOf (G004)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX5, DAT5, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                            F005,   31
                        }

                        Local3 = RefOf (F005)
                        Local4 = RefOf (G005)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX6, DAT6, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                            F006,   32
                        }

                        Local3 = RefOf (F006)
                        Local4 = RefOf (G006)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX7, DAT7, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                            F007,   33
                        }

                        Local3 = RefOf (F007)
                        Local4 = RefOf (G007)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX8, DAT8, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                            F008,   63
                        }

                        Local3 = RefOf (F008)
                        Local4 = RefOf (G008)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX9, DAT9, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                            F009,   64
                        }

                        Local3 = RefOf (F009)
                        Local4 = RefOf (G009)
                    }
                    Case (0x41)
                    {
                        IndexField (IDXA, DATA, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                            F00A,   65
                        }

                        Local3 = RefOf (F00A)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x45)
                    {
                        IndexField (IDXB, DATB, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                            F00B,   69
                        }

                        Local3 = RefOf (F00B)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x81)
                    {
                        IndexField (IDXC, DATC, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                            F00C,   129
                        }

                        Local3 = RefOf (F00C)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDXD, DATD, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                            F00D,   256
                        }

                        Local3 = RefOf (F00D)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDXE, DATE, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                            F00E,   1023
                        }

                        Local3 = RefOf (F00E)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX0, DAT0, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                            F00F,   1983
                        }

                        Local3 = RefOf (F00F)
                        Local4 = RefOf (G000)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX1, DAT1, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                                ,   1,
                            F010,   1
                        }

                        Local3 = RefOf (F010)
                        Local4 = RefOf (G001)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX2, DAT2, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                                ,   1,
                            F011,   6
                        }

                        Local3 = RefOf (F011)
                        Local4 = RefOf (G002)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX3, DAT3, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                                ,   1,
                            F012,   7
                        }

                        Local3 = RefOf (F012)
                        Local4 = RefOf (G003)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX4, DAT4, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                                ,   1,
                            F013,   8
                        }

                        Local3 = RefOf (F013)
                        Local4 = RefOf (G004)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX5, DAT5, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                                ,   1,
                            F014,   9
                        }

                        Local3 = RefOf (F014)
                        Local4 = RefOf (G005)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX6, DAT6, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                                ,   1,
                            F015,   31
                        }

                        Local3 = RefOf (F015)
                        Local4 = RefOf (G006)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX7, DAT7, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                                ,   1,
                            F016,   32
                        }

                        Local3 = RefOf (F016)
                        Local4 = RefOf (G007)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX8, DAT8, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                                ,   1,
                            F017,   33
                        }

                        Local3 = RefOf (F017)
                        Local4 = RefOf (G008)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX9, DAT9, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                                ,   1,
                            F018,   63
                        }

                        Local3 = RefOf (F018)
                        Local4 = RefOf (G009)
                    }
                    Case (0x40)
                    {
                        IndexField (IDXA, DATA, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                                ,   1,
                            F019,   64
                        }

                        Local3 = RefOf (F019)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x41)
                    {
                        IndexField (IDXB, DATB, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                                ,   1,
                            F01A,   65
                        }

                        Local3 = RefOf (F01A)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x45)
                    {
                        IndexField (IDXC, DATC, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                                ,   1,
                            F01B,   69
                        }

                        Local3 = RefOf (F01B)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x81)
                    {
                        IndexField (IDXD, DATD, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                                ,   1,
                            F01C,   129
                        }

                        Local3 = RefOf (F01C)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDXE, DATE, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                                ,   1,
                            F01D,   256
                        }

                        Local3 = RefOf (F01D)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX0, DAT0, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                                ,   1,
                            F01E,   1023
                        }

                        Local3 = RefOf (F01E)
                        Local4 = RefOf (G000)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX1, DAT1, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x00),
                                ,   1,
                            F01F,   1983
                        }

                        Local3 = RefOf (F01F)
                        Local4 = RefOf (G001)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX2, DAT2, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   2,
                            F020,   1
                        }

                        Local3 = RefOf (F020)
                        Local4 = RefOf (G002)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX3, DAT3, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   2,
                            F021,   6
                        }

                        Local3 = RefOf (F021)
                        Local4 = RefOf (G003)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX4, DAT4, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   2,
                            F022,   7
                        }

                        Local3 = RefOf (F022)
                        Local4 = RefOf (G004)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX5, DAT5, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   2,
                            F023,   8
                        }

                        Local3 = RefOf (F023)
                        Local4 = RefOf (G005)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX6, DAT6, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   2,
                            F024,   9
                        }

                        Local3 = RefOf (F024)
                        Local4 = RefOf (G006)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX7, DAT7, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   2,
                            F025,   31
                        }

                        Local3 = RefOf (F025)
                        Local4 = RefOf (G007)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX8, DAT8, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   2,
                            F026,   32
                        }

                        Local3 = RefOf (F026)
                        Local4 = RefOf (G008)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX9, DAT9, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   2,
                            F027,   33
                        }

                        Local3 = RefOf (F027)
                        Local4 = RefOf (G009)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDXA, DATA, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   2,
                            F028,   63
                        }

                        Local3 = RefOf (F028)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x40)
                    {
                        IndexField (IDXB, DATB, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   2,
                            F029,   64
                        }

                        Local3 = RefOf (F029)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x41)
                    {
                        IndexField (IDXC, DATC, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   2,
                            F02A,   65
                        }

                        Local3 = RefOf (F02A)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x45)
                    {
                        IndexField (IDXD, DATD, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   2,
                            F02B,   69
                        }

                        Local3 = RefOf (F02B)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x81)
                    {
                        IndexField (IDXE, DATE, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   2,
                            F02C,   129
                        }

                        Local3 = RefOf (F02C)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX0, DAT0, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   2,
                            F02D,   256
                        }

                        Local3 = RefOf (F02D)
                        Local4 = RefOf (G000)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX1, DAT1, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   2,
                            F02E,   1023
                        }

                        Local3 = RefOf (F02E)
                        Local4 = RefOf (G001)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX2, DAT2, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   2,
                            F02F,   1983
                        }

                        Local3 = RefOf (F02F)
                        Local4 = RefOf (G002)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX3, DAT3, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   3,
                            F030,   1
                        }

                        Local3 = RefOf (F030)
                        Local4 = RefOf (G003)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX4, DAT4, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   3,
                            F031,   6
                        }

                        Local3 = RefOf (F031)
                        Local4 = RefOf (G004)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX5, DAT5, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   3,
                            F032,   7
                        }

                        Local3 = RefOf (F032)
                        Local4 = RefOf (G005)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX6, DAT6, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   3,
                            F033,   8
                        }

                        Local3 = RefOf (F033)
                        Local4 = RefOf (G006)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX7, DAT7, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   3,
                            F034,   9
                        }

                        Local3 = RefOf (F034)
                        Local4 = RefOf (G007)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX8, DAT8, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   3,
                            F035,   31
                        }

                        Local3 = RefOf (F035)
                        Local4 = RefOf (G008)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX9, DAT9, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   3,
                            F036,   32
                        }

                        Local3 = RefOf (F036)
                        Local4 = RefOf (G009)
                    }
                    Case (0x21)
                    {
                        IndexField (IDXA, DATA, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   3,
                            F037,   33
                        }

                        Local3 = RefOf (F037)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDXB, DATB, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   3,
                            F038,   63
                        }

                        Local3 = RefOf (F038)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x40)
                    {
                        IndexField (IDXC, DATC, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   3,
                            F039,   64
                        }

                        Local3 = RefOf (F039)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x41)
                    {
                        IndexField (IDXD, DATD, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   3,
                            F03A,   65
                        }

                        Local3 = RefOf (F03A)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x45)
                    {
                        IndexField (IDXE, DATE, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   3,
                            F03B,   69
                        }

                        Local3 = RefOf (F03B)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX0, DAT0, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   3,
                            F03C,   129
                        }

                        Local3 = RefOf (F03C)
                        Local4 = RefOf (G000)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX1, DAT1, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   3,
                            F03D,   256
                        }

                        Local3 = RefOf (F03D)
                        Local4 = RefOf (G001)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX2, DAT2, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   3,
                            F03E,   1023
                        }

                        Local3 = RefOf (F03E)
                        Local4 = RefOf (G002)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX3, DAT3, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   3,
                            F03F,   1983
                        }

                        Local3 = RefOf (F03F)
                        Local4 = RefOf (G003)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX4, DAT4, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   4,
                            F040,   1
                        }

                        Local3 = RefOf (F040)
                        Local4 = RefOf (G004)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX5, DAT5, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   4,
                            F041,   6
                        }

                        Local3 = RefOf (F041)
                        Local4 = RefOf (G005)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX6, DAT6, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   4,
                            F042,   7
                        }

                        Local3 = RefOf (F042)
                        Local4 = RefOf (G006)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX7, DAT7, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   4,
                            F043,   8
                        }

                        Local3 = RefOf (F043)
                        Local4 = RefOf (G007)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX8, DAT8, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   4,
                            F044,   9
                        }

                        Local3 = RefOf (F044)
                        Local4 = RefOf (G008)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX9, DAT9, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   4,
                            F045,   31
                        }

                        Local3 = RefOf (F045)
                        Local4 = RefOf (G009)
                    }
                    Case (0x20)
                    {
                        IndexField (IDXA, DATA, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   4,
                            F046,   32
                        }

                        Local3 = RefOf (F046)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x21)
                    {
                        IndexField (IDXB, DATB, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   4,
                            F047,   33
                        }

                        Local3 = RefOf (F047)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDXC, DATC, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   4,
                            F048,   63
                        }

                        Local3 = RefOf (F048)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x40)
                    {
                        IndexField (IDXD, DATD, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   4,
                            F049,   64
                        }

                        Local3 = RefOf (F049)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x41)
                    {
                        IndexField (IDXE, DATE, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   4,
                            F04A,   65
                        }

                        Local3 = RefOf (F04A)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX0, DAT0, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   4,
                            F04B,   69
                        }

                        Local3 = RefOf (F04B)
                        Local4 = RefOf (G000)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX1, DAT1, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   4,
                            F04C,   129
                        }

                        Local3 = RefOf (F04C)
                        Local4 = RefOf (G001)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX2, DAT2, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   4,
                            F04D,   256
                        }

                        Local3 = RefOf (F04D)
                        Local4 = RefOf (G002)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX3, DAT3, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   4,
                            F04E,   1023
                        }

                        Local3 = RefOf (F04E)
                        Local4 = RefOf (G003)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX4, DAT4, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   4,
                            F04F,   1983
                        }

                        Local3 = RefOf (F04F)
                        Local4 = RefOf (G004)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX5, DAT5, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   5,
                            F050,   1
                        }

                        Local3 = RefOf (F050)
                        Local4 = RefOf (G005)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX6, DAT6, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   5,
                            F051,   6
                        }

                        Local3 = RefOf (F051)
                        Local4 = RefOf (G006)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX7, DAT7, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   5,
                            F052,   7
                        }

                        Local3 = RefOf (F052)
                        Local4 = RefOf (G007)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX8, DAT8, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   5,
                            F053,   8
                        }

                        Local3 = RefOf (F053)
                        Local4 = RefOf (G008)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX9, DAT9, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   5,
                            F054,   9
                        }

                        Local3 = RefOf (F054)
                        Local4 = RefOf (G009)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDXA, DATA, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   5,
                            F055,   31
                        }

                        Local3 = RefOf (F055)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x20)
                    {
                        IndexField (IDXB, DATB, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   5,
                            F056,   32
                        }

                        Local3 = RefOf (F056)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x21)
                    {
                        IndexField (IDXC, DATC, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   5,
                            F057,   33
                        }

                        Local3 = RefOf (F057)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDXD, DATD, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   5,
                            F058,   63
                        }

                        Local3 = RefOf (F058)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x40)
                    {
                        IndexField (IDXE, DATE, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   5,
                            F059,   64
                        }

                        Local3 = RefOf (F059)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX0, DAT0, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   5,
                            F05A,   65
                        }

                        Local3 = RefOf (F05A)
                        Local4 = RefOf (G000)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX1, DAT1, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   5,
                            F05B,   69
                        }

                        Local3 = RefOf (F05B)
                        Local4 = RefOf (G001)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX2, DAT2, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   5,
                            F05C,   129
                        }

                        Local3 = RefOf (F05C)
                        Local4 = RefOf (G002)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX3, DAT3, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   5,
                            F05D,   256
                        }

                        Local3 = RefOf (F05D)
                        Local4 = RefOf (G003)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX4, DAT4, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   5,
                            F05E,   1023
                        }

                        Local3 = RefOf (F05E)
                        Local4 = RefOf (G004)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX5, DAT5, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   5,
                            F05F,   1983
                        }

                        Local3 = RefOf (F05F)
                        Local4 = RefOf (G005)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX6, DAT6, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   6,
                            F060,   1
                        }

                        Local3 = RefOf (F060)
                        Local4 = RefOf (G006)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX7, DAT7, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   6,
                            F061,   6
                        }

                        Local3 = RefOf (F061)
                        Local4 = RefOf (G007)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX8, DAT8, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   6,
                            F062,   7
                        }

                        Local3 = RefOf (F062)
                        Local4 = RefOf (G008)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX9, DAT9, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   6,
                            F063,   8
                        }

                        Local3 = RefOf (F063)
                        Local4 = RefOf (G009)
                    }
                    Case (0x09)
                    {
                        IndexField (IDXA, DATA, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   6,
                            F064,   9
                        }

                        Local3 = RefOf (F064)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDXB, DATB, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   6,
                            F065,   31
                        }

                        Local3 = RefOf (F065)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x20)
                    {
                        IndexField (IDXC, DATC, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   6,
                            F066,   32
                        }

                        Local3 = RefOf (F066)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x21)
                    {
                        IndexField (IDXD, DATD, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   6,
                            F067,   33
                        }

                        Local3 = RefOf (F067)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDXE, DATE, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   6,
                            F068,   63
                        }

                        Local3 = RefOf (F068)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX0, DAT0, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   6,
                            F069,   64
                        }

                        Local3 = RefOf (F069)
                        Local4 = RefOf (G000)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX1, DAT1, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   6,
                            F06A,   65
                        }

                        Local3 = RefOf (F06A)
                        Local4 = RefOf (G001)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX2, DAT2, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   6,
                            F06B,   69
                        }

                        Local3 = RefOf (F06B)
                        Local4 = RefOf (G002)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX3, DAT3, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   6,
                            F06C,   129
                        }

                        Local3 = RefOf (F06C)
                        Local4 = RefOf (G003)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX4, DAT4, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   6,
                            F06D,   256
                        }

                        Local3 = RefOf (F06D)
                        Local4 = RefOf (G004)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX5, DAT5, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   6,
                            F06E,   1023
                        }

                        Local3 = RefOf (F06E)
                        Local4 = RefOf (G005)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX6, DAT6, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   6,
                            F06F,   1983
                        }

                        Local3 = RefOf (F06F)
                        Local4 = RefOf (G006)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX7, DAT7, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   7,
                            F070,   1
                        }

                        Local3 = RefOf (F070)
                        Local4 = RefOf (G007)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX8, DAT8, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   7,
                            F071,   6
                        }

                        Local3 = RefOf (F071)
                        Local4 = RefOf (G008)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX9, DAT9, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   7,
                            F072,   7
                        }

                        Local3 = RefOf (F072)
                        Local4 = RefOf (G009)
                    }
                    Case (0x08)
                    {
                        IndexField (IDXA, DATA, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   7,
                            F073,   8
                        }

                        Local3 = RefOf (F073)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x09)
                    {
                        IndexField (IDXB, DATB, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   7,
                            F074,   9
                        }

                        Local3 = RefOf (F074)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDXC, DATC, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   7,
                            F075,   31
                        }

                        Local3 = RefOf (F075)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x20)
                    {
                        IndexField (IDXD, DATD, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   7,
                            F076,   32
                        }

                        Local3 = RefOf (F076)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x21)
                    {
                        IndexField (IDXE, DATE, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   7,
                            F077,   33
                        }

                        Local3 = RefOf (F077)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX0, DAT0, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   7,
                            F078,   63
                        }

                        Local3 = RefOf (F078)
                        Local4 = RefOf (G000)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX1, DAT1, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   7,
                            F079,   64
                        }

                        Local3 = RefOf (F079)
                        Local4 = RefOf (G001)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX2, DAT2, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   7,
                            F07A,   65
                        }

                        Local3 = RefOf (F07A)
                        Local4 = RefOf (G002)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX3, DAT3, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   7,
                            F07B,   69
                        }

                        Local3 = RefOf (F07B)
                        Local4 = RefOf (G003)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX4, DAT4, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   7,
                            F07C,   129
                        }

                        Local3 = RefOf (F07C)
                        Local4 = RefOf (G004)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX5, DAT5, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   7,
                            F07D,   256
                        }

                        Local3 = RefOf (F07D)
                        Local4 = RefOf (G005)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX6, DAT6, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   7,
                            F07E,   1023
                        }

                        Local3 = RefOf (F07E)
                        Local4 = RefOf (G006)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX7, DAT7, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   7,
                            F07F,   1983
                        }

                        Local3 = RefOf (F07F)
                        Local4 = RefOf (G007)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX8, DAT8, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x01),
                            F080,   1
                        }

                        Local3 = RefOf (F080)
                        Local4 = RefOf (G008)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX9, DAT9, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x01),
                            F081,   6
                        }

                        Local3 = RefOf (F081)
                        Local4 = RefOf (G009)
                    }
                    Case (0x07)
                    {
                        IndexField (IDXA, DATA, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x01),
                            F082,   7
                        }

                        Local3 = RefOf (F082)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x08)
                    {
                        IndexField (IDXB, DATB, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x01),
                            F083,   8
                        }

                        Local3 = RefOf (F083)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x09)
                    {
                        IndexField (IDXC, DATC, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x01),
                            F084,   9
                        }

                        Local3 = RefOf (F084)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDXD, DATD, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x01),
                            F085,   31
                        }

                        Local3 = RefOf (F085)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x20)
                    {
                        IndexField (IDXE, DATE, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x01),
                            F086,   32
                        }

                        Local3 = RefOf (F086)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX0, DAT0, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x01),
                            F087,   33
                        }

                        Local3 = RefOf (F087)
                        Local4 = RefOf (G000)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX1, DAT1, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x01),
                            F088,   63
                        }

                        Local3 = RefOf (F088)
                        Local4 = RefOf (G001)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX2, DAT2, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x01),
                            F089,   64
                        }

                        Local3 = RefOf (F089)
                        Local4 = RefOf (G002)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX3, DAT3, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x01),
                            F08A,   65
                        }

                        Local3 = RefOf (F08A)
                        Local4 = RefOf (G003)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX4, DAT4, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x01),
                            F08B,   69
                        }

                        Local3 = RefOf (F08B)
                        Local4 = RefOf (G004)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX5, DAT5, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x01),
                            F08C,   129
                        }

                        Local3 = RefOf (F08C)
                        Local4 = RefOf (G005)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX6, DAT6, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x01),
                            F08D,   256
                        }

                        Local3 = RefOf (F08D)
                        Local4 = RefOf (G006)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX7, DAT7, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x01),
                            F08E,   1023
                        }

                        Local3 = RefOf (F08E)
                        Local4 = RefOf (G007)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX8, DAT8, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x01),
                            F08F,   1983
                        }

                        Local3 = RefOf (F08F)
                        Local4 = RefOf (G008)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX9, DAT9, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   9,
                            F090,   1
                        }

                        Local3 = RefOf (F090)
                        Local4 = RefOf (G009)
                    }
                    Case (0x06)
                    {
                        IndexField (IDXA, DATA, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   9,
                            F091,   6
                        }

                        Local3 = RefOf (F091)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x07)
                    {
                        IndexField (IDXB, DATB, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   9,
                            F092,   7
                        }

                        Local3 = RefOf (F092)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x08)
                    {
                        IndexField (IDXC, DATC, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   9,
                            F093,   8
                        }

                        Local3 = RefOf (F093)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x09)
                    {
                        IndexField (IDXD, DATD, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   9,
                            F094,   9
                        }

                        Local3 = RefOf (F094)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDXE, DATE, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   9,
                            F095,   31
                        }

                        Local3 = RefOf (F095)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX0, DAT0, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   9,
                            F096,   32
                        }

                        Local3 = RefOf (F096)
                        Local4 = RefOf (G000)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX1, DAT1, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   9,
                            F097,   33
                        }

                        Local3 = RefOf (F097)
                        Local4 = RefOf (G001)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX2, DAT2, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   9,
                            F098,   63
                        }

                        Local3 = RefOf (F098)
                        Local4 = RefOf (G002)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX3, DAT3, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   9,
                            F099,   64
                        }

                        Local3 = RefOf (F099)
                        Local4 = RefOf (G003)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX4, DAT4, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   9,
                            F09A,   65
                        }

                        Local3 = RefOf (F09A)
                        Local4 = RefOf (G004)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX5, DAT5, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   9,
                            F09B,   69
                        }

                        Local3 = RefOf (F09B)
                        Local4 = RefOf (G005)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX6, DAT6, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   9,
                            F09C,   129
                        }

                        Local3 = RefOf (F09C)
                        Local4 = RefOf (G006)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX7, DAT7, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   9,
                            F09D,   256
                        }

                        Local3 = RefOf (F09D)
                        Local4 = RefOf (G007)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX8, DAT8, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   9,
                            F09E,   1023
                        }

                        Local3 = RefOf (F09E)
                        Local4 = RefOf (G008)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX9, DAT9, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   9,
                            F09F,   1983
                        }

                        Local3 = RefOf (F09F)
                        Local4 = RefOf (G009)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDXA, DATA, WordAcc, NoLock, WriteAsOnes)
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
                        IndexField (IDXB, DATB, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A1,   6
                        }

                        Local3 = RefOf (F0A1)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x07)
                    {
                        IndexField (IDXC, DATC, WordAcc, NoLock, WriteAsOnes)
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
                        IndexField (IDXD, DATD, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A3,   8
                        }

                        Local3 = RefOf (F0A3)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x09)
                    {
                        IndexField (IDXE, DATE, WordAcc, NoLock, WriteAsOnes)
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
                        IndexField (IDX0, DAT0, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A5,   31
                        }

                        Local3 = RefOf (F0A5)
                        Local4 = RefOf (G000)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX1, DAT1, WordAcc, NoLock, WriteAsOnes)
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
                        IndexField (IDX2, DAT2, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A7,   33
                        }

                        Local3 = RefOf (F0A7)
                        Local4 = RefOf (G002)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX3, DAT3, WordAcc, NoLock, WriteAsOnes)
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
                        IndexField (IDX4, DAT4, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A9,   64
                        }

                        Local3 = RefOf (F0A9)
                        Local4 = RefOf (G004)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX5, DAT5, WordAcc, NoLock, WriteAsOnes)
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
                        IndexField (IDX6, DAT6, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x03),
                                ,   7,
                            F0AB,   69
                        }

                        Local3 = RefOf (F0AB)
                        Local4 = RefOf (G006)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX7, DAT7, WordAcc, NoLock, WriteAsOnes)
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
                        IndexField (IDX8, DAT8, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x03),
                                ,   7,
                            F0AD,   256
                        }

                        Local3 = RefOf (F0AD)
                        Local4 = RefOf (G008)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX9, DAT9, WordAcc, NoLock, WriteAsOnes)
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
                        IndexField (IDXA, DATA, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x03),
                                ,   7,
                            F0AF,   1983
                        }

                        Local3 = RefOf (F0AF)
                        Local4 = RefOf (G00A)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDXB, DATB, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x04),
                            F0B0,   1
                        }

                        Local3 = RefOf (F0B0)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x06)
                    {
                        IndexField (IDXC, DATC, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x04),
                            F0B1,   6
                        }

                        Local3 = RefOf (F0B1)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x07)
                    {
                        IndexField (IDXD, DATD, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x04),
                            F0B2,   7
                        }

                        Local3 = RefOf (F0B2)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x08)
                    {
                        IndexField (IDXE, DATE, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x04),
                            F0B3,   8
                        }

                        Local3 = RefOf (F0B3)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX0, DAT0, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x04),
                            F0B4,   9
                        }

                        Local3 = RefOf (F0B4)
                        Local4 = RefOf (G000)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX1, DAT1, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x04),
                            F0B5,   31
                        }

                        Local3 = RefOf (F0B5)
                        Local4 = RefOf (G001)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX2, DAT2, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x04),
                            F0B6,   32
                        }

                        Local3 = RefOf (F0B6)
                        Local4 = RefOf (G002)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX3, DAT3, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x04),
                            F0B7,   33
                        }

                        Local3 = RefOf (F0B7)
                        Local4 = RefOf (G003)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX4, DAT4, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x04),
                            F0B8,   63
                        }

                        Local3 = RefOf (F0B8)
                        Local4 = RefOf (G004)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX5, DAT5, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x04),
                            F0B9,   64
                        }

                        Local3 = RefOf (F0B9)
                        Local4 = RefOf (G005)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX6, DAT6, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x04),
                            F0BA,   65
                        }

                        Local3 = RefOf (F0BA)
                        Local4 = RefOf (G006)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX7, DAT7, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x04),
                            F0BB,   69
                        }

                        Local3 = RefOf (F0BB)
                        Local4 = RefOf (G007)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX8, DAT8, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x04),
                            F0BC,   129
                        }

                        Local3 = RefOf (F0BC)
                        Local4 = RefOf (G008)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX9, DAT9, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x04),
                            F0BD,   256
                        }

                        Local3 = RefOf (F0BD)
                        Local4 = RefOf (G009)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDXA, DATA, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x04),
                            F0BE,   1023
                        }

                        Local3 = RefOf (F0BE)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDXB, DATB, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x04),
                            F0BF,   1983
                        }

                        Local3 = RefOf (F0BF)
                        Local4 = RefOf (G00B)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDXC, DATC, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   33,
                            F0C0,   1
                        }

                        Local3 = RefOf (F0C0)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x06)
                    {
                        IndexField (IDXD, DATD, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   33,
                            F0C1,   6
                        }

                        Local3 = RefOf (F0C1)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x07)
                    {
                        IndexField (IDXE, DATE, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   33,
                            F0C2,   7
                        }

                        Local3 = RefOf (F0C2)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX0, DAT0, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   33,
                            F0C3,   8
                        }

                        Local3 = RefOf (F0C3)
                        Local4 = RefOf (G000)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX1, DAT1, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   33,
                            F0C4,   9
                        }

                        Local3 = RefOf (F0C4)
                        Local4 = RefOf (G001)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX2, DAT2, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   33,
                            F0C5,   31
                        }

                        Local3 = RefOf (F0C5)
                        Local4 = RefOf (G002)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX3, DAT3, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   33,
                            F0C6,   32
                        }

                        Local3 = RefOf (F0C6)
                        Local4 = RefOf (G003)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX4, DAT4, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   33,
                            F0C7,   33
                        }

                        Local3 = RefOf (F0C7)
                        Local4 = RefOf (G004)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX5, DAT5, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   33,
                            F0C8,   63
                        }

                        Local3 = RefOf (F0C8)
                        Local4 = RefOf (G005)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX6, DAT6, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   33,
                            F0C9,   64
                        }

                        Local3 = RefOf (F0C9)
                        Local4 = RefOf (G006)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX7, DAT7, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   33,
                            F0CA,   65
                        }

                        Local3 = RefOf (F0CA)
                        Local4 = RefOf (G007)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX8, DAT8, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   33,
                            F0CB,   69
                        }

                        Local3 = RefOf (F0CB)
                        Local4 = RefOf (G008)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX9, DAT9, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   33,
                            F0CC,   129
                        }

                        Local3 = RefOf (F0CC)
                        Local4 = RefOf (G009)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDXA, DATA, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   33,
                            F0CD,   256
                        }

                        Local3 = RefOf (F0CD)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDXB, DATB, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   33,
                            F0CE,   1023
                        }

                        Local3 = RefOf (F0CE)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDXC, DATC, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   33,
                            F0CF,   1983
                        }

                        Local3 = RefOf (F0CF)
                        Local4 = RefOf (G00C)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDXD, DATD, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   63,
                            F0D0,   1
                        }

                        Local3 = RefOf (F0D0)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x06)
                    {
                        IndexField (IDXE, DATE, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   63,
                            F0D1,   6
                        }

                        Local3 = RefOf (F0D1)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX0, DAT0, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   63,
                            F0D2,   7
                        }

                        Local3 = RefOf (F0D2)
                        Local4 = RefOf (G000)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX1, DAT1, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   63,
                            F0D3,   8
                        }

                        Local3 = RefOf (F0D3)
                        Local4 = RefOf (G001)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX2, DAT2, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   63,
                            F0D4,   9
                        }

                        Local3 = RefOf (F0D4)
                        Local4 = RefOf (G002)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX3, DAT3, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   63,
                            F0D5,   31
                        }

                        Local3 = RefOf (F0D5)
                        Local4 = RefOf (G003)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX4, DAT4, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   63,
                            F0D6,   32
                        }

                        Local3 = RefOf (F0D6)
                        Local4 = RefOf (G004)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX5, DAT5, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   63,
                            F0D7,   33
                        }

                        Local3 = RefOf (F0D7)
                        Local4 = RefOf (G005)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX6, DAT6, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   63,
                            F0D8,   63
                        }

                        Local3 = RefOf (F0D8)
                        Local4 = RefOf (G006)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX7, DAT7, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   63,
                            F0D9,   64
                        }

                        Local3 = RefOf (F0D9)
                        Local4 = RefOf (G007)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX8, DAT8, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   63,
                            F0DA,   65
                        }

                        Local3 = RefOf (F0DA)
                        Local4 = RefOf (G008)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX9, DAT9, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   63,
                            F0DB,   69
                        }

                        Local3 = RefOf (F0DB)
                        Local4 = RefOf (G009)
                    }
                    Case (0x81)
                    {
                        IndexField (IDXA, DATA, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   63,
                            F0DC,   129
                        }

                        Local3 = RefOf (F0DC)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDXB, DATB, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   63,
                            F0DD,   256
                        }

                        Local3 = RefOf (F0DD)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDXC, DATC, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   63,
                            F0DE,   1023
                        }

                        Local3 = RefOf (F0DE)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDXD, DATD, WordAcc, NoLock, WriteAsOnes)
                        {
                                ,   63,
                            F0DF,   1983
                        }

                        Local3 = RefOf (F0DF)
                        Local4 = RefOf (G00D)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDXE, DATE, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                            F0E0,   1
                        }

                        Local3 = RefOf (F0E0)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX0, DAT0, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                            F0E1,   6
                        }

                        Local3 = RefOf (F0E1)
                        Local4 = RefOf (G000)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX1, DAT1, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                            F0E2,   7
                        }

                        Local3 = RefOf (F0E2)
                        Local4 = RefOf (G001)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX2, DAT2, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                            F0E3,   8
                        }

                        Local3 = RefOf (F0E3)
                        Local4 = RefOf (G002)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX3, DAT3, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                            F0E4,   9
                        }

                        Local3 = RefOf (F0E4)
                        Local4 = RefOf (G003)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX4, DAT4, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                            F0E5,   31
                        }

                        Local3 = RefOf (F0E5)
                        Local4 = RefOf (G004)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX5, DAT5, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                            F0E6,   32
                        }

                        Local3 = RefOf (F0E6)
                        Local4 = RefOf (G005)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX6, DAT6, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                            F0E7,   33
                        }

                        Local3 = RefOf (F0E7)
                        Local4 = RefOf (G006)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX7, DAT7, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                            F0E8,   63
                        }

                        Local3 = RefOf (F0E8)
                        Local4 = RefOf (G007)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX8, DAT8, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                            F0E9,   64
                        }

                        Local3 = RefOf (F0E9)
                        Local4 = RefOf (G008)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX9, DAT9, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                            F0EA,   65
                        }

                        Local3 = RefOf (F0EA)
                        Local4 = RefOf (G009)
                    }
                    Case (0x45)
                    {
                        IndexField (IDXA, DATA, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                            F0EB,   69
                        }

                        Local3 = RefOf (F0EB)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x81)
                    {
                        IndexField (IDXB, DATB, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                            F0EC,   129
                        }

                        Local3 = RefOf (F0EC)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDXC, DATC, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                            F0ED,   256
                        }

                        Local3 = RefOf (F0ED)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDXD, DATD, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                            F0EE,   1023
                        }

                        Local3 = RefOf (F0EE)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDXE, DATE, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                            F0EF,   1983
                        }

                        Local3 = RefOf (F0EF)
                        Local4 = RefOf (G00E)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX0, DAT0, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F0,   1
                        }

                        Local3 = RefOf (F0F0)
                        Local4 = RefOf (G000)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX1, DAT1, WordAcc, NoLock, WriteAsOnes)
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
                        IndexField (IDX2, DAT2, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F2,   7
                        }

                        Local3 = RefOf (F0F2)
                        Local4 = RefOf (G002)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX3, DAT3, WordAcc, NoLock, WriteAsOnes)
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
                        IndexField (IDX4, DAT4, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F4,   9
                        }

                        Local3 = RefOf (F0F4)
                        Local4 = RefOf (G004)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX5, DAT5, WordAcc, NoLock, WriteAsOnes)
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
                        IndexField (IDX6, DAT6, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F6,   32
                        }

                        Local3 = RefOf (F0F6)
                        Local4 = RefOf (G006)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX7, DAT7, WordAcc, NoLock, WriteAsOnes)
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
                        IndexField (IDX8, DAT8, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F8,   63
                        }

                        Local3 = RefOf (F0F8)
                        Local4 = RefOf (G008)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX9, DAT9, WordAcc, NoLock, WriteAsOnes)
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
                        IndexField (IDXA, DATA, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                                ,   1,
                            F0FA,   65
                        }

                        Local3 = RefOf (F0FA)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x45)
                    {
                        IndexField (IDXB, DATB, WordAcc, NoLock, WriteAsOnes)
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
                        IndexField (IDXC, DATC, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                                ,   1,
                            F0FC,   129
                        }

                        Local3 = RefOf (F0FC)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDXD, DATD, WordAcc, NoLock, WriteAsOnes)
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
                        IndexField (IDXE, DATE, WordAcc, NoLock, WriteAsOnes)
                        {
                            Offset (0x08),
                                ,   1,
                            F0FE,   1023
                        }

                        Local3 = RefOf (F0FE)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX0, DAT0, WordAcc, NoLock, WriteAsOnes)
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
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Default
            {
                ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
                Return (Zero)
            }

        }

        M72D (Arg0, Local3, Arg2, Arg3, Arg4, Arg5, Local4)
    }

    /* Create IndexField Unit */
    /* (DWordAcc, NoLock, WriteAsZeros) */
    Method (M792, 6, Serialized)
    {
        OperationRegion (OPR0, SystemMemory, 0x1388, 0x87)
        /*
         * Consider different attributes of index/data fields
         * taking into account the following restrictions:
         * - the fields spanning the same access unit interfere,
         * - the fields exceeding 64 bits cause AE_BUFFER_OVERFLOW,
         * - index field exceeding 32 bits unexpectedly cause
         *   AE_BUFFER_OVERFLOW too,
         * - data field exceeding IndexField's Access Width
         *   causes overwriting of next memory bytes.
         */
        Field (OPR0, ByteAcc, NoLock, Preserve)
        {
            IDX0,   8,
            DAT0,   32
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
            G000,   2048
        }

        Field (OPR0, ByteAcc, NoLock, WriteAsOnes)
        {
            Offset (0x04),
            IDX1,   8,
            DAT1,   32
        }

        IndexField (IDX1, DAT1, ByteAcc, NoLock, Preserve)
        {
            G001,   2048
        }

        Field (OPR0, ByteAcc, NoLock, WriteAsZeros)
        {
            Offset (0x08),
            IDX2,   16,
            DAT2,   32
        }

        IndexField (IDX2, DAT2, ByteAcc, NoLock, Preserve)
        {
            G002,   2048
        }

        Field (OPR0, WordAcc, NoLock, Preserve)
        {
            Offset (0x0E),
            IDX3,   16,
            DAT3,   32
        }

        IndexField (IDX3, DAT3, ByteAcc, NoLock, Preserve)
        {
            G003,   2048
        }

        Field (OPR0, WordAcc, NoLock, WriteAsOnes)
        {
            Offset (0x14),
            IDX4,   16,
            DAT4,   32
        }

        IndexField (IDX4, DAT4, ByteAcc, NoLock, Preserve)
        {
            G004,   2048
        }

        Field (OPR0, WordAcc, NoLock, WriteAsZeros)
        {
            Offset (0x1A),
            IDX5,   32,
            DAT5,   32
        }

        IndexField (IDX5, DAT5, ByteAcc, NoLock, Preserve)
        {
            G005,   2048
        }

        Field (OPR0, DWordAcc, NoLock, Preserve)
        {
            Offset (0x22),
            IDX6,   8,
            Offset (0x24),
            DAT6,   32
        }

        IndexField (IDX6, DAT6, ByteAcc, NoLock, Preserve)
        {
            G006,   2048
        }

        Field (OPR0, DWordAcc, NoLock, WriteAsOnes)
        {
            Offset (0x28),
            IDX7,   32,
            DAT7,   32
        }

        IndexField (IDX7, DAT7, ByteAcc, NoLock, Preserve)
        {
            G007,   2048
        }

        Field (OPR0, DWordAcc, NoLock, WriteAsZeros)
        {
            Offset (0x30),
            IDX8,   32,
            DAT8,   32
        }

        IndexField (IDX8, DAT8, ByteAcc, NoLock, Preserve)
        {
            G008,   2048
        }

        Field (OPR0, QWordAcc, NoLock, Preserve)
        {
            Offset (0x3C),
            IDX9,   8,
            Offset (0x40),
            DAT9,   32
        }

        IndexField (IDX9, DAT9, ByteAcc, NoLock, Preserve)
        {
            G009,   2048
        }

        Field (OPR0, QWordAcc, NoLock, WriteAsOnes)
        {
            Offset (0x48),
            Offset (0x4C),
            /* Index field exceeding 32 bits causes AE_BUFFER_OVERFLOW */
            /* IDXA, 64, */
            /* Do not allow index/data interference */
            IDXA,   32,
            DATA,   32
        }

        IndexField (IDXA, DATA, ByteAcc, NoLock, Preserve)
        {
            G00A,   2048
        }

        Field (OPR0, QWordAcc, NoLock, WriteAsZeros)
        {
            Offset (0x58),
            IDXB,   32,
            Offset (0x60),
            DATB,   32
        }

        IndexField (IDXB, DATB, ByteAcc, NoLock, Preserve)
        {
            G00B,   2048
        }

        Field (OPR0, AnyAcc, NoLock, Preserve)
        {
            Offset (0x68),
            IDXC,   8,
            DATC,   32
        }

        IndexField (IDXC, DATC, ByteAcc, NoLock, Preserve)
        {
            G00C,   2048
        }

        Field (OPR0, AnyAcc, NoLock, WriteAsOnes)
        {
            Offset (0x6C),
            /* Index field exceeding 32 bits causes AE_BUFFER_OVERFLOW */
            /* IDXD, 64, */
            IDXD,   32,
            DATD,   32
        }

        IndexField (IDXD, DATD, ByteAcc, NoLock, Preserve)
        {
            G00D,   2048
        }

        Field (OPR0, AnyAcc, NoLock, WriteAsZeros)
        {
            Offset (0x7B),
            IDXE,   32,
            DATE,   32
        }

        IndexField (IDXE, DATE, ByteAcc, NoLock, Preserve)
        {
            G00E,   2048
        }

        Concatenate (Arg0, "-m792", Arg0)
        Switch (ToInteger (Arg2))
        {
            Case (0x00)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        IndexField (IDX0, DAT0, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                            F000,   1
                        }

                        Local3 = RefOf (F000)
                        Local4 = RefOf (G000)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX1, DAT1, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                            F001,   6
                        }

                        Local3 = RefOf (F001)
                        Local4 = RefOf (G001)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX2, DAT2, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                            F002,   7
                        }

                        Local3 = RefOf (F002)
                        Local4 = RefOf (G002)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX3, DAT3, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                            F003,   8
                        }

                        Local3 = RefOf (F003)
                        Local4 = RefOf (G003)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX4, DAT4, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                            F004,   9
                        }

                        Local3 = RefOf (F004)
                        Local4 = RefOf (G004)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX5, DAT5, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                            F005,   31
                        }

                        Local3 = RefOf (F005)
                        Local4 = RefOf (G005)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX6, DAT6, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                            F006,   32
                        }

                        Local3 = RefOf (F006)
                        Local4 = RefOf (G006)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX7, DAT7, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                            F007,   33
                        }

                        Local3 = RefOf (F007)
                        Local4 = RefOf (G007)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX8, DAT8, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                            F008,   63
                        }

                        Local3 = RefOf (F008)
                        Local4 = RefOf (G008)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX9, DAT9, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                            F009,   64
                        }

                        Local3 = RefOf (F009)
                        Local4 = RefOf (G009)
                    }
                    Case (0x41)
                    {
                        IndexField (IDXA, DATA, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                            F00A,   65
                        }

                        Local3 = RefOf (F00A)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x45)
                    {
                        IndexField (IDXB, DATB, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                            F00B,   69
                        }

                        Local3 = RefOf (F00B)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x81)
                    {
                        IndexField (IDXC, DATC, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                            F00C,   129
                        }

                        Local3 = RefOf (F00C)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDXD, DATD, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                            F00D,   256
                        }

                        Local3 = RefOf (F00D)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDXE, DATE, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                            F00E,   1023
                        }

                        Local3 = RefOf (F00E)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX0, DAT0, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                            F00F,   1983
                        }

                        Local3 = RefOf (F00F)
                        Local4 = RefOf (G000)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX1, DAT1, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                                ,   1,
                            F010,   1
                        }

                        Local3 = RefOf (F010)
                        Local4 = RefOf (G001)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX2, DAT2, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                                ,   1,
                            F011,   6
                        }

                        Local3 = RefOf (F011)
                        Local4 = RefOf (G002)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX3, DAT3, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                                ,   1,
                            F012,   7
                        }

                        Local3 = RefOf (F012)
                        Local4 = RefOf (G003)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX4, DAT4, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                                ,   1,
                            F013,   8
                        }

                        Local3 = RefOf (F013)
                        Local4 = RefOf (G004)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX5, DAT5, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                                ,   1,
                            F014,   9
                        }

                        Local3 = RefOf (F014)
                        Local4 = RefOf (G005)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX6, DAT6, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                                ,   1,
                            F015,   31
                        }

                        Local3 = RefOf (F015)
                        Local4 = RefOf (G006)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX7, DAT7, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                                ,   1,
                            F016,   32
                        }

                        Local3 = RefOf (F016)
                        Local4 = RefOf (G007)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX8, DAT8, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                                ,   1,
                            F017,   33
                        }

                        Local3 = RefOf (F017)
                        Local4 = RefOf (G008)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX9, DAT9, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                                ,   1,
                            F018,   63
                        }

                        Local3 = RefOf (F018)
                        Local4 = RefOf (G009)
                    }
                    Case (0x40)
                    {
                        IndexField (IDXA, DATA, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                                ,   1,
                            F019,   64
                        }

                        Local3 = RefOf (F019)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x41)
                    {
                        IndexField (IDXB, DATB, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                                ,   1,
                            F01A,   65
                        }

                        Local3 = RefOf (F01A)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x45)
                    {
                        IndexField (IDXC, DATC, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                                ,   1,
                            F01B,   69
                        }

                        Local3 = RefOf (F01B)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x81)
                    {
                        IndexField (IDXD, DATD, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                                ,   1,
                            F01C,   129
                        }

                        Local3 = RefOf (F01C)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDXE, DATE, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                                ,   1,
                            F01D,   256
                        }

                        Local3 = RefOf (F01D)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX0, DAT0, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                                ,   1,
                            F01E,   1023
                        }

                        Local3 = RefOf (F01E)
                        Local4 = RefOf (G000)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX1, DAT1, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x00),
                                ,   1,
                            F01F,   1983
                        }

                        Local3 = RefOf (F01F)
                        Local4 = RefOf (G001)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX2, DAT2, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   2,
                            F020,   1
                        }

                        Local3 = RefOf (F020)
                        Local4 = RefOf (G002)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX3, DAT3, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   2,
                            F021,   6
                        }

                        Local3 = RefOf (F021)
                        Local4 = RefOf (G003)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX4, DAT4, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   2,
                            F022,   7
                        }

                        Local3 = RefOf (F022)
                        Local4 = RefOf (G004)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX5, DAT5, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   2,
                            F023,   8
                        }

                        Local3 = RefOf (F023)
                        Local4 = RefOf (G005)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX6, DAT6, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   2,
                            F024,   9
                        }

                        Local3 = RefOf (F024)
                        Local4 = RefOf (G006)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX7, DAT7, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   2,
                            F025,   31
                        }

                        Local3 = RefOf (F025)
                        Local4 = RefOf (G007)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX8, DAT8, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   2,
                            F026,   32
                        }

                        Local3 = RefOf (F026)
                        Local4 = RefOf (G008)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX9, DAT9, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   2,
                            F027,   33
                        }

                        Local3 = RefOf (F027)
                        Local4 = RefOf (G009)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDXA, DATA, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   2,
                            F028,   63
                        }

                        Local3 = RefOf (F028)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x40)
                    {
                        IndexField (IDXB, DATB, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   2,
                            F029,   64
                        }

                        Local3 = RefOf (F029)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x41)
                    {
                        IndexField (IDXC, DATC, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   2,
                            F02A,   65
                        }

                        Local3 = RefOf (F02A)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x45)
                    {
                        IndexField (IDXD, DATD, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   2,
                            F02B,   69
                        }

                        Local3 = RefOf (F02B)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x81)
                    {
                        IndexField (IDXE, DATE, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   2,
                            F02C,   129
                        }

                        Local3 = RefOf (F02C)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX0, DAT0, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   2,
                            F02D,   256
                        }

                        Local3 = RefOf (F02D)
                        Local4 = RefOf (G000)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX1, DAT1, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   2,
                            F02E,   1023
                        }

                        Local3 = RefOf (F02E)
                        Local4 = RefOf (G001)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX2, DAT2, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   2,
                            F02F,   1983
                        }

                        Local3 = RefOf (F02F)
                        Local4 = RefOf (G002)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX3, DAT3, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   3,
                            F030,   1
                        }

                        Local3 = RefOf (F030)
                        Local4 = RefOf (G003)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX4, DAT4, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   3,
                            F031,   6
                        }

                        Local3 = RefOf (F031)
                        Local4 = RefOf (G004)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX5, DAT5, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   3,
                            F032,   7
                        }

                        Local3 = RefOf (F032)
                        Local4 = RefOf (G005)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX6, DAT6, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   3,
                            F033,   8
                        }

                        Local3 = RefOf (F033)
                        Local4 = RefOf (G006)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX7, DAT7, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   3,
                            F034,   9
                        }

                        Local3 = RefOf (F034)
                        Local4 = RefOf (G007)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX8, DAT8, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   3,
                            F035,   31
                        }

                        Local3 = RefOf (F035)
                        Local4 = RefOf (G008)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX9, DAT9, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   3,
                            F036,   32
                        }

                        Local3 = RefOf (F036)
                        Local4 = RefOf (G009)
                    }
                    Case (0x21)
                    {
                        IndexField (IDXA, DATA, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   3,
                            F037,   33
                        }

                        Local3 = RefOf (F037)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDXB, DATB, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   3,
                            F038,   63
                        }

                        Local3 = RefOf (F038)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x40)
                    {
                        IndexField (IDXC, DATC, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   3,
                            F039,   64
                        }

                        Local3 = RefOf (F039)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x41)
                    {
                        IndexField (IDXD, DATD, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   3,
                            F03A,   65
                        }

                        Local3 = RefOf (F03A)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x45)
                    {
                        IndexField (IDXE, DATE, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   3,
                            F03B,   69
                        }

                        Local3 = RefOf (F03B)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX0, DAT0, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   3,
                            F03C,   129
                        }

                        Local3 = RefOf (F03C)
                        Local4 = RefOf (G000)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX1, DAT1, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   3,
                            F03D,   256
                        }

                        Local3 = RefOf (F03D)
                        Local4 = RefOf (G001)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX2, DAT2, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   3,
                            F03E,   1023
                        }

                        Local3 = RefOf (F03E)
                        Local4 = RefOf (G002)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX3, DAT3, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   3,
                            F03F,   1983
                        }

                        Local3 = RefOf (F03F)
                        Local4 = RefOf (G003)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX4, DAT4, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   4,
                            F040,   1
                        }

                        Local3 = RefOf (F040)
                        Local4 = RefOf (G004)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX5, DAT5, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   4,
                            F041,   6
                        }

                        Local3 = RefOf (F041)
                        Local4 = RefOf (G005)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX6, DAT6, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   4,
                            F042,   7
                        }

                        Local3 = RefOf (F042)
                        Local4 = RefOf (G006)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX7, DAT7, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   4,
                            F043,   8
                        }

                        Local3 = RefOf (F043)
                        Local4 = RefOf (G007)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX8, DAT8, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   4,
                            F044,   9
                        }

                        Local3 = RefOf (F044)
                        Local4 = RefOf (G008)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX9, DAT9, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   4,
                            F045,   31
                        }

                        Local3 = RefOf (F045)
                        Local4 = RefOf (G009)
                    }
                    Case (0x20)
                    {
                        IndexField (IDXA, DATA, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   4,
                            F046,   32
                        }

                        Local3 = RefOf (F046)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x21)
                    {
                        IndexField (IDXB, DATB, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   4,
                            F047,   33
                        }

                        Local3 = RefOf (F047)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDXC, DATC, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   4,
                            F048,   63
                        }

                        Local3 = RefOf (F048)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x40)
                    {
                        IndexField (IDXD, DATD, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   4,
                            F049,   64
                        }

                        Local3 = RefOf (F049)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x41)
                    {
                        IndexField (IDXE, DATE, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   4,
                            F04A,   65
                        }

                        Local3 = RefOf (F04A)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX0, DAT0, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   4,
                            F04B,   69
                        }

                        Local3 = RefOf (F04B)
                        Local4 = RefOf (G000)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX1, DAT1, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   4,
                            F04C,   129
                        }

                        Local3 = RefOf (F04C)
                        Local4 = RefOf (G001)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX2, DAT2, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   4,
                            F04D,   256
                        }

                        Local3 = RefOf (F04D)
                        Local4 = RefOf (G002)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX3, DAT3, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   4,
                            F04E,   1023
                        }

                        Local3 = RefOf (F04E)
                        Local4 = RefOf (G003)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX4, DAT4, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   4,
                            F04F,   1983
                        }

                        Local3 = RefOf (F04F)
                        Local4 = RefOf (G004)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX5, DAT5, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   5,
                            F050,   1
                        }

                        Local3 = RefOf (F050)
                        Local4 = RefOf (G005)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX6, DAT6, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   5,
                            F051,   6
                        }

                        Local3 = RefOf (F051)
                        Local4 = RefOf (G006)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX7, DAT7, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   5,
                            F052,   7
                        }

                        Local3 = RefOf (F052)
                        Local4 = RefOf (G007)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX8, DAT8, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   5,
                            F053,   8
                        }

                        Local3 = RefOf (F053)
                        Local4 = RefOf (G008)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX9, DAT9, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   5,
                            F054,   9
                        }

                        Local3 = RefOf (F054)
                        Local4 = RefOf (G009)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDXA, DATA, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   5,
                            F055,   31
                        }

                        Local3 = RefOf (F055)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x20)
                    {
                        IndexField (IDXB, DATB, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   5,
                            F056,   32
                        }

                        Local3 = RefOf (F056)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x21)
                    {
                        IndexField (IDXC, DATC, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   5,
                            F057,   33
                        }

                        Local3 = RefOf (F057)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDXD, DATD, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   5,
                            F058,   63
                        }

                        Local3 = RefOf (F058)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x40)
                    {
                        IndexField (IDXE, DATE, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   5,
                            F059,   64
                        }

                        Local3 = RefOf (F059)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX0, DAT0, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   5,
                            F05A,   65
                        }

                        Local3 = RefOf (F05A)
                        Local4 = RefOf (G000)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX1, DAT1, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   5,
                            F05B,   69
                        }

                        Local3 = RefOf (F05B)
                        Local4 = RefOf (G001)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX2, DAT2, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   5,
                            F05C,   129
                        }

                        Local3 = RefOf (F05C)
                        Local4 = RefOf (G002)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX3, DAT3, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   5,
                            F05D,   256
                        }

                        Local3 = RefOf (F05D)
                        Local4 = RefOf (G003)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX4, DAT4, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   5,
                            F05E,   1023
                        }

                        Local3 = RefOf (F05E)
                        Local4 = RefOf (G004)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX5, DAT5, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   5,
                            F05F,   1983
                        }

                        Local3 = RefOf (F05F)
                        Local4 = RefOf (G005)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX6, DAT6, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   6,
                            F060,   1
                        }

                        Local3 = RefOf (F060)
                        Local4 = RefOf (G006)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX7, DAT7, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   6,
                            F061,   6
                        }

                        Local3 = RefOf (F061)
                        Local4 = RefOf (G007)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX8, DAT8, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   6,
                            F062,   7
                        }

                        Local3 = RefOf (F062)
                        Local4 = RefOf (G008)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX9, DAT9, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   6,
                            F063,   8
                        }

                        Local3 = RefOf (F063)
                        Local4 = RefOf (G009)
                    }
                    Case (0x09)
                    {
                        IndexField (IDXA, DATA, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   6,
                            F064,   9
                        }

                        Local3 = RefOf (F064)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDXB, DATB, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   6,
                            F065,   31
                        }

                        Local3 = RefOf (F065)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x20)
                    {
                        IndexField (IDXC, DATC, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   6,
                            F066,   32
                        }

                        Local3 = RefOf (F066)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x21)
                    {
                        IndexField (IDXD, DATD, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   6,
                            F067,   33
                        }

                        Local3 = RefOf (F067)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDXE, DATE, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   6,
                            F068,   63
                        }

                        Local3 = RefOf (F068)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX0, DAT0, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   6,
                            F069,   64
                        }

                        Local3 = RefOf (F069)
                        Local4 = RefOf (G000)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX1, DAT1, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   6,
                            F06A,   65
                        }

                        Local3 = RefOf (F06A)
                        Local4 = RefOf (G001)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX2, DAT2, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   6,
                            F06B,   69
                        }

                        Local3 = RefOf (F06B)
                        Local4 = RefOf (G002)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX3, DAT3, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   6,
                            F06C,   129
                        }

                        Local3 = RefOf (F06C)
                        Local4 = RefOf (G003)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX4, DAT4, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   6,
                            F06D,   256
                        }

                        Local3 = RefOf (F06D)
                        Local4 = RefOf (G004)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX5, DAT5, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   6,
                            F06E,   1023
                        }

                        Local3 = RefOf (F06E)
                        Local4 = RefOf (G005)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX6, DAT6, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   6,
                            F06F,   1983
                        }

                        Local3 = RefOf (F06F)
                        Local4 = RefOf (G006)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX7, DAT7, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   7,
                            F070,   1
                        }

                        Local3 = RefOf (F070)
                        Local4 = RefOf (G007)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX8, DAT8, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   7,
                            F071,   6
                        }

                        Local3 = RefOf (F071)
                        Local4 = RefOf (G008)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX9, DAT9, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   7,
                            F072,   7
                        }

                        Local3 = RefOf (F072)
                        Local4 = RefOf (G009)
                    }
                    Case (0x08)
                    {
                        IndexField (IDXA, DATA, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   7,
                            F073,   8
                        }

                        Local3 = RefOf (F073)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x09)
                    {
                        IndexField (IDXB, DATB, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   7,
                            F074,   9
                        }

                        Local3 = RefOf (F074)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDXC, DATC, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   7,
                            F075,   31
                        }

                        Local3 = RefOf (F075)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x20)
                    {
                        IndexField (IDXD, DATD, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   7,
                            F076,   32
                        }

                        Local3 = RefOf (F076)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x21)
                    {
                        IndexField (IDXE, DATE, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   7,
                            F077,   33
                        }

                        Local3 = RefOf (F077)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX0, DAT0, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   7,
                            F078,   63
                        }

                        Local3 = RefOf (F078)
                        Local4 = RefOf (G000)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX1, DAT1, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   7,
                            F079,   64
                        }

                        Local3 = RefOf (F079)
                        Local4 = RefOf (G001)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX2, DAT2, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   7,
                            F07A,   65
                        }

                        Local3 = RefOf (F07A)
                        Local4 = RefOf (G002)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX3, DAT3, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   7,
                            F07B,   69
                        }

                        Local3 = RefOf (F07B)
                        Local4 = RefOf (G003)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX4, DAT4, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   7,
                            F07C,   129
                        }

                        Local3 = RefOf (F07C)
                        Local4 = RefOf (G004)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX5, DAT5, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   7,
                            F07D,   256
                        }

                        Local3 = RefOf (F07D)
                        Local4 = RefOf (G005)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX6, DAT6, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   7,
                            F07E,   1023
                        }

                        Local3 = RefOf (F07E)
                        Local4 = RefOf (G006)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX7, DAT7, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   7,
                            F07F,   1983
                        }

                        Local3 = RefOf (F07F)
                        Local4 = RefOf (G007)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX8, DAT8, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x01),
                            F080,   1
                        }

                        Local3 = RefOf (F080)
                        Local4 = RefOf (G008)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX9, DAT9, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x01),
                            F081,   6
                        }

                        Local3 = RefOf (F081)
                        Local4 = RefOf (G009)
                    }
                    Case (0x07)
                    {
                        IndexField (IDXA, DATA, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x01),
                            F082,   7
                        }

                        Local3 = RefOf (F082)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x08)
                    {
                        IndexField (IDXB, DATB, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x01),
                            F083,   8
                        }

                        Local3 = RefOf (F083)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x09)
                    {
                        IndexField (IDXC, DATC, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x01),
                            F084,   9
                        }

                        Local3 = RefOf (F084)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDXD, DATD, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x01),
                            F085,   31
                        }

                        Local3 = RefOf (F085)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x20)
                    {
                        IndexField (IDXE, DATE, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x01),
                            F086,   32
                        }

                        Local3 = RefOf (F086)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX0, DAT0, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x01),
                            F087,   33
                        }

                        Local3 = RefOf (F087)
                        Local4 = RefOf (G000)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX1, DAT1, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x01),
                            F088,   63
                        }

                        Local3 = RefOf (F088)
                        Local4 = RefOf (G001)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX2, DAT2, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x01),
                            F089,   64
                        }

                        Local3 = RefOf (F089)
                        Local4 = RefOf (G002)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX3, DAT3, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x01),
                            F08A,   65
                        }

                        Local3 = RefOf (F08A)
                        Local4 = RefOf (G003)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX4, DAT4, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x01),
                            F08B,   69
                        }

                        Local3 = RefOf (F08B)
                        Local4 = RefOf (G004)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX5, DAT5, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x01),
                            F08C,   129
                        }

                        Local3 = RefOf (F08C)
                        Local4 = RefOf (G005)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX6, DAT6, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x01),
                            F08D,   256
                        }

                        Local3 = RefOf (F08D)
                        Local4 = RefOf (G006)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX7, DAT7, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x01),
                            F08E,   1023
                        }

                        Local3 = RefOf (F08E)
                        Local4 = RefOf (G007)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX8, DAT8, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x01),
                            F08F,   1983
                        }

                        Local3 = RefOf (F08F)
                        Local4 = RefOf (G008)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX9, DAT9, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   9,
                            F090,   1
                        }

                        Local3 = RefOf (F090)
                        Local4 = RefOf (G009)
                    }
                    Case (0x06)
                    {
                        IndexField (IDXA, DATA, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   9,
                            F091,   6
                        }

                        Local3 = RefOf (F091)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x07)
                    {
                        IndexField (IDXB, DATB, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   9,
                            F092,   7
                        }

                        Local3 = RefOf (F092)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x08)
                    {
                        IndexField (IDXC, DATC, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   9,
                            F093,   8
                        }

                        Local3 = RefOf (F093)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x09)
                    {
                        IndexField (IDXD, DATD, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   9,
                            F094,   9
                        }

                        Local3 = RefOf (F094)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDXE, DATE, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   9,
                            F095,   31
                        }

                        Local3 = RefOf (F095)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX0, DAT0, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   9,
                            F096,   32
                        }

                        Local3 = RefOf (F096)
                        Local4 = RefOf (G000)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX1, DAT1, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   9,
                            F097,   33
                        }

                        Local3 = RefOf (F097)
                        Local4 = RefOf (G001)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX2, DAT2, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   9,
                            F098,   63
                        }

                        Local3 = RefOf (F098)
                        Local4 = RefOf (G002)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX3, DAT3, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   9,
                            F099,   64
                        }

                        Local3 = RefOf (F099)
                        Local4 = RefOf (G003)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX4, DAT4, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   9,
                            F09A,   65
                        }

                        Local3 = RefOf (F09A)
                        Local4 = RefOf (G004)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX5, DAT5, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   9,
                            F09B,   69
                        }

                        Local3 = RefOf (F09B)
                        Local4 = RefOf (G005)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX6, DAT6, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   9,
                            F09C,   129
                        }

                        Local3 = RefOf (F09C)
                        Local4 = RefOf (G006)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX7, DAT7, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   9,
                            F09D,   256
                        }

                        Local3 = RefOf (F09D)
                        Local4 = RefOf (G007)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX8, DAT8, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   9,
                            F09E,   1023
                        }

                        Local3 = RefOf (F09E)
                        Local4 = RefOf (G008)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX9, DAT9, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   9,
                            F09F,   1983
                        }

                        Local3 = RefOf (F09F)
                        Local4 = RefOf (G009)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDXA, DATA, DWordAcc, NoLock, WriteAsZeros)
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
                        IndexField (IDXB, DATB, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A1,   6
                        }

                        Local3 = RefOf (F0A1)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x07)
                    {
                        IndexField (IDXC, DATC, DWordAcc, NoLock, WriteAsZeros)
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
                        IndexField (IDXD, DATD, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A3,   8
                        }

                        Local3 = RefOf (F0A3)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x09)
                    {
                        IndexField (IDXE, DATE, DWordAcc, NoLock, WriteAsZeros)
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
                        IndexField (IDX0, DAT0, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A5,   31
                        }

                        Local3 = RefOf (F0A5)
                        Local4 = RefOf (G000)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX1, DAT1, DWordAcc, NoLock, WriteAsZeros)
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
                        IndexField (IDX2, DAT2, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A7,   33
                        }

                        Local3 = RefOf (F0A7)
                        Local4 = RefOf (G002)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX3, DAT3, DWordAcc, NoLock, WriteAsZeros)
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
                        IndexField (IDX4, DAT4, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A9,   64
                        }

                        Local3 = RefOf (F0A9)
                        Local4 = RefOf (G004)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX5, DAT5, DWordAcc, NoLock, WriteAsZeros)
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
                        IndexField (IDX6, DAT6, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x03),
                                ,   7,
                            F0AB,   69
                        }

                        Local3 = RefOf (F0AB)
                        Local4 = RefOf (G006)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX7, DAT7, DWordAcc, NoLock, WriteAsZeros)
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
                        IndexField (IDX8, DAT8, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x03),
                                ,   7,
                            F0AD,   256
                        }

                        Local3 = RefOf (F0AD)
                        Local4 = RefOf (G008)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX9, DAT9, DWordAcc, NoLock, WriteAsZeros)
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
                        IndexField (IDXA, DATA, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x03),
                                ,   7,
                            F0AF,   1983
                        }

                        Local3 = RefOf (F0AF)
                        Local4 = RefOf (G00A)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDXB, DATB, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x04),
                            F0B0,   1
                        }

                        Local3 = RefOf (F0B0)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x06)
                    {
                        IndexField (IDXC, DATC, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x04),
                            F0B1,   6
                        }

                        Local3 = RefOf (F0B1)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x07)
                    {
                        IndexField (IDXD, DATD, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x04),
                            F0B2,   7
                        }

                        Local3 = RefOf (F0B2)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x08)
                    {
                        IndexField (IDXE, DATE, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x04),
                            F0B3,   8
                        }

                        Local3 = RefOf (F0B3)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX0, DAT0, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x04),
                            F0B4,   9
                        }

                        Local3 = RefOf (F0B4)
                        Local4 = RefOf (G000)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX1, DAT1, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x04),
                            F0B5,   31
                        }

                        Local3 = RefOf (F0B5)
                        Local4 = RefOf (G001)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX2, DAT2, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x04),
                            F0B6,   32
                        }

                        Local3 = RefOf (F0B6)
                        Local4 = RefOf (G002)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX3, DAT3, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x04),
                            F0B7,   33
                        }

                        Local3 = RefOf (F0B7)
                        Local4 = RefOf (G003)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX4, DAT4, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x04),
                            F0B8,   63
                        }

                        Local3 = RefOf (F0B8)
                        Local4 = RefOf (G004)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX5, DAT5, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x04),
                            F0B9,   64
                        }

                        Local3 = RefOf (F0B9)
                        Local4 = RefOf (G005)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX6, DAT6, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x04),
                            F0BA,   65
                        }

                        Local3 = RefOf (F0BA)
                        Local4 = RefOf (G006)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX7, DAT7, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x04),
                            F0BB,   69
                        }

                        Local3 = RefOf (F0BB)
                        Local4 = RefOf (G007)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX8, DAT8, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x04),
                            F0BC,   129
                        }

                        Local3 = RefOf (F0BC)
                        Local4 = RefOf (G008)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX9, DAT9, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x04),
                            F0BD,   256
                        }

                        Local3 = RefOf (F0BD)
                        Local4 = RefOf (G009)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDXA, DATA, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x04),
                            F0BE,   1023
                        }

                        Local3 = RefOf (F0BE)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDXB, DATB, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x04),
                            F0BF,   1983
                        }

                        Local3 = RefOf (F0BF)
                        Local4 = RefOf (G00B)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDXC, DATC, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   33,
                            F0C0,   1
                        }

                        Local3 = RefOf (F0C0)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x06)
                    {
                        IndexField (IDXD, DATD, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   33,
                            F0C1,   6
                        }

                        Local3 = RefOf (F0C1)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x07)
                    {
                        IndexField (IDXE, DATE, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   33,
                            F0C2,   7
                        }

                        Local3 = RefOf (F0C2)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX0, DAT0, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   33,
                            F0C3,   8
                        }

                        Local3 = RefOf (F0C3)
                        Local4 = RefOf (G000)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX1, DAT1, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   33,
                            F0C4,   9
                        }

                        Local3 = RefOf (F0C4)
                        Local4 = RefOf (G001)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX2, DAT2, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   33,
                            F0C5,   31
                        }

                        Local3 = RefOf (F0C5)
                        Local4 = RefOf (G002)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX3, DAT3, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   33,
                            F0C6,   32
                        }

                        Local3 = RefOf (F0C6)
                        Local4 = RefOf (G003)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX4, DAT4, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   33,
                            F0C7,   33
                        }

                        Local3 = RefOf (F0C7)
                        Local4 = RefOf (G004)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX5, DAT5, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   33,
                            F0C8,   63
                        }

                        Local3 = RefOf (F0C8)
                        Local4 = RefOf (G005)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX6, DAT6, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   33,
                            F0C9,   64
                        }

                        Local3 = RefOf (F0C9)
                        Local4 = RefOf (G006)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX7, DAT7, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   33,
                            F0CA,   65
                        }

                        Local3 = RefOf (F0CA)
                        Local4 = RefOf (G007)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX8, DAT8, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   33,
                            F0CB,   69
                        }

                        Local3 = RefOf (F0CB)
                        Local4 = RefOf (G008)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX9, DAT9, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   33,
                            F0CC,   129
                        }

                        Local3 = RefOf (F0CC)
                        Local4 = RefOf (G009)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDXA, DATA, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   33,
                            F0CD,   256
                        }

                        Local3 = RefOf (F0CD)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDXB, DATB, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   33,
                            F0CE,   1023
                        }

                        Local3 = RefOf (F0CE)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDXC, DATC, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   33,
                            F0CF,   1983
                        }

                        Local3 = RefOf (F0CF)
                        Local4 = RefOf (G00C)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDXD, DATD, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   63,
                            F0D0,   1
                        }

                        Local3 = RefOf (F0D0)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x06)
                    {
                        IndexField (IDXE, DATE, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   63,
                            F0D1,   6
                        }

                        Local3 = RefOf (F0D1)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX0, DAT0, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   63,
                            F0D2,   7
                        }

                        Local3 = RefOf (F0D2)
                        Local4 = RefOf (G000)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX1, DAT1, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   63,
                            F0D3,   8
                        }

                        Local3 = RefOf (F0D3)
                        Local4 = RefOf (G001)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX2, DAT2, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   63,
                            F0D4,   9
                        }

                        Local3 = RefOf (F0D4)
                        Local4 = RefOf (G002)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX3, DAT3, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   63,
                            F0D5,   31
                        }

                        Local3 = RefOf (F0D5)
                        Local4 = RefOf (G003)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX4, DAT4, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   63,
                            F0D6,   32
                        }

                        Local3 = RefOf (F0D6)
                        Local4 = RefOf (G004)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX5, DAT5, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   63,
                            F0D7,   33
                        }

                        Local3 = RefOf (F0D7)
                        Local4 = RefOf (G005)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX6, DAT6, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   63,
                            F0D8,   63
                        }

                        Local3 = RefOf (F0D8)
                        Local4 = RefOf (G006)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX7, DAT7, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   63,
                            F0D9,   64
                        }

                        Local3 = RefOf (F0D9)
                        Local4 = RefOf (G007)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX8, DAT8, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   63,
                            F0DA,   65
                        }

                        Local3 = RefOf (F0DA)
                        Local4 = RefOf (G008)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX9, DAT9, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   63,
                            F0DB,   69
                        }

                        Local3 = RefOf (F0DB)
                        Local4 = RefOf (G009)
                    }
                    Case (0x81)
                    {
                        IndexField (IDXA, DATA, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   63,
                            F0DC,   129
                        }

                        Local3 = RefOf (F0DC)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDXB, DATB, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   63,
                            F0DD,   256
                        }

                        Local3 = RefOf (F0DD)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDXC, DATC, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   63,
                            F0DE,   1023
                        }

                        Local3 = RefOf (F0DE)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDXD, DATD, DWordAcc, NoLock, WriteAsZeros)
                        {
                                ,   63,
                            F0DF,   1983
                        }

                        Local3 = RefOf (F0DF)
                        Local4 = RefOf (G00D)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDXE, DATE, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                            F0E0,   1
                        }

                        Local3 = RefOf (F0E0)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX0, DAT0, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                            F0E1,   6
                        }

                        Local3 = RefOf (F0E1)
                        Local4 = RefOf (G000)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX1, DAT1, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                            F0E2,   7
                        }

                        Local3 = RefOf (F0E2)
                        Local4 = RefOf (G001)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX2, DAT2, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                            F0E3,   8
                        }

                        Local3 = RefOf (F0E3)
                        Local4 = RefOf (G002)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX3, DAT3, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                            F0E4,   9
                        }

                        Local3 = RefOf (F0E4)
                        Local4 = RefOf (G003)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX4, DAT4, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                            F0E5,   31
                        }

                        Local3 = RefOf (F0E5)
                        Local4 = RefOf (G004)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX5, DAT5, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                            F0E6,   32
                        }

                        Local3 = RefOf (F0E6)
                        Local4 = RefOf (G005)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX6, DAT6, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                            F0E7,   33
                        }

                        Local3 = RefOf (F0E7)
                        Local4 = RefOf (G006)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX7, DAT7, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                            F0E8,   63
                        }

                        Local3 = RefOf (F0E8)
                        Local4 = RefOf (G007)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX8, DAT8, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                            F0E9,   64
                        }

                        Local3 = RefOf (F0E9)
                        Local4 = RefOf (G008)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX9, DAT9, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                            F0EA,   65
                        }

                        Local3 = RefOf (F0EA)
                        Local4 = RefOf (G009)
                    }
                    Case (0x45)
                    {
                        IndexField (IDXA, DATA, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                            F0EB,   69
                        }

                        Local3 = RefOf (F0EB)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x81)
                    {
                        IndexField (IDXB, DATB, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                            F0EC,   129
                        }

                        Local3 = RefOf (F0EC)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDXC, DATC, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                            F0ED,   256
                        }

                        Local3 = RefOf (F0ED)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDXD, DATD, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                            F0EE,   1023
                        }

                        Local3 = RefOf (F0EE)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDXE, DATE, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                            F0EF,   1983
                        }

                        Local3 = RefOf (F0EF)
                        Local4 = RefOf (G00E)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX0, DAT0, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F0,   1
                        }

                        Local3 = RefOf (F0F0)
                        Local4 = RefOf (G000)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX1, DAT1, DWordAcc, NoLock, WriteAsZeros)
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
                        IndexField (IDX2, DAT2, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F2,   7
                        }

                        Local3 = RefOf (F0F2)
                        Local4 = RefOf (G002)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX3, DAT3, DWordAcc, NoLock, WriteAsZeros)
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
                        IndexField (IDX4, DAT4, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F4,   9
                        }

                        Local3 = RefOf (F0F4)
                        Local4 = RefOf (G004)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX5, DAT5, DWordAcc, NoLock, WriteAsZeros)
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
                        IndexField (IDX6, DAT6, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F6,   32
                        }

                        Local3 = RefOf (F0F6)
                        Local4 = RefOf (G006)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX7, DAT7, DWordAcc, NoLock, WriteAsZeros)
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
                        IndexField (IDX8, DAT8, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F8,   63
                        }

                        Local3 = RefOf (F0F8)
                        Local4 = RefOf (G008)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX9, DAT9, DWordAcc, NoLock, WriteAsZeros)
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
                        IndexField (IDXA, DATA, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                                ,   1,
                            F0FA,   65
                        }

                        Local3 = RefOf (F0FA)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x45)
                    {
                        IndexField (IDXB, DATB, DWordAcc, NoLock, WriteAsZeros)
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
                        IndexField (IDXC, DATC, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                                ,   1,
                            F0FC,   129
                        }

                        Local3 = RefOf (F0FC)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDXD, DATD, DWordAcc, NoLock, WriteAsZeros)
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
                        IndexField (IDXE, DATE, DWordAcc, NoLock, WriteAsZeros)
                        {
                            Offset (0x08),
                                ,   1,
                            F0FE,   1023
                        }

                        Local3 = RefOf (F0FE)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX0, DAT0, DWordAcc, NoLock, WriteAsZeros)
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
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Default
            {
                ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
                Return (Zero)
            }

        }

        M72D (Arg0, Local3, Arg2, Arg3, Arg4, Arg5, Local4)
    }

    /* Create IndexField Unit */
    /* (QWordAcc, NoLock, Preserve) */
    Method (M793, 6, Serialized)
    {
        OperationRegion (OPR0, SystemMemory, 0x1770, 0xA8)
        /*
         * Consider different attributes of index/data fields
         * taking into account the following restrictions:
         * - the fields spanning the same access unit interfere,
         * - the fields exceeding 64 bits cause AE_BUFFER_OVERFLOW,
         * - index field exceeding 32 bits unexpectedly cause
         *   AE_BUFFER_OVERFLOW too,
         * - data field exceeding IndexField's Access Width
         *   causes overwriting of next memory bytes.
         */
        Field (OPR0, ByteAcc, NoLock, Preserve)
        {
            IDX0,   8,
            DAT0,   64
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
            G000,   2048
        }

        Field (OPR0, ByteAcc, NoLock, WriteAsOnes)
        {
            Offset (0x07),
            IDX1,   8,
            DAT1,   64
        }

        IndexField (IDX1, DAT1, ByteAcc, NoLock, Preserve)
        {
            G001,   2048
        }

        Field (OPR0, ByteAcc, NoLock, WriteAsZeros)
        {
            Offset (0x0E),
            IDX2,   16,
            DAT2,   64
        }

        IndexField (IDX2, DAT2, ByteAcc, NoLock, Preserve)
        {
            G002,   2048
        }

        Field (OPR0, WordAcc, NoLock, Preserve)
        {
            Offset (0x18),
            IDX3,   16,
            DAT3,   64
        }

        IndexField (IDX3, DAT3, ByteAcc, NoLock, Preserve)
        {
            G003,   2048
        }

        Field (OPR0, WordAcc, NoLock, WriteAsOnes)
        {
            Offset (0x22),
            IDX4,   16,
            DAT4,   64
        }

        IndexField (IDX4, DAT4, ByteAcc, NoLock, Preserve)
        {
            G004,   2048
        }

        Field (OPR0, WordAcc, NoLock, WriteAsZeros)
        {
            Offset (0x2C),
            IDX5,   32,
            DAT5,   64
        }

        IndexField (IDX5, DAT5, ByteAcc, NoLock, Preserve)
        {
            G005,   2048
        }

        Field (OPR0, DWordAcc, NoLock, Preserve)
        {
            Offset (0x38),
            IDX6,   8,
            Offset (0x3C),
            DAT6,   64
        }

        IndexField (IDX6, DAT6, ByteAcc, NoLock, Preserve)
        {
            G006,   2048
        }

        Field (OPR0, DWordAcc, NoLock, WriteAsOnes)
        {
            Offset (0x44),
            IDX7,   32,
            DAT7,   64
        }

        IndexField (IDX7, DAT7, ByteAcc, NoLock, Preserve)
        {
            G007,   2048
        }

        Field (OPR0, DWordAcc, NoLock, WriteAsZeros)
        {
            Offset (0x46),
            IDX8,   32,
            DAT8,   64
        }

        IndexField (IDX8, DAT8, ByteAcc, NoLock, Preserve)
        {
            G008,   2048
        }

        Field (OPR0, QWordAcc, NoLock, Preserve)
        {
            Offset (0x52),
            IDX9,   8,
            Offset (0x58),
            DAT9,   64
        }

        IndexField (IDX9, DAT9, ByteAcc, NoLock, Preserve)
        {
            G009,   2048
        }

        Field (OPR0, QWordAcc, NoLock, WriteAsOnes)
        {
            Offset (0x60),
            Offset (0x64),
            /* Index field exceeding 32 bits causes AE_BUFFER_OVERFLOW */
            /* IDXA, 64, */
            /* Do not allow index/data interference */
            IDXA,   32,
            DATA,   64
        }

        IndexField (IDXA, DATA, ByteAcc, NoLock, Preserve)
        {
            G00A,   2048
        }

        Field (OPR0, QWordAcc, NoLock, WriteAsZeros)
        {
            Offset (0x70),
            IDXB,   32,
            Offset (0x78),
            DATB,   64
        }

        IndexField (IDXB, DATB, ByteAcc, NoLock, Preserve)
        {
            G00B,   2048
        }

        Field (OPR0, AnyAcc, NoLock, Preserve)
        {
            Offset (0x80),
            IDXC,   8,
            DATC,   64
        }

        IndexField (IDXC, DATC, ByteAcc, NoLock, Preserve)
        {
            G00C,   2048
        }

        Field (OPR0, AnyAcc, NoLock, WriteAsOnes)
        {
            Offset (0x88),
            /* Index field exceeding 32 bits causes AE_BUFFER_OVERFLOW */
            /* IDXD, 64, */
            IDXD,   32,
            Offset (0x90),
            DATD,   64
        }

        IndexField (IDXD, DATD, ByteAcc, NoLock, Preserve)
        {
            G00D,   2048
        }

        Field (OPR0, AnyAcc, NoLock, WriteAsZeros)
        {
            Offset (0x98),
            IDXE,   32,
            Offset (0xA0),
            DATE,   64
        }

        IndexField (IDXE, DATE, ByteAcc, NoLock, Preserve)
        {
            G00E,   2048
        }

        Concatenate (Arg0, "-m793", Arg0)
        Switch (ToInteger (Arg2))
        {
            Case (0x00)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        IndexField (IDX0, DAT0, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F000,   1
                        }

                        Local3 = RefOf (F000)
                        Local4 = RefOf (G000)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX1, DAT1, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F001,   6
                        }

                        Local3 = RefOf (F001)
                        Local4 = RefOf (G001)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX2, DAT2, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F002,   7
                        }

                        Local3 = RefOf (F002)
                        Local4 = RefOf (G002)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX3, DAT3, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F003,   8
                        }

                        Local3 = RefOf (F003)
                        Local4 = RefOf (G003)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX4, DAT4, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F004,   9
                        }

                        Local3 = RefOf (F004)
                        Local4 = RefOf (G004)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX5, DAT5, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F005,   31
                        }

                        Local3 = RefOf (F005)
                        Local4 = RefOf (G005)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX6, DAT6, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F006,   32
                        }

                        Local3 = RefOf (F006)
                        Local4 = RefOf (G006)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX7, DAT7, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F007,   33
                        }

                        Local3 = RefOf (F007)
                        Local4 = RefOf (G007)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX8, DAT8, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F008,   63
                        }

                        Local3 = RefOf (F008)
                        Local4 = RefOf (G008)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX9, DAT9, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F009,   64
                        }

                        Local3 = RefOf (F009)
                        Local4 = RefOf (G009)
                    }
                    Case (0x41)
                    {
                        IndexField (IDXA, DATA, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F00A,   65
                        }

                        Local3 = RefOf (F00A)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x45)
                    {
                        IndexField (IDXB, DATB, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F00B,   69
                        }

                        Local3 = RefOf (F00B)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x81)
                    {
                        IndexField (IDXC, DATC, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F00C,   129
                        }

                        Local3 = RefOf (F00C)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDXD, DATD, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F00D,   256
                        }

                        Local3 = RefOf (F00D)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDXE, DATE, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F00E,   1023
                        }

                        Local3 = RefOf (F00E)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX0, DAT0, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                            F00F,   1983
                        }

                        Local3 = RefOf (F00F)
                        Local4 = RefOf (G000)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX1, DAT1, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F010,   1
                        }

                        Local3 = RefOf (F010)
                        Local4 = RefOf (G001)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX2, DAT2, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F011,   6
                        }

                        Local3 = RefOf (F011)
                        Local4 = RefOf (G002)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX3, DAT3, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F012,   7
                        }

                        Local3 = RefOf (F012)
                        Local4 = RefOf (G003)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX4, DAT4, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F013,   8
                        }

                        Local3 = RefOf (F013)
                        Local4 = RefOf (G004)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX5, DAT5, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F014,   9
                        }

                        Local3 = RefOf (F014)
                        Local4 = RefOf (G005)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX6, DAT6, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F015,   31
                        }

                        Local3 = RefOf (F015)
                        Local4 = RefOf (G006)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX7, DAT7, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F016,   32
                        }

                        Local3 = RefOf (F016)
                        Local4 = RefOf (G007)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX8, DAT8, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F017,   33
                        }

                        Local3 = RefOf (F017)
                        Local4 = RefOf (G008)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX9, DAT9, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F018,   63
                        }

                        Local3 = RefOf (F018)
                        Local4 = RefOf (G009)
                    }
                    Case (0x40)
                    {
                        IndexField (IDXA, DATA, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F019,   64
                        }

                        Local3 = RefOf (F019)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x41)
                    {
                        IndexField (IDXB, DATB, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F01A,   65
                        }

                        Local3 = RefOf (F01A)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x45)
                    {
                        IndexField (IDXC, DATC, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F01B,   69
                        }

                        Local3 = RefOf (F01B)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x81)
                    {
                        IndexField (IDXD, DATD, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F01C,   129
                        }

                        Local3 = RefOf (F01C)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDXE, DATE, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F01D,   256
                        }

                        Local3 = RefOf (F01D)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX0, DAT0, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F01E,   1023
                        }

                        Local3 = RefOf (F01E)
                        Local4 = RefOf (G000)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX1, DAT1, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F01F,   1983
                        }

                        Local3 = RefOf (F01F)
                        Local4 = RefOf (G001)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX2, DAT2, QWordAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F020,   1
                        }

                        Local3 = RefOf (F020)
                        Local4 = RefOf (G002)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX3, DAT3, QWordAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F021,   6
                        }

                        Local3 = RefOf (F021)
                        Local4 = RefOf (G003)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX4, DAT4, QWordAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F022,   7
                        }

                        Local3 = RefOf (F022)
                        Local4 = RefOf (G004)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX5, DAT5, QWordAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F023,   8
                        }

                        Local3 = RefOf (F023)
                        Local4 = RefOf (G005)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX6, DAT6, QWordAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F024,   9
                        }

                        Local3 = RefOf (F024)
                        Local4 = RefOf (G006)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX7, DAT7, QWordAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F025,   31
                        }

                        Local3 = RefOf (F025)
                        Local4 = RefOf (G007)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX8, DAT8, QWordAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F026,   32
                        }

                        Local3 = RefOf (F026)
                        Local4 = RefOf (G008)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX9, DAT9, QWordAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F027,   33
                        }

                        Local3 = RefOf (F027)
                        Local4 = RefOf (G009)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDXA, DATA, QWordAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F028,   63
                        }

                        Local3 = RefOf (F028)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x40)
                    {
                        IndexField (IDXB, DATB, QWordAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F029,   64
                        }

                        Local3 = RefOf (F029)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x41)
                    {
                        IndexField (IDXC, DATC, QWordAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F02A,   65
                        }

                        Local3 = RefOf (F02A)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x45)
                    {
                        IndexField (IDXD, DATD, QWordAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F02B,   69
                        }

                        Local3 = RefOf (F02B)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x81)
                    {
                        IndexField (IDXE, DATE, QWordAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F02C,   129
                        }

                        Local3 = RefOf (F02C)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX0, DAT0, QWordAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F02D,   256
                        }

                        Local3 = RefOf (F02D)
                        Local4 = RefOf (G000)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX1, DAT1, QWordAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F02E,   1023
                        }

                        Local3 = RefOf (F02E)
                        Local4 = RefOf (G001)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX2, DAT2, QWordAcc, NoLock, Preserve)
                        {
                                ,   2,
                            F02F,   1983
                        }

                        Local3 = RefOf (F02F)
                        Local4 = RefOf (G002)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX3, DAT3, QWordAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F030,   1
                        }

                        Local3 = RefOf (F030)
                        Local4 = RefOf (G003)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX4, DAT4, QWordAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F031,   6
                        }

                        Local3 = RefOf (F031)
                        Local4 = RefOf (G004)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX5, DAT5, QWordAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F032,   7
                        }

                        Local3 = RefOf (F032)
                        Local4 = RefOf (G005)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX6, DAT6, QWordAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F033,   8
                        }

                        Local3 = RefOf (F033)
                        Local4 = RefOf (G006)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX7, DAT7, QWordAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F034,   9
                        }

                        Local3 = RefOf (F034)
                        Local4 = RefOf (G007)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX8, DAT8, QWordAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F035,   31
                        }

                        Local3 = RefOf (F035)
                        Local4 = RefOf (G008)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX9, DAT9, QWordAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F036,   32
                        }

                        Local3 = RefOf (F036)
                        Local4 = RefOf (G009)
                    }
                    Case (0x21)
                    {
                        IndexField (IDXA, DATA, QWordAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F037,   33
                        }

                        Local3 = RefOf (F037)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDXB, DATB, QWordAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F038,   63
                        }

                        Local3 = RefOf (F038)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x40)
                    {
                        IndexField (IDXC, DATC, QWordAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F039,   64
                        }

                        Local3 = RefOf (F039)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x41)
                    {
                        IndexField (IDXD, DATD, QWordAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F03A,   65
                        }

                        Local3 = RefOf (F03A)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x45)
                    {
                        IndexField (IDXE, DATE, QWordAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F03B,   69
                        }

                        Local3 = RefOf (F03B)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX0, DAT0, QWordAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F03C,   129
                        }

                        Local3 = RefOf (F03C)
                        Local4 = RefOf (G000)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX1, DAT1, QWordAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F03D,   256
                        }

                        Local3 = RefOf (F03D)
                        Local4 = RefOf (G001)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX2, DAT2, QWordAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F03E,   1023
                        }

                        Local3 = RefOf (F03E)
                        Local4 = RefOf (G002)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX3, DAT3, QWordAcc, NoLock, Preserve)
                        {
                                ,   3,
                            F03F,   1983
                        }

                        Local3 = RefOf (F03F)
                        Local4 = RefOf (G003)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX4, DAT4, QWordAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F040,   1
                        }

                        Local3 = RefOf (F040)
                        Local4 = RefOf (G004)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX5, DAT5, QWordAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F041,   6
                        }

                        Local3 = RefOf (F041)
                        Local4 = RefOf (G005)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX6, DAT6, QWordAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F042,   7
                        }

                        Local3 = RefOf (F042)
                        Local4 = RefOf (G006)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX7, DAT7, QWordAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F043,   8
                        }

                        Local3 = RefOf (F043)
                        Local4 = RefOf (G007)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX8, DAT8, QWordAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F044,   9
                        }

                        Local3 = RefOf (F044)
                        Local4 = RefOf (G008)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX9, DAT9, QWordAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F045,   31
                        }

                        Local3 = RefOf (F045)
                        Local4 = RefOf (G009)
                    }
                    Case (0x20)
                    {
                        IndexField (IDXA, DATA, QWordAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F046,   32
                        }

                        Local3 = RefOf (F046)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x21)
                    {
                        IndexField (IDXB, DATB, QWordAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F047,   33
                        }

                        Local3 = RefOf (F047)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDXC, DATC, QWordAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F048,   63
                        }

                        Local3 = RefOf (F048)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x40)
                    {
                        IndexField (IDXD, DATD, QWordAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F049,   64
                        }

                        Local3 = RefOf (F049)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x41)
                    {
                        IndexField (IDXE, DATE, QWordAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F04A,   65
                        }

                        Local3 = RefOf (F04A)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX0, DAT0, QWordAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F04B,   69
                        }

                        Local3 = RefOf (F04B)
                        Local4 = RefOf (G000)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX1, DAT1, QWordAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F04C,   129
                        }

                        Local3 = RefOf (F04C)
                        Local4 = RefOf (G001)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX2, DAT2, QWordAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F04D,   256
                        }

                        Local3 = RefOf (F04D)
                        Local4 = RefOf (G002)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX3, DAT3, QWordAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F04E,   1023
                        }

                        Local3 = RefOf (F04E)
                        Local4 = RefOf (G003)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX4, DAT4, QWordAcc, NoLock, Preserve)
                        {
                                ,   4,
                            F04F,   1983
                        }

                        Local3 = RefOf (F04F)
                        Local4 = RefOf (G004)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX5, DAT5, QWordAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F050,   1
                        }

                        Local3 = RefOf (F050)
                        Local4 = RefOf (G005)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX6, DAT6, QWordAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F051,   6
                        }

                        Local3 = RefOf (F051)
                        Local4 = RefOf (G006)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX7, DAT7, QWordAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F052,   7
                        }

                        Local3 = RefOf (F052)
                        Local4 = RefOf (G007)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX8, DAT8, QWordAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F053,   8
                        }

                        Local3 = RefOf (F053)
                        Local4 = RefOf (G008)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX9, DAT9, QWordAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F054,   9
                        }

                        Local3 = RefOf (F054)
                        Local4 = RefOf (G009)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDXA, DATA, QWordAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F055,   31
                        }

                        Local3 = RefOf (F055)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x20)
                    {
                        IndexField (IDXB, DATB, QWordAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F056,   32
                        }

                        Local3 = RefOf (F056)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x21)
                    {
                        IndexField (IDXC, DATC, QWordAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F057,   33
                        }

                        Local3 = RefOf (F057)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDXD, DATD, QWordAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F058,   63
                        }

                        Local3 = RefOf (F058)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x40)
                    {
                        IndexField (IDXE, DATE, QWordAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F059,   64
                        }

                        Local3 = RefOf (F059)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX0, DAT0, QWordAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F05A,   65
                        }

                        Local3 = RefOf (F05A)
                        Local4 = RefOf (G000)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX1, DAT1, QWordAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F05B,   69
                        }

                        Local3 = RefOf (F05B)
                        Local4 = RefOf (G001)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX2, DAT2, QWordAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F05C,   129
                        }

                        Local3 = RefOf (F05C)
                        Local4 = RefOf (G002)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX3, DAT3, QWordAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F05D,   256
                        }

                        Local3 = RefOf (F05D)
                        Local4 = RefOf (G003)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX4, DAT4, QWordAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F05E,   1023
                        }

                        Local3 = RefOf (F05E)
                        Local4 = RefOf (G004)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX5, DAT5, QWordAcc, NoLock, Preserve)
                        {
                                ,   5,
                            F05F,   1983
                        }

                        Local3 = RefOf (F05F)
                        Local4 = RefOf (G005)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX6, DAT6, QWordAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F060,   1
                        }

                        Local3 = RefOf (F060)
                        Local4 = RefOf (G006)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX7, DAT7, QWordAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F061,   6
                        }

                        Local3 = RefOf (F061)
                        Local4 = RefOf (G007)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX8, DAT8, QWordAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F062,   7
                        }

                        Local3 = RefOf (F062)
                        Local4 = RefOf (G008)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX9, DAT9, QWordAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F063,   8
                        }

                        Local3 = RefOf (F063)
                        Local4 = RefOf (G009)
                    }
                    Case (0x09)
                    {
                        IndexField (IDXA, DATA, QWordAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F064,   9
                        }

                        Local3 = RefOf (F064)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDXB, DATB, QWordAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F065,   31
                        }

                        Local3 = RefOf (F065)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x20)
                    {
                        IndexField (IDXC, DATC, QWordAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F066,   32
                        }

                        Local3 = RefOf (F066)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x21)
                    {
                        IndexField (IDXD, DATD, QWordAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F067,   33
                        }

                        Local3 = RefOf (F067)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDXE, DATE, QWordAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F068,   63
                        }

                        Local3 = RefOf (F068)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX0, DAT0, QWordAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F069,   64
                        }

                        Local3 = RefOf (F069)
                        Local4 = RefOf (G000)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX1, DAT1, QWordAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F06A,   65
                        }

                        Local3 = RefOf (F06A)
                        Local4 = RefOf (G001)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX2, DAT2, QWordAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F06B,   69
                        }

                        Local3 = RefOf (F06B)
                        Local4 = RefOf (G002)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX3, DAT3, QWordAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F06C,   129
                        }

                        Local3 = RefOf (F06C)
                        Local4 = RefOf (G003)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX4, DAT4, QWordAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F06D,   256
                        }

                        Local3 = RefOf (F06D)
                        Local4 = RefOf (G004)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX5, DAT5, QWordAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F06E,   1023
                        }

                        Local3 = RefOf (F06E)
                        Local4 = RefOf (G005)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX6, DAT6, QWordAcc, NoLock, Preserve)
                        {
                                ,   6,
                            F06F,   1983
                        }

                        Local3 = RefOf (F06F)
                        Local4 = RefOf (G006)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX7, DAT7, QWordAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F070,   1
                        }

                        Local3 = RefOf (F070)
                        Local4 = RefOf (G007)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX8, DAT8, QWordAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F071,   6
                        }

                        Local3 = RefOf (F071)
                        Local4 = RefOf (G008)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX9, DAT9, QWordAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F072,   7
                        }

                        Local3 = RefOf (F072)
                        Local4 = RefOf (G009)
                    }
                    Case (0x08)
                    {
                        IndexField (IDXA, DATA, QWordAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F073,   8
                        }

                        Local3 = RefOf (F073)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x09)
                    {
                        IndexField (IDXB, DATB, QWordAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F074,   9
                        }

                        Local3 = RefOf (F074)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDXC, DATC, QWordAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F075,   31
                        }

                        Local3 = RefOf (F075)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x20)
                    {
                        IndexField (IDXD, DATD, QWordAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F076,   32
                        }

                        Local3 = RefOf (F076)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x21)
                    {
                        IndexField (IDXE, DATE, QWordAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F077,   33
                        }

                        Local3 = RefOf (F077)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX0, DAT0, QWordAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F078,   63
                        }

                        Local3 = RefOf (F078)
                        Local4 = RefOf (G000)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX1, DAT1, QWordAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F079,   64
                        }

                        Local3 = RefOf (F079)
                        Local4 = RefOf (G001)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX2, DAT2, QWordAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F07A,   65
                        }

                        Local3 = RefOf (F07A)
                        Local4 = RefOf (G002)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX3, DAT3, QWordAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F07B,   69
                        }

                        Local3 = RefOf (F07B)
                        Local4 = RefOf (G003)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX4, DAT4, QWordAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F07C,   129
                        }

                        Local3 = RefOf (F07C)
                        Local4 = RefOf (G004)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX5, DAT5, QWordAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F07D,   256
                        }

                        Local3 = RefOf (F07D)
                        Local4 = RefOf (G005)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX6, DAT6, QWordAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F07E,   1023
                        }

                        Local3 = RefOf (F07E)
                        Local4 = RefOf (G006)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX7, DAT7, QWordAcc, NoLock, Preserve)
                        {
                                ,   7,
                            F07F,   1983
                        }

                        Local3 = RefOf (F07F)
                        Local4 = RefOf (G007)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX8, DAT8, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F080,   1
                        }

                        Local3 = RefOf (F080)
                        Local4 = RefOf (G008)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX9, DAT9, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F081,   6
                        }

                        Local3 = RefOf (F081)
                        Local4 = RefOf (G009)
                    }
                    Case (0x07)
                    {
                        IndexField (IDXA, DATA, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F082,   7
                        }

                        Local3 = RefOf (F082)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x08)
                    {
                        IndexField (IDXB, DATB, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F083,   8
                        }

                        Local3 = RefOf (F083)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x09)
                    {
                        IndexField (IDXC, DATC, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F084,   9
                        }

                        Local3 = RefOf (F084)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDXD, DATD, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F085,   31
                        }

                        Local3 = RefOf (F085)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x20)
                    {
                        IndexField (IDXE, DATE, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F086,   32
                        }

                        Local3 = RefOf (F086)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX0, DAT0, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F087,   33
                        }

                        Local3 = RefOf (F087)
                        Local4 = RefOf (G000)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX1, DAT1, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F088,   63
                        }

                        Local3 = RefOf (F088)
                        Local4 = RefOf (G001)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX2, DAT2, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F089,   64
                        }

                        Local3 = RefOf (F089)
                        Local4 = RefOf (G002)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX3, DAT3, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F08A,   65
                        }

                        Local3 = RefOf (F08A)
                        Local4 = RefOf (G003)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX4, DAT4, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F08B,   69
                        }

                        Local3 = RefOf (F08B)
                        Local4 = RefOf (G004)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX5, DAT5, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F08C,   129
                        }

                        Local3 = RefOf (F08C)
                        Local4 = RefOf (G005)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX6, DAT6, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F08D,   256
                        }

                        Local3 = RefOf (F08D)
                        Local4 = RefOf (G006)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX7, DAT7, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F08E,   1023
                        }

                        Local3 = RefOf (F08E)
                        Local4 = RefOf (G007)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX8, DAT8, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x01),
                            F08F,   1983
                        }

                        Local3 = RefOf (F08F)
                        Local4 = RefOf (G008)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX9, DAT9, QWordAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F090,   1
                        }

                        Local3 = RefOf (F090)
                        Local4 = RefOf (G009)
                    }
                    Case (0x06)
                    {
                        IndexField (IDXA, DATA, QWordAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F091,   6
                        }

                        Local3 = RefOf (F091)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x07)
                    {
                        IndexField (IDXB, DATB, QWordAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F092,   7
                        }

                        Local3 = RefOf (F092)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x08)
                    {
                        IndexField (IDXC, DATC, QWordAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F093,   8
                        }

                        Local3 = RefOf (F093)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x09)
                    {
                        IndexField (IDXD, DATD, QWordAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F094,   9
                        }

                        Local3 = RefOf (F094)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDXE, DATE, QWordAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F095,   31
                        }

                        Local3 = RefOf (F095)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX0, DAT0, QWordAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F096,   32
                        }

                        Local3 = RefOf (F096)
                        Local4 = RefOf (G000)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX1, DAT1, QWordAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F097,   33
                        }

                        Local3 = RefOf (F097)
                        Local4 = RefOf (G001)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX2, DAT2, QWordAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F098,   63
                        }

                        Local3 = RefOf (F098)
                        Local4 = RefOf (G002)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX3, DAT3, QWordAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F099,   64
                        }

                        Local3 = RefOf (F099)
                        Local4 = RefOf (G003)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX4, DAT4, QWordAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F09A,   65
                        }

                        Local3 = RefOf (F09A)
                        Local4 = RefOf (G004)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX5, DAT5, QWordAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F09B,   69
                        }

                        Local3 = RefOf (F09B)
                        Local4 = RefOf (G005)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX6, DAT6, QWordAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F09C,   129
                        }

                        Local3 = RefOf (F09C)
                        Local4 = RefOf (G006)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX7, DAT7, QWordAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F09D,   256
                        }

                        Local3 = RefOf (F09D)
                        Local4 = RefOf (G007)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX8, DAT8, QWordAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F09E,   1023
                        }

                        Local3 = RefOf (F09E)
                        Local4 = RefOf (G008)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX9, DAT9, QWordAcc, NoLock, Preserve)
                        {
                                ,   9,
                            F09F,   1983
                        }

                        Local3 = RefOf (F09F)
                        Local4 = RefOf (G009)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDXA, DATA, QWordAcc, NoLock, Preserve)
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
                        IndexField (IDXB, DATB, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A1,   6
                        }

                        Local3 = RefOf (F0A1)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x07)
                    {
                        IndexField (IDXC, DATC, QWordAcc, NoLock, Preserve)
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
                        IndexField (IDXD, DATD, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A3,   8
                        }

                        Local3 = RefOf (F0A3)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x09)
                    {
                        IndexField (IDXE, DATE, QWordAcc, NoLock, Preserve)
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
                        IndexField (IDX0, DAT0, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A5,   31
                        }

                        Local3 = RefOf (F0A5)
                        Local4 = RefOf (G000)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX1, DAT1, QWordAcc, NoLock, Preserve)
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
                        IndexField (IDX2, DAT2, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A7,   33
                        }

                        Local3 = RefOf (F0A7)
                        Local4 = RefOf (G002)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX3, DAT3, QWordAcc, NoLock, Preserve)
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
                        IndexField (IDX4, DAT4, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A9,   64
                        }

                        Local3 = RefOf (F0A9)
                        Local4 = RefOf (G004)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX5, DAT5, QWordAcc, NoLock, Preserve)
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
                        IndexField (IDX6, DAT6, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0AB,   69
                        }

                        Local3 = RefOf (F0AB)
                        Local4 = RefOf (G006)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX7, DAT7, QWordAcc, NoLock, Preserve)
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
                        IndexField (IDX8, DAT8, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0AD,   256
                        }

                        Local3 = RefOf (F0AD)
                        Local4 = RefOf (G008)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX9, DAT9, QWordAcc, NoLock, Preserve)
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
                        IndexField (IDXA, DATA, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0AF,   1983
                        }

                        Local3 = RefOf (F0AF)
                        Local4 = RefOf (G00A)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDXB, DATB, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0B0,   1
                        }

                        Local3 = RefOf (F0B0)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x06)
                    {
                        IndexField (IDXC, DATC, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0B1,   6
                        }

                        Local3 = RefOf (F0B1)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x07)
                    {
                        IndexField (IDXD, DATD, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0B2,   7
                        }

                        Local3 = RefOf (F0B2)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x08)
                    {
                        IndexField (IDXE, DATE, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0B3,   8
                        }

                        Local3 = RefOf (F0B3)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX0, DAT0, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0B4,   9
                        }

                        Local3 = RefOf (F0B4)
                        Local4 = RefOf (G000)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX1, DAT1, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0B5,   31
                        }

                        Local3 = RefOf (F0B5)
                        Local4 = RefOf (G001)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX2, DAT2, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0B6,   32
                        }

                        Local3 = RefOf (F0B6)
                        Local4 = RefOf (G002)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX3, DAT3, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0B7,   33
                        }

                        Local3 = RefOf (F0B7)
                        Local4 = RefOf (G003)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX4, DAT4, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0B8,   63
                        }

                        Local3 = RefOf (F0B8)
                        Local4 = RefOf (G004)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX5, DAT5, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0B9,   64
                        }

                        Local3 = RefOf (F0B9)
                        Local4 = RefOf (G005)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX6, DAT6, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0BA,   65
                        }

                        Local3 = RefOf (F0BA)
                        Local4 = RefOf (G006)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX7, DAT7, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0BB,   69
                        }

                        Local3 = RefOf (F0BB)
                        Local4 = RefOf (G007)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX8, DAT8, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0BC,   129
                        }

                        Local3 = RefOf (F0BC)
                        Local4 = RefOf (G008)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX9, DAT9, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0BD,   256
                        }

                        Local3 = RefOf (F0BD)
                        Local4 = RefOf (G009)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDXA, DATA, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0BE,   1023
                        }

                        Local3 = RefOf (F0BE)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDXB, DATB, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x04),
                            F0BF,   1983
                        }

                        Local3 = RefOf (F0BF)
                        Local4 = RefOf (G00B)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDXC, DATC, QWordAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0C0,   1
                        }

                        Local3 = RefOf (F0C0)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x06)
                    {
                        IndexField (IDXD, DATD, QWordAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0C1,   6
                        }

                        Local3 = RefOf (F0C1)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x07)
                    {
                        IndexField (IDXE, DATE, QWordAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0C2,   7
                        }

                        Local3 = RefOf (F0C2)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX0, DAT0, QWordAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0C3,   8
                        }

                        Local3 = RefOf (F0C3)
                        Local4 = RefOf (G000)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX1, DAT1, QWordAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0C4,   9
                        }

                        Local3 = RefOf (F0C4)
                        Local4 = RefOf (G001)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX2, DAT2, QWordAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0C5,   31
                        }

                        Local3 = RefOf (F0C5)
                        Local4 = RefOf (G002)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX3, DAT3, QWordAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0C6,   32
                        }

                        Local3 = RefOf (F0C6)
                        Local4 = RefOf (G003)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX4, DAT4, QWordAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0C7,   33
                        }

                        Local3 = RefOf (F0C7)
                        Local4 = RefOf (G004)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX5, DAT5, QWordAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0C8,   63
                        }

                        Local3 = RefOf (F0C8)
                        Local4 = RefOf (G005)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX6, DAT6, QWordAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0C9,   64
                        }

                        Local3 = RefOf (F0C9)
                        Local4 = RefOf (G006)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX7, DAT7, QWordAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0CA,   65
                        }

                        Local3 = RefOf (F0CA)
                        Local4 = RefOf (G007)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX8, DAT8, QWordAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0CB,   69
                        }

                        Local3 = RefOf (F0CB)
                        Local4 = RefOf (G008)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX9, DAT9, QWordAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0CC,   129
                        }

                        Local3 = RefOf (F0CC)
                        Local4 = RefOf (G009)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDXA, DATA, QWordAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0CD,   256
                        }

                        Local3 = RefOf (F0CD)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDXB, DATB, QWordAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0CE,   1023
                        }

                        Local3 = RefOf (F0CE)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDXC, DATC, QWordAcc, NoLock, Preserve)
                        {
                                ,   33,
                            F0CF,   1983
                        }

                        Local3 = RefOf (F0CF)
                        Local4 = RefOf (G00C)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDXD, DATD, QWordAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0D0,   1
                        }

                        Local3 = RefOf (F0D0)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x06)
                    {
                        IndexField (IDXE, DATE, QWordAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0D1,   6
                        }

                        Local3 = RefOf (F0D1)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX0, DAT0, QWordAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0D2,   7
                        }

                        Local3 = RefOf (F0D2)
                        Local4 = RefOf (G000)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX1, DAT1, QWordAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0D3,   8
                        }

                        Local3 = RefOf (F0D3)
                        Local4 = RefOf (G001)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX2, DAT2, QWordAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0D4,   9
                        }

                        Local3 = RefOf (F0D4)
                        Local4 = RefOf (G002)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX3, DAT3, QWordAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0D5,   31
                        }

                        Local3 = RefOf (F0D5)
                        Local4 = RefOf (G003)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX4, DAT4, QWordAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0D6,   32
                        }

                        Local3 = RefOf (F0D6)
                        Local4 = RefOf (G004)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX5, DAT5, QWordAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0D7,   33
                        }

                        Local3 = RefOf (F0D7)
                        Local4 = RefOf (G005)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX6, DAT6, QWordAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0D8,   63
                        }

                        Local3 = RefOf (F0D8)
                        Local4 = RefOf (G006)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX7, DAT7, QWordAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0D9,   64
                        }

                        Local3 = RefOf (F0D9)
                        Local4 = RefOf (G007)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX8, DAT8, QWordAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0DA,   65
                        }

                        Local3 = RefOf (F0DA)
                        Local4 = RefOf (G008)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX9, DAT9, QWordAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0DB,   69
                        }

                        Local3 = RefOf (F0DB)
                        Local4 = RefOf (G009)
                    }
                    Case (0x81)
                    {
                        IndexField (IDXA, DATA, QWordAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0DC,   129
                        }

                        Local3 = RefOf (F0DC)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDXB, DATB, QWordAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0DD,   256
                        }

                        Local3 = RefOf (F0DD)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDXC, DATC, QWordAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0DE,   1023
                        }

                        Local3 = RefOf (F0DE)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDXD, DATD, QWordAcc, NoLock, Preserve)
                        {
                                ,   63,
                            F0DF,   1983
                        }

                        Local3 = RefOf (F0DF)
                        Local4 = RefOf (G00D)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDXE, DATE, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0E0,   1
                        }

                        Local3 = RefOf (F0E0)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX0, DAT0, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0E1,   6
                        }

                        Local3 = RefOf (F0E1)
                        Local4 = RefOf (G000)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX1, DAT1, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0E2,   7
                        }

                        Local3 = RefOf (F0E2)
                        Local4 = RefOf (G001)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX2, DAT2, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0E3,   8
                        }

                        Local3 = RefOf (F0E3)
                        Local4 = RefOf (G002)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX3, DAT3, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0E4,   9
                        }

                        Local3 = RefOf (F0E4)
                        Local4 = RefOf (G003)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX4, DAT4, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0E5,   31
                        }

                        Local3 = RefOf (F0E5)
                        Local4 = RefOf (G004)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX5, DAT5, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0E6,   32
                        }

                        Local3 = RefOf (F0E6)
                        Local4 = RefOf (G005)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX6, DAT6, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0E7,   33
                        }

                        Local3 = RefOf (F0E7)
                        Local4 = RefOf (G006)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX7, DAT7, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0E8,   63
                        }

                        Local3 = RefOf (F0E8)
                        Local4 = RefOf (G007)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX8, DAT8, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0E9,   64
                        }

                        Local3 = RefOf (F0E9)
                        Local4 = RefOf (G008)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX9, DAT9, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0EA,   65
                        }

                        Local3 = RefOf (F0EA)
                        Local4 = RefOf (G009)
                    }
                    Case (0x45)
                    {
                        IndexField (IDXA, DATA, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0EB,   69
                        }

                        Local3 = RefOf (F0EB)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x81)
                    {
                        IndexField (IDXB, DATB, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0EC,   129
                        }

                        Local3 = RefOf (F0EC)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDXC, DATC, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0ED,   256
                        }

                        Local3 = RefOf (F0ED)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDXD, DATD, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0EE,   1023
                        }

                        Local3 = RefOf (F0EE)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDXE, DATE, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                            F0EF,   1983
                        }

                        Local3 = RefOf (F0EF)
                        Local4 = RefOf (G00E)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX0, DAT0, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F0,   1
                        }

                        Local3 = RefOf (F0F0)
                        Local4 = RefOf (G000)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX1, DAT1, QWordAcc, NoLock, Preserve)
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
                        IndexField (IDX2, DAT2, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F2,   7
                        }

                        Local3 = RefOf (F0F2)
                        Local4 = RefOf (G002)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX3, DAT3, QWordAcc, NoLock, Preserve)
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
                        IndexField (IDX4, DAT4, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F4,   9
                        }

                        Local3 = RefOf (F0F4)
                        Local4 = RefOf (G004)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX5, DAT5, QWordAcc, NoLock, Preserve)
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
                        IndexField (IDX6, DAT6, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F6,   32
                        }

                        Local3 = RefOf (F0F6)
                        Local4 = RefOf (G006)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX7, DAT7, QWordAcc, NoLock, Preserve)
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
                        IndexField (IDX8, DAT8, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F8,   63
                        }

                        Local3 = RefOf (F0F8)
                        Local4 = RefOf (G008)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX9, DAT9, QWordAcc, NoLock, Preserve)
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
                        IndexField (IDXA, DATA, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0FA,   65
                        }

                        Local3 = RefOf (F0FA)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x45)
                    {
                        IndexField (IDXB, DATB, QWordAcc, NoLock, Preserve)
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
                        IndexField (IDXC, DATC, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0FC,   129
                        }

                        Local3 = RefOf (F0FC)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDXD, DATD, QWordAcc, NoLock, Preserve)
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
                        IndexField (IDXE, DATE, QWordAcc, NoLock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0FE,   1023
                        }

                        Local3 = RefOf (F0FE)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX0, DAT0, QWordAcc, NoLock, Preserve)
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
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Default
            {
                ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
                Return (Zero)
            }

        }

        M72D (Arg0, Local3, Arg2, Arg3, Arg4, Arg5, Local4)
    }

    /* Create IndexField Unit */
    /* (AnyAcc, Lock, Preserve) */
    Method (M794, 6, Serialized)
    {
        OperationRegion (OPR0, SystemMemory, 0x1B58, 0x87)
        /*
         * Consider different attributes of index/data fields
         * taking into account the following restrictions:
         * - the fields spanning the same access unit interfere,
         * - the fields exceeding 64 bits cause AE_BUFFER_OVERFLOW,
         * - index field exceeding 32 bits unexpectedly cause
         *   AE_BUFFER_OVERFLOW too,
         * - data field exceeding IndexField's Access Width
         *   causes overwriting of next memory bytes.
         */
        Field (OPR0, ByteAcc, NoLock, Preserve)
        {
            IDX0,   8,
            DAT0,   8
        }

        IndexField (IDX0, DAT0, ByteAcc, NoLock, Preserve)
        {
            G000,   2048
        }

        Field (OPR0, ByteAcc, NoLock, WriteAsOnes)
        {
            Offset (0x03),
            IDX1,   8,
            DAT1,   8
        }

        IndexField (IDX1, DAT1, ByteAcc, NoLock, Preserve)
        {
            G001,   2048
        }

        Field (OPR0, ByteAcc, NoLock, WriteAsZeros)
        {
            Offset (0x07),
            IDX2,   16,
            DAT2,   8
        }

        IndexField (IDX2, DAT2, ByteAcc, NoLock, Preserve)
        {
            G002,   2048
        }

        Field (OPR0, WordAcc, NoLock, Preserve)
        {
            Offset (0x0B),
            IDX3,   8,
            DAT3,   8
        }

        IndexField (IDX3, DAT3, ByteAcc, NoLock, Preserve)
        {
            G003,   2048
        }

        Field (OPR0, WordAcc, NoLock, WriteAsOnes)
        {
            Offset (0x0E),
            IDX4,   16,
            DAT4,   8
        }

        IndexField (IDX4, DAT4, ByteAcc, NoLock, Preserve)
        {
            G004,   2048
        }

        Field (OPR0, WordAcc, NoLock, WriteAsZeros)
        {
            Offset (0x12),
            IDX5,   32,
            DAT5,   8
        }

        IndexField (IDX5, DAT5, ByteAcc, NoLock, Preserve)
        {
            G005,   2048
        }

        Field (OPR0, DWordAcc, NoLock, Preserve)
        {
            Offset (0x1A),
            IDX6,   8,
            Offset (0x1C),
            DAT6,   8
        }

        IndexField (IDX6, DAT6, ByteAcc, NoLock, Preserve)
        {
            G006,   2048
        }

        Field (OPR0, DWordAcc, NoLock, WriteAsOnes)
        {
            Offset (0x20),
            IDX7,   32,
            DAT7,   8
        }

        IndexField (IDX7, DAT7, ByteAcc, NoLock, Preserve)
        {
            G007,   2048
        }

        Field (OPR0, DWordAcc, NoLock, WriteAsZeros)
        {
            Offset (0x28),
            IDX8,   32,
            DAT8,   8
        }

        IndexField (IDX8, DAT8, ByteAcc, NoLock, Preserve)
        {
            G008,   2048
        }

        Field (OPR0, QWordAcc, NoLock, Preserve)
        {
            Offset (0x38),
            IDX9,   8,
            Offset (0x40),
            DAT9,   8
        }

        IndexField (IDX9, DAT9, ByteAcc, NoLock, Preserve)
        {
            G009,   2048
        }

        Field (OPR0, QWordAcc, NoLock, WriteAsOnes)
        {
            Offset (0x48),
            Offset (0x4C),
            /* Index field exceeding 32 bits causes AE_BUFFER_OVERFLOW */
            /* IDXA, 64, */
            /* Do not allow index/data interference */
            IDXA,   32,
            DATA,   8
        }

        IndexField (IDXA, DATA, ByteAcc, NoLock, Preserve)
        {
            G00A,   2048
        }

        Field (OPR0, QWordAcc, NoLock, WriteAsZeros)
        {
            Offset (0x58),
            IDXB,   32,
            Offset (0x60),
            DATB,   8
        }

        IndexField (IDXB, DATB, ByteAcc, NoLock, Preserve)
        {
            G00B,   2048
        }

        Field (OPR0, AnyAcc, NoLock, Preserve)
        {
            Offset (0x68),
            IDXC,   8,
            DATC,   8
        }

        IndexField (IDXC, DATC, ByteAcc, NoLock, Preserve)
        {
            G00C,   2048
        }

        Field (OPR0, AnyAcc, NoLock, WriteAsOnes)
        {
            Offset (0x6B),
            /* Index field exceeding 32 bits causes AE_BUFFER_OVERFLOW */
            /* IDXD, 64, */
            IDXD,   32,
            DATD,   8
        }

        IndexField (IDXD, DATD, ByteAcc, NoLock, Preserve)
        {
            G00D,   2048
        }

        Field (OPR0, AnyAcc, NoLock, WriteAsZeros)
        {
            Offset (0x7B),
            IDXE,   32,
            DATE,   8
        }

        IndexField (IDXE, DATE, ByteAcc, NoLock, Preserve)
        {
            G00E,   2048
        }

        Concatenate (Arg0, "-m794", Arg0)
        BreakPoint
        Switch (ToInteger (Arg2))
        {
            Case (0x00)
            {
                Switch (ToInteger (Arg3))
                {
                    Case (0x01)
                    {
                        IndexField (IDX0, DAT0, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                            F000,   1
                        }

                        Local3 = RefOf (F000)
                        Local4 = RefOf (G000)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX1, DAT1, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                            F001,   6
                        }

                        Local3 = RefOf (F001)
                        Local4 = RefOf (G001)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX2, DAT2, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                            F002,   7
                        }

                        Local3 = RefOf (F002)
                        Local4 = RefOf (G002)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX3, DAT3, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                            F003,   8
                        }

                        Local3 = RefOf (F003)
                        Local4 = RefOf (G003)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX4, DAT4, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                            F004,   9
                        }

                        Local3 = RefOf (F004)
                        Local4 = RefOf (G004)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX5, DAT5, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                            F005,   31
                        }

                        Local3 = RefOf (F005)
                        Local4 = RefOf (G005)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX6, DAT6, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                            F006,   32
                        }

                        Local3 = RefOf (F006)
                        Local4 = RefOf (G006)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX7, DAT7, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                            F007,   33
                        }

                        Local3 = RefOf (F007)
                        Local4 = RefOf (G007)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX8, DAT8, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                            F008,   63
                        }

                        Local3 = RefOf (F008)
                        Local4 = RefOf (G008)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX9, DAT9, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                            F009,   64
                        }

                        Local3 = RefOf (F009)
                        Local4 = RefOf (G009)
                    }
                    Case (0x41)
                    {
                        IndexField (IDXA, DATA, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                            F00A,   65
                        }

                        Local3 = RefOf (F00A)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x45)
                    {
                        IndexField (IDXB, DATB, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                            F00B,   69
                        }

                        Local3 = RefOf (F00B)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x81)
                    {
                        IndexField (IDXC, DATC, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                            F00C,   129
                        }

                        Local3 = RefOf (F00C)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDXD, DATD, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                            F00D,   256
                        }

                        Local3 = RefOf (F00D)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDXE, DATE, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                            F00E,   1023
                        }

                        Local3 = RefOf (F00E)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX0, DAT0, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                            F00F,   1983
                        }

                        Local3 = RefOf (F00F)
                        Local4 = RefOf (G000)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX1, DAT1, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F010,   1
                        }

                        Local3 = RefOf (F010)
                        Local4 = RefOf (G001)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX2, DAT2, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F011,   6
                        }

                        Local3 = RefOf (F011)
                        Local4 = RefOf (G002)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX3, DAT3, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F012,   7
                        }

                        Local3 = RefOf (F012)
                        Local4 = RefOf (G003)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX4, DAT4, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F013,   8
                        }

                        Local3 = RefOf (F013)
                        Local4 = RefOf (G004)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX5, DAT5, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F014,   9
                        }

                        Local3 = RefOf (F014)
                        Local4 = RefOf (G005)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX6, DAT6, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F015,   31
                        }

                        Local3 = RefOf (F015)
                        Local4 = RefOf (G006)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX7, DAT7, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F016,   32
                        }

                        Local3 = RefOf (F016)
                        Local4 = RefOf (G007)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX8, DAT8, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F017,   33
                        }

                        Local3 = RefOf (F017)
                        Local4 = RefOf (G008)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX9, DAT9, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F018,   63
                        }

                        Local3 = RefOf (F018)
                        Local4 = RefOf (G009)
                    }
                    Case (0x40)
                    {
                        IndexField (IDXA, DATA, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F019,   64
                        }

                        Local3 = RefOf (F019)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x41)
                    {
                        IndexField (IDXB, DATB, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F01A,   65
                        }

                        Local3 = RefOf (F01A)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x45)
                    {
                        IndexField (IDXC, DATC, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F01B,   69
                        }

                        Local3 = RefOf (F01B)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x81)
                    {
                        IndexField (IDXD, DATD, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F01C,   129
                        }

                        Local3 = RefOf (F01C)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDXE, DATE, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F01D,   256
                        }

                        Local3 = RefOf (F01D)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX0, DAT0, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F01E,   1023
                        }

                        Local3 = RefOf (F01E)
                        Local4 = RefOf (G000)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX1, DAT1, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x00),
                                ,   1,
                            F01F,   1983
                        }

                        Local3 = RefOf (F01F)
                        Local4 = RefOf (G001)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX2, DAT2, AnyAcc, Lock, Preserve)
                        {
                                ,   2,
                            F020,   1
                        }

                        Local3 = RefOf (F020)
                        Local4 = RefOf (G002)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX3, DAT3, AnyAcc, Lock, Preserve)
                        {
                                ,   2,
                            F021,   6
                        }

                        Local3 = RefOf (F021)
                        Local4 = RefOf (G003)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX4, DAT4, AnyAcc, Lock, Preserve)
                        {
                                ,   2,
                            F022,   7
                        }

                        Local3 = RefOf (F022)
                        Local4 = RefOf (G004)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX5, DAT5, AnyAcc, Lock, Preserve)
                        {
                                ,   2,
                            F023,   8
                        }

                        Local3 = RefOf (F023)
                        Local4 = RefOf (G005)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX6, DAT6, AnyAcc, Lock, Preserve)
                        {
                                ,   2,
                            F024,   9
                        }

                        Local3 = RefOf (F024)
                        Local4 = RefOf (G006)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX7, DAT7, AnyAcc, Lock, Preserve)
                        {
                                ,   2,
                            F025,   31
                        }

                        Local3 = RefOf (F025)
                        Local4 = RefOf (G007)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX8, DAT8, AnyAcc, Lock, Preserve)
                        {
                                ,   2,
                            F026,   32
                        }

                        Local3 = RefOf (F026)
                        Local4 = RefOf (G008)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX9, DAT9, AnyAcc, Lock, Preserve)
                        {
                                ,   2,
                            F027,   33
                        }

                        Local3 = RefOf (F027)
                        Local4 = RefOf (G009)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDXA, DATA, AnyAcc, Lock, Preserve)
                        {
                                ,   2,
                            F028,   63
                        }

                        Local3 = RefOf (F028)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x40)
                    {
                        IndexField (IDXB, DATB, AnyAcc, Lock, Preserve)
                        {
                                ,   2,
                            F029,   64
                        }

                        Local3 = RefOf (F029)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x41)
                    {
                        IndexField (IDXC, DATC, AnyAcc, Lock, Preserve)
                        {
                                ,   2,
                            F02A,   65
                        }

                        Local3 = RefOf (F02A)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x45)
                    {
                        IndexField (IDXD, DATD, AnyAcc, Lock, Preserve)
                        {
                                ,   2,
                            F02B,   69
                        }

                        Local3 = RefOf (F02B)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x81)
                    {
                        IndexField (IDXE, DATE, AnyAcc, Lock, Preserve)
                        {
                                ,   2,
                            F02C,   129
                        }

                        Local3 = RefOf (F02C)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX0, DAT0, AnyAcc, Lock, Preserve)
                        {
                                ,   2,
                            F02D,   256
                        }

                        Local3 = RefOf (F02D)
                        Local4 = RefOf (G000)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX1, DAT1, AnyAcc, Lock, Preserve)
                        {
                                ,   2,
                            F02E,   1023
                        }

                        Local3 = RefOf (F02E)
                        Local4 = RefOf (G001)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX2, DAT2, AnyAcc, Lock, Preserve)
                        {
                                ,   2,
                            F02F,   1983
                        }

                        Local3 = RefOf (F02F)
                        Local4 = RefOf (G002)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX3, DAT3, AnyAcc, Lock, Preserve)
                        {
                                ,   3,
                            F030,   1
                        }

                        Local3 = RefOf (F030)
                        Local4 = RefOf (G003)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX4, DAT4, AnyAcc, Lock, Preserve)
                        {
                                ,   3,
                            F031,   6
                        }

                        Local3 = RefOf (F031)
                        Local4 = RefOf (G004)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX5, DAT5, AnyAcc, Lock, Preserve)
                        {
                                ,   3,
                            F032,   7
                        }

                        Local3 = RefOf (F032)
                        Local4 = RefOf (G005)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX6, DAT6, AnyAcc, Lock, Preserve)
                        {
                                ,   3,
                            F033,   8
                        }

                        Local3 = RefOf (F033)
                        Local4 = RefOf (G006)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX7, DAT7, AnyAcc, Lock, Preserve)
                        {
                                ,   3,
                            F034,   9
                        }

                        Local3 = RefOf (F034)
                        Local4 = RefOf (G007)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX8, DAT8, AnyAcc, Lock, Preserve)
                        {
                                ,   3,
                            F035,   31
                        }

                        Local3 = RefOf (F035)
                        Local4 = RefOf (G008)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX9, DAT9, AnyAcc, Lock, Preserve)
                        {
                                ,   3,
                            F036,   32
                        }

                        Local3 = RefOf (F036)
                        Local4 = RefOf (G009)
                    }
                    Case (0x21)
                    {
                        IndexField (IDXA, DATA, AnyAcc, Lock, Preserve)
                        {
                                ,   3,
                            F037,   33
                        }

                        Local3 = RefOf (F037)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDXB, DATB, AnyAcc, Lock, Preserve)
                        {
                                ,   3,
                            F038,   63
                        }

                        Local3 = RefOf (F038)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x40)
                    {
                        IndexField (IDXC, DATC, AnyAcc, Lock, Preserve)
                        {
                                ,   3,
                            F039,   64
                        }

                        Local3 = RefOf (F039)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x41)
                    {
                        IndexField (IDXD, DATD, AnyAcc, Lock, Preserve)
                        {
                                ,   3,
                            F03A,   65
                        }

                        Local3 = RefOf (F03A)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x45)
                    {
                        IndexField (IDXE, DATE, AnyAcc, Lock, Preserve)
                        {
                                ,   3,
                            F03B,   69
                        }

                        Local3 = RefOf (F03B)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX0, DAT0, AnyAcc, Lock, Preserve)
                        {
                                ,   3,
                            F03C,   129
                        }

                        Local3 = RefOf (F03C)
                        Local4 = RefOf (G000)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX1, DAT1, AnyAcc, Lock, Preserve)
                        {
                                ,   3,
                            F03D,   256
                        }

                        Local3 = RefOf (F03D)
                        Local4 = RefOf (G001)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX2, DAT2, AnyAcc, Lock, Preserve)
                        {
                                ,   3,
                            F03E,   1023
                        }

                        Local3 = RefOf (F03E)
                        Local4 = RefOf (G002)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX3, DAT3, AnyAcc, Lock, Preserve)
                        {
                                ,   3,
                            F03F,   1983
                        }

                        Local3 = RefOf (F03F)
                        Local4 = RefOf (G003)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX4, DAT4, AnyAcc, Lock, Preserve)
                        {
                                ,   4,
                            F040,   1
                        }

                        Local3 = RefOf (F040)
                        Local4 = RefOf (G004)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX5, DAT5, AnyAcc, Lock, Preserve)
                        {
                                ,   4,
                            F041,   6
                        }

                        Local3 = RefOf (F041)
                        Local4 = RefOf (G005)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX6, DAT6, AnyAcc, Lock, Preserve)
                        {
                                ,   4,
                            F042,   7
                        }

                        Local3 = RefOf (F042)
                        Local4 = RefOf (G006)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX7, DAT7, AnyAcc, Lock, Preserve)
                        {
                                ,   4,
                            F043,   8
                        }

                        Local3 = RefOf (F043)
                        Local4 = RefOf (G007)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX8, DAT8, AnyAcc, Lock, Preserve)
                        {
                                ,   4,
                            F044,   9
                        }

                        Local3 = RefOf (F044)
                        Local4 = RefOf (G008)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX9, DAT9, AnyAcc, Lock, Preserve)
                        {
                                ,   4,
                            F045,   31
                        }

                        Local3 = RefOf (F045)
                        Local4 = RefOf (G009)
                    }
                    Case (0x20)
                    {
                        IndexField (IDXA, DATA, AnyAcc, Lock, Preserve)
                        {
                                ,   4,
                            F046,   32
                        }

                        Local3 = RefOf (F046)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x21)
                    {
                        IndexField (IDXB, DATB, AnyAcc, Lock, Preserve)
                        {
                                ,   4,
                            F047,   33
                        }

                        Local3 = RefOf (F047)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDXC, DATC, AnyAcc, Lock, Preserve)
                        {
                                ,   4,
                            F048,   63
                        }

                        Local3 = RefOf (F048)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x40)
                    {
                        IndexField (IDXD, DATD, AnyAcc, Lock, Preserve)
                        {
                                ,   4,
                            F049,   64
                        }

                        Local3 = RefOf (F049)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x41)
                    {
                        IndexField (IDXE, DATE, AnyAcc, Lock, Preserve)
                        {
                                ,   4,
                            F04A,   65
                        }

                        Local3 = RefOf (F04A)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX0, DAT0, AnyAcc, Lock, Preserve)
                        {
                                ,   4,
                            F04B,   69
                        }

                        Local3 = RefOf (F04B)
                        Local4 = RefOf (G000)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX1, DAT1, AnyAcc, Lock, Preserve)
                        {
                                ,   4,
                            F04C,   129
                        }

                        Local3 = RefOf (F04C)
                        Local4 = RefOf (G001)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX2, DAT2, AnyAcc, Lock, Preserve)
                        {
                                ,   4,
                            F04D,   256
                        }

                        Local3 = RefOf (F04D)
                        Local4 = RefOf (G002)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX3, DAT3, AnyAcc, Lock, Preserve)
                        {
                                ,   4,
                            F04E,   1023
                        }

                        Local3 = RefOf (F04E)
                        Local4 = RefOf (G003)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX4, DAT4, AnyAcc, Lock, Preserve)
                        {
                                ,   4,
                            F04F,   1983
                        }

                        Local3 = RefOf (F04F)
                        Local4 = RefOf (G004)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX5, DAT5, AnyAcc, Lock, Preserve)
                        {
                                ,   5,
                            F050,   1
                        }

                        Local3 = RefOf (F050)
                        Local4 = RefOf (G005)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX6, DAT6, AnyAcc, Lock, Preserve)
                        {
                                ,   5,
                            F051,   6
                        }

                        Local3 = RefOf (F051)
                        Local4 = RefOf (G006)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX7, DAT7, AnyAcc, Lock, Preserve)
                        {
                                ,   5,
                            F052,   7
                        }

                        Local3 = RefOf (F052)
                        Local4 = RefOf (G007)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX8, DAT8, AnyAcc, Lock, Preserve)
                        {
                                ,   5,
                            F053,   8
                        }

                        Local3 = RefOf (F053)
                        Local4 = RefOf (G008)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX9, DAT9, AnyAcc, Lock, Preserve)
                        {
                                ,   5,
                            F054,   9
                        }

                        Local3 = RefOf (F054)
                        Local4 = RefOf (G009)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDXA, DATA, AnyAcc, Lock, Preserve)
                        {
                                ,   5,
                            F055,   31
                        }

                        Local3 = RefOf (F055)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x20)
                    {
                        IndexField (IDXB, DATB, AnyAcc, Lock, Preserve)
                        {
                                ,   5,
                            F056,   32
                        }

                        Local3 = RefOf (F056)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x21)
                    {
                        IndexField (IDXC, DATC, AnyAcc, Lock, Preserve)
                        {
                                ,   5,
                            F057,   33
                        }

                        Local3 = RefOf (F057)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDXD, DATD, AnyAcc, Lock, Preserve)
                        {
                                ,   5,
                            F058,   63
                        }

                        Local3 = RefOf (F058)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x40)
                    {
                        IndexField (IDXE, DATE, AnyAcc, Lock, Preserve)
                        {
                                ,   5,
                            F059,   64
                        }

                        Local3 = RefOf (F059)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX0, DAT0, AnyAcc, Lock, Preserve)
                        {
                                ,   5,
                            F05A,   65
                        }

                        Local3 = RefOf (F05A)
                        Local4 = RefOf (G000)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX1, DAT1, AnyAcc, Lock, Preserve)
                        {
                                ,   5,
                            F05B,   69
                        }

                        Local3 = RefOf (F05B)
                        Local4 = RefOf (G001)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX2, DAT2, AnyAcc, Lock, Preserve)
                        {
                                ,   5,
                            F05C,   129
                        }

                        Local3 = RefOf (F05C)
                        Local4 = RefOf (G002)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX3, DAT3, AnyAcc, Lock, Preserve)
                        {
                                ,   5,
                            F05D,   256
                        }

                        Local3 = RefOf (F05D)
                        Local4 = RefOf (G003)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX4, DAT4, AnyAcc, Lock, Preserve)
                        {
                                ,   5,
                            F05E,   1023
                        }

                        Local3 = RefOf (F05E)
                        Local4 = RefOf (G004)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX5, DAT5, AnyAcc, Lock, Preserve)
                        {
                                ,   5,
                            F05F,   1983
                        }

                        Local3 = RefOf (F05F)
                        Local4 = RefOf (G005)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX6, DAT6, AnyAcc, Lock, Preserve)
                        {
                                ,   6,
                            F060,   1
                        }

                        Local3 = RefOf (F060)
                        Local4 = RefOf (G006)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX7, DAT7, AnyAcc, Lock, Preserve)
                        {
                                ,   6,
                            F061,   6
                        }

                        Local3 = RefOf (F061)
                        Local4 = RefOf (G007)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX8, DAT8, AnyAcc, Lock, Preserve)
                        {
                                ,   6,
                            F062,   7
                        }

                        Local3 = RefOf (F062)
                        Local4 = RefOf (G008)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX9, DAT9, AnyAcc, Lock, Preserve)
                        {
                                ,   6,
                            F063,   8
                        }

                        Local3 = RefOf (F063)
                        Local4 = RefOf (G009)
                    }
                    Case (0x09)
                    {
                        IndexField (IDXA, DATA, AnyAcc, Lock, Preserve)
                        {
                                ,   6,
                            F064,   9
                        }

                        Local3 = RefOf (F064)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDXB, DATB, AnyAcc, Lock, Preserve)
                        {
                                ,   6,
                            F065,   31
                        }

                        Local3 = RefOf (F065)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x20)
                    {
                        IndexField (IDXC, DATC, AnyAcc, Lock, Preserve)
                        {
                                ,   6,
                            F066,   32
                        }

                        Local3 = RefOf (F066)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x21)
                    {
                        IndexField (IDXD, DATD, AnyAcc, Lock, Preserve)
                        {
                                ,   6,
                            F067,   33
                        }

                        Local3 = RefOf (F067)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDXE, DATE, AnyAcc, Lock, Preserve)
                        {
                                ,   6,
                            F068,   63
                        }

                        Local3 = RefOf (F068)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX0, DAT0, AnyAcc, Lock, Preserve)
                        {
                                ,   6,
                            F069,   64
                        }

                        Local3 = RefOf (F069)
                        Local4 = RefOf (G000)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX1, DAT1, AnyAcc, Lock, Preserve)
                        {
                                ,   6,
                            F06A,   65
                        }

                        Local3 = RefOf (F06A)
                        Local4 = RefOf (G001)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX2, DAT2, AnyAcc, Lock, Preserve)
                        {
                                ,   6,
                            F06B,   69
                        }

                        Local3 = RefOf (F06B)
                        Local4 = RefOf (G002)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX3, DAT3, AnyAcc, Lock, Preserve)
                        {
                                ,   6,
                            F06C,   129
                        }

                        Local3 = RefOf (F06C)
                        Local4 = RefOf (G003)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX4, DAT4, AnyAcc, Lock, Preserve)
                        {
                                ,   6,
                            F06D,   256
                        }

                        Local3 = RefOf (F06D)
                        Local4 = RefOf (G004)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX5, DAT5, AnyAcc, Lock, Preserve)
                        {
                                ,   6,
                            F06E,   1023
                        }

                        Local3 = RefOf (F06E)
                        Local4 = RefOf (G005)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX6, DAT6, AnyAcc, Lock, Preserve)
                        {
                                ,   6,
                            F06F,   1983
                        }

                        Local3 = RefOf (F06F)
                        Local4 = RefOf (G006)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX7, DAT7, AnyAcc, Lock, Preserve)
                        {
                                ,   7,
                            F070,   1
                        }

                        Local3 = RefOf (F070)
                        Local4 = RefOf (G007)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX8, DAT8, AnyAcc, Lock, Preserve)
                        {
                                ,   7,
                            F071,   6
                        }

                        Local3 = RefOf (F071)
                        Local4 = RefOf (G008)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX9, DAT9, AnyAcc, Lock, Preserve)
                        {
                                ,   7,
                            F072,   7
                        }

                        Local3 = RefOf (F072)
                        Local4 = RefOf (G009)
                    }
                    Case (0x08)
                    {
                        IndexField (IDXA, DATA, AnyAcc, Lock, Preserve)
                        {
                                ,   7,
                            F073,   8
                        }

                        Local3 = RefOf (F073)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x09)
                    {
                        IndexField (IDXB, DATB, AnyAcc, Lock, Preserve)
                        {
                                ,   7,
                            F074,   9
                        }

                        Local3 = RefOf (F074)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDXC, DATC, AnyAcc, Lock, Preserve)
                        {
                                ,   7,
                            F075,   31
                        }

                        Local3 = RefOf (F075)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x20)
                    {
                        IndexField (IDXD, DATD, AnyAcc, Lock, Preserve)
                        {
                                ,   7,
                            F076,   32
                        }

                        Local3 = RefOf (F076)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x21)
                    {
                        IndexField (IDXE, DATE, AnyAcc, Lock, Preserve)
                        {
                                ,   7,
                            F077,   33
                        }

                        Local3 = RefOf (F077)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX0, DAT0, AnyAcc, Lock, Preserve)
                        {
                                ,   7,
                            F078,   63
                        }

                        Local3 = RefOf (F078)
                        Local4 = RefOf (G000)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX1, DAT1, AnyAcc, Lock, Preserve)
                        {
                                ,   7,
                            F079,   64
                        }

                        Local3 = RefOf (F079)
                        Local4 = RefOf (G001)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX2, DAT2, AnyAcc, Lock, Preserve)
                        {
                                ,   7,
                            F07A,   65
                        }

                        Local3 = RefOf (F07A)
                        Local4 = RefOf (G002)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX3, DAT3, AnyAcc, Lock, Preserve)
                        {
                                ,   7,
                            F07B,   69
                        }

                        Local3 = RefOf (F07B)
                        Local4 = RefOf (G003)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX4, DAT4, AnyAcc, Lock, Preserve)
                        {
                                ,   7,
                            F07C,   129
                        }

                        Local3 = RefOf (F07C)
                        Local4 = RefOf (G004)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX5, DAT5, AnyAcc, Lock, Preserve)
                        {
                                ,   7,
                            F07D,   256
                        }

                        Local3 = RefOf (F07D)
                        Local4 = RefOf (G005)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX6, DAT6, AnyAcc, Lock, Preserve)
                        {
                                ,   7,
                            F07E,   1023
                        }

                        Local3 = RefOf (F07E)
                        Local4 = RefOf (G006)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX7, DAT7, AnyAcc, Lock, Preserve)
                        {
                                ,   7,
                            F07F,   1983
                        }

                        Local3 = RefOf (F07F)
                        Local4 = RefOf (G007)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX8, DAT8, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x01),
                            F080,   1
                        }

                        Local3 = RefOf (F080)
                        Local4 = RefOf (G008)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX9, DAT9, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x01),
                            F081,   6
                        }

                        Local3 = RefOf (F081)
                        Local4 = RefOf (G009)
                    }
                    Case (0x07)
                    {
                        IndexField (IDXA, DATA, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x01),
                            F082,   7
                        }

                        Local3 = RefOf (F082)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x08)
                    {
                        IndexField (IDXB, DATB, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x01),
                            F083,   8
                        }

                        Local3 = RefOf (F083)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x09)
                    {
                        IndexField (IDXC, DATC, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x01),
                            F084,   9
                        }

                        Local3 = RefOf (F084)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDXD, DATD, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x01),
                            F085,   31
                        }

                        Local3 = RefOf (F085)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x20)
                    {
                        IndexField (IDXE, DATE, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x01),
                            F086,   32
                        }

                        Local3 = RefOf (F086)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX0, DAT0, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x01),
                            F087,   33
                        }

                        Local3 = RefOf (F087)
                        Local4 = RefOf (G000)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX1, DAT1, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x01),
                            F088,   63
                        }

                        Local3 = RefOf (F088)
                        Local4 = RefOf (G001)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX2, DAT2, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x01),
                            F089,   64
                        }

                        Local3 = RefOf (F089)
                        Local4 = RefOf (G002)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX3, DAT3, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x01),
                            F08A,   65
                        }

                        Local3 = RefOf (F08A)
                        Local4 = RefOf (G003)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX4, DAT4, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x01),
                            F08B,   69
                        }

                        Local3 = RefOf (F08B)
                        Local4 = RefOf (G004)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX5, DAT5, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x01),
                            F08C,   129
                        }

                        Local3 = RefOf (F08C)
                        Local4 = RefOf (G005)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX6, DAT6, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x01),
                            F08D,   256
                        }

                        Local3 = RefOf (F08D)
                        Local4 = RefOf (G006)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX7, DAT7, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x01),
                            F08E,   1023
                        }

                        Local3 = RefOf (F08E)
                        Local4 = RefOf (G007)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX8, DAT8, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x01),
                            F08F,   1983
                        }

                        Local3 = RefOf (F08F)
                        Local4 = RefOf (G008)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX9, DAT9, AnyAcc, Lock, Preserve)
                        {
                                ,   9,
                            F090,   1
                        }

                        Local3 = RefOf (F090)
                        Local4 = RefOf (G009)
                    }
                    Case (0x06)
                    {
                        IndexField (IDXA, DATA, AnyAcc, Lock, Preserve)
                        {
                                ,   9,
                            F091,   6
                        }

                        Local3 = RefOf (F091)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x07)
                    {
                        IndexField (IDXB, DATB, AnyAcc, Lock, Preserve)
                        {
                                ,   9,
                            F092,   7
                        }

                        Local3 = RefOf (F092)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x08)
                    {
                        IndexField (IDXC, DATC, AnyAcc, Lock, Preserve)
                        {
                                ,   9,
                            F093,   8
                        }

                        Local3 = RefOf (F093)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x09)
                    {
                        IndexField (IDXD, DATD, AnyAcc, Lock, Preserve)
                        {
                                ,   9,
                            F094,   9
                        }

                        Local3 = RefOf (F094)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDXE, DATE, AnyAcc, Lock, Preserve)
                        {
                                ,   9,
                            F095,   31
                        }

                        Local3 = RefOf (F095)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX0, DAT0, AnyAcc, Lock, Preserve)
                        {
                                ,   9,
                            F096,   32
                        }

                        Local3 = RefOf (F096)
                        Local4 = RefOf (G000)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX1, DAT1, AnyAcc, Lock, Preserve)
                        {
                                ,   9,
                            F097,   33
                        }

                        Local3 = RefOf (F097)
                        Local4 = RefOf (G001)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX2, DAT2, AnyAcc, Lock, Preserve)
                        {
                                ,   9,
                            F098,   63
                        }

                        Local3 = RefOf (F098)
                        Local4 = RefOf (G002)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX3, DAT3, AnyAcc, Lock, Preserve)
                        {
                                ,   9,
                            F099,   64
                        }

                        Local3 = RefOf (F099)
                        Local4 = RefOf (G003)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX4, DAT4, AnyAcc, Lock, Preserve)
                        {
                                ,   9,
                            F09A,   65
                        }

                        Local3 = RefOf (F09A)
                        Local4 = RefOf (G004)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX5, DAT5, AnyAcc, Lock, Preserve)
                        {
                                ,   9,
                            F09B,   69
                        }

                        Local3 = RefOf (F09B)
                        Local4 = RefOf (G005)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX6, DAT6, AnyAcc, Lock, Preserve)
                        {
                                ,   9,
                            F09C,   129
                        }

                        Local3 = RefOf (F09C)
                        Local4 = RefOf (G006)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX7, DAT7, AnyAcc, Lock, Preserve)
                        {
                                ,   9,
                            F09D,   256
                        }

                        Local3 = RefOf (F09D)
                        Local4 = RefOf (G007)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX8, DAT8, AnyAcc, Lock, Preserve)
                        {
                                ,   9,
                            F09E,   1023
                        }

                        Local3 = RefOf (F09E)
                        Local4 = RefOf (G008)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX9, DAT9, AnyAcc, Lock, Preserve)
                        {
                                ,   9,
                            F09F,   1983
                        }

                        Local3 = RefOf (F09F)
                        Local4 = RefOf (G009)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDXA, DATA, AnyAcc, Lock, Preserve)
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
                        IndexField (IDXB, DATB, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A1,   6
                        }

                        Local3 = RefOf (F0A1)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x07)
                    {
                        IndexField (IDXC, DATC, AnyAcc, Lock, Preserve)
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
                        IndexField (IDXD, DATD, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A3,   8
                        }

                        Local3 = RefOf (F0A3)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x09)
                    {
                        IndexField (IDXE, DATE, AnyAcc, Lock, Preserve)
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
                        IndexField (IDX0, DAT0, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A5,   31
                        }

                        Local3 = RefOf (F0A5)
                        Local4 = RefOf (G000)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX1, DAT1, AnyAcc, Lock, Preserve)
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
                        IndexField (IDX2, DAT2, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A7,   33
                        }

                        Local3 = RefOf (F0A7)
                        Local4 = RefOf (G002)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX3, DAT3, AnyAcc, Lock, Preserve)
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
                        IndexField (IDX4, DAT4, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0A9,   64
                        }

                        Local3 = RefOf (F0A9)
                        Local4 = RefOf (G004)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX5, DAT5, AnyAcc, Lock, Preserve)
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
                        IndexField (IDX6, DAT6, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0AB,   69
                        }

                        Local3 = RefOf (F0AB)
                        Local4 = RefOf (G006)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX7, DAT7, AnyAcc, Lock, Preserve)
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
                        IndexField (IDX8, DAT8, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0AD,   256
                        }

                        Local3 = RefOf (F0AD)
                        Local4 = RefOf (G008)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDX9, DAT9, AnyAcc, Lock, Preserve)
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
                        IndexField (IDXA, DATA, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x03),
                                ,   7,
                            F0AF,   1983
                        }

                        Local3 = RefOf (F0AF)
                        Local4 = RefOf (G00A)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDXB, DATB, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x04),
                            F0B0,   1
                        }

                        Local3 = RefOf (F0B0)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x06)
                    {
                        IndexField (IDXC, DATC, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x04),
                            F0B1,   6
                        }

                        Local3 = RefOf (F0B1)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x07)
                    {
                        IndexField (IDXD, DATD, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x04),
                            F0B2,   7
                        }

                        Local3 = RefOf (F0B2)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x08)
                    {
                        IndexField (IDXE, DATE, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x04),
                            F0B3,   8
                        }

                        Local3 = RefOf (F0B3)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX0, DAT0, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x04),
                            F0B4,   9
                        }

                        Local3 = RefOf (F0B4)
                        Local4 = RefOf (G000)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX1, DAT1, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x04),
                            F0B5,   31
                        }

                        Local3 = RefOf (F0B5)
                        Local4 = RefOf (G001)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX2, DAT2, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x04),
                            F0B6,   32
                        }

                        Local3 = RefOf (F0B6)
                        Local4 = RefOf (G002)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX3, DAT3, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x04),
                            F0B7,   33
                        }

                        Local3 = RefOf (F0B7)
                        Local4 = RefOf (G003)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX4, DAT4, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x04),
                            F0B8,   63
                        }

                        Local3 = RefOf (F0B8)
                        Local4 = RefOf (G004)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX5, DAT5, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x04),
                            F0B9,   64
                        }

                        Local3 = RefOf (F0B9)
                        Local4 = RefOf (G005)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX6, DAT6, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x04),
                            F0BA,   65
                        }

                        Local3 = RefOf (F0BA)
                        Local4 = RefOf (G006)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX7, DAT7, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x04),
                            F0BB,   69
                        }

                        Local3 = RefOf (F0BB)
                        Local4 = RefOf (G007)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX8, DAT8, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x04),
                            F0BC,   129
                        }

                        Local3 = RefOf (F0BC)
                        Local4 = RefOf (G008)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDX9, DAT9, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x04),
                            F0BD,   256
                        }

                        Local3 = RefOf (F0BD)
                        Local4 = RefOf (G009)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDXA, DATA, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x04),
                            F0BE,   1023
                        }

                        Local3 = RefOf (F0BE)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDXB, DATB, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x04),
                            F0BF,   1983
                        }

                        Local3 = RefOf (F0BF)
                        Local4 = RefOf (G00B)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDXC, DATC, AnyAcc, Lock, Preserve)
                        {
                                ,   33,
                            F0C0,   1
                        }

                        Local3 = RefOf (F0C0)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x06)
                    {
                        IndexField (IDXD, DATD, AnyAcc, Lock, Preserve)
                        {
                                ,   33,
                            F0C1,   6
                        }

                        Local3 = RefOf (F0C1)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x07)
                    {
                        IndexField (IDXE, DATE, AnyAcc, Lock, Preserve)
                        {
                                ,   33,
                            F0C2,   7
                        }

                        Local3 = RefOf (F0C2)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX0, DAT0, AnyAcc, Lock, Preserve)
                        {
                                ,   33,
                            F0C3,   8
                        }

                        Local3 = RefOf (F0C3)
                        Local4 = RefOf (G000)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX1, DAT1, AnyAcc, Lock, Preserve)
                        {
                                ,   33,
                            F0C4,   9
                        }

                        Local3 = RefOf (F0C4)
                        Local4 = RefOf (G001)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX2, DAT2, AnyAcc, Lock, Preserve)
                        {
                                ,   33,
                            F0C5,   31
                        }

                        Local3 = RefOf (F0C5)
                        Local4 = RefOf (G002)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX3, DAT3, AnyAcc, Lock, Preserve)
                        {
                                ,   33,
                            F0C6,   32
                        }

                        Local3 = RefOf (F0C6)
                        Local4 = RefOf (G003)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX4, DAT4, AnyAcc, Lock, Preserve)
                        {
                                ,   33,
                            F0C7,   33
                        }

                        Local3 = RefOf (F0C7)
                        Local4 = RefOf (G004)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX5, DAT5, AnyAcc, Lock, Preserve)
                        {
                                ,   33,
                            F0C8,   63
                        }

                        Local3 = RefOf (F0C8)
                        Local4 = RefOf (G005)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX6, DAT6, AnyAcc, Lock, Preserve)
                        {
                                ,   33,
                            F0C9,   64
                        }

                        Local3 = RefOf (F0C9)
                        Local4 = RefOf (G006)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX7, DAT7, AnyAcc, Lock, Preserve)
                        {
                                ,   33,
                            F0CA,   65
                        }

                        Local3 = RefOf (F0CA)
                        Local4 = RefOf (G007)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX8, DAT8, AnyAcc, Lock, Preserve)
                        {
                                ,   33,
                            F0CB,   69
                        }

                        Local3 = RefOf (F0CB)
                        Local4 = RefOf (G008)
                    }
                    Case (0x81)
                    {
                        IndexField (IDX9, DAT9, AnyAcc, Lock, Preserve)
                        {
                                ,   33,
                            F0CC,   129
                        }

                        Local3 = RefOf (F0CC)
                        Local4 = RefOf (G009)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDXA, DATA, AnyAcc, Lock, Preserve)
                        {
                                ,   33,
                            F0CD,   256
                        }

                        Local3 = RefOf (F0CD)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDXB, DATB, AnyAcc, Lock, Preserve)
                        {
                                ,   33,
                            F0CE,   1023
                        }

                        Local3 = RefOf (F0CE)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDXC, DATC, AnyAcc, Lock, Preserve)
                        {
                                ,   33,
                            F0CF,   1983
                        }

                        Local3 = RefOf (F0CF)
                        Local4 = RefOf (G00C)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDXD, DATD, AnyAcc, Lock, Preserve)
                        {
                                ,   63,
                            F0D0,   1
                        }

                        Local3 = RefOf (F0D0)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x06)
                    {
                        IndexField (IDXE, DATE, AnyAcc, Lock, Preserve)
                        {
                                ,   63,
                            F0D1,   6
                        }

                        Local3 = RefOf (F0D1)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX0, DAT0, AnyAcc, Lock, Preserve)
                        {
                                ,   63,
                            F0D2,   7
                        }

                        Local3 = RefOf (F0D2)
                        Local4 = RefOf (G000)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX1, DAT1, AnyAcc, Lock, Preserve)
                        {
                                ,   63,
                            F0D3,   8
                        }

                        Local3 = RefOf (F0D3)
                        Local4 = RefOf (G001)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX2, DAT2, AnyAcc, Lock, Preserve)
                        {
                                ,   63,
                            F0D4,   9
                        }

                        Local3 = RefOf (F0D4)
                        Local4 = RefOf (G002)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX3, DAT3, AnyAcc, Lock, Preserve)
                        {
                                ,   63,
                            F0D5,   31
                        }

                        Local3 = RefOf (F0D5)
                        Local4 = RefOf (G003)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX4, DAT4, AnyAcc, Lock, Preserve)
                        {
                                ,   63,
                            F0D6,   32
                        }

                        Local3 = RefOf (F0D6)
                        Local4 = RefOf (G004)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX5, DAT5, AnyAcc, Lock, Preserve)
                        {
                                ,   63,
                            F0D7,   33
                        }

                        Local3 = RefOf (F0D7)
                        Local4 = RefOf (G005)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX6, DAT6, AnyAcc, Lock, Preserve)
                        {
                                ,   63,
                            F0D8,   63
                        }

                        Local3 = RefOf (F0D8)
                        Local4 = RefOf (G006)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX7, DAT7, AnyAcc, Lock, Preserve)
                        {
                                ,   63,
                            F0D9,   64
                        }

                        Local3 = RefOf (F0D9)
                        Local4 = RefOf (G007)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX8, DAT8, AnyAcc, Lock, Preserve)
                        {
                                ,   63,
                            F0DA,   65
                        }

                        Local3 = RefOf (F0DA)
                        Local4 = RefOf (G008)
                    }
                    Case (0x45)
                    {
                        IndexField (IDX9, DAT9, AnyAcc, Lock, Preserve)
                        {
                                ,   63,
                            F0DB,   69
                        }

                        Local3 = RefOf (F0DB)
                        Local4 = RefOf (G009)
                    }
                    Case (0x81)
                    {
                        IndexField (IDXA, DATA, AnyAcc, Lock, Preserve)
                        {
                                ,   63,
                            F0DC,   129
                        }

                        Local3 = RefOf (F0DC)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDXB, DATB, AnyAcc, Lock, Preserve)
                        {
                                ,   63,
                            F0DD,   256
                        }

                        Local3 = RefOf (F0DD)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDXC, DATC, AnyAcc, Lock, Preserve)
                        {
                                ,   63,
                            F0DE,   1023
                        }

                        Local3 = RefOf (F0DE)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDXD, DATD, AnyAcc, Lock, Preserve)
                        {
                                ,   63,
                            F0DF,   1983
                        }

                        Local3 = RefOf (F0DF)
                        Local4 = RefOf (G00D)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDXE, DATE, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                            F0E0,   1
                        }

                        Local3 = RefOf (F0E0)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX0, DAT0, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                            F0E1,   6
                        }

                        Local3 = RefOf (F0E1)
                        Local4 = RefOf (G000)
                    }
                    Case (0x07)
                    {
                        IndexField (IDX1, DAT1, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                            F0E2,   7
                        }

                        Local3 = RefOf (F0E2)
                        Local4 = RefOf (G001)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX2, DAT2, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                            F0E3,   8
                        }

                        Local3 = RefOf (F0E3)
                        Local4 = RefOf (G002)
                    }
                    Case (0x09)
                    {
                        IndexField (IDX3, DAT3, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                            F0E4,   9
                        }

                        Local3 = RefOf (F0E4)
                        Local4 = RefOf (G003)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX4, DAT4, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                            F0E5,   31
                        }

                        Local3 = RefOf (F0E5)
                        Local4 = RefOf (G004)
                    }
                    Case (0x20)
                    {
                        IndexField (IDX5, DAT5, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                            F0E6,   32
                        }

                        Local3 = RefOf (F0E6)
                        Local4 = RefOf (G005)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX6, DAT6, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                            F0E7,   33
                        }

                        Local3 = RefOf (F0E7)
                        Local4 = RefOf (G006)
                    }
                    Case (0x3F)
                    {
                        IndexField (IDX7, DAT7, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                            F0E8,   63
                        }

                        Local3 = RefOf (F0E8)
                        Local4 = RefOf (G007)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX8, DAT8, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                            F0E9,   64
                        }

                        Local3 = RefOf (F0E9)
                        Local4 = RefOf (G008)
                    }
                    Case (0x41)
                    {
                        IndexField (IDX9, DAT9, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                            F0EA,   65
                        }

                        Local3 = RefOf (F0EA)
                        Local4 = RefOf (G009)
                    }
                    Case (0x45)
                    {
                        IndexField (IDXA, DATA, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                            F0EB,   69
                        }

                        Local3 = RefOf (F0EB)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x81)
                    {
                        IndexField (IDXB, DATB, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                            F0EC,   129
                        }

                        Local3 = RefOf (F0EC)
                        Local4 = RefOf (G00B)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDXC, DATC, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                            F0ED,   256
                        }

                        Local3 = RefOf (F0ED)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x03FF)
                    {
                        IndexField (IDXD, DATD, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                            F0EE,   1023
                        }

                        Local3 = RefOf (F0EE)
                        Local4 = RefOf (G00D)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDXE, DATE, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                            F0EF,   1983
                        }

                        Local3 = RefOf (F0EF)
                        Local4 = RefOf (G00E)
                    }
                    Default
                    {
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
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
                        IndexField (IDX0, DAT0, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F0,   1
                        }

                        Local3 = RefOf (F0F0)
                        Local4 = RefOf (G000)
                    }
                    Case (0x06)
                    {
                        IndexField (IDX1, DAT1, AnyAcc, Lock, Preserve)
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
                        IndexField (IDX2, DAT2, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F2,   7
                        }

                        Local3 = RefOf (F0F2)
                        Local4 = RefOf (G002)
                    }
                    Case (0x08)
                    {
                        IndexField (IDX3, DAT3, AnyAcc, Lock, Preserve)
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
                        IndexField (IDX4, DAT4, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F4,   9
                        }

                        Local3 = RefOf (F0F4)
                        Local4 = RefOf (G004)
                    }
                    Case (0x1F)
                    {
                        IndexField (IDX5, DAT5, AnyAcc, Lock, Preserve)
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
                        IndexField (IDX6, DAT6, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F6,   32
                        }

                        Local3 = RefOf (F0F6)
                        Local4 = RefOf (G006)
                    }
                    Case (0x21)
                    {
                        IndexField (IDX7, DAT7, AnyAcc, Lock, Preserve)
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
                        IndexField (IDX8, DAT8, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0F8,   63
                        }

                        Local3 = RefOf (F0F8)
                        Local4 = RefOf (G008)
                    }
                    Case (0x40)
                    {
                        IndexField (IDX9, DAT9, AnyAcc, Lock, Preserve)
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
                        IndexField (IDXA, DATA, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0FA,   65
                        }

                        Local3 = RefOf (F0FA)
                        Local4 = RefOf (G00A)
                    }
                    Case (0x45)
                    {
                        IndexField (IDXB, DATB, AnyAcc, Lock, Preserve)
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
                        IndexField (IDXC, DATC, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0FC,   129
                        }

                        Local3 = RefOf (F0FC)
                        Local4 = RefOf (G00C)
                    }
                    Case (0x0100)
                    {
                        IndexField (IDXD, DATD, AnyAcc, Lock, Preserve)
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
                        IndexField (IDXE, DATE, AnyAcc, Lock, Preserve)
                        {
                            Offset (0x08),
                                ,   1,
                            F0FE,   1023
                        }

                        Local3 = RefOf (F0FE)
                        Local4 = RefOf (G00E)
                    }
                    Case (0x07BF)
                    {
                        IndexField (IDX0, DAT0, AnyAcc, Lock, Preserve)
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
                        ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
                        Return (Zero)
                    }

                }
            }
            Default
            {
                ERR (Arg0, Z144, __LINE__, 0x00, 0x00, Arg2, Arg3)
                Return (Zero)
            }

        }

        M72D (Arg0, Local3, Arg2, Arg3, Arg4, Arg5, Local4)
    }

    /* Run-method */

    Method (IFC0, 0, Serialized)
    {
        SRMT ("m770")
        M770 (__METHOD__)
        /* Access to 1-bit IndexFields, ByteAcc */

        SRMT ("m771")
        M771 (__METHOD__)
        /* Access to 1-bit IndexFields, WordAcc */

        SRMT ("m772")
        M772 (__METHOD__)
        /* Access to 1-bit IndexFields, DWordAcc */

        SRMT ("m773")
        M773 (__METHOD__)
        /* Access to 1-bit IndexFields, QWordAcc */

        SRMT ("m774")
        If (Y215)
        {
            M774 (__METHOD__)
        }
        Else
        {
            BLCK ()
        }

        /* Splitting of IndexFields */

        SRMT ("m775")
        M775 (__METHOD__)
        /* Check IndexField access: ByteAcc, NoLock, Preserve */

        SRMT ("m776")
        If (Y224)
        {
            M776 (__METHOD__)
        }
        Else
        {
            BLCK ()
        }

        /* Check IndexField access: WordAcc, NoLock, WriteAsOnes */

        SRMT ("m777")
        If (Y224)
        {
            M777 (__METHOD__)
        }
        Else
        {
            BLCK ()
        }

        /* Check IndexField access: DWordAcc, NoLock, WriteAsZeros */

        SRMT ("m778")
        If (Y224)
        {
            M778 (__METHOD__)
        }
        Else
        {
            BLCK ()
        }

        /* Check IndexField access: QWordAcc, NoLock, Preserve */

        SRMT ("m779")
        If (Y224)
        {
            M779 (__METHOD__)
        }
        Else
        {
            BLCK ()
        }

        /* Check IndexField access: AnyAcc, Lock, Preserve */

        SRMT ("m77a")
        If (Y224)
        {
            M77A (__METHOD__)
        }
        Else
        {
            BLCK ()
        }
    }
