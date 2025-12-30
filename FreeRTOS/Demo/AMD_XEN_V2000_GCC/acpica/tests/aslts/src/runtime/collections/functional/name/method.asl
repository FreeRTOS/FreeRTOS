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
     * Miscellaneous named object creation
     */
    Name (Z133, 0x85)
    /*
     * This sub-test is intended to comprehensively verify
     * the Control Method declaration syntax implementation.
     *
     * Declare the Control Method Objects of different signature,
     * check that properly specified or default arguments values
     * provide required functionality.
     *
     *    17.5.75    Method (Declare Control Method)
     *    Syntax
     * Method (MethodName, NumArgs, SerializeRule, SyncLevel,
     *         ReturnType, ParameterTypes) {TermList}
     *
     *    Validated Assertions:
     *
     * - Control Method declaration creates an Object in the ACPI
     *   namespace which can be referred by the specified MethodName
     *   either to initiate its invocation or to obtain its AML Object
     *   type. Also MethodName can be used to save a copy of the Object
     *   or a reference to it in another AML Object.
     *
     * - ASL compiler should allow only a Namestring data type in the
     *   MethodName position.
     *
     * - ASL compiler should allow only an Type3Opcode (integer) constant
     *   expression of the value in the range 0-7 in the NumArgs position.
     *   NumArgs is optional argument.
     *
     * - ASL compiler should allow only the keywords 'NotSerialized'
     *   and 'Serialized' in the SerializeRule position. SerializeRule
     *   is optional argument.
     *
     * - ASL compiler should allow only an Type3Opcode (integer) constant
     *   expression of the value in the range 0-15 in the SyncLevel position.
     *   SyncLevel is optional argument. If no SyncLevel is specified, SyncLevel
     *   0 is assumed.
     *
     * - ASL compiler should allow only an ObjectTypeKeyword or
     *   a comma-separated ObjectTypeKeywords enclosed with curly
     *   brackets (OTK package) in the ReturnType position. ReturnType
     *   is optional argument. If no ReturnType is specified, ReturnType
     *   UnknownObj is assumed.
     *   ObjectTypeKeyword := UnknownObj | IntObj | StrObj | BuffObj |
     *                        PkgObj | FieldUnitObj | DeviceObj | EventObj |
     *                        MethodObj | MutexObj | OpRegionObj | PowerResObj |
     *                        ThermalZoneObj | BuffFieldObj | DDBHandleObj
     *
     * - Every ASL data type should have a respective unique ObjectType Keyword.
     *
     * - ASL compiler should report an error when an actual Object specified
     *   to be returned is of inappropriate type.
     *
     * - ASL compiler should report an error when there is at least one
     *   control path in the method that returns no any actual Object.
     *
     * - ASL compiler should report an error when some different from
     *   UnknownObj ObjectType Keyword specified in the ReturnType position
     *   but no any actual Object specified to be returned.
     *
     * - ASL compiler should allow only an OTK package or a package
     *   containing OTK packages along with ObjectTypeKeywords in the
     *   ParameterTypes position.
     *
     * - ASL compiler should report an error when ParameterTypes is specified
     *   and the number of members in the ParameterTypes package don't match
     *   NumArgs.
     *
     * - ASL compiler should report an error when an actual Object
     *   specified to be a respective argument of the Method is of
     *   inappropriate type.
     *
     * - System software should execute a control method by referencing
     *   the objects in the Method body in order.
     *
     * - Method opens a name scope. All namespace references that occur
     *   during the method execution are relative to the Method package
     *   location.
     *
     * - If the  method is declared as Serialized, it can be called
     *   recursively, maybe, through another auxiliary method.
     *
     * - One method declared as Serialized can call another
     *   one declared as Serialized too when the SyncLevel of
     *   the second method is not less than that of the first.
     *
     * - The method declared as Serialized can acquire an Mutex
     *   when the SyncLevel of the Mutex is not less than that of
     *   the method.
     *
     * - If some method acquired an Mutex it can call another one
     *   declared as Serialized when the SyncLevel of the called
     *   method is not less than that of the Mutex.
     *
     * - All Acquire terms must refer to a synchronization object
     *   with an equal or greater SyncLevel to the current Method level.
     *
     * - The method declared as Serialized can release an Mutex
     *   when the SyncLevel of the Mutex is not less than that of
     *   the method.
     *
     * - All namespace objects created by a method should be destroyed
     *   when method execution exits.
     *
     */
    /* Flags of types of Computational Data Objects */
    /* (Fields and Integer, String, Buffer) */
    Name (BZ00, Buffer (0x12)
    {
        /* 0000 */  0x00, 0x01, 0x01, 0x01, 0x00, 0x01, 0x00, 0x00,  // ........
        /* 0008 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00,  // ........
        /* 0010 */  0x00, 0x00                                       // ..
    })
    /* Check Result of operation on equal to Benchmark value */
    /* m680(<method name>, */
    /*	<internal type of error if it occurs>, */
    /*	<Result>, */
    /*	<Benchmark value>) */
    Method (M205, 4, NotSerialized)
    {
        Local0 = ObjectType (Arg2)
        Local1 = ObjectType (Arg3)
        If ((Local0 != Local1))
        {
            ERR (Concatenate (Arg0, "-OType"), Z133, __LINE__, 0x00, 0x00, Local0, Local1)
            Return (0x01)
        }
        ElseIf (DerefOf (BZ00 [Local0]))
        {
            If (!Y119)
            {
                If ((Local1 == 0x01))
                {
                    /* Cast 64-bit to 32-bit */

                    If (!F64)
                    {
                        Arg3 = Arg3
                    }
                }
            }

            If ((Arg2 != Arg3))
            {
                ERR (Arg0, Z133, __LINE__, 0x00, 0x00, Arg2, Arg3)
                Return (0x01)
            }
        }
        ElseIf ((Local0 == 0x08))
        {
            /* Methods, compare the results of them */

            Local2 = M209 (Concatenate (Arg0, "-Method"), Arg1, Arg2, Arg3)
            Return (Local2)
        }
        ElseIf ((Local0 == 0x04))
        {
            /* Packages */

            Local2 = M20A (Concatenate (Arg0, "-Pack"), Arg1, Arg2, Arg3)
            Return (Local2)
        }

        Return (0x00)
    }

    /* Check that Results of the Methods are equal each other */

    Method (M209, 4, Serialized)
    {
        Name (MMM0, 0x00)
        Name (MMM1, 0x00)
        CopyObject (Arg2, MMM0) /* \M209.MMM0 */
        CopyObject (Arg3, MMM1) /* \M209.MMM1 */
        Return (M205 (Arg0, Arg1, MMM0, MMM1))
    }

    /* Check that two Packages are equal each other */

    Method (M20A, 4, NotSerialized)
    {
        Local0 = SizeOf (Arg3)
        If ((SizeOf (Arg2) != Local0))
        {
            ERR (Concatenate (Arg0, "-Size"), Z133, __LINE__, 0x00, 0x00, SizeOf (Arg2), Local0)
            Return (0x01)
        }

        While (Local0)
        {
            Local0--
            Local1 = ObjectType (DerefOf (Arg2 [Local0]))
            Local2 = ObjectType (DerefOf (Arg3 [Local0]))
            If ((Local1 != Local2))
            {
                /* ObjectType is corrupted */

                ERR (Concatenate (Arg0, "-OType"), Z133, __LINE__, 0x00, 0x00, Local1, Local2)
                Return (0x01)
            }
            ElseIf (DerefOf (BZ00 [Local1]))
            {
                /* the computational data type */

                If ((DerefOf (Arg2 [Local0]) != DerefOf (Arg3 [Local0]
                    )))
                {
                    /* The value is corrupted */

                    ERR (Arg0, Z133, __LINE__, 0x00, 0x00, DerefOf (Arg2 [Local0]), DerefOf (
                        Arg3 [Local0]))
                    Return (0x01)
                }
            }
        }

        Return (0x00)
    }

    Scope (\_SB)
    {
        Method (M206, 0, NotSerialized)
        {
        }
    }

    Method (M207, 0, Serialized)
    {
        Method (M240, 0, NotSerialized)
        {
            Method (MM00, 0, NotSerialized)
            {
                Return ("\\m207.m240.mm00")
            }

            Method (\_SB.M206.MM00, 0, NotSerialized)
            {
                Return ("\\_SB.m206.mm00")
            }

            M205 (__METHOD__, 0x01, ObjectType (MM00), 0x08)
            M205 (__METHOD__, 0x02, MM00 (), "\\m207.m240.mm00")
            M205 (__METHOD__, 0x03, ObjectType (\M207.M240.MM00), 0x08)
            M205 (__METHOD__, 0x04, \M207.M240.MM00 (), "\\m207.m240.mm00")
            M205 (__METHOD__, 0x05, ObjectType (^M240.MM00), 0x08)
            M205 (__METHOD__, 0x06, ^M240.MM00 (), "\\m207.m240.mm00")
            M205 (__METHOD__, 0x07, ObjectType (\_SB.M206.MM00), 0x08)
            M205 (__METHOD__, 0x08, \_SB.M206.MM00 (), "\\_SB.m206.mm00")
        }

        Method (M241, 0, NotSerialized)
        {
            Method (MM10, 0, NotSerialized)
            {
                Return ("\\m207.m241.mm10")
            }

            Method (MM20, 0, NotSerialized)
            {
                Return ("\\m207.m241.mm20")
            }

            Method (MM30, 0, NotSerialized)
            {
                Return ("\\m207.m241.mm30")
            }

            Method (MM40, 0, NotSerialized)
            {
                Return ("\\m207.m241.mm40")
            }

            Method (MM50, 0, NotSerialized)
            {
                Return ("\\m207.m241.mm50")
            }

            Method (MM60, 0, NotSerialized)
            {
                Return ("\\m207.m241.mm60")
            }

            Method (MM00, 0, NotSerialized)
            {
                Return ("\\m207.m241.mm00")
            }

            Method (MM01, 1, NotSerialized)
            {
                Return ("\\m207.m241.mm01")
            }

            Method (MM02, 2, NotSerialized)
            {
                Return ("\\m207.m241.mm02")
            }

            Method (MM03, 3, NotSerialized)
            {
                Return ("\\m207.m241.mm03")
            }

            Method (MM04, 4, NotSerialized)
            {
                Return ("\\m207.m241.mm04")
            }

            Method (MM05, 5, NotSerialized)
            {
                Return ("\\m207.m241.mm05")
            }

            Method (MM06, 6, NotSerialized)
            {
                Return ("\\m207.m241.mm06")
            }

            Method (MM07, 7, NotSerialized)
            {
                Return ("\\m207.m241.mm07")
            }

            /* Numargs as Type3Opcode (integer) constant expression */
            /* Invalid checksum warning */
            /*		Method(mm09, Add(6, 1)) {Return ("\\m207.m241.mm09")} */
            M205 (__METHOD__, 0x09, ObjectType (MM10), 0x08)
            M205 (__METHOD__, 0x0A, MM10 (), "\\m207.m241.mm10")
            M205 (__METHOD__, 0x0B, ObjectType (MM20), 0x08)
            M205 (__METHOD__, 0x0C, MM20 (), "\\m207.m241.mm20")
            M205 (__METHOD__, 0x0D, ObjectType (MM30), 0x08)
            M205 (__METHOD__, 0x0E, MM30 (), "\\m207.m241.mm30")
            M205 (__METHOD__, 0x0F, ObjectType (MM40), 0x08)
            M205 (__METHOD__, 0x10, MM40 (), "\\m207.m241.mm40")
            M205 (__METHOD__, 0x11, ObjectType (MM50), 0x08)
            M205 (__METHOD__, 0x12, MM50 (), "\\m207.m241.mm50")
            M205 (__METHOD__, 0x13, ObjectType (MM60), 0x08)
            If (Y157)
            {
                M205 (__METHOD__, 0x14, MM60 (), "\\m207.m241.mm60")
            }

            M205 (__METHOD__, 0x15, ObjectType (MM00), 0x08)
            M205 (__METHOD__, 0x16, MM00 (), "\\m207.m241.mm00")
            M205 (__METHOD__, 0x17, ObjectType (MM01), 0x08)
            M205 (__METHOD__, 0x18, MM01 (0x00), "\\m207.m241.mm01")
            M205 (__METHOD__, 0x19, ObjectType (MM02), 0x08)
            M205 (__METHOD__, 0x1A, MM02 (0x00, 0x01), "\\m207.m241.mm02")
            M205 (__METHOD__, 0x1B, ObjectType (MM03), 0x08)
            M205 (__METHOD__, 0x1C, MM03 (0x00, 0x01, 0x02), "\\m207.m241.mm03")
            M205 (__METHOD__, 0x1D, ObjectType (MM04), 0x08)
            M205 (__METHOD__, 0x1E, MM04 (0x00, 0x01, 0x02, 0x03), "\\m207.m241.mm04")
            M205 (__METHOD__, 0x1F, ObjectType (MM05), 0x08)
            M205 (__METHOD__, 0x20, MM05 (0x00, 0x01, 0x02, 0x03, 0x04), "\\m207.m241.mm05")
            M205 (__METHOD__, 0x21, ObjectType (MM06), 0x08)
            M205 (__METHOD__, 0x22, MM06 (0x00, 0x01, 0x02, 0x03, 0x04, 0x05), "\\m207.m241.mm06")
            M205 (__METHOD__, 0x23, ObjectType (MM07), 0x08)
            M205 (__METHOD__, 0x24, MM07 (0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06), "\\m207.m241.mm07")
                /* Invalid checksum warning */
        /*		m205(ts, 37, ObjectType(mm09), 8) */
        /* Too many arguments ^  (MM09 requires 0) */
        /*		m205(ts, 38, mm09(0, 1, 2, 3, 4, 5, 6), "\\m207.m241.mm09") */
        }

        Method (M242, 0, NotSerialized)
        {
            Method (MM10, 0, NotSerialized)
            {
                Return ("\\m207.m242.mm10")
            }

            Method (MM20, 0, Serialized)
            {
                Return ("\\m207.m242.mm20")
            }

            Method (MM30, 0, NotSerialized)
            {
                Return ("\\m207.m242.mm30")
            }

            Method (MM40, 0, Serialized)
            {
                Return ("\\m207.m242.mm40")
            }

            Method (MM50, 0, NotSerialized)
            {
                Return ("\\m207.m242.mm50")
            }

            Method (MM60, 0, Serialized)
            {
                Return ("\\m207.m242.mm60")
            }

            Method (MM00, 0, Serialized)
            {
                Return ("\\m207.m242.mm00")
            }

            Method (MM01, 1, Serialized, 1)
            {
                Return ("\\m207.m242.mm01")
            }

            Method (MM02, 2, Serialized, 2)
            {
                Return ("\\m207.m242.mm02")
            }

            Method (MM03, 3, Serialized, 3)
            {
                Return ("\\m207.m242.mm03")
            }

            Method (MM04, 4, Serialized, 4)
            {
                Return ("\\m207.m242.mm04")
            }

            Method (MM05, 5, Serialized, 5)
            {
                Return ("\\m207.m242.mm05")
            }

            Method (MM06, 6, Serialized, 6)
            {
                Return ("\\m207.m242.mm06")
            }

            Method (MM07, 7, Serialized, 7)
            {
                Return ("\\m207.m242.mm07")
            }

            Method (MM08, 0, Serialized, 8)
            {
                Return ("\\m207.m242.mm08")
            }

            Method (MM09, 1, Serialized, 9)
            {
                Return ("\\m207.m242.mm09")
            }

            Method (MM0A, 2, Serialized, 10)
            {
                Return ("\\m207.m242.mm0a")
            }

            Method (MM0B, 3, Serialized, 11)
            {
                Return ("\\m207.m242.mm0b")
            }

            Method (MM0C, 4, Serialized, 12)
            {
                Return ("\\m207.m242.mm0c")
            }

            Method (MM0D, 5, Serialized, 13)
            {
                Return ("\\m207.m242.mm0d")
            }

            Method (MM0E, 6, Serialized, 14)
            {
                Return ("\\m207.m242.mm0e")
            }

            Method (MM0F, 7, Serialized, 15)
            {
                Return ("\\m207.m242.mm0f")
            }

            /* Numargs as Type3Opcode (integer) constant expression */
            /* Invalid checksum warning */
            /*		Method(mm70, Add(6, 1), NotSerialized) {Return ("\\m207.m242.mm70")} */
            /* SyncLevel as Type3Opcode (integer) constant expression */
            Method (MM80, 7, Serialized, 15)
            {
                Return ("\\m207.m242.mm80")
            }

            /* Both Numargs and SyncLevel as Type3Opcode (integer) constant expressions */
            /* Invalid checksum warning */
            /*		Method(mm90, Add(6, 1), Serialized, Add(14, 1)) {Return ("\\m207.m242.mm90")} */
            M205 (__METHOD__, 0x27, ObjectType (MM10), 0x08)
            M205 (__METHOD__, 0x28, MM10 (), "\\m207.m242.mm10")
            M205 (__METHOD__, 0x29, ObjectType (MM10), 0x08)
            M205 (__METHOD__, 0x2A, MM20 (), "\\m207.m242.mm20")
            M205 (__METHOD__, 0x2B, ObjectType (MM10), 0x08)
            M205 (__METHOD__, 0x2C, MM30 (), "\\m207.m242.mm30")
            M205 (__METHOD__, 0x2D, ObjectType (MM10), 0x08)
            M205 (__METHOD__, 0x2E, MM40 (), "\\m207.m242.mm40")
            M205 (__METHOD__, 0x2F, ObjectType (MM10), 0x08)
            If (Y157)
            {
                M205 (__METHOD__, 0x30, MM50 (), "\\m207.m242.mm50")
            }

            M205 (__METHOD__, 0x31, ObjectType (MM10), 0x08)
            If (Y157)
            {
                M205 (__METHOD__, 0x32, MM60 (), "\\m207.m242.mm60")
            }

            M205 (__METHOD__, 0x33, ObjectType (MM00), 0x08)
            M205 (__METHOD__, 0x34, MM00 (), "\\m207.m242.mm00")
            M205 (__METHOD__, 0x35, ObjectType (MM01), 0x08)
            M205 (__METHOD__, 0x36, MM01 (0x00), "\\m207.m242.mm01")
            M205 (__METHOD__, 0x37, ObjectType (MM02), 0x08)
            M205 (__METHOD__, 0x38, MM02 (0x00, 0x01), "\\m207.m242.mm02")
            M205 (__METHOD__, 0x39, ObjectType (MM03), 0x08)
            M205 (__METHOD__, 0x3A, MM03 (0x00, 0x01, 0x02), "\\m207.m242.mm03")
            M205 (__METHOD__, 0x3B, ObjectType (MM04), 0x08)
            M205 (__METHOD__, 0x3C, MM04 (0x00, 0x01, 0x02, 0x03), "\\m207.m242.mm04")
            M205 (__METHOD__, 0x3D, ObjectType (MM05), 0x08)
            M205 (__METHOD__, 0x3E, MM05 (0x00, 0x01, 0x02, 0x03, 0x04), "\\m207.m242.mm05")
            M205 (__METHOD__, 0x3F, ObjectType (MM06), 0x08)
            M205 (__METHOD__, 0x40, MM06 (0x00, 0x01, 0x02, 0x03, 0x04, 0x05), "\\m207.m242.mm06")
            M205 (__METHOD__, 0x41, ObjectType (MM07), 0x08)
            M205 (__METHOD__, 0x42, MM07 (0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06), "\\m207.m242.mm07")
            M205 (__METHOD__, 0x43, ObjectType (MM00), 0x08)
            M205 (__METHOD__, 0x44, MM08 (), "\\m207.m242.mm08")
            M205 (__METHOD__, 0x45, ObjectType (MM01), 0x08)
            M205 (__METHOD__, 0x46, MM09 (0x00), "\\m207.m242.mm09")
            M205 (__METHOD__, 0x47, ObjectType (MM02), 0x08)
            M205 (__METHOD__, 0x48, MM0A (0x00, 0x01), "\\m207.m242.mm0a")
            M205 (__METHOD__, 0x49, ObjectType (MM03), 0x08)
            M205 (__METHOD__, 0x4A, MM0B (0x00, 0x01, 0x02), "\\m207.m242.mm0b")
            M205 (__METHOD__, 0x4B, ObjectType (MM04), 0x08)
            M205 (__METHOD__, 0x4C, MM0C (0x00, 0x01, 0x02, 0x03), "\\m207.m242.mm0c")
            M205 (__METHOD__, 0x4D, ObjectType (MM05), 0x08)
            M205 (__METHOD__, 0x4E, MM0D (0x00, 0x01, 0x02, 0x03, 0x04), "\\m207.m242.mm0d")
            M205 (__METHOD__, 0x4F, ObjectType (MM06), 0x08)
            M205 (__METHOD__, 0x50, MM0E (0x00, 0x01, 0x02, 0x03, 0x04, 0x05), "\\m207.m242.mm0e")
            M205 (__METHOD__, 0x51, ObjectType (MM07), 0x08)
            M205 (__METHOD__, 0x52, MM0F (0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06), "\\m207.m242.mm0f")
            /* Invalid checksum warning */
            /*		m205(ts, 83, ObjectType(mm70), 8) */
            /*	Too many arguments ^  (MM70 requires 0) */
            /*		m205(ts, 84, mm70(0, 1, 2, 3, 4, 5, 6), "\\m207.m242.mm70") */
            M205 (__METHOD__, 0x55, ObjectType (MM80), 0x08)
                /* Outstanding allocations */
        /*		m205(ts, 86, mm80(0, 1, 2, 3, 4, 5, 6), "\\m207.m242.mm80") */
        /* Invalid checksum warning */
        /*		m205(ts, 87, ObjectType(mm90), 8) */
        /*	Too many arguments ^  (MM90 requires 0) */
        /*		m205(ts, 88, mm90(0, 1, 2, 3, 4, 5, 6), "\\m207.m242.mm90") */
        }

        /* Integer */

        Name (INT0, 0xFEDCBA9876543210)
        /* String */

        Name (STR0, "source string")
        /* Buffer */

        Name (BUF0, Buffer (0x09)
        {
            /* 0000 */  0x09, 0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02,  // ........
            /* 0008 */  0x01                                             // .
        })
        /* Initializer of Fields */

        Name (BUF2, Buffer (0x09)
        {
            /* 0000 */  0x95, 0x85, 0x75, 0x65, 0x55, 0x45, 0x35, 0x25,  // ..ueUE5%
            /* 0008 */  0x15                                             // .
        })
        /* Base of Buffer Fields */

        Name (BUFZ, Buffer (0x30){})
        /* Package */

        Name (PAC0, Package (0x03)
        {
            0xFEDCBA987654321F,
            "test package",
            Buffer (0x09)
            {
                /* 0000 */  0x13, 0x12, 0x11, 0x10, 0x0F, 0x0E, 0x0D, 0x0C,  // ........
                /* 0008 */  0x0B                                             // .
            }
        })
        /* Operation Region */

        OperationRegion (OPR0, SystemMemory, 0x00, 0x30)
        /* Field Unit */

        Field (OPR0, ByteAcc, NoLock, Preserve)
        {
            FLU0,   69,
            FLU2,   64,
            FLU4,   32
        }

        /* Device */

        Device (DEV0)
        {
            Name (S000, "DEV0")
        }

        /* Event */

        Event (EVE0)
        /* Method */

        Method (MMM0, 0, NotSerialized)
        {
            Return ("ff0X")
        }

        /* Mutex */

        Mutex (MTX0, 0x00)
        /* Power Resource */

        PowerResource (PWR0, 0x00, 0x0000)
        {
            Name (S000, "PWR0")
        }

        /* Processor */

        Processor (CPU0, 0x00, 0xFFFFFFFF, 0x00)
        {
            Name (S000, "CPU0")
        }

        /* Thermal Zone */

        ThermalZone (TZN0)
        {
            Name (S000, "TZN0")
        }

        /* Buffer Field */

        CreateField (BUFZ, 0x00, 0x45, BFL0)
        CreateField (BUFZ, 0x50, 0x40, BFL2)
        CreateField (BUFZ, 0xA0, 0x20, BFL4)
        /* DDBHandle */

        Name (DDB0, Ones)
        /* Reference */

        Name (ORF0, "ORF0")
        Name (REF0, Package (0x01){})
        Method (M243, 0, NotSerialized)
        {
            Method (MM00, 1, NotSerialized)
            {
                Arg0 = (DerefOf (Arg0) + 0x01)
            }

            Method (MM01, 0, NotSerialized)
            {
                Return (INT0) /* \M207.INT0 */
            }

            Method (MM11, 0, NotSerialized)
            {
                Return (INT0) /* \M207.INT0 */
            }

            Method (MM02, 0, NotSerialized)
            {
                Return (STR0) /* \M207.STR0 */
            }

            Method (MM03, 0, NotSerialized)
            {
                Return (BUF0) /* \M207.BUF0 */
            }

            Method (MM04, 0, NotSerialized)
            {
                Return (PAC0) /* \M207.PAC0 */
            }

            Method (MM05, 0, NotSerialized)
            {
                Return (FLU0) /* \M207.FLU0 */
            }

            Method (MM06, 0, NotSerialized)
            {
                Return (DEV0) /* \M207.DEV0 */
            }

            Method (MM07, 0, NotSerialized)
            {
                Return (EVE0) /* \M207.EVE0 */
            }

            Method (MM08, 0, NotSerialized)
            {
                CopyObject (MMM0 (), Local0)
                Return (Local0)
            }

            Method (MM09, 0, NotSerialized)
            {
                Return (MTX0) /* \M207.MTX0 */
            }

            Method (MM0A, 0, NotSerialized)
            {
                Return (OPR0) /* \M207.OPR0 */
            }

            Method (MM0B, 0, NotSerialized)
            {
                Return (PWR0) /* \M207.PWR0 */
            }

            Method (MM0C, 0, NotSerialized)
            {
                Return (CPU0) /* \M207.CPU0 */
            }

            Method (MM0D, 0, NotSerialized)
            {
                Return (TZN0) /* \M207.TZN0 */
            }

            Method (MM0E, 0, NotSerialized)
            {
                Return (BFL0) /* \M207.BFL0 */
            }

            Method (MM0F, 0, NotSerialized)
            {
                Return (DDB0) /* \M207.DDB0 */
            }

            /* Formal declaration */
            /* Method(mm0g, , , , DebugObj) {Return (Debug)} */
            Method (MM0H, 0, NotSerialized)
            {
                Return (RefOf (ORF0))
            }

            Local0 = 0xFEDCBA9876543210
            M205 (__METHOD__, 0x59, ObjectType (MM00), 0x08)
            MM00 (RefOf (Local0))
            M205 (__METHOD__, 0x5A, Local0, 0xFEDCBA9876543211)
            M205 (__METHOD__, 0x5B, ObjectType (MM01), 0x08)
            M205 (__METHOD__, 0x5C, MM01 (), INT0)
            M205 (__METHOD__, 0x5D, ObjectType (MM02), 0x08)
            M205 (__METHOD__, 0x5E, MM02 (), STR0)
            M205 (__METHOD__, 0x5F, ObjectType (MM03), 0x08)
            M205 (__METHOD__, 0x60, MM03 (), BUF0)
            M205 (__METHOD__, 0x61, ObjectType (MM04), 0x08)
            M205 (__METHOD__, 0x62, MM04 (), PAC0)
            M205 (__METHOD__, 0x63, ObjectType (MM05), 0x08)
            M205 (__METHOD__, 0x64, MM05 (), FLU0)
            M205 (__METHOD__, 0x65, ObjectType (MM06), 0x08)
            M205 (__METHOD__, 0x66, MM06 (), DEV0)
            M205 (__METHOD__, 0x67, ObjectType (MM07), 0x08)
            M205 (__METHOD__, 0x68, MM07 (), EVE0)
            M205 (__METHOD__, 0x69, ObjectType (MM08), 0x08)
            CopyObject (MMM0 (), Local0)
            M205 (__METHOD__, 0x6A, MM08 (), Local0)
            M205 (__METHOD__, 0x6B, ObjectType (MM09), 0x08)
            M205 (__METHOD__, 0x6C, MM09 (), MTX0)
            M205 (__METHOD__, 0x6D, ObjectType (MM0A), 0x08)
            M205 (__METHOD__, 0x6E, MM0A (), OPR0)
            M205 (__METHOD__, 0x6F, ObjectType (MM0B), 0x08)
            M205 (__METHOD__, 0x70, MM0B (), PWR0)
            M205 (__METHOD__, 0x71, ObjectType (MM0C), 0x08)
            M205 (__METHOD__, 0x72, MM0C (), CPU0)
            M205 (__METHOD__, 0x73, ObjectType (MM0D), 0x08)
            If (Y350)
            {
                M205 (__METHOD__, 0x74, MM0D (), TZN0)
            }

            M205 (__METHOD__, 0x75, ObjectType (MM0E), 0x08)
            M205 (__METHOD__, 0x76, MM0E (), BFL0)
            M205 (__METHOD__, 0x77, ObjectType (MM0F), 0x08)
            M205 (__METHOD__, 0x78, MM0F (), DDB0)
            /*
             m205(ts, 121, ObjectType(mm0g), 8)
             m205(ts, 122, mm0g(), Debug)
             */
            M205 (__METHOD__, 0x7B, ObjectType (MM0H), 0x08)
            M205 (__METHOD__, 0x7C, DerefOf (MM0H ()), ORF0)
        }

        Method (M244, 0, NotSerialized)
        {
            Method (MM00, 0, NotSerialized)
            {
                Return (STR0) /* \M207.STR0 */
            }

            Method (MM01, 0, NotSerialized)
            {
                Return (INT0) /* \M207.INT0 */
            }

            M205 (__METHOD__, 0x7D, ObjectType (MM00), 0x08)
            M205 (__METHOD__, 0x7E, MM00 (), STR0)
            M205 (__METHOD__, 0x7F, ObjectType (MM01), 0x08)
            M205 (__METHOD__, 0x80, MM01 (), INT0)
        }

        Method (M245, 0, Serialized)
        {
            Name (FLAG, Ones)
            /* List of types of the parameters contains the same keyword */

            Method (MM00, 1, NotSerialized)
            {
                FLAG = 0x00
            }

            Method (MM01, 1, NotSerialized)
            {
                FLAG = 0x01
            }

            Method (MM02, 2, NotSerialized)
            {
                FLAG = 0x02
            }

            Method (MM03, 3, NotSerialized)
            {
                FLAG = 0x03
            }

            Method (MM04, 4, NotSerialized)
            {
                FLAG = 0x04
            }

            Method (MM05, 5, NotSerialized)
            {
                FLAG = 0x05
            }

            Method (MM06, 6, NotSerialized)
            {
                FLAG = 0x06
            }

            Method (MM07, 7, NotSerialized)
            {
                FLAG = 0x07
            }

            /* List of types of the parameters contains the UnknownObj keyword */

            Method (MM08, 1, NotSerialized)
            {
                FLAG = 0x08
            }

            Method (MM09, 1, NotSerialized)
            {
                FLAG = 0x09
            }

            Method (MM0A, 7, NotSerialized)
            {
                FLAG = 0x0A
            }

            /* List of types of the parameters contains different keywords */

            Method (MM10, 2, NotSerialized)
            {
                FLAG = 0x10
            }

            Method (MM11, 2, NotSerialized)
            {
                FLAG = 0x11
            }

            Method (MM12, 2, NotSerialized)
            {
                FLAG = 0x12
            }

            Method (MM13, 3, NotSerialized)
            {
                FLAG = 0x13
            }

            Method (MM14, 4, NotSerialized)
            {
                FLAG = 0x14
            }

            Method (MM15, 5, NotSerialized)
            {
                FLAG = 0x15
            }

            Method (MM16, 6, NotSerialized)
            {
                FLAG = 0x16
            }

            Method (MM17, 7, NotSerialized)
            {
                FLAG = 0x17
            }

            Method (MM18, 7, NotSerialized)
            {
                FLAG = 0x18
            }

            /* List of types of the parameters contains keyword packages */
            /* along with different keywords */
            Method (MM20, 1, NotSerialized)
            {
                FLAG = 0x20
            }

            Method (MM21, 1, NotSerialized)
            {
                FLAG = 0x21
            }

            /*
             // Bug 148
             Method(mm22, 1, , , , {{IntObj, StrObj, BuffObj, PkgObj,
             FieldUnitObj, DeviceObj, EventObj, MethodObj,
             MutexObj, OpRegionObj, PowerResObj, //ProcessorObj,
             ThermalZoneObj, BuffFieldObj, DDBHandleObj}}) {Store(34, Flag)}
             */
            Method (MM23, 2, NotSerialized)
            {
                FLAG = 0x23
            }

            Method (MM24, 2, NotSerialized)
            {
                FLAG = 0x24
            }

            Method (MM25, 2, NotSerialized)
            {
                FLAG = 0x25
            }

            Method (MM26, 2, NotSerialized)
            {
                FLAG = 0x26
            }

            Method (MM27, 2, NotSerialized)
            {
                FLAG = 0x27
            }

            Method (MM28, 2, NotSerialized)
            {
                FLAG = 0x28
            }

            Method (MM29, 2, NotSerialized)
            {
                FLAG = 0x29
            }

            /*
             // Bug 148
             Method(mm2a, 7, , , , {
             {IntObj, StrObj, BuffObj, PkgObj, FieldUnitObj, DeviceObj, EventObj, MethodObj,
             MutexObj, OpRegionObj, PowerResObj, ThermalZoneObj, BuffFieldObj, DDBHandleObj},
             {IntObj, StrObj, BuffObj, PkgObj, FieldUnitObj, DeviceObj, EventObj, MethodObj,
             MutexObj, OpRegionObj, PowerResObj, ThermalZoneObj, BuffFieldObj, DDBHandleObj},
             {IntObj, StrObj, BuffObj, PkgObj, FieldUnitObj, DeviceObj, EventObj, MethodObj,
             MutexObj, OpRegionObj, PowerResObj, ThermalZoneObj, BuffFieldObj, DDBHandleObj},
             {IntObj, StrObj, BuffObj, PkgObj, FieldUnitObj, DeviceObj, EventObj, MethodObj,
             MutexObj, OpRegionObj, PowerResObj, ThermalZoneObj, BuffFieldObj, DDBHandleObj},
             {IntObj, StrObj, BuffObj, PkgObj, FieldUnitObj, DeviceObj, EventObj, MethodObj,
             MutexObj, OpRegionObj, PowerResObj, ThermalZoneObj, BuffFieldObj, DDBHandleObj},
             {IntObj, StrObj, BuffObj, PkgObj, FieldUnitObj, DeviceObj, EventObj, MethodObj,
             MutexObj, OpRegionObj, PowerResObj, ThermalZoneObj, BuffFieldObj, DDBHandleObj},
             {IntObj, StrObj, BuffObj, PkgObj, FieldUnitObj, DeviceObj, EventObj, MethodObj,
             MutexObj, OpRegionObj, PowerResObj, ThermalZoneObj, BuffFieldObj, DDBHandleObj},
             }) {Store(42, Flag)}
             */
            /* List of types of the parameters contains the same keyword */
            M205 (__METHOD__, 0x81, ObjectType (MM00), 0x08)
            MM00 (0x01)
            M205 (__METHOD__, 0x82, FLAG, 0x00)
            M205 (__METHOD__, 0x83, ObjectType (MM01), 0x08)
            MM01 (0x01)
            M205 (__METHOD__, 0x84, FLAG, 0x01)
            M205 (__METHOD__, 0x85, ObjectType (MM02), 0x08)
            MM02 (0x01, 0x02)
            M205 (__METHOD__, 0x86, FLAG, 0x02)
            M205 (__METHOD__, 0x87, ObjectType (MM03), 0x08)
            MM03 (0x01, 0x02, 0x03)
            M205 (__METHOD__, 0x88, FLAG, 0x03)
            M205 (__METHOD__, 0x89, ObjectType (MM04), 0x08)
            MM04 (0x01, 0x02, 0x03, 0x04)
            M205 (__METHOD__, 0x8A, FLAG, 0x04)
            M205 (__METHOD__, 0x8B, ObjectType (MM05), 0x08)
            MM05 (0x01, 0x02, 0x03, 0x04, 0x05)
            M205 (__METHOD__, 0x8C, FLAG, 0x05)
            M205 (__METHOD__, 0x8D, ObjectType (MM06), 0x08)
            MM06 (0x01, 0x02, 0x03, 0x04, 0x05, 0x06)
            M205 (__METHOD__, 0x8E, FLAG, 0x06)
            M205 (__METHOD__, 0x8F, ObjectType (MM07), 0x08)
            MM07 (0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07)
            M205 (__METHOD__, 0x90, FLAG, 0x07)
            /* List of types of the parameters contains the UnknownObj keyword */

            M205 (__METHOD__, 0x91, ObjectType (MM08), 0x08)
            MM08 (0x01)
            M205 (__METHOD__, 0x92, FLAG, 0x08)
            M205 (__METHOD__, 0x93, ObjectType (MM09), 0x08)
            MM09 (0x01)
            M205 (__METHOD__, 0x94, FLAG, 0x09)
            M205 (__METHOD__, 0x95, ObjectType (MM0A), 0x08)
            MM0A (0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07)
            M205 (__METHOD__, 0x96, FLAG, 0x0A)
            /* List of types of the parameters contains different keywords */

            M205 (__METHOD__, 0x97, ObjectType (MM10), 0x08)
            MM10 (0x01, 0x02)
            M205 (__METHOD__, 0x98, FLAG, 0x10)
            M205 (__METHOD__, 0x99, ObjectType (MM11), 0x08)
            MM11 (0x01, 0x02)
            M205 (__METHOD__, 0x9A, FLAG, 0x11)
            M205 (__METHOD__, 0x9B, ObjectType (MM12), 0x08)
            MM12 (0x01, 0x02)
            M205 (__METHOD__, 0x9C, FLAG, 0x12)
            M205 (__METHOD__, 0x9D, ObjectType (MM13), 0x08)
            MM13 (0x01, 0x02, 0x03)
            M205 (__METHOD__, 0x9E, FLAG, 0x13)
            M205 (__METHOD__, 0x9F, ObjectType (MM14), 0x08)
            MM14 (0x01, 0x02, 0x03, 0x04)
            M205 (__METHOD__, 0xA0, FLAG, 0x14)
            M205 (__METHOD__, 0xA1, ObjectType (MM15), 0x08)
            MM15 (0x01, 0x02, 0x03, 0x04, 0x05)
            M205 (__METHOD__, 0xA2, FLAG, 0x15)
            M205 (__METHOD__, 0xA3, ObjectType (MM16), 0x08)
            MM16 (0x01, 0x02, 0x03, 0x04, 0x05, 0x06)
            M205 (__METHOD__, 0xA4, FLAG, 0x16)
            M205 (__METHOD__, 0xA5, ObjectType (MM17), 0x08)
            MM17 (0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07)
            M205 (__METHOD__, 0xA6, FLAG, 0x17)
            M205 (__METHOD__, 0xA7, ObjectType (MM18), 0x08)
            MM18 (0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07)
            M205 (__METHOD__, 0xA8, FLAG, 0x18)
            /* List of types of the parameters contains keyword packages */
            /* along with different keywords */
            M205 (__METHOD__, 0xA9, ObjectType (MM20), 0x08)
            MM20 (0x01)
            M205 (__METHOD__, 0xAA, FLAG, 0x20)
            M205 (__METHOD__, 0xAB, ObjectType (MM21), 0x08)
            MM21 (0x01)
            M205 (__METHOD__, 0xAC, FLAG, 0x21)
            /*
             // Bug 148
             m205(ts, 173, ObjectType(mm22), 8)
             mm22(1)
             m205(ts, 174, Flag, 34)
             */
            M205 (__METHOD__, 0xAF, ObjectType (MM23), 0x08)
            MM23 (0x01, 0x02)
            M205 (__METHOD__, 0xB0, FLAG, 0x23)
            M205 (__METHOD__, 0xB1, ObjectType (MM24), 0x08)
            MM24 (0x01, 0x02)
            M205 (__METHOD__, 0xB2, FLAG, 0x24)
            M205 (__METHOD__, 0xB3, ObjectType (MM25), 0x08)
            MM25 (0x01, 0x02)
            M205 (__METHOD__, 0xB4, FLAG, 0x25)
            M205 (__METHOD__, 0xB5, ObjectType (MM26), 0x08)
            MM26 (0x01, 0x02)
            M205 (__METHOD__, 0xB6, FLAG, 0x26)
            M205 (__METHOD__, 0xB7, ObjectType (MM27), 0x08)
            MM27 (0x01, 0x02)
            M205 (__METHOD__, 0xB8, FLAG, 0x27)
            M205 (__METHOD__, 0xB9, ObjectType (MM28), 0x08)
            MM28 (0x01, 0x02)
            M205 (__METHOD__, 0xBA, FLAG, 0x28)
            M205 (__METHOD__, 0xBB, ObjectType (MM29), 0x08)
            MM29 (0x01, 0x02)
            M205 (__METHOD__, 0xBC, FLAG, 0x29)
                /*
         // Bug 148
         m205(ts, 189, ObjectType(mm2a), 8)
         mm2a(1, 2, 3, 4, 5, 6, 7)
         m205(ts, 190, Flag, 42)
         */
        }

        /* UnSerialized Method can be invoked recursively */

        Method (M246, 0, Serialized)
        {
            Name (I000, 0x00)
            Method (MM00, 1, NotSerialized)
            {
                I000++
                If (Arg0)
                {
                    MM01 ()
                }
            }

            Method (MM01, 0, NotSerialized)
            {
                MM00 (0x00)
            }

            I000 = 0x00
            MM00 (0x00)
            M205 (__METHOD__, 0xBF, I000, 0x01)
            I000 = 0x00
            MM00 (0x01)
            M205 (__METHOD__, 0xC0, I000, 0x02)
        }

        /* Serialized Method can be invoked recursively */

        Method (M247, 0, Serialized)
        {
            Name (I000, 0x00)
            Method (MM00, 1, Serialized)
            {
                I000++
                If (Arg0)
                {
                    MM01 ()
                }
            }

            Method (MM01, 0, NotSerialized)
            {
                MM00 (0x00)
            }

            I000 = 0x00
            MM00 (0x00)
            M205 (__METHOD__, 0xC1, I000, 0x01)
            I000 = 0x00
            MM00 (0x01)
            M205 (__METHOD__, 0xC2, I000, 0x02)
        }

        /* Serialized Method can invoke another Serialized One */
        /* if SyncLevel is not lowered */
        Method (M248, 0, Serialized)
        {
            Name (I000, 0x00)
            Method (MM00, 1, Serialized)
            {
                I000++
                If (Arg0)
                {
                    MM01 ()
                }
            }

            Method (MM01, 0, Serialized, 15)
            {
                I000++
            }

            I000 = 0x00
            MM00 (0x00)
            M205 (__METHOD__, 0xC3, I000, 0x01)
            I000 = 0x00
            MM00 (0x01)
            M205 (__METHOD__, 0xC4, I000, 0x02)
        }

        /* Serialized Method can acquire an Mutex */
        /* if SyncLevel is not lowered */
        Method (M249, 0, Serialized)
        {
            Mutex (MTX0, 0x0F)
            Name (I000, 0x00)
            Method (MM00, 1, Serialized)
            {
                I000++
                If (Arg0)
                {
                    Local0 = Acquire (MTX0, 0x0000)
                    If (!M205 (__METHOD__, 0xC5, Local0, Zero))
                    {
                        I000++
                        Release (MTX0)
                    }
                }
            }

            I000 = 0x00
            MM00 (0x00)
            M205 (__METHOD__, 0xC6, I000, 0x01)
            I000 = 0x00
            MM00 (0x01)
            M205 (__METHOD__, 0xC7, I000, 0x02)
        }

        /* When Serialized Method calls another one then */
        /* the last can acquire an Mutex if SyncLevel is not lowered */
        Method (M24A, 0, Serialized)
        {
            Mutex (MTX1, 0x0F)
            Name (I000, 0x00)
            Method (MM00, 1, Serialized)
            {
                I000++
                If (Arg0)
                {
                    MM01 ()
                }
            }

            Method (MM01, 0, NotSerialized)
            {
                Local0 = Acquire (MTX1, 0x0000)
                If (!M205 (__METHOD__, 0xC8, Local0, Zero))
                {
                    I000++
                    Release (MTX1)
                }
            }

            I000 = 0x00
            MM00 (0x00)
            M205 (__METHOD__, 0xC9, I000, 0x01)
            I000 = 0x00
            MM00 (0x01)
            M205 (__METHOD__, 0xCA, I000, 0x02)
        }

        /* UnSerialized Method acquiring an Mutex can invoke */
        /* another Serialized One if SyncLevel is not lowered */
        Method (M24B, 0, Serialized)
        {
            Mutex (MTX0, 0x00)
            Name (I000, 0x00)
            Method (MM00, 1, NotSerialized)
            {
                Local0 = Acquire (MTX0, 0x0000)
                If (!M205 (__METHOD__, 0xCB, Local0, Zero))
                {
                    I000++
                    If (Arg0)
                    {
                        MM01 ()
                    }

                    Release (MTX0)
                }
            }

            Method (MM01, 0, Serialized, 15)
            {
                I000++
            }

            I000 = 0x00
            MM00 (0x00)
            M205 (__METHOD__, 0xCC, I000, 0x01)
            I000 = 0x00
            MM00 (0x01)
            M205 (__METHOD__, 0xCD, I000, 0x02)
        }

        /* When UnSerialized Method acquiring an Mutex invokes */
        /* another Serialized One then the last can release the */
        /* Mutex if Mutex's SyncLevel is not lower than the Method's */
        Method (M24C, 0, Serialized)
        {
            Mutex (MTX0, 0x00)
            Name (I000, 0x00)
            Method (MM00, 1, NotSerialized)
            {
                Local0 = Acquire (MTX0, 0x0000)
                If (!M205 (__METHOD__, 0xCE, Local0, Zero))
                {
                    I000++
                    If (Arg0)
                    {
                        MM01 ()
                    }
                    Else
                    {
                        Release (MTX0)
                    }
                }
            }

            Method (MM01, 0, Serialized)
            {
                I000++
                Release (MTX0)
            }

            I000 = 0x00
            MM00 (0x00)
            M205 (__METHOD__, 0xCF, I000, 0x01)
            I000 = 0x00
            MM00 (0x01)
            M205 (__METHOD__, 0xD0, I000, 0x02)
        }

        SRMT ("m240")
        M240 ()
        SRMT ("m241")
        M241 ()
        SRMT ("m242")
        M242 ()
        SRMT ("m243")
        M243 ()
        SRMT ("m244")
        M244 ()
        SRMT ("m245")
        M245 ()
        SRMT ("m246")
        M246 ()
        SRMT ("m247")
        If (Y349)
        {
            M247 ()
        }
        Else
        {
            BLCK ()
        }

        SRMT ("m248")
        M248 ()
        SRMT ("m249")
        M249 ()
        SRMT ("m24a")
        M24A ()
        SRMT ("m24b")
        M24B ()
        SRMT ("m24c")
        M24C ()
    }

    /* Run-method */

    Method (NM01, 0, NotSerialized)
    {
        Debug = "TEST: NM01, Declare Control Method Named Object"
        M207 ()
        CH03 ("NM01", Z133, __LINE__, 0x00, 0x00)
    }
