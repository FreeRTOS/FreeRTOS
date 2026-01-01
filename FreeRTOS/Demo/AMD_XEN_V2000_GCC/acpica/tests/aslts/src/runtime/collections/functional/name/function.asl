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
    Name (Z134, 0x86)
    /*
     * This sub-test is intended to comprehensively verify
     * the Function declaration syntax implementation.
     *
     * Declare the Function Control Method Objects of different,
     * signature check that properly specified or default arguments
     * values provide required functionality.
     *
     * The overall functionality of the Function Objects is indirectly
     * verified by other tests as far as "Functions are equivalent to a
     * Method that specifies NotSerialized".
     *
     *    17.5.49    Function (Declare Control Method)
     *    Syntax
     * Function (FunctionName, ReturnType, ParameterTypes) {TermList}
     *
     *    Validated Assertions:
     *
     * - Function declaration creates an Object in the ACPI
     *   namespace which can be referred by the specified FunctionName
     *   either to initiate its invocation or to obtain its AML Object
     *   type. Also FunctionName can be used to save a copy of the Object
     *   or a reference to it in another AML Object.
     *
     * - ASL compiler should allow only a Namestring data type in the
     *   FunctionName position.
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
     *   and the number of members in the ParameterTypes package exceeds 7.
     *
     * - If ParameterTypes is not specified, then the number of parameters
     *   is Zero.
     *
     * - ASL compiler should report an error when an actual Object
     *   specified to be a respective argument of the Method is of
     *   inappropriate type.
     *
     * - System software should execute a Function control method
     *   by referencing the objects in the Function body in order.
     *
     * - Function opens a name scope. All namespace references that occur
     *   during the method execution are relative to the Function package
     *   location.
     *
     * - All namespace objects created by a Function should be destroyed
     *   when Function execution exits.
     *
     */
    Scope (\_SB)
    {
        Method (M20D, 0, NotSerialized)
        {
        }
    }

    Method (M20E, 0, Serialized)
    {
        Method (M316, 0, NotSerialized)
        {
            Method (MM00, 0, NotSerialized)
            {
                Return ("\\m20e.m316.mm00")
            }

            Method (\_SB.M20D.MM00, 0, NotSerialized)
            {
                Return ("\\_SB.m20d.mm00")
            }

            M205 (__METHOD__, 0x01, ObjectType (MM00), 0x08)
            M205 (__METHOD__, 0x02, MM00 (), "\\m20e.m316.mm00")
            M205 (__METHOD__, 0x03, ObjectType (\M20E.M316.MM00), 0x08)
            M205 (__METHOD__, 0x04, \M20E.M316.MM00 (), "\\m20e.m316.mm00")
            M205 (__METHOD__, 0x05, ObjectType (^M316.MM00), 0x08)
            M205 (__METHOD__, 0x06, ^M316.MM00 (), "\\m20e.m316.mm00")
            M205 (__METHOD__, 0x07, ObjectType (\_SB.M20D.MM00), 0x08)
            M205 (__METHOD__, 0x08, \_SB.M20D.MM00 (), "\\_SB.m20d.mm00")
        }

        Method (M317, 0, NotSerialized)
        {
            Method (MM10, 0, NotSerialized)
            {
                Return ("\\m20e.m317.mm10")
            }

            Method (MM20, 0, NotSerialized)
            {
                Return ("\\m20e.m317.mm20")
            }

            Method (MM30, 0, NotSerialized)
            {
                Return ("\\m20e.m317.mm30")
            }

            M205 (__METHOD__, 0x09, ObjectType (MM10), 0x08)
            M205 (__METHOD__, 0x0A, MM10 (), "\\m20e.m317.mm10")
            M205 (__METHOD__, 0x0B, ObjectType (MM20), 0x08)
            M205 (__METHOD__, 0x0C, MM20 (), "\\m20e.m317.mm20")
            M205 (__METHOD__, 0x0D, ObjectType (MM30), 0x08)
            If (Y157)
            {
                M205 (__METHOD__, 0x0E, MM30 (), "\\m20e.m317.mm30")
            }
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
        Method (M318, 0, NotSerialized)
        {
            Method (MM00, 1, NotSerialized)
            {
                Arg0 = (DerefOf (Arg0) + 0x01)
            }

            Method (MM01, 0, NotSerialized)
            {
                Return (INT0) /* \M20E.INT0 */
            }

            Method (MM11, 0, NotSerialized)
            {
                Return (INT0) /* \M20E.INT0 */
            }

            Method (MM02, 0, NotSerialized)
            {
                Return (STR0) /* \M20E.STR0 */
            }

            Method (MM03, 0, NotSerialized)
            {
                Return (BUF0) /* \M20E.BUF0 */
            }

            Method (MM04, 0, NotSerialized)
            {
                Return (PAC0) /* \M20E.PAC0 */
            }

            Method (MM05, 0, NotSerialized)
            {
                Return (FLU0) /* \M20E.FLU0 */
            }

            Method (MM06, 0, NotSerialized)
            {
                Return (DEV0) /* \M20E.DEV0 */
            }

            Method (MM07, 0, NotSerialized)
            {
                Return (EVE0) /* \M20E.EVE0 */
            }

            Method (MM08, 0, NotSerialized)
            {
                CopyObject (MMM0 (), Local0)
                Return (Local0)
            }

            Method (MM09, 0, NotSerialized)
            {
                Return (MTX0) /* \M20E.MTX0 */
            }

            Method (MM0A, 0, NotSerialized)
            {
                Return (OPR0) /* \M20E.OPR0 */
            }

            Method (MM0B, 0, NotSerialized)
            {
                Return (PWR0) /* \M20E.PWR0 */
            }

            Method (MM0C, 0, NotSerialized)
            {
                Return (CPU0) /* \M20E.CPU0 */
            }

            Method (MM0D, 0, NotSerialized)
            {
                Return (TZN0) /* \M20E.TZN0 */
            }

            Method (MM0E, 0, NotSerialized)
            {
                Return (BFL0) /* \M20E.BFL0 */
            }

            Method (MM0F, 0, NotSerialized)
            {
                Return (DDB0) /* \M20E.DDB0 */
            }

            /* Formal declaration */
            /*		Function(mm0g, DebugObj) {Return (Debug)} */
            Method (MM0H, 0, NotSerialized)
            {
                Return (RefOf (ORF0))
            }

            Local0 = 0xFEDCBA9876543210
            M205 (__METHOD__, 0x0F, ObjectType (MM00), 0x08)
            /*
             // Bug 148
             mm00(Refof(Local0))
             m205(ts, 16, Local0, 0xfedcba9876543211)
             */
            M205 (__METHOD__, 0x11, ObjectType (MM01), 0x08)
            M205 (__METHOD__, 0x12, MM01 (), INT0)
            M205 (__METHOD__, 0x13, ObjectType (MM02), 0x08)
            M205 (__METHOD__, 0x14, MM02 (), STR0)
            M205 (__METHOD__, 0x15, ObjectType (MM03), 0x08)
            M205 (__METHOD__, 0x16, MM03 (), BUF0)
            M205 (__METHOD__, 0x17, ObjectType (MM04), 0x08)
            M205 (__METHOD__, 0x18, MM04 (), PAC0)
            M205 (__METHOD__, 0x19, ObjectType (MM05), 0x08)
            M205 (__METHOD__, 0x1A, MM05 (), FLU0)
            M205 (__METHOD__, 0x1B, ObjectType (MM06), 0x08)
            M205 (__METHOD__, 0x1C, MM06 (), DEV0)
            M205 (__METHOD__, 0x1D, ObjectType (MM07), 0x08)
            M205 (__METHOD__, 0x1E, MM07 (), EVE0)
            M205 (__METHOD__, 0x1F, ObjectType (MM08), 0x08)
            CopyObject (MMM0 (), Local0)
            M205 (__METHOD__, 0x20, MM08 (), Local0)
            M205 (__METHOD__, 0x21, ObjectType (MM09), 0x08)
            M205 (__METHOD__, 0x22, MM09 (), MTX0)
            M205 (__METHOD__, 0x23, ObjectType (MM0A), 0x08)
            M205 (__METHOD__, 0x24, MM0A (), OPR0)
            M205 (__METHOD__, 0x25, ObjectType (MM0B), 0x08)
            M205 (__METHOD__, 0x26, MM0B (), PWR0)
            M205 (__METHOD__, 0x27, ObjectType (MM0C), 0x08)
            M205 (__METHOD__, 0x28, MM0C (), CPU0)
            M205 (__METHOD__, 0x29, ObjectType (MM0D), 0x08)
            If (Y350)
            {
                M205 (__METHOD__, 0x2A, MM0D (), TZN0)
            }

            M205 (__METHOD__, 0x2B, ObjectType (MM0E), 0x08)
            M205 (__METHOD__, 0x2C, MM0E (), BFL0)
            M205 (__METHOD__, 0x2D, ObjectType (MM0F), 0x08)
            M205 (__METHOD__, 0x2E, MM0F (), DDB0)
            /*
             m205(ts, 47, ObjectType(mm0g), 8)
             m205(ts, 48, mm0g(), Debug)
             */
            M205 (__METHOD__, 0x31, ObjectType (MM0H), 0x08)
            M205 (__METHOD__, 0x32, DerefOf (MM0H ()), ORF0)
        }

        Method (M319, 0, NotSerialized)
        {
            Method (MM00, 0, NotSerialized)
            {
                Return (STR0) /* \M20E.STR0 */
            }

            Method (MM01, 0, NotSerialized)
            {
                Return (INT0) /* \M20E.INT0 */
            }

            M205 (__METHOD__, 0x33, ObjectType (MM00), 0x08)
            M205 (__METHOD__, 0x34, MM00 (), STR0)
            M205 (__METHOD__, 0x35, ObjectType (MM01), 0x08)
            M205 (__METHOD__, 0x36, MM01 (), INT0)
        }

        Method (M31A, 0, Serialized)
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

            Method (MM21, 2, NotSerialized)
            {
                FLAG = 0x21
            }

            /*
             // Bug 148
             Function(mm22, , {{IntObj, StrObj, BuffObj, PkgObj,
             FieldUnitObj, DeviceObj, EventObj, MethodObj,
             MutexObj, OpRegionObj, PowerResObj, ProcessorObj,
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
         Function(mm3a, , {
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
        /*
         // Bug 148
         // List of types of the parameters contains the same keyword
         m205(ts, 55, ObjectType(mm00), 8)
         mm00(1)
         m205(ts, 56, Flag, 0)
         m205(ts, 57, ObjectType(mm01), 8)
         mm01(1)
         m205(ts, 58, Flag, 1)
         m205(ts, 59, ObjectType(mm02), 8)
         mm02(1, 2)
         m205(ts, 60, Flag, 2)
         m205(ts, 61, ObjectType(mm03), 8)
         mm03(1, 2, 3)
         m205(ts, 62, Flag, 3)
         m205(ts, 63, ObjectType(mm04), 8)
         mm04(1, 2, 3, 4)
         m205(ts, 64, Flag, 4)
         m205(ts, 65, ObjectType(mm05), 8)
         mm05(1, 2, 3, 4, 5)
         m205(ts, 66, Flag, 5)
         m205(ts, 67, ObjectType(mm06), 8)
         mm06(1, 2, 3, 4, 5, 6)
         m205(ts, 68, Flag, 6)
         m205(ts, 69, ObjectType(mm07), 8)
         mm07(1, 2, 3, 4, 5, 6, 7)
         m205(ts, 70, Flag, 7)
         // List of types of the parameters contains the UnknownObj keyword
         m205(ts, 71, ObjectType(mm08), 8)
         mm08(1)
         m205(ts, 72, Flag, 8)
         m205(ts, 73, ObjectType(mm09), 8)
         mm09(1)
         m205(ts, 74, Flag, 9)
         m205(ts, 75, ObjectType(mm0a), 8)
         mm08(1, 2, 3, 4, 5, 6, 7)
         m205(ts, 76, Flag, 10)
         // List of types of the parameters contains different keywords
         m205(ts, 77, ObjectType(mm10), 8)
         mm10(1, 2)
         m205(ts, 78, Flag, 16)
         m205(ts, 79, ObjectType(mm11), 8)
         mm11(1, 2)
         m205(ts, 80, Flag, 17)
         m205(ts, 81, ObjectType(mm12), 8)
         mm12(1, 2)
         m205(ts, 82, Flag, 18)
         m205(ts, 83, ObjectType(mm13), 8)
         mm13(1, 2, 3)
         m205(ts, 84, Flag, 19)
         m205(ts, 85, ObjectType(mm14), 8)
         mm14(1, 2, 3, 4)
         m205(ts, 86, Flag, 20)
         m205(ts, 87, ObjectType(mm15), 8)
         mm15(1, 2, 3, 4, 5)
         m205(ts, 88, Flag, 21)
         m205(ts, 89, ObjectType(mm16), 8)
         mm16(1, 2, 3, 4, 5, 6)
         m205(ts, 90, Flag, 22)
         m205(ts, 91, ObjectType(mm17), 8)
         mm17(1, 2, 3, 4, 5, 6, 7)
         m205(ts, 92, Flag, 23)
         m205(ts, 93, ObjectType(mm18), 8)
         mm18(1, 2, 3, 4, 5, 6, 7)
         m205(ts, 94, Flag, 24)
         // List of types of the parameters contains keyword packages
         // along with different keywords
         m205(ts, 95, ObjectType(mm20), 8)
         mm20(1)
         m205(ts, 96, Flag, 32)
         m205(ts, 97, ObjectType(mm21), 8)
         mm21(1)
         m205(ts, 98, Flag, 33)
         m205(ts, 99, ObjectType(mm22), 8)
         mm22(1)
         m205(ts, 100, Flag, 34)
         m205(ts, 101, ObjectType(mm23), 8)
         mm23(1, 2)
         m205(ts, 102, Flag, 35)
         m205(ts, 103, ObjectType(mm24), 8)
         mm24(1, 2)
         m205(ts, 104, Flag, 36)
         m205(ts, 105, ObjectType(mm25), 8)
         mm25(1, 2)
         m205(ts, 106, Flag, 37)
         m205(ts, 107, ObjectType(mm26), 8)
         mm26(1, 2)
         m205(ts, 108, Flag, 38)
         m205(ts, 109, ObjectType(mm27), 8)
         mm27(1, 2)
         m205(ts, 110, Flag, 39)
         m205(ts, 149, ObjectType(mm28), 8)
         mm28(1, 2)
         m205(ts, 111, Flag, 40)
         m205(ts, 112, ObjectType(mm29), 8)
         mm29(1, 2)
         m205(ts, 113, Flag, 41)
         m205(ts, 114, ObjectType(mm2a), 8)
         mm2a(1, 2, 3, 4, 5, 6, 7)
         m205(ts, 115, Flag, 42)
         */
        }

        SRMT ("m316")
        M316 ()
        SRMT ("m317")
        M317 ()
        SRMT ("m318")
        M318 ()
        SRMT ("m319")
        M319 ()
        SRMT ("m31a")
        M31A ()
    }

    /* Run-method */

    Method (NM02, 0, NotSerialized)
    {
        Debug = "TEST: NM02, Declare Function Control Method Named Object"
        M20E ()
        CH03 ("NM02", Z134, __LINE__, 0x00, 0x00)
    }
