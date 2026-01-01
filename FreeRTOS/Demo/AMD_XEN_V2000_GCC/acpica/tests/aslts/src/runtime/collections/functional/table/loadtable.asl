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
     * LoadTable ASL operator functionality
     */
    /*
     * This sub-test is intended to comprehensively verify
     * the LoadTable ASL operator functionality.
     *
     * Performs a run-time load of a Definition Block from the XSDT.
     *
     *    17.5.68   LoadTable (Load Definition Block From XSDT)
     *    Syntax
     * LoadTable (SignatureString, OEMIDString, OEMTableIDString,
     *   RootPathString, ParameterPathString, ParameterData) => DDBHandle
     *
     * On testing the following issues should be covered:
     *
     * - loading from the XSDT of a Definition Block in which the Signature
     *   field (should differ from "DSDT" and "SSDT") matches SignatureString,
     *   the OEM ID field matches OEMIDString, and the OEM Table ID matches
     *   OEMTableIDString,
     *
     * - all comparisons are case sensitive,
     *
     * - the result of the LoadTable operator is an Object of the DDBHandle type,
     *
     * - if no table matches the specified parameters, then 0 is returned,
     *
     * - the DDBHandle Object returned from the LoadTable operator can be used
     *   to unload the table,
     *
     * - any of the optional parameters (RootPathString, ParameterPathString,
     *   and ParameterData) can be omitted,
     *
     * - different sources of the String parameters: literals, Named Objects,
     *   LocalX, ArgX, elements of Packages, results of functions, any TermArg
     *
     * - different sources of the optional parameters: literals, Named Objects,
     *   LocalX, ArgX, elements of Packages, results of functions, any TermArg
     *
     * - implicit operand conversion of the parameters specified to be strings,
     *
     * - namespace location to load the Definition Block is determined by the
     *   RootPathString parameter,
     *
     * - the RootPathString is evaluated using normal scoping rules, assuming
     *   that the scope of the LoadTable operator is the current scope,
     *
     * - if RootPathString is not specified, "\" is assumed,
     *
     * - if ParameterPathString and ParameterData are specified, the data object
     *   specified by ParameterData is stored into the object specified by
     *   ParameterPathString after the table has been added into the namespace,
     *
     * - if the first character of ParameterPathString is a backslash or caret
     *   character, then the path of the object is ParameterPathString. Otherwise,
     *   it is RootPathString.ParameterPathString,
     *
     * - if some SSDT matching the LoadTable parameters is originally not listed
     *   in XSDT, LoadTable returns 0,
     *
     * - exceptional conditions caused by inappropriate data:
     *   = the SignatureString is greater than four characters,
     *   = the OEMIDString is greater than six characters,
     *   = the OEMTableID is greater than eight characters,
     *   = incorrect types of the parameters,
     *   = some DSDT or SSDT matching the LoadTable parameters is already loaded
     *     (actually on initial loading of tables listed in XSDT),
     *   = the matched table is already loaded,
     *   = there already is an previously loaded Object referred by the path
     *     in the Namespace,
     *   = the object specified by the ParameterPathString does not exist,
     *   = storing of data of the ParameterData data type is not allowed,
     *   = AE_OWNER_ID_LIMIT exception when too many Tables loaded.
     *
     * Can not be tested following issues:
     * - providing of the table matched the LoadTable parameters to be "in memory
     *   marked by AddressRangeReserved or AddressRangeNVS",
     * - overriding the supplied table with "a newer revision Definition Block
     *   of the same OEM Table ID" by the OS,
     * - loading a Definition Block to be a synchronous operation ("the control
     *   methods defined in the Definition Block are not executed during load
     *   time").
     *
     * Note: the tests is based on the current representation of the auxiliary
     *       OEM1 table in the artificial set of tables in the RSDT of acpiexec.
     */
    Name (Z176, 0xB0)
    Device (DTM2)
    {
        Device (DEVR)
        {
            Name (S000, "DEVR")
        }

        /* Contents of the OEM1 signature table addressed by the RSDT in acpiexec */

        Name (OEMT, Buffer (0x38)
        {
            /* 0000 */  0x4F, 0x45, 0x4D, 0x31, 0x38, 0x00, 0x00, 0x00,  // OEM18...
            /* 0008 */  0x01, 0x4B, 0x49, 0x6E, 0x74, 0x65, 0x6C, 0x00,  // .KIntel.
            /* 0010 */  0x4D, 0x61, 0x6E, 0x79, 0x00, 0x00, 0x00, 0x00,  // Many....
            /* 0018 */  0x01, 0x00, 0x00, 0x00, 0x49, 0x4E, 0x54, 0x4C,  // ....INTL
            /* 0020 */  0x18, 0x09, 0x03, 0x20, 0x08, 0x5F, 0x58, 0x54,  // ... ._XT
            /* 0028 */  0x32, 0x0A, 0x04, 0x14, 0x0C, 0x5F, 0x58, 0x54,  // 2...._XT
            /* 0030 */  0x31, 0x00, 0x70, 0x01, 0x5F, 0x58, 0x54, 0x32   // 1.p._XT2
        })
        CreateField (OEMT, 0x00, 0x20, FOEM)
        CreateField (OEMT, 0x50, 0x30, FOID)
        CreateField (OEMT, 0x80, 0x40, FTID)
        Name (SOEM, "OEM1")
        Name (SOID, "Intel")
        Name (STID, "Many")
        Name (POEM, Package (0x03)
        {
            "OEM1",
            "Intel",
            "Many"
        })
        Name (RPST, "\\DTM2")
        Name (PLDT, 0x00)
        Name (PPST, "\\DTM2.PLDT")
        Name (DDBH, 0x00)
        /* Check DataTable Region */

        Method (CHDR, 1, Serialized)
        {
            DataTableRegion (DR00, "OEM1", "", "")
            Field (DR00, AnyAcc, NoLock, Preserve)
            {
                FU00,   448
            }

            Concatenate (Arg0, "-tst0", Arg0)
            If ((OEMT != FU00))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, FU00, OEMT)
                Return (0x01)
            }

            Return (0x00)
        }

        /* Simple Loadtable test */

        Method (TST0, 1, Serialized)
        {
            Name (DDBH, 0x00)
            Concatenate (Arg0, "-tst0", Arg0)
            If (CHDR (Arg0))
            {
                Return (0x01)
            }

            If (CondRefOf (\_XT2, Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\_XT2", 0x01)
                Return (0x01)
            }

            \DTM2.PLDT = 0x00
            DDBH = LoadTable ("OEM1", "", "", "\\", PPST, 0x01)
            If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            Local1 = ObjectType (DDBH)
            If ((Local1 != C017))
            {
                /* DDB Handle */

                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local1, C017)
                Return (0x01)
            }

            If ((0x01 != \DTM2.PLDT))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, \DTM2.PLDT, 0x01)
            }

            If (CondRefOf (\_XT2, Local0)){}
            Else
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\_XT2", 0x00)
            }

            Unload (DDBH)
            Debug = "OEM1 unloaded"
            If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            If (CondRefOf (\_XT2, Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\_XT2", 0x01)
            }

            Return (0x00)
        }

        /* All comparisons of Loadtable parameters are case sensitive, */
        /* if no table matches the specified parameters, then 0 is returned */
        Method (TST1, 1, Serialized)
        {
            Name (DDBH, 0x00)
            Concatenate (Arg0, "-tst1", Arg0)
            If (CondRefOf (\_XT2, Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\_XT2", 0x01)
                Return (0x01)
            }

            /* Successful comparison */

            \DTM2.PLDT = 0x00
            If (Y281)
            {
                DDBH = LoadTable ("OEM1", "Intel", "Many", "\\", PPST, 0x01)
            }
            Else
            {
                DDBH = LoadTable ("OEM1", "", "", "\\", PPST, 0x01)
            }

            If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            Local1 = ObjectType (DDBH)
            If ((Local1 != C017))
            {
                /* DDB Handle */

                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local1, C017)
                Return (0x01)
            }

            If ((0x01 != \DTM2.PLDT))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, \DTM2.PLDT, 0x01)
            }

            If (CondRefOf (\_XT2, Local0)){}
            Else
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\_XT2", 0x00)
            }

            Unload (DDBH)
            Debug = "OEM1 unloaded"
            If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            If (CondRefOf (\_XT2, Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\_XT2", 0x01)
            }

            /* Unhappy comparison due to the SignatureString */

            \DTM2.PLDT = 0x00
            Local1 = ObjectType (Local2)
            If ((Local1 != C008))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local1, C008)
            }

            Local2 = LoadTable ("OeM1", "Intel", "Many", "\\", PPST, 0x01)
            If (Y281)
            {
                /* No exception */

                If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
                {
                    Return (0x01)
                }
            }
            ElseIf            /* Exception: AE_BAD_SIGNATURE */

 (CH04 (Arg0, 0x01, 0x25, Z176, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            Local1 = ObjectType (Local2)
            If (Y281)
            {
                If ((Local1 != C009))
                {
                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local1, C009)
                }

                If ((Local2 != 0x00))
                {
                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local2, 0x00)
                }
            }
            ElseIf ((Local1 != C008))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local1, C008)
            }

            If ((0x00 != \DTM2.PLDT))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, \DTM2.PLDT, 0x00)
            }

            If (CondRefOf (\_XT2, Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\_XT2", 0x01)
            }

            /* Unhappy comparison due to the OEMIDString */

            \DTM2.PLDT = 0x00
            Local1 = ObjectType (Local3)
            If ((Local1 != C008))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local1, C008)
            }

            Local3 = LoadTable ("OEM1", "InteL", "Many", "\\", PPST, 0x01)
            If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            Local1 = ObjectType (Local3)
            If ((Local1 != C009))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local1, C009)
            }

            If ((Local3 != 0x00))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local3, 0x00)
            }

            If ((0x00 != \DTM2.PLDT))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, \DTM2.PLDT, 0x00)
            }

            If (CondRefOf (\_XT2, Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\_XT2", 0x01)
            }

            /* Unhappy comparison due to the OEMTableIDString */

            \DTM2.PLDT = 0x00
            Local1 = ObjectType (Local4)
            If ((Local1 != C008))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local1, C008)
            }

            Local4 = LoadTable ("OEM1", "Intel", "many", "\\", PPST, 0x01)
            If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            Local1 = ObjectType (Local4)
            If ((Local1 != C009))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local1, C009)
            }

            If ((Local4 != 0x00))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local4, 0x00)
            }

            If ((0x00 != \DTM2.PLDT))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, \DTM2.PLDT, 0x00)
            }

            If (CondRefOf (\_XT2, Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\_XT2", 0x01)
            }

            Return (0x00)
        }

        /* Any of the RootPathString, ParameterPathString, and ParameterData */
        /* parameters in LoadTable expression can be omitted */
        Method (TST2, 1, Serialized)
        {
            Name (DDB0, 0x00)
            Name (DDB1, 0x00)
            Name (DDB2, 0x00)
            Name (DDB3, 0x00)
            Concatenate (Arg0, "-tst2", Arg0)
            If (CondRefOf (\_XT2, Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\_XT2", 0x01)
                Return (0x01)
            }

            /* Check when RootPathString omitted */

            \DTM2.PLDT = 0x00
            DDB0 = LoadTable ("OEM1", "", "", "", PPST, 0x01)
            If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            Local1 = ObjectType (DDB0)
            If ((Local1 != C017))
            {
                /* DDB Handle */

                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local1, C017)
                Return (0x01)
            }

            If ((0x01 != \DTM2.PLDT))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, \DTM2.PLDT, 0x01)
            }

            If (CondRefOf (\_XT2, Local0)){}
            Else
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\_XT2", 0x00)
            }

            Unload (DDB0)
            Debug = "OEM1 unloaded"
            If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            If (CondRefOf (\_XT2, Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\_XT2", 0x01)
            }

            /* Check when ParameterPathString omitted */

            \DTM2.PLDT = 0x00
            DDB1 = LoadTable ("OEM1", "", "", "\\", "", 0x01)
            If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            Local1 = ObjectType (DDB1)
            If ((Local1 != C017))
            {
                /* DDB Handle */

                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local1, C017)
                Return (0x01)
            }

            If ((0x00 != \DTM2.PLDT))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, \DTM2.PLDT, 0x00)
            }

            If (CondRefOf (\_XT2, Local0)){}
            Else
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\_XT2", 0x00)
            }

            Unload (DDB1)
            Debug = "OEM1 unloaded"
            If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            If (CondRefOf (\_XT2, Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\_XT2", 0x01)
            }

            /* Check when ParameterData omitted */

            \DTM2.PLDT = 0x00
            DDB2 = LoadTable ("OEM1", "", "", "\\", PPST, Zero)
            If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            Local1 = ObjectType (DDB2)
            If ((Local1 != C017))
            {
                /* DDB Handle */

                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local1, C017)
                Return (0x01)
            }

            If ((0x00 != \DTM2.PLDT))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, \DTM2.PLDT, 0x00)
            }

            If (CondRefOf (\_XT2, Local0)){}
            Else
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\_XT2", 0x00)
            }

            Unload (DDB2)
            Debug = "OEM1 unloaded"
            If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            If (CondRefOf (\_XT2, Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\_XT2", 0x01)
            }

            /* Check when all optional parameters omitted */

            \DTM2.PLDT = 0x00
            DDB3 = LoadTable ("OEM1", "", "", "", "", Zero)
            If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            Local1 = ObjectType (DDB3)
            If ((Local1 != C017))
            {
                /* DDB Handle */

                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local1, C017)
                Return (0x01)
            }

            If ((0x00 != \DTM2.PLDT))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, \DTM2.PLDT, 0x00)
            }

            If (CondRefOf (\_XT2, Local0)){}
            Else
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\_XT2", 0x00)
            }

            Unload (DDB3)
            Debug = "OEM1 unloaded"
            If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            If (CondRefOf (\_XT2, Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\_XT2", 0x01)
            }

            Return (0x00)
        }

        /* Different sources of the String parameters: Named Objects, LocalX, */
        /* ArgX, elements of Packages, results of functions, any TermArg */
        Method (TST3, 1, Serialized)
        {
            Name (DDB0, 0x00)
            Name (DDB1, 0x00)
            Name (DDB2, 0x00)
            Name (DDB3, 0x00)
            Name (DDB4, 0x00)
            Name (DDB5, 0x00)
            Name (DDB6, 0x00)
            Name (SOID, "")
            Name (STID, "")
            Name (POEM, Package (0x03)
            {
                "OEM1",
                "",
                ""
            })
            Method (M000, 1, NotSerialized)
            {
                Return (Arg0)
            }

            Method (M001, 3, NotSerialized)
            {
                Concatenate (Arg0, Arg2, Arg0)
                If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
                {
                    Return (0x01)
                }

                Local1 = ObjectType (Arg1)
                If ((Local1 != C017))
                {
                    /* DDB Handle */

                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local1, C017)
                    Return (0x01)
                }

                If ((0x00 != \DTM2.PLDT))
                {
                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, \DTM2.PLDT, 0x00)
                }

                If (CondRefOf (\_XT2, Local0)){}
                Else
                {
                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\DTM2._XT2", 0x00)
                }

                Unload (Arg1)
                Debug = "OEM1 unloaded"
                If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
                {
                    Return (0x01)
                }

                If (CondRefOf (\_XT2, Local0))
                {
                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\DTM2._XT2", 0x01)
                    Return (0x01)
                }

                Return (0x00)
            }

            Method (M002, 3, NotSerialized)
            {
                Return (LoadTable (Arg0, DerefOf (Arg1), DerefOf (Arg2), "", "", Zero))
            }

            Method (M003, 3, NotSerialized)
            {
                Return (LoadTable (DerefOf (Arg0), Arg1, DerefOf (Arg2), "", "", Zero))
            }

            Method (M004, 3, NotSerialized)
            {
                Return (LoadTable (DerefOf (Arg0), DerefOf (Arg1), Arg2, "", "", Zero))
            }

            Concatenate (Arg0, "-tst3", Arg0)
            If (Y281)
            {
                SOID = ^SOID /* \DTM2.SOID */
                STID = ^STID /* \DTM2.STID */
                POEM = ^POEM /* \DTM2.POEM */
            }

            If (CondRefOf (\DTM2._XT2, Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\_XT2", 0x01)
                Return (0x01)
            }

            /* Check LoadTable(Named, LocalX, Method(), , , ) */

            \DTM2.PLDT = 0x00
            Local2 = SOID /* \DTM2.TST3.SOID */
            DDB0 = LoadTable (SOEM, Local2, M000 (STID), "", "", Zero)
            If (M001 (Arg0, DDB0, ".NLM"))
            {
                Return (0x01)
            }

            /* Check LoadTable(Method(), Named, LocalX, , , ) */

            \DTM2.PLDT = 0x00
            Local2 = STID /* \DTM2.TST3.STID */
            DDB1 = LoadTable (M000 (SOEM), SOID, Local2, "", "", Zero)
            If (M001 (Arg0, DDB1, ".MNL"))
            {
                Return (0x01)
            }

            /* Check LoadTable(LocalX, Method(), Named, , , ) */

            \DTM2.PLDT = 0x00
            Local2 = SOEM /* \DTM2.SOEM */
            DDB2 = LoadTable (Local2, M000 (SOID), STID, "", "", Zero)
            If (M001 (Arg0, DDB2, ".LMN"))
            {
                Return (0x01)
            }

            /* Check LoadTable(ArgX, Derefof(Refof), Derefof(Index), , , ) */

            \DTM2.PLDT = 0x00
            Local2 = RefOf (SOID)
            Store (POEM [0x02], Local3)
            DDB3 = M002 (SOEM, Local2, Local3)
            If (M001 (Arg0, DDB3, ".ARI"))
            {
                Return (0x01)
            }

            /* Check LoadTable(Derefof(Index), ArgX, Derefof(Refof), , , ) */

            \DTM2.PLDT = 0x00
            Local2 = RefOf (STID)
            Store (POEM [0x00], Local3)
            DDB4 = M003 (Local3, SOID, Local2)
            If (M001 (Arg0, DDB4, ".IAR"))
            {
                Return (0x01)
            }

            /* Check LoadTable(Derefof(Refof), Derefof(Index), ArgX, , , ) */

            \DTM2.PLDT = 0x00
            Local2 = RefOf (SOEM)
            Store (POEM [0x01], Local3)
            DDB5 = M004 (Local2, Local3, STID)
            If (M001 (Arg0, DDB5, ".RIA"))
            {
                Return (0x01)
            }

            /* Check LoadTable(TermArg, TermArg, TermArg, , , ) */

            \DTM2.PLDT = 0x00
            Local2 = Concatenate ("term", SOEM)
            Local2 = ToBuffer (Local2)
            Local3 = ToBuffer (SOID)
            Local4 = ""
            DDB6 = LoadTable (Mid (ToString (Local2, Ones), 0x04, 0x04), ToString (
                M000 (Local3), Ones), Concatenate (M000 (STID), Local4), "", "", Zero)
            If (M001 (Arg0, DDB6, ".TTT"))
            {
                Return (0x01)
            }

            Return (0x00)
        }

        /* Different sources of the optional parameters (RootPathString, */
        /* ParameterPathString, and ParameterData): Named Objects, LocalX, */
        /* ArgX, elements of Packages, results of functions, any TermArg */
        Method (TST4, 1, Serialized)
        {
            Name (DDB0, 0x00)
            Name (DDB1, 0x00)
            Name (DDB2, 0x00)
            Name (DDB3, 0x00)
            Name (DDB4, 0x00)
            Name (DDB5, 0x00)
            Name (DDB6, 0x00)
            Name (RPST, "\\DTM2")
            Name (PPST, "\\DTM2.PLDT")
            Name (NVAL, 0x01)
            Name (POPT, Package (0x03)
            {
                "\\DTM2",
                "\\DTM2.PLDT",
                0x01
            })
            Method (M000, 1, NotSerialized)
            {
                Return (Arg0)
            }

            Method (M001, 3, NotSerialized)
            {
                Concatenate (Arg0, Arg2, Arg0)
                If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
                {
                    Return (0x01)
                }

                Local1 = ObjectType (Arg1)
                If ((Local1 != C017))
                {
                    /* DDB Handle */

                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local1, C017)
                    Return (0x01)
                }

                If ((0x01 != \DTM2.PLDT))
                {
                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, \DTM2.PLDT, 0x01)
                }

                If (CondRefOf (\DTM2._XT2, Local0)){}
                Else
                {
                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\DTM2._XT2", 0x00)
                }

                Unload (Arg1)
                Debug = "OEM1 unloaded"
                If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
                {
                    Return (0x01)
                }

                If (CondRefOf (\DTM2._XT2, Local0))
                {
                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\DTM2._XT2", 0x01)
                    Return (0x01)
                }

                Return (0x00)
            }

            Method (M002, 3, NotSerialized)
            {
                /* Bug 288: iASL unexpectedly forbids ParameterData of Loadtable to be LocalX or UserTerm */
                /*			return (LoadTable("OEM1", "", "", Arg0, Derefof(Arg1), Derefof(Arg2))) */
                /*	                                        parse error, expecting `')'' ^ */
                Return (LoadTable ("OEM1", "", "", Arg0, DerefOf (Arg1), 0x01))
            }

            Method (M003, 3, NotSerialized)
            {
                /* Bug 288: iASL unexpectedly forbids ParameterData of Loadtable to be LocalX or UserTerm */
                /*			return (LoadTable("OEM1", "", "", Derefof(Arg0), Arg1, Derefof(Arg2))) */
                /*	                                        parse error, expecting `')'' ^ */
                Return (LoadTable ("OEM1", "", "", DerefOf (Arg0), Arg1, 0x01))
            }

            Method (M004, 3, NotSerialized)
            {
                /* Bug 288: iASL unexpectedly forbids ParameterData of Loadtable to be LocalX or UserTerm */
                /*			return (LoadTable("OEM1", "", "", Derefof(Arg0), Derefof(Arg1), Arg2)) */
                /*	                                              parse error, expecting `')'' ^ */
                Return (LoadTable ("OEM1", "", "", DerefOf (Arg0), DerefOf (Arg1), 0x01))
            }

            Concatenate (Arg0, "-tst4", Arg0)
            If (CondRefOf (\DTM2._XT2, Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\DTM2._XT2", 0x01)
                Return (0x01)
            }

            /* Check LoadTable(..., Named, LocalX, Method()) */

            \DTM2.PLDT = 0x00
            Local2 = PPST /* \DTM2.TST4.PPST */
            /* Bug 288: iASL unexpectedly forbids ParameterData of Loadtable to be LocalX or UserTerm */
            /*		Store(LoadTable("OEM1", "", "", RPST, Local2, m000(1)), DDB0) */
            /*	                         parse error, expecting `')'' ^ */
            DDB0 = LoadTable ("OEM1", "", "", RPST, Local2, 0x01)
            If (M001 (Arg0, DDB0, ".NLM"))
            {
                Return (0x01)
            }

            /* Check LoadTable(..., Method(), Named, LocalX) */

            \DTM2.PLDT = 0x00
            Local2 = 0x01
            /* Bug 288: iASL unexpectedly forbids ParameterData of Loadtable to be LocalX or UserTerm */
            /*		Store(LoadTable("OEM1", "", "", m000(RPST), PPST, Local2), DDB1) */
            /*	                              parse error, expecting `')'' ^ */
            DDB1 = LoadTable ("OEM1", "", "", M000 (RPST), PPST, 0x01)
            If (M001 (Arg0, DDB1, ".MNL"))
            {
                Return (0x01)
            }

            /* Check LoadTable(..., LocalX, Method(), Named) */

            \DTM2.PLDT = 0x00
            Local2 = RPST /* \DTM2.TST4.RPST */
            DDB2 = LoadTable ("OEM1", "", "", Local2, M000 (PPST), NVAL)
            If (M001 (Arg0, DDB2, ".LMN"))
            {
                Return (0x01)
            }

            /* Check LoadTable(..., ArgX, Derefof(Refof), Derefof(Index)) */

            \DTM2.PLDT = 0x00
            Local2 = RefOf (PPST)
            Store (POPT [0x02], Local3)
            DDB3 = M002 (RPST, Local2, Local3)
            If (M001 (Arg0, DDB3, ".ARI"))
            {
                Return (0x01)
            }

            /* Check LoadTable(..., Derefof(Index), ArgX, Derefof(Refof)) */

            \DTM2.PLDT = 0x00
            Local2 = RefOf (NVAL)
            Store (POPT [0x00], Local3)
            DDB4 = M003 (Local3, PPST, Local2)
            If (M001 (Arg0, DDB4, ".ARI"))
            {
                Return (0x01)
            }

            /* Check LoadTable(..., Derefof(Refof), Derefof(Index), ArgX) */

            \DTM2.PLDT = 0x00
            Local2 = RefOf (RPST)
            Store (POPT [0x01], Local3)
            DDB5 = M004 (Local2, Local3, NVAL)
            If (M001 (Arg0, DDB5, ".ARI"))
            {
                Return (0x01)
            }

            /* Check LoadTable(..., TermArg, TermArg, TermArg) */

            \DTM2.PLDT = 0x00
            Local2 = Concatenate ("term", RPST)
            Local2 = ToBuffer (Local2)
            Local3 = ToBuffer (PPST)
            Local4 = 0x03
            DDB6 = LoadTable ("OEM1", "", "", Mid (ToString (Local2, Ones), 0x04,
                0x05), ToString (M000 (Local3), Ones),                     /* Bug 288: iASL unexpectedly forbids ParameterData of Loadtable to be LocalX or UserTerm */
                    /*				Subtract(m000(Local4), 2)), */
(0x03 - 0x02))
            If (M001 (Arg0, DDB6, ".TTT"))
            {
                Return (0x01)
            }

            Return (0x00)
        }

        /* Namespace location to load the Definition Block is determined */
        /* by the RootPathString parameter of Loadtable */
        /* Arg1: RootPathString */
        Method (TST5, 2, Serialized)
        {
            Name (DDBH, 0x00)
            Concatenate (Arg0, "-tst5", Arg0)
            If (CondRefOf (\_XT2, Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\_XT2", 0x01)
                Return (0x01)
            }

            If (CondRefOf (\DTM2.DEVR._XT2, Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\DTM2.DEVR._XT2", 0x01)
                Return (0x01)
            }

            \DTM2.PLDT = 0x00
            DDBH = LoadTable ("OEM1", "", "", Arg1, PPST, 0x01)
            If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            Local1 = ObjectType (DDBH)
            If ((Local1 != C017))
            {
                /* DDB Handle */

                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local1, C017)
                Return (0x01)
            }

            If ((0x01 != \DTM2.PLDT))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, \DTM2.PLDT, 0x01)
            }

            If (CondRefOf (\_XT2, Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\_XT2", 0x01)
            }

            If (CondRefOf (\DTM2.DEVR._XT2, Local0)){}
            Else
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\DTM2.DEVR._XT2", 0x00)
            }

            Unload (DDBH)
            Debug = "OEM1 unloaded"
            If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            If (CondRefOf (\_XT2, Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\_XT2", 0x01)
            }

            If (CondRefOf (\DTM2.DEVR._XT2, Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\DTM2.DEVR._XT2", 0x01)
            }

            Return (0x00)
        }

        /* "\" is assumed to be Namespace location to load the Definition */
        /* Block if RootPathString parameter is not specified */
        Method (TST6, 1, Serialized)
        {
            Name (DDBH, 0x00)
            Concatenate (Arg0, "-tst6", Arg0)
            If (CondRefOf (\_XT2, Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\_XT2", 0x01)
                Return (0x01)
            }

            \DTM2.PLDT = 0x00
            DDBH = LoadTable ("OEM1", "", "", "", PPST, 0x01)
            If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            Local1 = ObjectType (DDBH)
            If ((Local1 != C017))
            {
                /* DDB Handle */

                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local1, C017)
                Return (0x01)
            }

            If ((0x01 != \DTM2.PLDT))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, \DTM2.PLDT, 0x01)
            }

            If (CondRefOf (\_XT2, Local0)){}
            Else
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\_XT2", 0x00)
            }

            Unload (DDBH)
            Debug = "OEM1 unloaded"
            If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            If (CondRefOf (\_XT2, Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\_XT2", 0x01)
            }

            Return (0x00)
        }

        /* If the first character of ParameterPathString is a backslash */
        /* or caret character, then the path of the object set up on success */
        /* is ParameterPathString. It is RootPathString.ParameterPathString */
        /* in any case. */
        Method (TST7, 1, Serialized)
        {
            Name (DDBH, 0x00)
            Name (PLDT, 0x00)
            Concatenate (Arg0, "-tst7", Arg0)
            DDBH = LoadTable ("OEM1", "", "", RPST, "^TST7.PLDT", 0x01)
            If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            Local1 = ObjectType (DDBH)
            If ((Local1 != C017))
            {
                /* DDB Handle */

                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local1, C017)
                Return (0x01)
            }

            If ((0x01 != PLDT))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, PLDT, 0x01)
            }

            Unload (DDBH)
            If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            PLDT = 0x00
            \DTM2.PLDT = 0x00
            DDBH = LoadTable ("OEM1", "", "", RPST, "PLDT", 0x01)
            If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            Local1 = ObjectType (DDBH)
            If ((Local1 != C017))
            {
                /* DDB Handle */

                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local1, C017)
                Return (0x01)
            }

            If ((0x00 != PLDT))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, PLDT, 0x00)
            }

            If ((0x01 != \DTM2.PLDT))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, \DTM2.PLDT, 0x01)
            }

            Unload (DDBH)
            If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            Return (0x00)
        }

        /* Exceptions when the SignatureString is greater than four characters, */
        /* the OEMIDString is greater than six characters, or the OEMTableID is */
        /* greater than eight characters */
        Method (TST8, 1, Serialized)
        {
            Name (DDBH, 0x00)
            Concatenate (Arg0, "-tst8", Arg0)
            \DTM2.PLDT = 0x00
            /* SignatureString is greater than four characters */

            If (Y287)
            {
                DDBH = LoadTable ("OEM1X", "", "", RPST, PPST, 0x01)
            }
            Else
            {
                LoadTable ("OEM1X", "", "", RPST, PPST, 0x01)
            }

            CH04 (Arg0, 0x00, 0x3D, Z176, __LINE__, 0x00, 0x00) /* AE_AML_STRING_LIMIT */
            If ((0x00 != \DTM2.PLDT))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, \DTM2.PLDT, 0x01)
                If (Y287)
                {
                    Return (0x01)
                }
                Else
                {
                    /* Cleanup */

                    Unload (DDBH)
                    \DTM2.PLDT = 0x00
                }
            }

            /* OEMIDString is greater than six characters */

            LoadTable ("OEM1", "IntelXX", "", RPST, PPST, 0x01)
            CH04 (Arg0, 0x00, 0x3D, Z176, __LINE__, 0x00, 0x00) /* AE_AML_STRING_LIMIT */
            If ((0x00 != \DTM2.PLDT))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, \DTM2.PLDT, 0x01)
                Return (0x01)
            }

            /* OEMTableID is greater than eight characters */

            LoadTable ("OEM1", "", "ManyXXXXX", RPST, PPST, 0x01)
            CH04 (Arg0, 0x00, 0x3D, Z176, __LINE__, 0x00, 0x00) /* AE_AML_STRING_LIMIT */
            If ((0x00 != \DTM2.PLDT))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, \DTM2.PLDT, 0x01)
                Return (0x01)
            }

            Return (0x00)
        }

        /* Exceptions when some DSDT or SSDT matching the LoadTable parameters */
        /* is already loaded (actually on initial loading of tables listed in XSDT) */
        Method (TST9, 1, NotSerialized)
        {
            Concatenate (Arg0, "-tst9", Arg0)
            \DTM2.PLDT = 0x00
            /* SignatureString is "DSDT" */

            LoadTable ("DSDT", "", "", RPST, PPST, 0x01)
            CH04 (Arg0, 0x00, 0x07, Z176, __LINE__, 0x00, 0x00)  /* AE_ALREADY_EXISTS */
            If ((0x00 != \DTM2.PLDT))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, \DTM2.PLDT, 0x01)
            }

            /* SignatureString is "SSDT" */

            LoadTable ("SSDT", "", "", RPST, PPST, 0x01)
            CH04 (Arg0, 0x00, 0x07, Z176, __LINE__, 0x00, 0x00)  /* AE_ALREADY_EXISTS */
            If ((0x00 != \DTM2.PLDT))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, \DTM2.PLDT, 0x01)
            }

            Return (0x00)
        }

        /* Exceptions when the matched table is already loaded */

        Method (TSTA, 1, Serialized)
        {
            Name (DDBH, 0x00)
            Concatenate (Arg0, "-tsta", Arg0)
            If (CondRefOf (\_XT2, Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\_XT2", 0x01)
                Return (0x01)
            }

            \DTM2.PLDT = 0x00
            DDBH = LoadTable ("OEM1", "", "", "\\", PPST, 0x01)
            If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            Local1 = ObjectType (DDBH)
            If ((Local1 != C017))
            {
                /* DDB Handle */

                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local1, C017)
                Return (0x01)
            }

            If ((0x01 != \DTM2.PLDT))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, \DTM2.PLDT, 0x01)
            }

            If (CondRefOf (\_XT2, Local0)){}
            Else
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\_XT2", 0x00)
            }

            \DTM2.PLDT = 0x00
            LoadTable ("OEM1", "", "", "\\DTM2", PPST, 0x01)
            CH04 (Arg0, 0x00, 0x07, Z176, __LINE__, 0x00, 0x00)  /* AE_ALREADY_EXISTS */
            If ((0x00 != \DTM2.PLDT))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, \DTM2.PLDT, 0x00)
            }

            If (CondRefOf (\DTM2._XT2, Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\DTM2._XT2", 0x01)
            }

            If (CondRefOf (\_XT2, Local0)){}
            Else
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\_XT2", 0x00)
            }

            Unload (DDBH)
            Debug = "OEM1 unloaded"
            If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            If (CondRefOf (\_XT2, Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\_XT2", 0x01)
            }

            Return (0x00)
        }

        /* Originated from ssdt4.asl: iasl -tc ssdt4.asl */

        Name (BUF4, Buffer (0x44)
        {
            /* 0000 */  0x53, 0x53, 0x44, 0x54, 0x44, 0x00, 0x00, 0x00,  // SSDTD...
            /* 0008 */  0x02, 0x08, 0x69, 0x41, 0x53, 0x4C, 0x54, 0x53,  // ..iASLTS
            /* 0010 */  0x4C, 0x54, 0x42, 0x4C, 0x30, 0x30, 0x30, 0x31,  // LTBL0001
            /* 0018 */  0x01, 0x00, 0x00, 0x00, 0x49, 0x4E, 0x54, 0x4C,  // ....INTL
            /* 0020 */  0x15, 0x12, 0x06, 0x20, 0x10, 0x1F, 0x5C, 0x00,  // ... ..\.
            /* 0028 */  0x08, 0x5F, 0x58, 0x54, 0x32, 0x0D, 0x61, 0x62,  // ._XT2.ab
            /* 0030 */  0x73, 0x6F, 0x6C, 0x75, 0x74, 0x65, 0x20, 0x6C,  // solute l
            /* 0038 */  0x6F, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x20,  // ocation
            /* 0040 */  0x6F, 0x62, 0x6A, 0x00                           // obj.
        })
        OperationRegion (IST4, SystemMemory, 0x0600, 0x44)
        Field (IST4, ByteAcc, NoLock, Preserve)
        {
            RFU4,   544
        }

        /* Exceptions when there already is an previously loaded Object */
        /* referred by the path in the Namespace */
        Method (TSTB, 1, Serialized)
        {
            Name (DDBH, 0x00)
            Concatenate (Arg0, "-tstb", Arg0)
            If (CondRefOf (\_XT2, Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\_XT2", 0x01)
                Return (0x01)
            }

            RFU4 = BUF4 /* \DTM2.BUF4 */
            Load (RFU4, DDBH) /* \DTM2.TSTB.DDBH */
            If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            Local1 = ObjectType (DDBH)
            If ((Local1 != C017))
            {
                /* DDB Handle */

                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local1, C017)
                Return (0x01)
            }

            If (CondRefOf (\_XT2, Local0)){}
            Else
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\_XT2", 0x00)
            }

            \DTM2.PLDT = 0x00
            LoadTable ("OEM1", "", "", "\\", PPST, 0x01)
            CH04 (Arg0, 0x00, 0x07, Z176, __LINE__, 0x00, 0x00)  /* AE_ALREADY_EXISTS */
            If ((0x00 != \DTM2.PLDT))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, \DTM2.PLDT, 0x00)
            }

            If (CondRefOf (\_XT2, Local0)){}
            Else
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\_XT2", 0x00)
            }

            Unload (DDBH)
            Debug = "SSDT unloaded"
            If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            If (CondRefOf (\_XT2, Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\_XT2", 0x01)
            }

            Return (0x00)
        }

        /* Exceptions when the object specified by the ParameterPathString */
        /* does not exist */
        Method (TSTC, 1, NotSerialized)
        {
            Concatenate (Arg0, "-tstc", Arg0)
            LoadTable ("DSDT", "", "", RPST, "\\DTM2.NULL", 0x01)
            CH04 (Arg0, 0x00, 0x05, Z176, __LINE__, 0x00, 0x00)  /* AE_NOT_FOUND */
            Return (0x00)
        }

        /* Exceptions when storing of data of the ParameterData data type */
        /* to the specified object is not allowed. */
        Method (TSTD, 1, NotSerialized)
        {
            Concatenate (Arg0, "-tstd", Arg0)
            \DTM2.PLDT = 0x00
            LoadTable ("OEM1", "", "", "\\", "\\DTM2.PLDT", \DTM2.DEVR)
            CH04 (Arg0, 0x00, 0x2F, Z176, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            If ((0x00 != \DTM2.PLDT))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, \DTM2.PLDT, 0x00)
            }

            If (CondRefOf (\_XT2, Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\_XT2", 0x01)
            }

            Return (0x00)
        }

        /* Implicit operand conversion of the parameters specified to be strings */

        Method (TSTE, 1, Serialized)
        {
            Name (DDBH, 0x02)
            Name (SOID, "")
            Name (STID, "")
            Name (RPST, "\\")
            Name (PPST, "DTM2.PLDT")
            Name (DSTR, "01234")
            Method (M000, 3, Serialized)
            {
                Name (DDBH, 0x02)
                \DTM2.PLDT = 0x00
                Concatenate (Arg0, "-m000.", Arg0)
                Concatenate (Arg0, Mid (DSTR, Arg2, 0x01), Arg0)
                Switch (ToInteger (Arg2))
                {
                    Case (0x00)
                    {
                        LoadTable (Arg1, SOID, STID, RPST, PPST, 0x01)
                        Return (CH04 (Arg0, 0x00, 0x25, Z176, __LINE__, 0x00, 0x00))/* AE_BAD_SIGNATURE */
                    }
                    Case (0x01)
                    {
                        DDBH = LoadTable (SOEM, Arg1, STID, RPST, PPST, 0x01)
                    }
                    Case (0x02)
                    {
                        DDBH = LoadTable (SOEM, SOID, Arg1, RPST, PPST, 0x01)
                    }
                    Case (0x03)
                    {
                        LoadTable (SOEM, SOID, STID, Arg1, PPST, 0x01)
                        Return (CH04 (Arg0, 0x00, 0x1E, Z176, __LINE__, 0x00, 0x00)) /* AE_BAD_PATHNAME */
                    }
                    Case (0x04)
                    {
                        LoadTable (SOEM, SOID, STID, RPST, Arg1, 0x01)
                        Return (CH04 (Arg0, 0x00, 0x1E, Z176, __LINE__, 0x00, 0x00)) /* AE_BAD_PATHNAME */
                    }

                }

                If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
                {
                    Return (0x01)
                }

                If ((0x00 != \DTM2.PLDT))
                {
                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, \DTM2.PLDT, 0x00)
                    Return (0x01)
                }

                Local5 = ObjectType (DDBH)
                If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
                {
                    Return (0x01)
                }

                If ((Local5 != C009))
                {
                    /* Integer */

                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local5, C009)
                    Return (0x01)
                }

                If ((0x00 != DDBH))
                {
                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, DDBH, 0x00)
                    Return (0x01)
                }

                Return (0x00)
            }

            Concatenate (Arg0, "-tste", Arg0)
            If (Y281)
            {
                SOID = ^SOID /* \DTM2.SOID */
                STID = ^STID /* \DTM2.STID */
            }

            /* Buffer to String implicit conversion, only check that then */
            /* no exception occurs. Actually due to the conversion rule */
            /* resulting strings will not match the table fields */
            ToBuffer (SOEM, Local0)
            ToBuffer (SOID, Local1)
            ToBuffer (STID, Local2)
            ToBuffer (RPST, Local3)
            ToBuffer (PPST, Local4)
            If (M000 (Arg0, Local0, 0x00))
            {
                Return (0x01)
            }

            If (M000 (Arg0, Local1, 0x01))
            {
                Return (0x01)
            }

            If (M000 (Arg0, Local2, 0x02))
            {
                Return (0x01)
            }

            If (M000 (Arg0, Local3, 0x03))
            {
                Return (0x01)
            }

            If (M000 (Arg0, Local4, 0x04))
            {
                Return (0x01)
            }

            /* Check consistency of the parameters */

            If ((ToBuffer (SOEM) != Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local0, ToBuffer (SOEM))
                Return (0x01)
            }

            If ((ToBuffer (SOID) != Local1))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local1, ToBuffer (SOID))
                Return (0x01)
            }

            If ((ToBuffer (STID) != Local2))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local2, ToBuffer (STID))
                Return (0x01)
            }

            If ((ToBuffer (RPST) != Local3))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local3, ToBuffer (RPST))
                Return (0x01)
            }

            If ((ToBuffer (PPST) != Local4))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local4, ToBuffer (PPST))
                Return (0x01)
            }

            /* Integer to String implicit conversion */

            ToInteger (Local0, Local0)
            ToInteger (Local1, Local1)
            ToInteger (Local2, Local2)
            ToInteger (Local3, Local3)
            ToInteger (Local4, Local4)
            /*if (m000(arg0, Local0, 0)) {return (1)} */
            /*if (m000(arg0, Local1, 1)) {return (1)} */
            /*if (m000(arg0, Local2, 2)) {return (1)} */
            If (M000 (Arg0, Local3, 0x03))
            {
                Return (0x01)
            }

            If (M000 (Arg0, Local4, 0x04))
            {
                Return (0x01)
            }

            /* Actual trivial Buffer to String implicit conversion */

            If (Y293)
            {
                If (CondRefOf (\_XT2, Local0))
                {
                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\_XT2", 0x01)
                    Return (0x01)
                }

                Local0 = 0x00
                Local1 = Buffer (Local0){}
                \DTM2.PLDT = 0x00
                DDBH = LoadTable (SOEM, Local1, Local1, RPST, PPST, 0x01)
                If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
                {
                    Return (0x01)
                }

                If ((0x01 != \DTM2.PLDT))
                {
                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, \DTM2.PLDT, 0x01)
                    Return (0x01)
                }

                If (CondRefOf (\_XT2, Local0)){}
                Else
                {
                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\_XT2", 0x01)
                    Return (0x01)
                }

                Unload (DDBH)
                If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
                {
                    Return (0x01)
                }

                If (CondRefOf (\_XT2, Local0))
                {
                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, "\\_XT2", 0x01)
                    Return (0x01)
                }
            }

            Return (0x00)
        }

        /* LoadTable returns 0 if some SSDT matching the LoadTable */
        /* parameters is originally not listed in XSDT */
        /*
         * This test should never happen in real ASL code. So it is removed.
         *
         * The Load operation will add a table to global table list, which is
         * the master list that can be find in XSDT.
         *
         * The Unload operation will just delete the namespace owned by the table,
         * release OwnerId and reset the table flag, but the table remains in
         * global table list.
         *
         * So, LoadTable after Load and UnLoad operation will cause exception.
         *
         * Nothing like this should happen in real ASL code. The BIOS writer
         * knows whether the table is in the XSDT or not.
         */
        /*
         Method(tstf, 1)
         {
         Name(DDBH, 0)
         Concatenate(arg0, "-tstf", arg0)
         if (CondRefof(\_XT2, Local0)) {
         err(arg0, z176, __LINE__, 0, 0, "\\_XT2", 1)
         return (1)
         }
         Store(BUF4, RFU4)
         Load(RFU4, DDBH)
         if (CH03(arg0, z176, 0x0f2, __LINE__, 0)) {
         return (1)
         }
         Store(ObjectType(DDBH), Local1)
         if (LNotEqual(Local1, c017)) { // DDB Handle
         err(arg0, z176, __LINE__, 0, 0, Local1, c017)
         return (1)
         }
         if (CondRefof(\_XT2, Local0)) {
         } else {
         err(arg0, z176, __LINE__, 0, 0, "\\_XT2", 0)
         }
         UnLoad(DDBH)
         Store("SSDT unloaded", Debug)
         if (CH03(arg0, z176, 0x0f5, __LINE__, 0)) {
         return (1)
         }
         if (CondRefof(\_XT2, Local0)) {
         err(arg0, z176, __LINE__, 0, 0, "\\_XT2", 1)
         return (1)
         }
         Store(0, \DTM2.PLDT)
         if (y289) {
         LoadTable("SSDT", "iASLTS", "LTBL0001", "\\", PPST, 1)
         } else {
         Store(LoadTable("SSDT", "iASLTS", "LTBL0001", "\\", PPST, 1), DDBH)
         }
         CH04(arg0, 0, 28, z176, __LINE__, 0, 0)	// AE_BAD_PARAMETER
         if (LNotEqual(0, \DTM2.PLDT)) {
         err(arg0, z176, __LINE__, 0, 0, \DTM2.PLDT, 0)
         }
         if (CondRefof(\_XT2, Local0)) {
         err(arg0, z176, __LINE__, 0, 0, "\\_XT2", 1)
         if (y289) {
         // Cleanup
         UnLoad(DDBH)
         }
         }
         return (0)
         }
         */
        /* AE_OWNER_ID_LIMIT exception when too many Tables loaded */
        Method (TSTG, 1, NotSerialized)
        {
            Concatenate (Arg0, "-tstg-\\DTM0", Arg0)
            \DTM0.TSTH (Arg0, 0x01)
        }

        /* Exceptions when the parameter of the Loadtable operator */
        /* is of incorrect types */
        Method (TSTH, 1, Serialized)
        {
            Name (DDB0, 0x00)
            Name (DDB1, 0x00)
            Name (BTYP, Buffer (0x10)
            {
                /* 0000 */  0x00, 0x01, 0x01, 0x01, 0x00, 0x01, 0x00, 0x00,  // ........
                /* 0008 */  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00   // ........
            })
            Method (M000, 4, NotSerialized)
            {
                Concatenate (Arg0, "-m000.", Arg0)
                Concatenate (Arg0, Arg1, Arg0)
                Local0 = ObjectType (Arg2)
                If ((Arg3 != Local0))
                {
                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local0, Arg3)
                    Return (0x01)
                }

                LoadTable (DerefOf (Arg2), "", "", "\\", "\\DTM2.PLDT", 0x01)
                CH04 (Arg0, 0x00, 0x2F, Z176, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
                Return (0x00)
            }

            Method (M001, 4, NotSerialized)
            {
                Concatenate (Arg0, "-m001.", Arg0)
                Concatenate (Arg0, Arg1, Arg0)
                Local0 = ObjectType (Arg2)
                If ((Arg3 != Local0))
                {
                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local0, Arg3)
                    Return (0x01)
                }

                LoadTable ("OEM1", DerefOf (Arg2), "", "\\", "\\DTM2.PLDT", 0x01)
                CH04 (Arg0, 0x00, 0x2F, Z176, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
                Return (0x00)
            }

            Method (M002, 4, NotSerialized)
            {
                Concatenate (Arg0, "-m002.", Arg0)
                Concatenate (Arg0, Arg1, Arg0)
                Local0 = ObjectType (Arg2)
                If ((Arg3 != Local0))
                {
                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local0, Arg3)
                    Return (0x01)
                }

                LoadTable ("OEM1", "", DerefOf (Arg2), "\\", "\\DTM2.PLDT", 0x01)
                CH04 (Arg0, 0x00, 0x2F, Z176, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
                Return (0x00)
            }

            Method (M003, 4, NotSerialized)
            {
                Concatenate (Arg0, "-m003.", Arg0)
                Concatenate (Arg0, Arg1, Arg0)
                Local0 = ObjectType (Arg2)
                If ((Arg3 != Local0))
                {
                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local0, Arg3)
                    Return (0x01)
                }

                LoadTable ("OEM1", "", "", DerefOf (Arg2), "\\DTM2.PLDT", 0x01)
                If (DerefOf (BTYP [Arg3]))
                {
                    CH04 (Arg0, 0x00, 0x1E, Z176, __LINE__, 0x00, 0x00) /* AE_BAD_PATHNAME */
                }
                Else
                {
                    CH04 (Arg0, 0x00, 0x2F, Z176, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
                }

                Return (0x00)
            }

            Method (M004, 4, NotSerialized)
            {
                Concatenate (Arg0, "-m004.", Arg0)
                Concatenate (Arg0, Arg1, Arg0)
                Local0 = ObjectType (Arg2)
                If ((Arg3 != Local0))
                {
                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local0, Arg3)
                    Return (0x01)
                }

                LoadTable ("OEM1", "", "", "\\", DerefOf (Arg2), 0x01)
                If (DerefOf (BTYP [Arg3]))
                {
                    CH04 (Arg0, 0x00, 0x1E, Z176, __LINE__, 0x00, 0x00) /* AE_BAD_PATHNAME */
                }
                Else
                {
                    CH04 (Arg0, 0x00, 0x2F, Z176, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
                }

                Return (0x00)
            }

            Concatenate (Arg0, "-tsth", Arg0)
            /* Load Auxiliry table */

            \DTM0.RFU3 = \DTM0.BUF3
            Load (\DTM0.RFU3, DDB0) /* \DTM2.TSTH.DDB0 */
            If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            /* Uninitialized */

            If (0x00)
            {
                Local1 = 0x00
            }

            Local0 = ObjectType (Local1)
            If ((C008 != Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local0, C008)
            }
            Else
            {
                LoadTable (Local1, "", "", "\\", "\\DTM2.PLDT", 0x01)
                If (SLCK)
                {
                    CH04 (Arg0, 0x00, 0x3D, Z176, __LINE__, 0x00, 0x00) /* AE_AML_STRING_LIMIT */
                }
                Else
                {
                    CH04 (Arg0, 0x00, 0x31, Z176, __LINE__, 0x00, 0x00) /* AE_AML_UNINITIALIZED_LOCAL */
                }

                LoadTable ("OEM1", Local1, "", "\\", "\\DTM2.PLDT", 0x01)
                If (SLCK)
                {
                    CH04 (Arg0, 0x00, 0x3D, Z176, __LINE__, 0x00, 0x00) /* AE_AML_STRING_LIMIT */
                }
                Else
                {
                    CH04 (Arg0, 0x00, 0x31, Z176, __LINE__, 0x00, 0x00) /* AE_AML_UNINITIALIZED_LOCAL */
                }

                LoadTable ("OEM1", "", Local1, "\\", "\\DTM2.PLDT", 0x01)
                If (SLCK)
                {
                    /* ACPI_OEM_TABLE_ID_SIZE should be less than 8. */
                    /* The size of the "Integer" converted from "Any" is ISZ0*2. */
                    If ((ISZ0 <= 0x04))
                    {
                        CH03 (Arg0, Z176, __LINE__, 0x00, 0x00) /* No exception */
                    }
                    Else
                    {
                        CH04 (Arg0, 0x00, 0x3D, Z176, __LINE__, 0x00, 0x00) /* AE_AML_STRING_LIMIT */
                    }
                }
                Else
                {
                    CH04 (Arg0, 0x00, 0x31, Z176, __LINE__, 0x00, 0x00) /* AE_AML_UNINITIALIZED_LOCAL */
                }

                LoadTable ("OEM1", "", "", Local1, "\\DTM2.PLDT", 0x01)
                If (SLCK)
                {
                    CH04 (Arg0, 0x00, 0x1E, Z176, __LINE__, 0x00, 0x00) /* AE_BAD_PATHNAME */
                }
                Else
                {
                    CH04 (Arg0, 0x00, 0x31, Z176, __LINE__, 0x00, 0x00) /* AE_AML_UNINITIALIZED_LOCAL */
                }

                LoadTable ("OEM1", "", "", "\\", Local1, 0x01)
                If (SLCK)
                {
                    CH04 (Arg0, 0x00, 0x1E, Z176, __LINE__, 0x00, 0x00) /* AE_BAD_PATHNAME */
                }
                Else
                {
                    CH04 (Arg0, 0x00, 0x31, Z176, __LINE__, 0x00, 0x00) /* AE_AML_UNINITIALIZED_LOCAL */
                }
            }

            /* Integer */

            M003 (Arg0, "int", RefOf (\AUXD.INT0), C009)
            M004 (Arg0, "int", RefOf (\AUXD.INT0), C009)
            /* String */

            M003 (Arg0, "str", RefOf (\AUXD.STR0), C00A)
            M004 (Arg0, "str", RefOf (\AUXD.STR0), C00A)
            /* Buffer */

            M003 (Arg0, "buf", RefOf (\AUXD.BUF0), C00B)
            M004 (Arg0, "buf", RefOf (\AUXD.BUF0), C00B)
            /* Package */

            If (Y286)
            {
                M000 (Arg0, "pac", RefOf (\AUXD.PAC0), C00C)
                M001 (Arg0, "pac", RefOf (\AUXD.PAC0), C00C)
                M002 (Arg0, "pac", RefOf (\AUXD.PAC0), C00C)
                M003 (Arg0, "pac", RefOf (\AUXD.PAC0), C00C)
                M004 (Arg0, "pac", RefOf (\AUXD.PAC0), C00C)
            }

            LoadTable (\AUXD.PAC0, "", "", "\\", "\\DTM2.PLDT", 0x01)
            CH04 (Arg0, 0x00, 0x2F, Z176, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            LoadTable ("OEM1", \AUXD.PAC0, "", "\\", "\\DTM2.PLDT", 0x01)
            CH04 (Arg0, 0x00, 0x2F, Z176, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            LoadTable ("OEM1", "", \AUXD.PAC0, "\\", "\\DTM2.PLDT", 0x01)
            CH04 (Arg0, 0x00, 0x2F, Z176, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            LoadTable ("OEM1", "", "", \AUXD.PAC0, "\\DTM2.PLDT", 0x01)
            CH04 (Arg0, 0x00, 0x2F, Z176, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            LoadTable ("OEM1", "", "", "\\", \AUXD.PAC0, 0x01)
            CH04 (Arg0, 0x00, 0x2F, Z176, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            Local0 = ObjectType (\AUXD.PAC0)
            If ((C00C != Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local0, C00C)
            }

            /* Field Unit */

            M003 (Arg0, "flu", RefOf (\AUXD.FLU0), C00D)
            M004 (Arg0, "flu", RefOf (\AUXD.FLU0), C00D)
            /* Device */

            LoadTable (\AUXD.DEV0, "", "", "\\", "\\DTM2.PLDT", 0x01)
            CH04 (Arg0, 0x00, 0x2F, Z176, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            LoadTable ("OEM1", \AUXD.DEV0, "", "\\", "\\DTM2.PLDT", 0x01)
            CH04 (Arg0, 0x00, 0x2F, Z176, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            LoadTable ("OEM1", "", \AUXD.DEV0, "\\", "\\DTM2.PLDT", 0x01)
            CH04 (Arg0, 0x00, 0x2F, Z176, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            LoadTable ("OEM1", "", "", \AUXD.DEV0, "\\DTM2.PLDT", 0x01)
            CH04 (Arg0, 0x00, 0x2F, Z176, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            LoadTable ("OEM1", "", "", "\\", \AUXD.DEV0, 0x01)
            CH04 (Arg0, 0x00, 0x2F, Z176, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            Local0 = ObjectType (\AUXD.DEV0)
            If ((C00E != Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local0, C00E)
            }

            /* Event */

            M000 (Arg0, "evt", RefOf (\AUXD.EVE0), C00F)
            M001 (Arg0, "evt", RefOf (\AUXD.EVE0), C00F)
            M002 (Arg0, "evt", RefOf (\AUXD.EVE0), C00F)
            M003 (Arg0, "evt", RefOf (\AUXD.EVE0), C00F)
            M004 (Arg0, "evt", RefOf (\AUXD.EVE0), C00F)
            /* Method */

            M000 (Arg0, "met", RefOf (\AUXD.MMM0), C010)
            M001 (Arg0, "met", RefOf (\AUXD.MMM0), C010)
            M002 (Arg0, "met", RefOf (\AUXD.MMM0), C010)
            M003 (Arg0, "met", RefOf (\AUXD.MMM0), C010)
            M004 (Arg0, "met", RefOf (\AUXD.MMM0), C010)
            /* Mutex */

            M000 (Arg0, "mtx", RefOf (\AUXD.MTX0), C011)
            M001 (Arg0, "mtx", RefOf (\AUXD.MTX0), C011)
            M002 (Arg0, "mtx", RefOf (\AUXD.MTX0), C011)
            M003 (Arg0, "mtx", RefOf (\AUXD.MTX0), C011)
            M004 (Arg0, "mtx", RefOf (\AUXD.MTX0), C011)
            /* OpRegion */

            M000 (Arg0, "opr", RefOf (\AUXD.OPR0), C012)
            M001 (Arg0, "opr", RefOf (\AUXD.OPR0), C012)
            M002 (Arg0, "opr", RefOf (\AUXD.OPR0), C012)
            M003 (Arg0, "opr", RefOf (\AUXD.OPR0), C012)
            M004 (Arg0, "opr", RefOf (\AUXD.OPR0), C012)
            /* Power Resource */

            M000 (Arg0, "pwr", RefOf (\AUXD.PWR0), C013)
            M001 (Arg0, "pwr", RefOf (\AUXD.PWR0), C013)
            M002 (Arg0, "pwr", RefOf (\AUXD.PWR0), C013)
            M003 (Arg0, "pwr", RefOf (\AUXD.PWR0), C013)
            M004 (Arg0, "pwr", RefOf (\AUXD.PWR0), C013)
            /* Processor */

            M000 (Arg0, "cpu", RefOf (\AUXD.CPU0), C014)
            M001 (Arg0, "cpu", RefOf (\AUXD.CPU0), C014)
            M002 (Arg0, "cpu", RefOf (\AUXD.CPU0), C014)
            M003 (Arg0, "cpu", RefOf (\AUXD.CPU0), C014)
            M004 (Arg0, "cpu", RefOf (\AUXD.CPU0), C014)
            /* Thermal Zone */

            LoadTable (\AUXD.TZN0, "", "", "\\", "\\DTM2.PLDT", 0x01)
            CH04 (Arg0, 0x00, 0x2F, Z176, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            LoadTable ("OEM1", \AUXD.TZN0, "", "\\", "\\DTM2.PLDT", 0x01)
            CH04 (Arg0, 0x00, 0x2F, Z176, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            LoadTable ("OEM1", "", \AUXD.TZN0, "\\", "\\DTM2.PLDT", 0x01)
            CH04 (Arg0, 0x00, 0x2F, Z176, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            LoadTable ("OEM1", "", "", \AUXD.TZN0, "\\DTM2.PLDT", 0x01)
            CH04 (Arg0, 0x00, 0x2F, Z176, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            LoadTable ("OEM1", "", "", "\\", \AUXD.TZN0, 0x01)
            CH04 (Arg0, 0x00, 0x2F, Z176, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            Local0 = ObjectType (\AUXD.TZN0)
            If ((C015 != Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local0, C015)
            }

            /* Buffer Field */

            M003 (Arg0, "bfl", RefOf (\AUXD.BFL0), C016)
            M004 (Arg0, "bfl", RefOf (\AUXD.BFL0), C016)
            Unload (DDB0)
            CH03 (Arg0, Z176, __LINE__, 0x00, 0x00)
            Return (0x00)
        }

        /* Exceptions when the ParameterData parameter of the Loadtable operator */
        /* can not be saved into the Object referred by ParameterPathString */
        Method (TSTI, 1, Serialized)
        {
            Name (DDB0, 0x00)
            Name (DDB1, 0x00)
            Concatenate (Arg0, "-tsti", Arg0)
            /* Load Auxiliry table */

            \DTM0.RFU3 = \DTM0.BUF3
            Load (\DTM0.RFU3, DDB0) /* \DTM2.TSTI.DDB0 */
            If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            /* Uninitialized */

            If (0x00)
            {
                Local1 = 0x00
            }

            Local0 = ObjectType (Local1)
            If ((C008 != Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local0, C008)
            }
            /* Bug 288: iASL unexpectedly forbids ParameterData of Loadtable to be LocalX or UserTerm */
            /*
             LoadTable("OEM1", "", "", "\\", "\\DTM2.PLDT", Local1)
             if (SLCK) {
             CH04(arg0, 0, 47, z176, __LINE__, 0, 0) // AE_AML_OPERAND_TYPE
             } else {
             CH04(arg0, 0, 49, z176, __LINE__, 0, 0) // AE_AML_UNINITIALIZED_LOCAL
             }
             */
            Else
            {
            }

            /* Integer */

            Local0 = ObjectType (\DTM2.PLDT)
            If ((C009 != Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local0, C009)
                Return (0x01)
            }

            DDB1 = LoadTable ("OEM1", "", "", "\\", "\\DTM2.PLDT", \AUXD.INT0)
            If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            Local0 = ObjectType (\DTM2.PLDT)
            If ((C009 != Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local0, C009)
                Return (0x01)
            }

            If ((\DTM2.PLDT != \AUXD.INT0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, \DTM2.PLDT, \AUXD.INT0)
                Return (0x01)
            }

            Unload (DDB1)
            If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            Local0 = ObjectType (\AUXD.INT0)
            If ((C009 != Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local0, C009)
            }

            /* String */

            If (Y296)
            {
                Local0 = ObjectType (\DTM2.PLDT)
                If ((C009 != Local0))
                {
                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local0, C009)
                    Return (0x01)
                }

                DDB1 = LoadTable ("OEM1", "", "", "\\", "\\DTM2.PLDT", \AUXD.STR0)
                If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
                {
                    Return (0x01)
                }

                Local0 = ObjectType (\DTM2.PLDT)
                If ((C009 != Local0))
                {
                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local0, C009)
                    Return (0x01)
                }

                If ((\DTM2.PLDT != \AUXD.STR0))
                {
                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, \DTM2.PLDT, \AUXD.STR0)
                    Return (0x01)
                }

                Unload (DDB1)
                If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
                {
                    Return (0x01)
                }

                Local0 = ObjectType (\AUXD.STR0)
                If ((C00A != Local0))
                {
                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local0, C00A)
                }
            }

            /* Buffer */

            If (Y296)
            {
                Local0 = ObjectType (\DTM2.PLDT)
                If ((C009 != Local0))
                {
                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local0, C009)
                    Return (0x01)
                }

                DDB1 = LoadTable ("OEM1", "", "", "\\", "\\DTM2.PLDT", \AUXD.BUF0)
                If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
                {
                    Return (0x01)
                }

                Local0 = ObjectType (\DTM2.PLDT)
                If ((C009 != Local0))
                {
                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local0, C009)
                    Return (0x01)
                }

                If ((\DTM2.PLDT != \AUXD.BUF0))
                {
                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, \DTM2.PLDT, \AUXD.BUF0)
                    Return (0x01)
                }

                Unload (DDB1)
                If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
                {
                    Return (0x01)
                }

                Local0 = ObjectType (\AUXD.BUF0)
                If ((C00B != Local0))
                {
                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local0, C00B)
                }
            }

            /* Package */

            LoadTable ("OEM1", "", "", "\\", "\\DTM2.PLDT", \AUXD.PAC0)
            CH04 (Arg0, 0x00, 0x2F, Z176, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            Local0 = ObjectType (\AUXD.PAC0)
            If ((C00C != Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local0, C00C)
            }

            /* Field Unit */

            If (Y296)
            {
                Local0 = ObjectType (\DTM2.PLDT)
                If ((C009 != Local0))
                {
                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local0, C009)
                    Return (0x01)
                }

                DDB1 = LoadTable ("OEM1", "", "", "\\", "\\DTM2.PLDT", \AUXD.FLU0)
                If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
                {
                    Return (0x01)
                }

                Local0 = ObjectType (\DTM2.PLDT)
                If ((C009 != Local0))
                {
                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local0, C009)
                    Return (0x01)
                }

                If ((\DTM2.PLDT != \AUXD.FLU0))
                {
                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, \DTM2.PLDT, \AUXD.FLU0)
                    Return (0x01)
                }

                Unload (DDB1)
                If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
                {
                    Return (0x01)
                }

                Local0 = ObjectType (\AUXD.FLU0)
                If ((C00D != Local0))
                {
                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local0, C00D)
                }
            }

            /* Device */

            LoadTable ("OEM1", "", "", "\\", "\\DTM2.PLDT", \AUXD.DEV0)
            CH04 (Arg0, 0x00, 0x2F, Z176, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            Local0 = ObjectType (\AUXD.DEV0)
            If ((C00E != Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local0, C00E)
            }

            /* Event */

            LoadTable ("OEM1", "", "", "\\", "\\DTM2.PLDT", \AUXD.EVE0)
            CH04 (Arg0, 0x00, 0x2F, Z176, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            Local0 = ObjectType (\AUXD.EVE0)
            If ((C00F != Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local0, C00F)
            }

            /* Method */

            If (Y288)
            {
                LoadTable ("OEM1", "", "", "\\", "\\DTM2.PLDT", \AUXD.MMM0)
                CH04 (Arg0, 0x00, 0x2F, Z176, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
                Local0 = ObjectType (\AUXD.MMM0)
                If ((C010 != Local0))
                {
                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local0, C010)
                }
            }

            /* Mutex */

            LoadTable ("OEM1", "", "", "\\", "\\DTM2.PLDT", \AUXD.MTX0)
            CH04 (Arg0, 0x00, 0x2F, Z176, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            Local0 = ObjectType (\AUXD.MTX0)
            If ((C011 != Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local0, C011)
            }

            /* OpRegion */

            LoadTable ("OEM1", "", "", "\\", "\\DTM2.PLDT", \AUXD.OPR0)
            CH04 (Arg0, 0x00, 0x2F, Z176, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            Local0 = ObjectType (\AUXD.OPR0)
            If ((C012 != Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local0, C012)
            }

            /* Power Resource */

            LoadTable ("OEM1", "", "", "\\", "\\DTM2.PLDT", \AUXD.PWR0)
            CH04 (Arg0, 0x00, 0x2F, Z176, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            Local0 = ObjectType (\AUXD.PWR0)
            If ((C013 != Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local0, C013)
            }

            /* Processor */

            LoadTable ("OEM1", "", "", "\\", "\\DTM2.PLDT", \AUXD.CPU0)
            CH04 (Arg0, 0x00, 0x2F, Z176, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            Local0 = ObjectType (\AUXD.CPU0)
            If ((C014 != Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local0, C014)
            }

            /* Thermal Zone */

            LoadTable ("OEM1", "", "", "\\", "\\DTM2.PLDT", \AUXD.TZN0)
            CH04 (Arg0, 0x00, 0x2F, Z176, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            Local0 = ObjectType (\AUXD.TZN0)
            If ((C015 != Local0))
            {
                ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local0, C015)
            }

            /* Buffer Field */

            If (Y296)
            {
                Local0 = ObjectType (\DTM2.PLDT)
                If ((C009 != Local0))
                {
                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local0, C009)
                    Return (0x01)
                }

                DDB1 = LoadTable ("OEM1", "", "", "\\", "\\DTM2.PLDT", \AUXD.BFL0)
                If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
                {
                    Return (0x01)
                }

                Local0 = ObjectType (\DTM2.PLDT)
                If ((C009 != Local0))
                {
                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local0, C009)
                    Return (0x01)
                }

                If ((\DTM2.PLDT != \AUXD.BFL0))
                {
                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, \DTM2.PLDT, \AUXD.BFL0)
                    Return (0x01)
                }

                Unload (DDB1)
                If (CH03 (Arg0, Z176, __LINE__, 0x00, 0x00))
                {
                    Return (0x01)
                }

                Local0 = ObjectType (\AUXD.BFL0)
                If ((C016 != Local0))
                {
                    ERR (Arg0, Z176, __LINE__, 0x00, 0x00, Local0, C016)
                }
            }

            Unload (DDB0)
            CH03 (Arg0, Z176, __LINE__, 0x00, 0x00)
            Return (0x00)
        }
    }

    Method (TLT0, 0, Serialized)
    {
        CH03 (__METHOD__, Z176, __LINE__, 0x00, 0x00)
        /* Simple Loadtable test */

        SRMT ("TLT0.tst0")
        \DTM2.TST0 (__METHOD__)
        CH03 (__METHOD__, Z176, __LINE__, 0x00, 0x00)
        /* All comparisons of Loadtable parameters are case sensitive, */
        /* if no table matches the specified parameters, then 0 is returned */
        SRMT ("TLT0.tst1")
        \DTM2.TST1 (__METHOD__)
        CH03 (__METHOD__, Z176, __LINE__, 0x00, 0x00)
        /* Any of the RootPathString, ParameterPathString, and ParameterData */
        /* parameters in LoadTable expression can be omitted */
        SRMT ("TLT0.tst2")
        \DTM2.TST2 (__METHOD__)
        CH03 (__METHOD__, Z176, __LINE__, 0x00, 0x00)
        /* Different sources of the String parameters: Named Objects, LocalX, */
        /* ArgX, elements of Packages, results of functions, any TermArg */
        SRMT ("TLT0.tst3")
        \DTM2.TST3 (__METHOD__)
        CH03 (__METHOD__, Z176, __LINE__, 0x00, 0x00)
        /* Different sources of the optional parameters (RootPathString, */
        /* ParameterPathString, and ParameterData): Named Objects, LocalX, */
        /* ArgX, elements of Packages, results of functions, any TermArg */
        SRMT ("TLT0.tst4")
        \DTM2.TST4 (__METHOD__)
        CH03 (__METHOD__, Z176, __LINE__, 0x00, 0x00)
        /* Namespace location to load the Definition Block is determined */
        /* by the RootPathString parameter of Loadtable */
        SRMT ("TLT0.tst5.0")
        \DTM2.TST5 (__METHOD__, "\\DTM2.DEVR")
        CH03 (__METHOD__, Z176, __LINE__, 0x00, 0x00)
        /* The RootPathString value is evaluated using normal scoping rules, */
        /* assuming that the scope of the LoadTable operator is the current */
        /* scope */
        SRMT ("TLT0.tst5.1")
        \DTM2.TST5 (__METHOD__, "^DEVR")
        CH03 (__METHOD__, Z176, __LINE__, 0x00, 0x00)
        /* "\" is assumed to be Namespace location to load the Definition */
        /* Block if RootPathString parameter is not specified */
        SRMT ("TLT0.tst6")
        \DTM2.TST6 (__METHOD__)
        CH03 (__METHOD__, Z176, __LINE__, 0x00, 0x00)
        /* If the first character of ParameterPathString is a backslash */
        /* or caret character, then the path of the object set up on success */
        /* is ParameterPathString. It is RootPathString.ParameterPathString */
        /* in any case. */
        SRMT ("TLT0.tst7")
        \DTM2.TST7 (__METHOD__)
        CH03 (__METHOD__, Z176, __LINE__, 0x00, 0x00)
        /* Implicit operand conversion of the parameters specified to be strings */

        SRMT ("TLT0.tste")
        \DTM2.TSTE (__METHOD__)
        CH03 (__METHOD__, Z176, __LINE__, 0x00, 0x00)
        /* LoadTable returns 0 if some SSDT matching the LoadTable */
        /* parameters is originally not listed in XSDT */
        /*SRMT("TLT0.tstf") */
        /*\DTM2.tstf(ts) */
        CH03 (__METHOD__, Z176, __LINE__, 0x00, 0x00)
    }

    /* Exceptional conditions */

    Method (TLT1, 0, Serialized)
    {
        /* Exceptions when the SignatureString is greater than four characters, */
        /* the OEMIDString is greater than six characters, or the OEMTableID is */
        /* greater than eight characters */
        SRMT ("TLT1.tst8")
        \DTM2.TST8 (__METHOD__)
        /* Exceptions when some DSDT or SSDT matching the LoadTable parameters */
        /* is already loaded (actually on initial loading of tables listed in XSDT) */
        SRMT ("TLT1.tst9")
        \DTM2.TST9 (__METHOD__)
        /* Exceptions when the matched table is already loaded */

        SRMT ("TLT1.tsta")
        \DTM2.TSTA (__METHOD__)
        /* Exceptions when there already is an previously loaded Object */
        /* referred by the path in the Namespace */
        SRMT ("TLT1.tstb")
        \DTM2.TSTB (__METHOD__)
        /* Exceptions when the object specified by the ParameterPathString */
        /* does not exist */
        SRMT ("TLT1.tstc")
        \DTM2.TSTC (__METHOD__)
        /* Exceptions when storing of data of the ParameterData data type */
        /* to the specified object is not allowed. */
        SRMT ("TLT1.tstd")
        \DTM2.TSTD (__METHOD__)
        /* AE_OWNER_ID_LIMIT exception when too many Tables loaded */

        SRMT ("TLT1.tstg")
        If (Y294)
        {
            \DTM2.TSTG (__METHOD__)
        }
        Else
        {
            BLCK ()
        }

        /* Exceptions when the parameter of the Loadtable operator */
        /* is of incorrect types */
        SRMT ("TLT1.tsth")
        \DTM2.TSTH (__METHOD__)
        /* Exceptions when the ParameterData parameter of the Loadtable operator */
        /* can not be saved into the Object referred by ParameterPathString */
        SRMT ("TLT1.tsti")
        \DTM2.TSTI (__METHOD__)
    }
