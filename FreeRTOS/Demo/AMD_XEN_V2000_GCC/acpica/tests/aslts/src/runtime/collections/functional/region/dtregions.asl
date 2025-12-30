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
     * Data Table Region declarations
     */
    /*
     * On testing following issues should be covered:
     * - String objects can be used as DataTableRegion arguments,
     * - global and dynamic DataTableRegion declarations,
     * - check of the Table Length on access to appropriate Fields,
     * - any table referenced in XSDT can be accessed,
     * - computational data is allowed to be DataTableRegion arguments,
     * - possibility to write into appropriate Fields.
     *
     * Can not be tested following issues:
     * - providing of DataTableRegions to be "in memory marked by
     *   AddressRangeReserved or AddressRangeNVS".
     */
    Name (Z142, 0x8E)
    Device (DTR0)
    {
        DataTableRegion (DR00, "DSDT", "", "")
        DataTableRegion (DR01, "SSDT", "", "")
        /* This SSDT must be identical to SSDT1 in the AcpiExec utility */

        Name (SSDT, Buffer (0x3E)
        {
            /* 0000 */  0x53, 0x53, 0x44, 0x54, 0x3E, 0x00, 0x00, 0x00,  // SSDT>...
            /* 0008 */  0x02, 0x08, 0x49, 0x6E, 0x74, 0x65, 0x6C, 0x00,  // ..Intel.
            /* 0010 */  0x73, 0x73, 0x64, 0x74, 0x31, 0x00, 0x00, 0x00,  // ssdt1...
            /* 0018 */  0x01, 0x00, 0x00, 0x00, 0x49, 0x4E, 0x54, 0x4C,  // ....INTL
            /* 0020 */  0x20, 0x06, 0x12, 0x20, 0x14, 0x19, 0x5F, 0x54,  //  .. .._T
            /* 0028 */  0x39, 0x38, 0x01, 0x70, 0x0D, 0x53, 0x53, 0x44,  // 98.p.SSD
            /* 0030 */  0x54, 0x31, 0x20, 0x2D, 0x20, 0x5F, 0x54, 0x39,  // T1 - _T9
            /* 0038 */  0x38, 0x00, 0x5B, 0x31, 0xA4, 0x00               // 8.[1..
        })
        Name (NFLG, 0x02)   /* Number of turn on/off Flag values */
        Name (IRSK, 0x00)   /* Counter of the Invalid RSKs */
        Name (IFLG, 0x00)   /* Counter of the Invalid Flags */
        Name (VRSK, 0x00)   /* Counter of the Valid RSK 0x07 */
        Name (ERSK, 0x02)   /* Expected Counters of the Valid RSK */
        Name (VFLG,       /* Counters of the Valid Flags */Package (NFLG)
        {
            0x00,
            0x00
        })
        /* Specific DataTable Regions availability notification Method */
        /* \DTR0._REG(RegionSpaceKeyword, Flag) */
        OperationRegion (JUNK, SystemMemory, 0x2000, 0x0100)
        Method (_REG, 2, Serialized)  // _REG: Region Availability
        {
            Name (DBGF, 0x01)
            If (DBGF)
            {
                DNAM (Arg0, Arg1, "\\DTR0._REG")
            }

            /*
             * 0x7E is the SpaceID for DataTableRegions (subject to change
             * with new releases of ACPI specification -- because this
             * ID is an internal-ACPICA-only ID)
             */
            If ((Arg0 == 0x7E))
            {
                VRSK++
            }
            Else
            {
                IRSK++
            }

            If ((Arg1 < NFLG))
            {
                Local1 = VFLG [Arg1]
                Local2 = RefOf (Local1)
                DerefOf (Local2) = (DerefOf (Local1) + 0x01)
            }
            Else
            {
                IFLG++
            }
        }
    }

    /* Global DataTableRegions */

    Method (M7F0, 1, NotSerialized)
    {
        Concatenate (Arg0, "-m7f0", Arg0)
        \DTR0._REG (0x0101, 0x02)
        If ((\DTR0.IRSK != 0x01))
        {
            ERR (Arg0, Z142, __LINE__, 0x00, 0x00, \DTR0.IRSK, 0x01)
        }

        If ((\DTR0.IFLG != 0x01))
        {
            ERR (Arg0, Z142, __LINE__, 0x00, 0x00, \DTR0.IFLG, 0x01)
        }

        If ((\DTR0.VRSK != 0x02))
        {
            ERR (Arg0, Z142, __LINE__, 0x00, 0x00, \DTR0.VRSK, 0x02)
        }

        If ((DerefOf (\DTR0.VFLG [0x01]) != 0x02))
        {
            ERR (Arg0, Z142, __LINE__, 0x00, 0x00, DerefOf (\DTR0.VFLG [0x01]), 0x02)
        }
    }

    /* Dynamic DataTableRegions */
    /* m7f1(CallChain) */
    /* CallChain: String */
    Method (M7F1, 1, Serialized)
    {
        Name (NFLG, 0x02)   /* Number of turn on/off Flag values */
        Name (IRSK, 0x00)   /* Counter of the Invalid RSKs */
        Name (IFLG, 0x00)   /* Counter of the Invalid Flags */
        Name (VRSK, 0x00)   /* Counter of the Valid RSK 0x7E (DataTableRegion) */
        Name (ERSK, 0x02)   /* Expected Counters of the Valid RSK */
        Name (VFLG,       /* Counters of the Valid Flags */Package (NFLG)
        {
            0x00,
            0x00
        })
        /* Specific DataTable Regions availability notification Method */
        /* \m7f1._REG(RegionSpaceKeyword, Flag) */
        OperationRegion (JUNK, SystemMemory, 0x2000, 0x0100)
        Method (_REG, 2, Serialized)  // _REG: Region Availability
        {
            Name (DBGF, 0x01)
            If (DBGF)
            {
                DNAM (Arg0, Arg1, "\\m7f1._REG")
            }

            /* DataTableRegion is SpaceID 0x7E */

            If ((Arg0 == 0x7E))
            {
                VRSK++
            }
            Else
            {
                IRSK++
            }

            If ((Arg1 < NFLG))
            {
                Local1 = VFLG [Arg1]
                Local2 = RefOf (Local1)
                DerefOf (Local2) = (DerefOf (Local1) + 0x01)
            }
            Else
            {
                IFLG++
            }
        }

        Concatenate (Arg0, "-m7f1", Arg0)
        If ((VRSK != 0x00))
        {
            ERR (Arg0, Z142, __LINE__, 0x00, 0x00, VRSK, 0x00)
        }

        If ((DerefOf (VFLG [0x01]) != 0x00))
        {
            ERR (Arg0, Z142, __LINE__, 0x00, 0x00, DerefOf (VFLG [0x01]), 0x00)
        }

        DataTableRegion (DR00, "SSDT", "", "")
        If ((IRSK != 0x00))
        {
            ERR (Arg0, Z142, __LINE__, 0x00, 0x00, IRSK, 0x00)
        }

        If ((IFLG != 0x00))
        {
            ERR (Arg0, Z142, __LINE__, 0x00, 0x00, IFLG, 0x00)
        }

        _REG (0x0101, 0x02)
        If ((IRSK != 0x01))
        {
            ERR (Arg0, Z142, __LINE__, 0x00, 0x00, IRSK, 0x01)
        }

        If ((IFLG != 0x01))
        {
            ERR (Arg0, Z142, __LINE__, 0x00, 0x00, IFLG, 0x01)
        }

        If ((VRSK != 0x01))
        {
            ERR (Arg0, Z142, __LINE__, 0x00, 0x00, VRSK, 0x01)
        }

        If ((DerefOf (VFLG [0x01]) != 0x01))
        {
            ERR (Arg0, Z142, __LINE__, 0x00, 0x00, DerefOf (VFLG [0x01]), 0x01)
        }
    }

    /* DataTableRegion Lengths */
    /* m7f2(CallChain) */
    /* CallChain: String */
    Method (M7F2, 1, Serialized)
    {
        Concatenate (Arg0, "-m7f2", Arg0)
        Field (\DTR0.DR01, AnyAcc, NoLock, Preserve)
        {
            FU01,   496
        }

        /* 0x1F0 == length of SSDT */

        Local0 = RefOf (FU01)
        Local1 = RefOf (Local0)
        Local2 = DerefOf (Local0)
        CH03 (Arg0, Z142, __LINE__, 0x00, 0x00)
        Local3 = \DTR0.SSDT
        If ((Local2 != Local3))
        {
            ERR (Arg0, Z142, __LINE__, 0x00, 0x00, Local2, Local3)
        }
    }

    /* Check non-constant DataTableRegion *String arguments */
    /* m7f3(CallChain) */
    /* CallChain: String */
    Method (M7F3, 1, Serialized)
    {
        Name (S000, "SSDT")
        Name (S001, "")
        Name (S002, "")
        Method (M000, 1, Serialized)
        {
            DataTableRegion (DR00, "SSDT", "", "")
            Field (DR00, AnyAcc, NoLock, Preserve)
            {
                FU01,   496
            }

            /* 0x1F0 == length of SSDT */

            Local0 = FU01 /* \M7F3.M000.FU01 */
            Local1 = \DTR0.SSDT
            If ((Local0 != Local1))
            {
                ERR (Arg0, Z142, __LINE__, 0x00, 0x00, Local0, Local1)
            }
        }

        /* ArgX */

        Method (M001, 4, Serialized)
        {
            DataTableRegion (DR00, Arg1, Arg2, Arg3)
            Field (DR00, AnyAcc, NoLock, Preserve)
            {
                FU01,   496
            }

            /* 0x1F0 == length of SSDT */

            Local0 = FU01 /* \M7F3.M001.FU01 */
            Local1 = \DTR0.SSDT
            If ((Local0 != Local1))
            {
                ERR (Arg0, Z142, __LINE__, 0x00, 0x00, Local0, Local1)
            }
        }

        /* Named */

        Method (M002, 1, Serialized)
        {
            DataTableRegion (DR00, S000, S001, S002)
            Field (DR00, AnyAcc, NoLock, Preserve)
            {
                FU01,   496
            }

            /* 0x1F0 == length of SSDT */

            Local0 = FU01 /* \M7F3.M002.FU01 */
            Local1 = \DTR0.SSDT
            If ((Local0 != Local1))
            {
                ERR (Arg0, Z142, __LINE__, 0x00, 0x00, Local0, Local1)
            }
        }

        /* LocalX */

        Method (M003, 1, Serialized)
        {
            Local2 = S000 /* \M7F3.S000 */
            Local3 = S001 /* \M7F3.S001 */
            Local4 = S002 /* \M7F3.S002 */
            DataTableRegion (DR00, Local2, Local3, Local4)
            Field (DR00, AnyAcc, NoLock, Preserve)
            {
                FU01,   496
            }

            /* 0x1F0 == length of SSDT */

            Local0 = FU01 /* \M7F3.M003.FU01 */
            Local1 = \DTR0.SSDT
            If ((Local0 != Local1))
            {
                ERR (Arg0, Z142, __LINE__, 0x00, 0x00, Local0, Local1)
            }
        }

        /* Expression */

        Method (M004, 1, Serialized)
        {
            Local2 = "SS"
            Local3 = "DT"
            DataTableRegion (DR00, Concatenate (Local2, Local3), Mid (S000, 0x01, 0x00), S002)
            Field (DR00, AnyAcc, NoLock, Preserve)
            {
                FU01,   496
            }

            /* 0x1F0 == length of SSDT */

            Local0 = FU01 /* \M7F3.M004.FU01 */
            Local1 = \DTR0.SSDT
            If ((Local0 != Local1))
            {
                ERR (Arg0, Z142, __LINE__, 0x00, 0x00, Local0, Local1)
            }
        }

        Concatenate (Arg0, "-m7f1", Arg0)
        M000 (Arg0)
        M001 (Arg0, "SSDT", "", "")
        M002 (Arg0)
        M003 (Arg0)
        M004 (Arg0)
    }

    /* Check different Table signatures */
    /* m7f4(CallChain) */
    /* CallChain: String */
    Method (M7F4, 1, NotSerialized)
    {
        Method (M000, 3, Serialized)
        {
            DataTableRegion (DR00, Arg1, "", "")
            Field (DR00, AnyAcc, NoLock, Preserve)
            {
                FU00,   32
            }

            Local0 = ToString (FU00, 0x04)
            If ((Local0 != Arg1))
            {
                ERR (Arg0, Z142, __LINE__, 0x00, 0x00, Local0, Arg1)
            }
        }

        Concatenate (Arg0, "-m7f4", Arg0)
        M000 (Arg0, "DSDT", 0x1B)
        M000 (Arg0, "SSDT", 0x1C)
        /* no RSDT in simulator */
        /*m000(arg0, "RSDT", 29) */
        M000 (Arg0, "TEST", 0x1E)
        M000 (Arg0, "BAD!", 0x1F)
        M000 (Arg0, "FACP", 0x20)
        M000 (Arg0, "SSDT", 0x21)
        M000 (Arg0, "OEM1", 0x22)
    }

    Method (DRC0, 0, Serialized)
    {
        /* Global DataTableRegions */

        SRMT ("m7f0")
        M7F0 (__METHOD__)
        /* Dynamic DataTableRegions */

        SRMT ("m7f1")
        M7F1 (__METHOD__)
        /* DataTableRegion Lengths */

        SRMT ("m7f2")
        M7F2 (__METHOD__)
        /* Non-constant DataTableRegion *String arguments */

        SRMT ("m7f3")
        If (Y223)
        {
            M7F3 (__METHOD__)
        }
        Else
        {
            BLCK ()
        }

        /* Different Table signatures */

        SRMT ("m7f4")
        If (Y223)
        {
            M7F4 (__METHOD__)
        }
        Else
        {
            BLCK ()
        }
    }
