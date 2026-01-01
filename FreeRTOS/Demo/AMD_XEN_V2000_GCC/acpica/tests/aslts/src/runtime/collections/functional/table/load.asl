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
     * Load ASL operator functionality
     */
    /*
     * This sub-test is intended to comprehensively verify
     * the Load ASL operator functionality.
     *
     * Performs a run-time load of a Definition Block.
     *
     *    17.5.67   Load (Load Definition Block)
     *    Syntax
     * Load (Object, DDBHandle)
     *
     * On testing the following issues should be covered:
     *
     * - loading SSDT from a SystemMemory OpRegion,
     *
     * - loading SSDT from a Region Field in a OpRegion of any type,
     *
     * - "namespace location to load the Definition Block is relative
     *   to the current namespace" scope,
     *
     * - loading a number of different SSDTs,
     *
     * - global and dynamic declarations of OpRegions and the appropriate
     *   _REG Methods invocation for the loaded SSDT,
     *
     * - global and dynamic declarations of OpRegions and Region Fields,
     *   containing the loaded SSDT,
     *
     * - an Object of any type can be used as the DDBHandle argument,
     *
     * - the DDBHandle argument of the Load operator becomes an Object
     *   of the DDBHandle type,
     *
     * - the DDBHandle Object returned from the Load operator can be used
     *   to unload the SSDT,
     *
     * - exceptional conditions caused by inappropriate data:
     *   = the Object argument does not refer to an operation region field
     *     or an operation region,
     *   = an OpRegion passed as the Object argument is not of SystemMemory type,
     *   = the table contained in an OpRegion (Field) is not an SSDT,
     *   = the length of the supplied SSDT is greater than the length of the
     *     respective OpRegion or Region Field,
     *   = the length of the supplied SSDT is less than the length the Header
     *   = the checksum of the supplied SSDT is invalid,
     *   = AE_OWNER_ID_LIMIT exception when too many Tables loaded,
     *   = the specified SSDT is already loaded,
     *   = there already is an previously loaded Object referred by the path
     *     in the Namespace.
     *
     * Can not be tested following issues:
     * - providing of the table referenced by Load to be "in memory marked by
     *   AddressRangeReserved or AddressRangeNVS",
     * - overriding the supplied SSDT with "a newer revision Definition Block
     *   of the same OEM Table ID" by the OS,
     * - loading a SSDT to be a synchronous operation ("the control methods
     *   defined in the Definition Block are not executed during load time")
     */
    /* Integer */
    External (\AUXD.INT0, UnknownObj)
    /* String */

    External (\AUXD.STR0, UnknownObj)
    /* Buffer */

    External (\AUXD.BUF0, UnknownObj)
    /* Package */

    External (\AUXD.PAC0, UnknownObj)
    /* Device */

    External (\AUXD.DEV0, UnknownObj)
    /* Event */

    External (\AUXD.EVE0, UnknownObj)
    /* Method */

    External (\AUXD.MMM0, UnknownObj)
    /* Mutex */

    External (\AUXD.MTX0, UnknownObj)
    /* Power Resource */

    External (\AUXD.PWR0, UnknownObj)
    /* Processor */

    External (\AUXD.CPU0, UnknownObj)
    /* Thermal Zone */

    External (\AUXD.TZN0, UnknownObj)
    /* Buffer Field */

    External (\AUXD.BFL0, UnknownObj)
    /* Field Unit */

    External (\AUXD.FLU0, UnknownObj)
    /* OpRegion */

    External (\AUXD.OPR0, UnknownObj)
    Name (Z174, 0xAE)
    Device (DTM0)
    {
        /* Originated from ssdt0.asl: iasl -tc ssdt0.asl */

        Name (BUF0, Buffer (0x34)
        {
            /* 0000 */  0x53, 0x53, 0x44, 0x54, 0x34, 0x00, 0x00, 0x00,  // SSDT4...
            /* 0008 */  0x02, 0x98, 0x49, 0x6E, 0x74, 0x65, 0x6C, 0x00,  // ..Intel.
            /* 0010 */  0x4D, 0x61, 0x6E, 0x79, 0x00, 0x00, 0x00, 0x00,  // Many....
            /* 0018 */  0x01, 0x00, 0x00, 0x00, 0x49, 0x4E, 0x54, 0x4C,  // ....INTL
            /* 0020 */  0x15, 0x12, 0x06, 0x20, 0x14, 0x0F, 0x5C, 0x53,  // ... ..\S
            /* 0028 */  0x53, 0x53, 0x30, 0x00, 0xA4, 0x0D, 0x5C, 0x53,  // SS0...\S
            /* 0030 */  0x53, 0x53, 0x30, 0x00                           // SS0.
        })
        Name (SNML, "0123456789ABCDEF")
        Name (NNML, 0x10) /* <= sizeof (SNML) */
        /* Take into account AE_OWNER_ID_LIMIT */

        Name (HI0M, 0x0100) /* <= (NNML * NNML) */
        Name (HI0P, Package (HI0M){})
        Name (HI0N, 0x00)
        Name (INIF, 0x00)
        OperationRegion (IST0, SystemMemory, 0x00, 0x34)
        Field (IST0, ByteAcc, NoLock, Preserve)
        {
            RFU0,   416
        }

        Field (IST0, ByteAcc, NoLock, Preserve)
        {
            SIG,    32,
            LENG,   32,
            REV,    8,
            SUM,    8,
            OID,    48,
            OTID,   64,
            OREV,   32,
            CID,    32,
            CREV,   32,
            Offset (0x27),
            SSNM,   32
        }

        /* components/utilities/utmisc.c AcpiUtGenerateChecksum() analog */

        Method (CHSM, 2, Serialized)
        {
            Name (LPN0, 0x00)
            Name (LPC0, 0x00)
            Local0 = 0x00 /* sum */
            LPN0 = Arg1
            LPC0 = 0x00
            While (LPN0)
            {
                Local1 = DerefOf (Arg0 [LPC0])
                Local0 += Local1
                Local0 %= 0x0100
                LPN0--
                LPC0++
            }

            Local0 = (0x00 - Local0)
            Local0 %= 0x0100
            Debug = "checksum"
            Debug = Local0
            Return (Local0)
        }

        /* Initializes multiple Tables Load test */

        Method (INIT, 0, NotSerialized)
        {
            Local0 = SizeOf (SNML)
            If ((NNML > Local0))
            {
                Debug = Concatenate ("INIT: test error, check NNML <= Sizeof(SNML):", ToDecimalString (Local0))
                Return (0x01)
            }

            Local0 *= Local0
            If ((HI0M > Local0))
            {
                Debug = Concatenate ("INIT: test error, check HI0M <= 0x", Local0)
                Return (0x01)
            }

            If (INIF)
            {
                Debug = "INIT: OpRegion has been initialized previously"
                Return (0x01)
            }

            RFU0 = BUF0 /* \DTM0.BUF0 */
            INIF = 0x01
            Debug = "INIT: OpRegion initialized with SSDT"
            Return (0x00)
        }

        /* Prepares and Loads the next Table of multiple Tables Load test */

        Method (LD, 0, Serialized)
        {
            If ((HI0N >= HI0M))
            {
                Debug = "LD: too many tables loaded"
                Return (0x01)
            }

            Local2 = (HI0N * 0x30)
            OperationRegion (IST0, SystemMemory, Local2, 0x34)
            Field (IST0, ByteAcc, NoLock, Preserve)
            {
                RFU0,   416
            }

            Field (IST0, ByteAcc, NoLock, Preserve)
            {
                SIG,    32,
                LENG,   32,
                REV,    8,
                SUM,    8,
                OID,    48,
                OTID,   64,
                OREV,   32,
                CID,    32,
                CREV,   32,
                Offset (0x27),
                SSNM,   32,
                Offset (0x2F),
                SSRT,   32
            }

            RFU0 = BUF0 /* \DTM0.BUF0 */
            /* Modify Revision field of SSDT */

            Store ((CREV + 0x01), CREV) /* \DTM0.LD__.CREV */
            /* Modify SSNM Object Name */

            Divide (HI0N, NNML, Local0, Local1)
            Local1 = DerefOf (SNML [Local1])
            Local1 <<= 0x10
            Local0 = DerefOf (SNML [Local0])
            Local0 <<= 0x18
            Local0 += Local1
            Local0 += 0x5353
            SSNM = Local0
            Debug = SSNM /* \DTM0.LD__.SSNM */
            /* Modify SSNM Method Return String */

            SSRT = Local0
            /* Recalculate and save CheckSum */

            Local0 = RFU0 /* \DTM0.LD__.RFU0 */
            Store ((SUM + CHSM (Local0, SizeOf (Local0))), SUM) /* \DTM0.LD__.SUM_ */
            Load (RFU0, HI0P [HI0N])
            HI0N++
            Debug = "LD: SSDT Loaded"
            Return (0x00)
        }

        /* UnLoads the last Table of multiple Tables Load test */

        Method (UNLD, 0, NotSerialized)
        {
            If ((HI0N == 0x00))
            {
                Debug = "UNLD: there are no SSDT loaded"
                Return (0x01)
            }

            HI0N--
            Unload (DerefOf (HI0P [HI0N]))
            Debug = "UNLD: SSDT UnLoaded"
            Return (0x00)
        }

        External (\SSS0, MethodObj)
        Name (HI0, 0x00)
        /* Simple Load test auxiliary method */
        /* Arg1: DDBH, 0 - Local Named, 1 - Global Named, */
        /*             2 - LocalX, 3 - element of Package */
        Method (M000, 2, Serialized)
        {
            Name (HI0, 0x00)
            Name (PHI0, Package (0x01){})
            Concatenate (Arg0, "-m000", Arg0)
            RFU0 = BUF0 /* \DTM0.BUF0 */
            If (CondRefOf (\SSS0, Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\SSS0", 0x01)
                Return (Zero)
            }

            /* Modify Revision field of SSDT */

            Store ((CREV + 0x01), CREV) /* \DTM0.CREV */
            /* Recalculate and save CheckSum */

            Local0 = RFU0 /* \DTM0.RFU0 */
            Store ((SUM + CHSM (Local0, SizeOf (Local0))), SUM) /* \DTM0.SUM_ */
            If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
            {
                Return (Zero)
            }

            /* Load operator execution */

            Switch (ToInteger (Arg1))
            {
                Case (0x00)
                {
                    Load (RFU0, HI0) /* \DTM0.M000.HI0_ */
                }
                Case (0x01)
                {
                    Load (RFU0, \DTM0.HI0)
                }
                Case (0x02)
                {
                    Load (RFU0, Local2)
                }
                Case (0x03)
                {
                    Load (RFU0, PHI0 [0x00])
                }
                Default
                {
                    Debug = "Unexpected parameter of the test"
                    ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\SSS0", 0x01)
                    Return (Zero)
                }

            }

            If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
            {
                Return (Zero)
            }

            Debug = "Table Loaded"
            /* Check DDBHandle ObjectType */

            Switch (ToInteger (Arg1))
            {
                Case (0x00)
                {
                    Local1 = ObjectType (HI0)
                }
                Case (0x01)
                {
                    Local1 = ObjectType (\DTM0.HI0)
                }
                Case (0x02)
                {
                    Local1 = ObjectType (Local2)
                }
                Case (0x03)
                {
                    Local1 = ObjectType (PHI0 [0x00])
                }

            }

            If ((Local1 != C017))
            {
                /* DDB Handle */

                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local1, C017)
            }

            /* Check the new Object appears */

            If (CondRefOf (\SSS0, Local0)){}
            Else
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\SSS0", 0x00)
            }

            Local1 = ObjectType (Local0)
            If ((Local1 != C010))
            {
                /* Method */

                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local1, C010)
            }
            Else
            {
                Local0 = \SSS0 ()
                If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x01))
                {
                    Return (Zero)
                }

                If (("\\SSS0" != Local0))
                {
                    ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local0, "\\SSS0")
                }
            }

            /* UnLoad operator execution */

            Switch (ToInteger (Arg1))
            {
                Case (0x00)
                {
                    Unload (HI0)
                }
                Case (0x01)
                {
                    Unload (\DTM0.HI0)
                }
                Case (0x02)
                {
                    Unload (Local2)
                }
                Case (0x03)
                {
                    Unload (DerefOf (PHI0 [0x00]))
                }

            }

            If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
            {
                Return (Zero)
            }

            Debug = "Table Unloaded"
            If (CondRefOf (\SSS0, Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\SSS0", 0x01)
            }

            Return (Zero)
        }

        /* Simple Load test auxiliary method for ArgX, part1 */
        /* Arg1 - reference to store the DDBHandle */
        Method (M001, 2, NotSerialized)
        {
            Concatenate (Arg0, "-m001", Arg0)
            RFU0 = BUF0 /* \DTM0.BUF0 */
            If (CondRefOf (\SSS0, Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\SSS0", 0x01)
                Return (0x01)
            }

            /* Modify Revision field of SSDT */

            Store ((CREV + 0x01), CREV) /* \DTM0.CREV */
            /* Recalculate and save CheckSum */

            Local0 = RFU0 /* \DTM0.RFU0 */
            Store ((SUM + CHSM (Local0, SizeOf (Local0))), SUM) /* \DTM0.SUM_ */
            If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            /* Load operator execution */

            Load (RFU0, Arg1)
            If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            Debug = "SSDT Loaded"
            Return (0x00)
        }

        /* Simple Load test auxiliary method for ArgX, part2 */
        /* Arg1 - DDBHandle */
        Method (M002, 2, NotSerialized)
        {
            Concatenate (Arg0, "-m002", Arg0)
            /* Check DDBHandle ObjectType */

            Local1 = ObjectType (Arg1)
            If ((Local1 != C017))
            {
                /* DDB Handle */

                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local1, C017)
            }

            /* Check the new Object appears */

            If (CondRefOf (\SSS0, Local0)){}
            Else
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\SSS0", 0x00)
            }

            Local1 = ObjectType (Local0)
            If ((Local1 != C010))
            {
                /* Method */

                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local1, C010)
            }
            Else
            {
                Local0 = \SSS0 ()
                If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x01))
                {
                    Return (Zero)
                }

                If (("\\SSS0" != Local0))
                {
                    ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local0, "\\SSS0")
                }
            }

            Unload (Arg1)
            If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
            {
                Return (Zero)
            }

            Debug = "SSDT Unloaded"
            If (CondRefOf (\SSS0, Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\SSS0", 0x01)
            }

            Return (Zero)
        }

        /* Loading SSDT from a SystemMemory OpRegion, */
        /* different targets for DDBHandle. */
        /* Check DDBHandle storing into different Object locations: */
        /* DDBHandle storing into Named Integer */
        Method (TST0, 1, NotSerialized)
        {
            Concatenate (Arg0, "-tst0", Arg0)
            /* Local Named Integer */

            M000 (Arg0, 0x00)
            /* Global Named Integer */

            M000 (Arg0, 0x01)
        }

        /* DDBHandle storing into LocalX */

        Method (TST1, 1, NotSerialized)
        {
            Concatenate (Arg0, "-tst1", Arg0)
            /* LocalX */

            M000 (Arg0, 0x02)
        }

        /* DDBHandle storing into Package element */

        Method (TST2, 1, NotSerialized)
        {
            Concatenate (Arg0, "-tst2", Arg0)
            /* Package element */
            /* Crash on copying the specific reference Object */
            If (Y261)
            {
                M000 (Arg0, 0x03)
            }
        }

        /* DDBHandle storing into an Object by Reference in Argx */

        Method (TST3, 1, Serialized)
        {
            Name (HI0, 0x00)
            Concatenate (Arg0, "-tst3", Arg0)
            /* Named by Reference in ArgX */

            If (M001 (Arg0, RefOf (HI0)))
            {
                Return (Zero)
            }

            M002 (Arg0, HI0)
            /* LocalX by Reference in ArgX */

            If (M001 (Arg0, RefOf (Local2)))
            {
                Return (Zero)
            }

            M002 (Arg0, Local2)
            /* Package element by Reference in ArgX */

            If (Y133)
            {
                Name (PHI0, Package (0x01)
                {
                    0x00
                })
                Store (PHI0 [0x00], Local0)
                If (M001 (Arg0, Local0))
                {
                    Return (Zero)
                }

                M002 (Arg0, DerefOf (Local0))
            }

            Return (Zero)
        }

        /* Combination of the OperationRegion operator arguments */

        OperationRegion (RGN0, SystemMemory, 0x00, 0x0201)
        OperationRegion (RGN1, SystemIO, 0x0200, 0x0203)
        OperationRegion (RGN2, PCI_Config, 0x0400, 0x0205)
        OperationRegion (RGN3, EmbeddedControl, 0x0600, 0x0207)
        OperationRegion (RGN4, SMBus, 0x0800, 0x0209)
        OperationRegion (RGN5, SystemCMOS, 0x0A00, 0x020B)
        OperationRegion (RGN6, PCIBARTarget, 0x0C00, 0x020D)
        /* UserDefRegionSpace */

        OperationRegion (RGN7, 0x80, 0x0D00, 0x0217)
        OperationRegion (RGN8, 0xCF, 0x0E00, 0x0218)
        OperationRegion (RGN9, 0xFF, 0x0F00, 0x0219)
        /* Loading SSDT from a Field of an OpRegion of any type, */
        /* different targets for DDBHandle. */
        /* Check DDBHandle storing into different Object locations: */
        /* Named Integer, LocalX, by Reference in Argx, etc. */
        /* m003(CallChain, Index, Region) */
        Method (M003, 3, NotSerialized)
        {
            Concatenate (Arg0, "-m003", Arg0)
            /* Auxiliary method: */
            /* Arg1 - choice of a target */
            /* Arg2 - OpRegion Object of a specified type */
            Method (M000, 3, Serialized)
            {
                Name (HI0, 0x00)
                Name (PHI0, Package (0x01){})
                OperationRegion (OPRM, 0xFF, 0x00, 0x1000)
                Concatenate (Arg0, "-m000", Arg0)
                CopyObject (Arg2, OPRM) /* \DTM0.M003.M000.OPRM */
                Field (OPRM, ByteAcc, NoLock, Preserve)
                {
                    RFU0,   416
                }

                Field (OPRM, ByteAcc, NoLock, Preserve)
                {
                    SIG,    32,
                    LENG,   32,
                    REV,    8,
                    SUM,    8,
                    OID,    48,
                    OTID,   64,
                    OREV,   32,
                    CID,    32,
                    CREV,   32,
                    Offset (0x27),
                    SSNM,   32
                }

                RFU0 = BUF0 /* \DTM0.BUF0 */
                If (CondRefOf (\SSS0, Local0))
                {
                    ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\SSS0", 0x01)
                    Return (Zero)
                }

                /* Modify Revision field of SSDT */

                Store ((CREV + 0x01), CREV) /* \DTM0.M003.M000.CREV */
                /* Recalculate and save CheckSum */

                Local0 = RFU0 /* \DTM0.M003.M000.RFU0 */
                Store ((SUM + CHSM (Local0, SizeOf (Local0))), SUM) /* \DTM0.M003.M000.SUM_ */
                If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
                {
                    Return (Zero)
                }

                /* Load operator execution */

                Switch (ToInteger (Arg1))
                {
                    Case (0x00)
                    {
                        Load (RFU0, HI0) /* \DTM0.M003.M000.HI0_ */
                    }
                    Case (0x01)
                    {
                        Load (RFU0, \DTM0.HI0)
                    }
                    Case (0x02)
                    {
                        Load (RFU0, Local2)
                    }
                    Case (0x03)
                    {
                        Load (RFU0, PHI0 [0x00])
                    }
                    Default
                    {
                        Debug = "Unexpected parameter of the test"
                        ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\SSS0", 0x01)
                        Return (Zero)
                    }

                }

                If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
                {
                    Return (Zero)
                }

                Debug = "SSDT Loaded"
                /* Check DDBHandle ObjectType */

                Switch (ToInteger (Arg1))
                {
                    Case (0x00)
                    {
                        Local1 = ObjectType (HI0)
                    }
                    Case (0x01)
                    {
                        Local1 = ObjectType (\DTM0.HI0)
                    }
                    Case (0x02)
                    {
                        Local1 = ObjectType (Local2)
                    }
                    Case (0x03)
                    {
                        Local1 = ObjectType (PHI0 [0x00])
                    }

                }

                If ((Local1 != C017))
                {
                    /* DDB Handle */

                    ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local1, C017)
                }

                /* Check the new Object appears */

                If (CondRefOf (\SSS0, Local0)){}
                Else
                {
                    ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\SSS0", 0x00)
                }

                Local1 = ObjectType (Local0)
                If ((Local1 != C010))
                {
                    /* Method */

                    ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local1, C010)
                }
                Else
                {
                    Local0 = \SSS0 ()
                    If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x01))
                    {
                        Return (Zero)
                    }

                    If (("\\SSS0" != Local0))
                    {
                        ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local0, "\\SSS0")
                    }
                }

                /* UnLoad operator execution */

                Switch (ToInteger (Arg1))
                {
                    Case (0x00)
                    {
                        Unload (HI0)
                    }
                    Case (0x01)
                    {
                        Unload (\DTM0.HI0)
                    }
                    Case (0x02)
                    {
                        Unload (Local2)
                    }
                    Case (0x03)
                    {
                        Unload (DerefOf (PHI0 [0x00]))
                    }

                }

                If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
                {
                    Return (Zero)
                }

                Debug = "SSDT Unloaded"
                If (CondRefOf (\SSS0, Local0))
                {
                    ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\SSS0", 0x01)
                }

                Return (Zero)
            }

            /* Auxiliary method for ArgX, part1 */
            /* Arg1 - reference to store the DDBHandle */
            /* Arg2 - OpRegion Object of a specified type */
            Method (M001, 3, Serialized)
            {
                OperationRegion (OPRM, 0xFF, 0x00, 0x1000)
                Concatenate (Arg0, "-m001", Arg0)
                CopyObject (Arg2, OPRM) /* \DTM0.M003.M001.OPRM */
                Field (OPRM, ByteAcc, NoLock, Preserve)
                {
                    RFU0,   416
                }

                Field (OPRM, ByteAcc, NoLock, Preserve)
                {
                    SIG,    32,
                    LENG,   32,
                    REV,    8,
                    SUM,    8,
                    OID,    48,
                    OTID,   64,
                    OREV,   32,
                    CID,    32,
                    CREV,   32,
                    Offset (0x27),
                    SSNM,   32
                }

                RFU0 = BUF0 /* \DTM0.BUF0 */
                If (CondRefOf (\SSS0, Local0))
                {
                    ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\SSS0", 0x01)
                    Return (0x01)
                }

                /* Modify Revision field of SSDT */

                Store ((CREV + 0x01), CREV) /* \DTM0.M003.M001.CREV */
                /* Recalculate and save CheckSum */

                Local0 = RFU0 /* \DTM0.M003.M001.RFU0 */
                Store ((SUM + CHSM (Local0, SizeOf (Local0))), SUM) /* \DTM0.M003.M001.SUM_ */
                If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
                {
                    Return (0x01)
                }

                /* Load operator execution */

                Load (RFU0, Arg1)
                If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
                {
                    Return (0x01)
                }

                Debug = "SSDT Loaded"
                Return (0x00)
            }

            /* Arg1 - OpRegion Object of a specified type */

            Method (M003, 2, Serialized)
            {
                Concatenate (Arg0, "-m003", Arg0)
                /* Local Named Integer */

                M000 (Arg0, 0x00, Arg1)
                /* Global Named Integer */

                M000 (Arg0, 0x01, Arg1)
                /* LocalX */

                M000 (Arg0, 0x02, Arg1)
                /* Package element */
                /* Crash on copying the specific reference Object */
                If (Y261)
                {
                    M000 (Arg0, 0x03, Arg1)
                }

                /* ArgX */

                If (M001 (Arg0, RefOf (Local2), Arg1))
                {
                    Return (Zero)
                }

                M002 (Arg0, Local2)
                /* Package element as ArgX */

                If (Y133)
                {
                    Name (PHI0, Package (0x01)
                    {
                        0x00
                    })
                    Store (PHI0 [0x00], Local0)
                    If (M001 (Arg0, Local0, Arg1))
                    {
                        Return (Zero)
                    }

                    M002 (Arg0, DerefOf (Local0))
                }

                Return (Zero)
            }

            /* Region type's Address Space Handler installed flags, */
            /* only those types' OpRegion can be tested. */
                            /* 0xff - UserDefRegionSpace */

Local2 = Buffer (0x0A)
                {
                    /* 0000 */  0x01, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x01,  // ........
                    /* 0008 */  0x00, 0x00                                       // ..
                }
            Local3 = DerefOf (Local2 [Arg1])
            If (Local3)
            {
                Concatenate (Arg0, "-0x", Local4)
                Concatenate (Local4, Mid (ToHexString (Arg1), (0x06 + (F64 * 0x08)
                    ), 0x02), Local4)
                Debug = Local4
                M003 (Local4, Arg2)
            }
            Else
            {
                Debug = "This Region type\'s AddrSpace Handler not installed"
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local2, Arg1)
            }
        }

        /* SystemMemory Region */

        Method (TST4, 1, NotSerialized)
        {
            Concatenate (Arg0, "-tst4", Arg0)
            M003 (Arg0, 0x00, RGN0)
        }

        /* SystemIO Region */

        Method (TST5, 1, NotSerialized)
        {
            Concatenate (Arg0, "-tst5", Arg0)
            M003 (Arg0, 0x01, RGN1)
        }

        /* EmbeddedControl Region */

        Method (TST6, 1, NotSerialized)
        {
            Concatenate (Arg0, "-tst6", Arg0)
            M003 (Arg0, 0x03, RGN3)
        }

        /* User defined Region */

        Method (TST7, 1, NotSerialized)
        {
            Concatenate (Arg0, "-tst7", Arg0)
            M003 (Arg0, 0x07, RGN7)
        }

        /* Note: We load the table objects relative to the root of the namespace. */
        /* This appears to go against the ACPI specification, but we do it for */
        /* compatibility with other ACPI implementations. */
        /* Originated from ssdt1.asl: iasl -tc ssdt1.asl */
        Name (BUF1, Buffer (0x5F)
        {
            /* 0000 */  0x53, 0x53, 0x44, 0x54, 0x5F, 0x00, 0x00, 0x00,  // SSDT_...
            /* 0008 */  0x02, 0x33, 0x49, 0x6E, 0x74, 0x65, 0x6C, 0x00,  // .3Intel.
            /* 0010 */  0x4D, 0x61, 0x6E, 0x79, 0x00, 0x00, 0x00, 0x00,  // Many....
            /* 0018 */  0x01, 0x00, 0x00, 0x00, 0x49, 0x4E, 0x54, 0x4C,  // ....INTL
            /* 0020 */  0x15, 0x12, 0x06, 0x20, 0x10, 0x1F, 0x5C, 0x00,  // ... ..\.
            /* 0028 */  0x08, 0x4E, 0x41, 0x42, 0x53, 0x0D, 0x61, 0x62,  // .NABS.ab
            /* 0030 */  0x73, 0x6F, 0x6C, 0x75, 0x74, 0x65, 0x20, 0x6C,  // solute l
            /* 0038 */  0x6F, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x20,  // ocation
            /* 0040 */  0x6F, 0x62, 0x6A, 0x00, 0x08, 0x4E, 0x43, 0x52,  // obj..NCR
            /* 0048 */  0x52, 0x0D, 0x63, 0x75, 0x72, 0x72, 0x65, 0x6E,  // R.curren
            /* 0050 */  0x74, 0x20, 0x6C, 0x6F, 0x63, 0x61, 0x74, 0x69,  // t locati
            /* 0058 */  0x6F, 0x6E, 0x20, 0x6F, 0x62, 0x6A, 0x00         // on obj.
        })
        OperationRegion (IST1, SystemMemory, 0x0100, 0x5F)
        Field (IST1, ByteAcc, NoLock, Preserve)
        {
            RFU1,   760
        }

        Method (TST8, 1, Serialized)
        {
            Name (DDBH, 0x00)
            Concatenate (Arg0, "-tst8", Arg0)
            /* Check absence */

            If (CondRefOf (NABS, Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "NABS", 0x01)
            }

            If (CondRefOf (NCRR, Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "NCRR", 0x01)
            }

            RFU1 = BUF1 /* \DTM0.BUF1 */
            Load (RFU1, DDBH) /* \DTM0.TST8.DDBH */
            Debug = "SSDT loaded"
            /* Check existence */

            If (CondRefOf (NABS, Local0))
            {
                If (("absolute location obj" != DerefOf (Local0)))
                {
                    ERR (Arg0, Z174, __LINE__, 0x00, 0x00, DerefOf (Local0), "absolute location obj")
                }
            }
            Else
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "NABS", 0x00)
            }

            If (CondRefOf (NCRR, Local0))
            {
                If (("current location obj" != DerefOf (Local0)))
                {
                    ERR (Arg0, Z174, __LINE__, 0x00, 0x00, DerefOf (Local0), "current location obj")
                }
            }
            Else
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "NCRR", 0x00)
            }

            /* Check location */

            If (CondRefOf (\NABS, Local0)){}
            Else
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "NABS", 0x00)
            }

            /*Note: We load the table objects relative to the root of the namespace. */

            If (CondRefOf (\NCRR, Local0)){}
            Else
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\NCRR", 0x01)
            }

            If (CondRefOf (\DTM0.NCRR, Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\DTM0.NCRR", 0x01)
            }

            If (CondRefOf (\DTM0.TST8.NCRR, Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\DTM0.TST8.NCRR", 0x00)
            }

            Unload (DDBH)
            Debug = "SSDT unloaded"
            /* Check absence */

            If (CondRefOf (NABS, Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "NABS", 0x01)
            }

            If (CondRefOf (NCRR, Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "NCRR", 0x01)
            }
        }

        /* Check global and dynamic declarations of OpRegions */
        /* and the appropriate _REG Methods invocation for the */
        /* loaded SSDT */
        /* Originated from ssdt2.asl: iasl -tc ssdt2.asl */
        Name (BUF2, Buffer (0x0117)
        {
            /* 0000 */  0x53, 0x53, 0x44, 0x54, 0x17, 0x01, 0x00, 0x00,  // SSDT....
            /* 0008 */  0x02, 0x7B, 0x49, 0x6E, 0x74, 0x65, 0x6C, 0x00,  // .{Intel.
            /* 0010 */  0x4D, 0x61, 0x6E, 0x79, 0x00, 0x00, 0x00, 0x00,  // Many....
            /* 0018 */  0x01, 0x00, 0x00, 0x00, 0x49, 0x4E, 0x54, 0x4C,  // ....INTL
            /* 0020 */  0x15, 0x12, 0x06, 0x20, 0x5B, 0x82, 0x41, 0x0F,  // ... [.A.
            /* 0028 */  0x41, 0x55, 0x58, 0x44, 0x5B, 0x80, 0x4F, 0x50,  // AUXD[.OP
            /* 0030 */  0x52, 0x30, 0x80, 0x0C, 0x00, 0x00, 0x00, 0x01,  // R0......
            /* 0038 */  0x0A, 0x04, 0x5B, 0x81, 0x0B, 0x4F, 0x50, 0x52,  // ..[..OPR
            /* 0040 */  0x30, 0x03, 0x52, 0x46, 0x30, 0x30, 0x20, 0x08,  // 0.RF00 .
            /* 0048 */  0x52, 0x45, 0x47, 0x43, 0x0C, 0xFF, 0xFF, 0xFF,  // REGC....
            /* 0050 */  0xFF, 0x08, 0x52, 0x45, 0x47, 0x50, 0x0A, 0x00,  // ..REGP..
            /* 0058 */  0x08, 0x52, 0x45, 0x47, 0x44, 0x0C, 0xFF, 0xFF,  // .REGD...
            /* 0060 */  0xFF, 0xFF, 0x08, 0x52, 0x45, 0x47, 0x52, 0x0A,  // ...REGR.
            /* 0068 */  0x00, 0x14, 0x33, 0x5F, 0x52, 0x45, 0x47, 0x02,  // ..3_REG.
            /* 0070 */  0x70, 0x0D, 0x5C, 0x41, 0x55, 0x58, 0x44, 0x2E,  // p.\AUXD.
            /* 0078 */  0x5F, 0x52, 0x45, 0x47, 0x3A, 0x00, 0x5B, 0x31,  // _REG:.[1
            /* 0080 */  0x70, 0x68, 0x5B, 0x31, 0x70, 0x69, 0x5B, 0x31,  // ph[1pi[1
            /* 0088 */  0xA0, 0x14, 0x93, 0x68, 0x0A, 0x80, 0x70, 0x52,  // ...h..pR
            /* 0090 */  0x45, 0x47, 0x43, 0x52, 0x45, 0x47, 0x50, 0x70,  // EGCREGPp
            /* 0098 */  0x69, 0x52, 0x45, 0x47, 0x43, 0x14, 0x49, 0x07,  // iREGC.I.
            /* 00A0 */  0x4D, 0x30, 0x30, 0x30, 0x00, 0x14, 0x38, 0x5F,  // M000..8_
            /* 00A8 */  0x52, 0x45, 0x47, 0x02, 0x70, 0x0D, 0x5C, 0x41,  // REG.p.\A
            /* 00B0 */  0x55, 0x58, 0x44, 0x2E, 0x4D, 0x30, 0x30, 0x30,  // UXD.M000
            /* 00B8 */  0x2E, 0x5F, 0x52, 0x45, 0x47, 0x3A, 0x00, 0x5B,  // ._REG:.[
            /* 00C0 */  0x31, 0x70, 0x68, 0x5B, 0x31, 0x70, 0x69, 0x5B,  // 1ph[1pi[
            /* 00C8 */  0x31, 0xA0, 0x14, 0x93, 0x68, 0x0A, 0x80, 0x70,  // 1...h..p
            /* 00D0 */  0x52, 0x45, 0x47, 0x44, 0x52, 0x45, 0x47, 0x52,  // REGDREGR
            /* 00D8 */  0x70, 0x69, 0x52, 0x45, 0x47, 0x44, 0x5B, 0x80,  // piREGD[.
            /* 00E0 */  0x4F, 0x50, 0x52, 0x31, 0x80, 0x0C, 0x10, 0x00,  // OPR1....
            /* 00E8 */  0x00, 0x01, 0x0A, 0x04, 0x5B, 0x81, 0x0B, 0x4F,  // ....[..O
            /* 00F0 */  0x50, 0x52, 0x31, 0x03, 0x52, 0x46, 0x30, 0x31,  // PR1.RF01
            /* 00F8 */  0x20, 0x70, 0x0D, 0x5C, 0x41, 0x55, 0x58, 0x44,  //  p.\AUXD
            /* 0100 */  0x2E, 0x4D, 0x30, 0x30, 0x30, 0x3A, 0x00, 0x5B,  // .M000:.[
            /* 0108 */  0x31, 0x70, 0x52, 0x46, 0x30, 0x31, 0x5B, 0x31,  // 1pRF01[1
            /* 0110 */  0x70, 0x52, 0x45, 0x47, 0x52, 0x5B, 0x31         // pREGR[1
        })
        OperationRegion (IST2, SystemMemory, 0x0200, 0x0117)
        Field (IST2, ByteAcc, NoLock, Preserve)
        {
            RFU2,   2232
        }

        External (\AUXD.M000, MethodObj)
        Method (TST9, 1, Serialized)
        {
            Name (DDBH, 0x00)
            Concatenate (Arg0, "-tst9", Arg0)
            RFU2 = BUF2 /* \DTM0.BUF2 */
            If (CondRefOf (\AUXD, Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\AUXD", 0x01)
                Return (Zero)
            }

            If (CH03 (Arg0, 0x00, __LINE__, 0x00, 0x00))
            {
                Return (Zero)
            }

            Load (RFU2, DDBH) /* \DTM0.TST9.DDBH */
            If (CH03 (Arg0, 0x00, __LINE__, 0x00, 0x00))
            {
                Return (Zero)
            }

            If (CondRefOf (\AUXD, Local0)){}
            Else
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\AUXD", 0x00)
                Return (Zero)
            }

            Local1 = ObjectType (Local0)
            If ((Local1 != 0x06))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local1, 0x06)
                Return (Zero)
            }

            If (CondRefOf (\AUXD.REGC, Local0)){}
            Else
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\AUXD.REGC", 0x00)
                Return (Zero)
            }

            Local1 = DerefOf (Local0)
            If ((0x01 != Local1))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local1, 0x01)
            }

            If (CondRefOf (\AUXD.REGD, Local0)){}
            Else
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\AUXD.REGD", 0x00)
                Return (Zero)
            }

            Local1 = DerefOf (Local0)
            If ((0xFFFFFFFF != Local1))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local1, 0xFFFFFFFF)
            }
            ElseIf (CondRefOf (\AUXD.M000, Local2))
            {
                \AUXD.M000 ()
                Local1 = DerefOf (Local0)
                If ((0x01 != Local1))
                {
                    ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local1, 0x01)
                }
            }
            Else
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\AUXD.M000", 0x00)
            }

            Unload (DDBH)
            If (CondRefOf (\AUXD, Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\AUXD", 0x01)
            }

            Return (Zero)
        }

        /* Checks that only specified Tables objects present in the NS */

        Method (LDCH, 1, NotSerialized)
        {
            Method (MAUX, 0, NotSerialized)
            {
                Return ("MAUX")
            }

            Concatenate (Arg0, "-LDCH", Arg0)
            If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            /* Specify to check up to 3 successive \SSxx names */

            Local0 = 0x01
            If (HI0N)
            {
                Local1 = (HI0N - 0x01)
                If (Local1)
                {
                    Local1--
                }
            }
            Else
            {
                Local1 = 0x00
            }

            If (((Local1 + 0x01) < HI0M))
            {
                Local0++
                If (((Local1 + 0x02) < HI0M))
                {
                    Local0++
                }
            }

            While (Local0)
            {
                Divide (Local1, NNML, Local3, Local4)
                Local5 = "\\SSS0"
                Local5 [0x03] = DerefOf (SNML [Local4])
                Local5 [0x04] = DerefOf (SNML [Local3])
                Debug = Local5
                /* Access the next \SSxx Object */

                CopyObject (DerefOf (Local5), MAUX) /* \DTM0.LDCH.MAUX */
                If ((Local1 < HI0N))
                {
                    If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
                    {
                        Return (0x02)
                    }

                    Local2 = MAUX ()
                    If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
                    {
                        Return (0x03)
                    }

                    If ((Local5 != Local2))
                    {
                        ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local2, Local5)
                    }
                }
                ElseIf (CH04 (Arg0, 0x00, 0xFF, Z174, __LINE__, 0x00, 0x00))
                {
                    /* AE_NOT_FOUND */

                    Return (0x04)
                }

                Local1++
                Local0--
            }

            Return (0x00)
        }

        /* Loading a number of different SSDTs */
        /* Arg1: the number of SSDT to load */
        Method (TSTA, 2, NotSerialized)
        {
            Concatenate (Arg0, "-tsta", Arg0)
            If (INIT ())
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "INIT", 0x01)
                Return (0x01)
            }

            If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            Local0 = Arg1
            While (Local0)
            {
                If (LD ())
                {
                    ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "HI0N", HI0N)
                    Return (0x01)
                }

                If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
                {
                    Return (0x01)
                }

                Local0--
                If (LDCH (Arg0))
                {
                    ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "HI0N", HI0N)
                    Return (0x01)
                }
            }

            Local0 = Arg1
            While (Local0)
            {
                If (UNLD ())
                {
                    ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "HI0N", HI0N)
                    Return (0x01)
                }

                If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
                {
                    Return (0x01)
                }

                Local0--
                If (LDCH (Arg0))
                {
                    ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "HI0N", HI0N)
                    Return (0x01)
                }
            }

            Return (0x00)
        }

        /* Exceptions when the Object argument does not refer to */
        /* an operation region field or an operation region */
        /* Originated from ssdt3.asl: iasl -tc ssdt3.asl */
        Name (BUF3, Buffer (0x011D)
        {
            /* 0000 */  0x53, 0x53, 0x44, 0x54, 0x1D, 0x01, 0x00, 0x00,  // SSDT....
            /* 0008 */  0x02, 0x4F, 0x49, 0x6E, 0x74, 0x65, 0x6C, 0x00,  // .OIntel.
            /* 0010 */  0x4D, 0x61, 0x6E, 0x79, 0x00, 0x00, 0x00, 0x00,  // Many....
            /* 0018 */  0x01, 0x00, 0x00, 0x00, 0x49, 0x4E, 0x54, 0x4C,  // ....INTL
            /* 0020 */  0x31, 0x08, 0x16, 0x20, 0x5B, 0x82, 0x47, 0x0F,  // 1.. [.G.
            /* 0028 */  0x41, 0x55, 0x58, 0x44, 0x08, 0x49, 0x4E, 0x54,  // AUXD.INT
            /* 0030 */  0x30, 0x0E, 0x10, 0x32, 0x54, 0x76, 0x98, 0xBA,  // 0..2Tv..
            /* 0038 */  0xDC, 0xFE, 0x08, 0x53, 0x54, 0x52, 0x30, 0x0D,  // ...STR0.
            /* 0040 */  0x73, 0x6F, 0x75, 0x72, 0x63, 0x65, 0x20, 0x73,  // source s
            /* 0048 */  0x74, 0x72, 0x69, 0x6E, 0x67, 0x30, 0x00, 0x08,  // tring0..
            /* 0050 */  0x42, 0x55, 0x46, 0x30, 0x11, 0x0C, 0x0A, 0x09,  // BUF0....
            /* 0058 */  0x09, 0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02,  // ........
            /* 0060 */  0x01, 0x08, 0x50, 0x41, 0x43, 0x30, 0x12, 0x27,  // ..PAC0.'
            /* 0068 */  0x03, 0x0E, 0x1F, 0x32, 0x54, 0x76, 0x98, 0xBA,  // ...2Tv..
            /* 0070 */  0xDC, 0xFE, 0x0D, 0x74, 0x65, 0x73, 0x74, 0x20,  // ...test
            /* 0078 */  0x70, 0x61, 0x63, 0x6B, 0x61, 0x67, 0x65, 0x30,  // package0
            /* 0080 */  0x00, 0x11, 0x0C, 0x0A, 0x09, 0x13, 0x12, 0x11,  // ........
            /* 0088 */  0x10, 0x0F, 0x0E, 0x0D, 0x0C, 0x0B, 0x5B, 0x80,  // ......[.
            /* 0090 */  0x4F, 0x50, 0x52, 0x30, 0x00, 0x0C, 0x21, 0x43,  // OPR0..!C
            /* 0098 */  0x65, 0x07, 0x0A, 0x98, 0x5B, 0x81, 0x0B, 0x4F,  // e...[..O
            /* 00A0 */  0x50, 0x52, 0x30, 0x01, 0x46, 0x4C, 0x55, 0x30,  // PR0.FLU0
            /* 00A8 */  0x20, 0x5B, 0x82, 0x10, 0x44, 0x45, 0x56, 0x30,  //  [..DEV0
            /* 00B0 */  0x08, 0x53, 0x30, 0x30, 0x30, 0x0D, 0x44, 0x45,  // .S000.DE
            /* 00B8 */  0x56, 0x30, 0x00, 0x5B, 0x02, 0x45, 0x56, 0x45,  // V0.[.EVE
            /* 00C0 */  0x30, 0x14, 0x08, 0x4D, 0x4D, 0x4D, 0x30, 0x00,  // 0..MMM0.
            /* 00C8 */  0xA4, 0x00, 0x5B, 0x01, 0x4D, 0x54, 0x58, 0x30,  // ..[.MTX0
            /* 00D0 */  0x00, 0x5B, 0x84, 0x13, 0x50, 0x57, 0x52, 0x30,  // .[..PWR0
            /* 00D8 */  0x00, 0x00, 0x00, 0x08, 0x53, 0x30, 0x30, 0x30,  // ....S000
            /* 00E0 */  0x0D, 0x50, 0x57, 0x52, 0x30, 0x00, 0x5B, 0x83,  // .PWR0.[.
            /* 00E8 */  0x16, 0x43, 0x50, 0x55, 0x30, 0x00, 0xFF, 0xFF,  // .CPU0...
            /* 00F0 */  0xFF, 0xFF, 0x00, 0x08, 0x53, 0x30, 0x30, 0x30,  // ....S000
            /* 00F8 */  0x0D, 0x43, 0x50, 0x55, 0x30, 0x00, 0x5B, 0x85,  // .CPU0.[.
            /* 0100 */  0x10, 0x54, 0x5A, 0x4E, 0x30, 0x08, 0x53, 0x30,  // .TZN0.S0
            /* 0108 */  0x30, 0x30, 0x0D, 0x54, 0x5A, 0x4E, 0x30, 0x00,  // 00.TZN0.
            /* 0110 */  0x5B, 0x13, 0x42, 0x55, 0x46, 0x30, 0x00, 0x0A,  // [.BUF0..
            /* 0118 */  0x45, 0x42, 0x46, 0x4C, 0x30                     // EBFL0
        })
        OperationRegion (IST3, SystemMemory, 0x0400, 0x011F)
        Field (IST3, ByteAcc, NoLock, Preserve)
        {
            RFU3,   2296
        }

        Method (TSTB, 1, Serialized)
        {
            Name (DDB0, 0x00)
            Name (DDBH, 0x00)
            Concatenate (Arg0, "-tstb", Arg0)
            RFU3 = BUF3 /* \DTM0.BUF3 */
            Load (RFU3, DDB0) /* \DTM0.TSTB.DDB0 */
            If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            /* Uninitialized: it can not be applied to Load which */
            /* allows NameString only to be used as Object parameter */
            /* Integer */
            Load (\AUXD.INT0, DDBH) /* \DTM0.TSTB.DDBH */
            CH04 (Arg0, 0x00, 0x2F, Z174, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            Local0 = ObjectType (\AUXD.INT0)
            If ((C009 != Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local0, C009)
            }

            /* String */

            Load (\AUXD.STR0, DDBH) /* \DTM0.TSTB.DDBH */
            CH04 (Arg0, 0x00, 0x2F, Z174, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            Local0 = ObjectType (\AUXD.STR0)
            If ((C00A != Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local0, C00A)
            }

            /* Buffer */

            If (Y282)
            {
                /* TBD: LBZ480 update allows Buffer to be Source of Load */

                Load (\AUXD.BUF0, DDBH) /* \DTM0.TSTB.DDBH */
                CH04 (Arg0, 0x00, 0x2F, Z174, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
                Local0 = ObjectType (\AUXD.BUF0)
                If ((C00B != Local0))
                {
                    ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local0, C00B)
                }
            }

            /* Package */

            Load (\AUXD.PAC0, DDBH) /* \DTM0.TSTB.DDBH */
            CH04 (Arg0, 0x00, 0x2F, Z174, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            Local0 = ObjectType (\AUXD.PAC0)
            If ((C00C != Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local0, C00C)
            }

            /* Field Unit */
            /* Device */
            Load (\AUXD.DEV0, DDBH) /* \DTM0.TSTB.DDBH */
            CH04 (Arg0, 0x00, 0x2F, Z174, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            Local0 = ObjectType (\AUXD.DEV0)
            If ((C00E != Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local0, C00E)
            }

            /* Event */

            Load (\AUXD.EVE0, DDBH) /* \DTM0.TSTB.DDBH */
            CH04 (Arg0, 0x00, 0x2F, Z174, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            Local0 = ObjectType (\AUXD.EVE0)
            If ((C00F != Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local0, C00F)
            }

            /* Method */

            Load (\AUXD.MMM0, DDBH) /* \DTM0.TSTB.DDBH */
            CH04 (Arg0, 0x00, 0x2F, Z174, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            Local0 = ObjectType (\AUXD.MMM0)
            If ((C010 != Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local0, C010)
            }

            /* Mutex */

            Load (\AUXD.MTX0, DDBH) /* \DTM0.TSTB.DDBH */
            CH04 (Arg0, 0x00, 0x2F, Z174, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            Local0 = ObjectType (\AUXD.MTX0)
            If ((C011 != Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local0, C011)
            }

            /* OpRegion */
            /* Power Resource */
            Load (\AUXD.PWR0, DDBH) /* \DTM0.TSTB.DDBH */
            CH04 (Arg0, 0x00, 0x2F, Z174, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            Local0 = ObjectType (\AUXD.PWR0)
            If ((C013 != Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local0, C013)
            }

            /* Processor */

            Load (\AUXD.CPU0, DDBH) /* \DTM0.TSTB.DDBH */
            CH04 (Arg0, 0x00, 0x2F, Z174, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            Local0 = ObjectType (\AUXD.CPU0)
            If ((C014 != Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local0, C014)
            }

            /* Thermal Zone */

            Load (\AUXD.TZN0, DDBH) /* \DTM0.TSTB.DDBH */
            CH04 (Arg0, 0x00, 0x2F, Z174, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            Local0 = ObjectType (\AUXD.TZN0)
            If ((C015 != Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local0, C015)
            }

            /* Buffer Field */

            If (Y282)
            {
                /* TBD: LBZ480 update allows Buffer Field to be Source of Load */

                Load (\AUXD.BFL0, DDBH) /* \DTM0.TSTB.DDBH */
                CH04 (Arg0, 0x00, 0x2F, Z174, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
                Local0 = ObjectType (\AUXD.BFL0)
                If ((C016 != Local0))
                {
                    ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local0, C016)
                }
            }

            /* DDB Handle */

            Load (DDB0, DDBH) /* \DTM0.TSTB.DDBH */
            CH04 (Arg0, 0x00, 0x2F, Z174, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            Local0 = ObjectType (DDB0)
            If ((C017 != Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local0, C017)
            }

            Unload (DDB0)
            Return (0x00)
        }

        /* Exceptions when an OpRegion passed as the Object */
        /* parameter of Load is not of SystemMemory type */
        Method (TSTC, 1, Serialized)
        {
            Name (DDBH, 0x00)
            Concatenate (Arg0, "-tstc", Arg0)
            OperationRegion (RGN1, SystemIO, 0x0280, 0x0123)
            OperationRegion (RGN2, PCI_Config, 0x0480, 0x0125)
            OperationRegion (RGN3, EmbeddedControl, 0x0680, 0x0127)
            OperationRegion (RGN4, SMBus, 0x0880, 0x0109)
            OperationRegion (RGN5, SystemCMOS, 0x0A80, 0x012B)
            OperationRegion (RGN6, PCIBARTarget, 0x0C80, 0x012D)
            /* UserDefRegionSpace */

            OperationRegion (RGN7, 0x80, 0x0D80, 0x0137)
            OperationRegion (RGN8, 0xCF, 0x0E80, 0x0138)
            OperationRegion (RGN9, 0xFF, 0x0F80, 0x0139)
            If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            /* SystemIO */

            Load (RGN1, DDBH) /* \DTM0.TSTC.DDBH */
            CH04 (Arg0, 0x00, 0x2F, Z174, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            Local0 = ObjectType (RGN1)
            If ((C012 != Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local0, C012)
            }

            /* PCI_Config */

            Load (RGN2, DDBH) /* \DTM0.TSTC.DDBH */
            CH04 (Arg0, 0x00, 0x2F, Z174, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            Local0 = ObjectType (RGN2)
            If ((C012 != Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local0, C012)
            }

            /* EmbeddedControl */

            Load (RGN3, DDBH) /* \DTM0.TSTC.DDBH */
            CH04 (Arg0, 0x00, 0x2F, Z174, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            Local0 = ObjectType (RGN3)
            If ((C012 != Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local0, C012)
            }

            /* SMBus */

            Load (RGN4, DDBH) /* \DTM0.TSTC.DDBH */
            CH04 (Arg0, 0x00, 0x2F, Z174, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            Local0 = ObjectType (RGN4)
            If ((C012 != Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local0, C012)
            }

            /* SystemCMOS */

            Load (RGN5, DDBH) /* \DTM0.TSTC.DDBH */
            CH04 (Arg0, 0x00, 0x2F, Z174, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            Local0 = ObjectType (RGN5)
            If ((C012 != Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local0, C012)
            }

            /* PciBarTarget */

            Load (RGN6, DDBH) /* \DTM0.TSTC.DDBH */
            CH04 (Arg0, 0x00, 0x2F, Z174, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            Local0 = ObjectType (RGN6)
            If ((C012 != Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local0, C012)
            }

            /* UserDefRegionSpace 0x80 */

            Load (RGN7, DDBH) /* \DTM0.TSTC.DDBH */
            CH04 (Arg0, 0x00, 0x2F, Z174, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            Local0 = ObjectType (RGN7)
            If ((C012 != Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local0, C012)
            }

            /* UserDefRegionSpace 0xcf */

            Load (RGN8, DDBH) /* \DTM0.TSTC.DDBH */
            CH04 (Arg0, 0x00, 0x2F, Z174, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            Local0 = ObjectType (RGN8)
            If ((C012 != Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local0, C012)
            }

            /* UserDefRegionSpace 0xff */

            Load (RGN9, DDBH) /* \DTM0.TSTC.DDBH */
            CH04 (Arg0, 0x00, 0x2F, Z174, __LINE__, 0x00, 0x00) /* AE_AML_OPERAND_TYPE */
            Local0 = ObjectType (RGN9)
            If ((C012 != Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local0, C012)
            }

            Return (0x00)
        }

        /* Exceptions when the table contained in an OpRegion */
        /* (Field) is not an SSDT */
        Method (TSTD, 1, Serialized)
        {
            Name (HI0, 0x00)
            Concatenate (Arg0, "-tstd", Arg0)
            If (CondRefOf (\SSS0, Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\SSS0", 0x01)
                Return (0x01)
            }

            RFU0 = BUF0 /* \DTM0.BUF0 */
            /* Modify the Signature field of the Table Header */

            Local0 = SIG /* \DTM0.SIG_ */
            Local0++
            SIG = Local0
            /* Recalculate and save CheckSum */

            Local0 = RFU0 /* \DTM0.RFU0 */
            Store ((SUM + CHSM (Local0, SizeOf (Local0))), SUM) /* \DTM0.SUM_ */
            If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            /* Load operator execution, OpRegion case */

            If (Y290)
            {
                Load (IST0, HI0) /* \DTM0.TSTD.HI0_ */
                CH04 (Arg0, 0x00, 0x25, Z174, __LINE__, 0x00, 0x00) /* AE_BAD_SIGNATURE */
                If (CondRefOf (\SSS0, Local0))
                {
                    ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\SSS0", 0x01)
                    Return (0x01)
                }
            }

            /* Load operator execution, OpRegion Field case */

            Load (RFU0, HI0) /* \DTM0.TSTD.HI0_ */
            CH04 (Arg0, 0x00, 0x25, Z174, __LINE__, 0x00, 0x00) /* AE_BAD_SIGNATURE */
            If (CondRefOf (\SSS0, Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\SSS0", 0x01)
            }

            Return (0x00)
        }

        /* Exceptions when the length of the supplied SSDT is greater */
        /* than the length of the respective OpRegion or Region Field, */
        /* or less than the length of the Table Header */
        /* Arg1: 0 - the 'greater' case, 1 - the 'less' case */
        Method (TSTE, 2, Serialized)
        {
            Name (HI0, 0x00)
            Concatenate (Arg0, "-tste", Arg0)
            If (Arg1)
            {
                Concatenate (Arg0, ".less", Arg0)
            }

            If (CondRefOf (\SSS0, Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\SSS0", 0x01)
                Return (0x01)
            }

            RFU0 = BUF0 /* \DTM0.BUF0 */
            /* Modify the Length field of the Table Header */

            If (Arg1)
            {
                Local0 = 0x23
            }
            Else
            {
                Local0 = SizeOf (BUF0)
                Local0++
            }

            LENG = Local0
            /* Recalculate and save CheckSum */

            Local0 = RFU0 /* \DTM0.RFU0 */
            Store ((SUM + CHSM (Local0, SizeOf (Local0))), SUM) /* \DTM0.SUM_ */
            If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            /* Load operator execution, OpRegion case */

            If (Y290)
            {
                Load (IST0, HI0) /* \DTM0.TSTE.HI0_ */
                CH04 (Arg0, 0x00, 0x2A, Z174, __LINE__, 0x00, 0x00) /* AE_INVALID_TABLE_LENGTH */
                If (CondRefOf (\SSS0, Local0))
                {
                    ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\SSS0", 0x01)
                    /* CleanUp */

                    Unload (HI0)
                    If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
                    {
                        Return (0x01)
                    }

                    If (CondRefOf (\SSS0, Local0))
                    {
                        ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\SSS0", 0x01)
                        Return (0x01)
                    }
                }
            }

            /* Load operator execution, OpRegion Field case */

            Load (RFU0, HI0) /* \DTM0.TSTE.HI0_ */
            If (!Arg1)
            {
                /* If the table length in the header is larger than the buffer. */

                CH04 (Arg0, 0x00, 0x36, Z174, __LINE__, 0x00, 0x00) /* AE_AML_BUFFER_LIMIT */
            }
            Else
            {
                /* If the table length is smaller than an ACPI table header. */

                CH04 (Arg0, 0x00, 0x2A, Z174, __LINE__, 0x00, 0x00)    /* AE_INVALID_TABLE_LENGTH */
            }

            If (CondRefOf (\SSS0, Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\SSS0", 0x01)
                Unload (HI0)
                If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
                {
                    Return (0x01)
                }

                If (CondRefOf (\SSS0, Local0))
                {
                    ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\SSS0", 0x01)
                    Return (0x01)
                }
            }

            Return (0x00)
        }

        /* Exceptions when the checksum of the supplied SSDT is invalid */

        Method (TSTF, 1, Serialized)
        {
            Name (HI0, 0x00)
            Concatenate (Arg0, "-tstf", Arg0)
            If (CondRefOf (\SSS0, Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\SSS0", 0x01)
                Return (0x01)
            }

            RFU0 = BUF0 /* \DTM0.BUF0 */
            /* Recalculate and save CheckSum */

            Local0 = RFU0 /* \DTM0.RFU0 */
            Store ((SUM + CHSM (Local0, SizeOf (Local0))), SUM) /* \DTM0.SUM_ */
            /* Spoil the CheckSum */

            Store ((SUM + 0x01), SUM) /* \DTM0.SUM_ */
            If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            /* Load operator execution, OpRegion case */

            If (Y290)
            {
                Load (IST0, HI0) /* \DTM0.TSTF.HI0_ */
                CH04 (Arg0, 0x00, 0x27, Z174, __LINE__, 0x00, 0x00) /* AE_BAD_CHECKSUM */
                If (CondRefOf (\SSS0, Local0))
                {
                    ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\SSS0", 0x01)
                    /*Cleanup */

                    Unload (HI0)
                    If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
                    {
                        Return (0x01)
                    }

                    Store ((SUM + 0x01), SUM) /* \DTM0.SUM_ */
                }
            }

            /* Load operator execution, OpRegion Field case */

            Load (RFU0, HI0) /* \DTM0.TSTF.HI0_ */
            CH04 (Arg0, 0x00, 0x27, Z174, __LINE__, 0x00, 0x00) /* AE_BAD_CHECKSUM */
            If (CondRefOf (\SSS0, Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\SSS0", 0x01)
                /*Cleanup */

                Unload (HI0)
                If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
                {
                    Return (0x01)
                }

                If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
                {
                    Return (0x01)
                }
            }

            Return (0x00)
        }

        /* Object of any type (expect Field Units and Buffer Fields) */
        /* can be used as the DDBHandle argument */
        Method (TSTG, 1, Serialized)
        {
            Name (DDB0, 0x00)
            Name (DDB1, 0x00)
            Name (DDBH, 0x00)
            Method (M000, 4, NotSerialized)
            {
                Concatenate (Arg0, "-m000.", Arg0)
                Concatenate (Arg0, Arg1, Arg0)
                Local0 = ObjectType (Arg2)
                If ((Arg3 != Local0))
                {
                    ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local0, Arg3)
                    Return (0x01)
                }

                If (CondRefOf (\SSS0, Local0))
                {
                    ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\SSS0", 0x01)
                    Return (0x01)
                }

                Load (RFU0, Arg2)
                If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
                {
                    Return (0x01)
                }

                Local0 = ObjectType (Arg2)
                If ((C017 != Local0))
                {
                    ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local0, C017)
                }

                If (CondRefOf (\SSS0, Local0)){}
                Else
                {
                    ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\SSS0", 0x00)
                    Return (0x01)
                }

                Unload (DerefOf (Arg2))
                If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
                {
                    Return (0x01)
                }

                If (CondRefOf (\SSS0, Local0))
                {
                    ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\SSS0", 0x01)
                    Return (0x01)
                }

                Return (0x00)
            }

            Concatenate (Arg0, "-tstg", Arg0)
            /* Load Auxiliry table */

            RFU3 = BUF3 /* \DTM0.BUF3 */
            Load (RFU3, DDB0) /* \DTM0.TSTG.DDB0 */
            RFU0 = BUF0 /* \DTM0.BUF0 */
            /* Recalculate and save CheckSum */

            Local0 = RFU0 /* \DTM0.RFU0 */
            Store ((SUM + CHSM (Local0, SizeOf (Local0))), SUM) /* \DTM0.SUM_ */
            If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            /* Uninitialized */

            M000 (Arg0, "uni", RefOf (Local1), C008)
            /* Integer */

            M000 (Arg0, "int", RefOf (\AUXD.INT0), C009)
            /* String */

            M000 (Arg0, "str", RefOf (\AUXD.STR0), C00A)
            /* Buffer */

            M000 (Arg0, "buf", RefOf (\AUXD.BUF0), C00B)
            /* Writing NewObj to ArgX which is a RefOf(OldObj), should */
            /* result in RefOf(NewObj), but this is currently not */
            /* working. */
            If (Y260)
            {
                /* Package */

                M000 (Arg0, "pac", RefOf (\AUXD.PAC0), C00C)
                /* Field Unit */

                M000 (Arg0, "flu", RefOf (\AUXD.FLU0), C00D)
                /* Device */

                M000 (Arg0, "dev", RefOf (\AUXD.DEV0), C00E)
                /* Event */

                M000 (Arg0, "evt", RefOf (\AUXD.EVE0), C00F)
                /* Method */

                M000 (Arg0, "met", RefOf (\AUXD.MMM0), C010)
                /* Mutex */

                M000 (Arg0, "mtx", RefOf (\AUXD.MTX0), C011)
                /* OpRegion */

                M000 (Arg0, "opr", RefOf (\AUXD.OPR0), C012)
                /* Power Resource */

                M000 (Arg0, "pwr", RefOf (\AUXD.PWR0), C013)
                /* Processor */

                M000 (Arg0, "cpu", RefOf (\AUXD.CPU0), C014)
                /* Thermal Zone */

                M000 (Arg0, "tzn", RefOf (\AUXD.TZN0), C015)
                /* Buffer Field */

                M000 (Arg0, "bfl", RefOf (\AUXD.BFL0), C016)
                /* DDB Handle */

                CopyObject (DDB0, DDB1) /* \DTM0.TSTG.DDB1 */
                M000 (Arg0, "ddb", RefOf (DDB1), C017)
            }

            Unload (DDB0)
            CH03 (Arg0, Z174, __LINE__, 0x00, 0x00)
            Return (0x00)
        }

        /* AE_OWNER_ID_LIMIT exception when too many Tables loaded, */
        /* Arg1: 0 - Load case, 1 - LoadTable case */
        Method (TSTH, 2, Serialized)
        {
            Name (MAXT, 0xF6)
            Name (DDB1, 0x00)
            Name (DDB3, 0x00)
            Concatenate (Arg0, "-tsth", Arg0)
            If (INIT ())
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "INIT", 0x01)
                Return (0x01)
            }

            If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            RFU1 = BUF1 /* \DTM0.BUF1 */
            RFU3 = BUF3 /* \DTM0.BUF3 */
            Local0 = MAXT /* \DTM0.TSTH.MAXT */
            While (Local0)
            {
                Debug = HI0N /* \DTM0.HI0N */
                If (LD ())
                {
                    ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "HI0N", HI0N)
                    Return (0x01)
                }

                If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
                {
                    Return (0x01)
                }

                Local0--
            }

            /* Methods can not be called after the following Load */
            /* (OWNER_ID is exhausted) */
            Load (RFU1, DDB1) /* \DTM0.TSTH.DDB1 */
            /* The following Load should cause AE_OWNER_ID_LIMIT */

            If (Arg1)
            {
                LoadTable ("OEM1", "", "", "", "", Zero)
            }
            Else
            {
                Load (RFU3, DDB3) /* \DTM0.TSTH.DDB3 */
            }

            /* Further 1 Method can be called */

            Unload (DDB1)
            CH04 (Arg0, 0x00, 0x56, Z174, __LINE__, 0x00, 0x00) /* AE_OWNER_ID_LIMIT */
            Local0 = MAXT /* \DTM0.TSTH.MAXT */
            While (Local0)
            {
                If (UNLD ())
                {
                    ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "HI0N", HI0N)
                    Return (0x01)
                }

                If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
                {
                    Return (0x01)
                }

                Local0--
            }

            If (LDCH (0x00))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "HI0N", HI0N)
                Return (0x01)
            }

            Return (0x00)
        }

        /* Exception when SSDT specified as the Object parameter */
        /* of the Load operator is already loaded */
        Method (TSTI, 1, Serialized)
        {
            Name (HI0, 0x00)
            Name (HI1, 0x00)
            Concatenate (Arg0, "-tsti", Arg0)
            If (CondRefOf (\SSS0, Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\SSS0", 0x01)
                Return (0x01)
            }

            RFU0 = BUF0 /* \DTM0.BUF0 */
            /* Recalculate and save CheckSum */

            Local0 = RFU0 /* \DTM0.RFU0 */
            Store ((SUM + CHSM (Local0, SizeOf (Local0))), SUM) /* \DTM0.SUM_ */
            If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            /* Load operator execution */

            Load (RFU0, HI0) /* \DTM0.TSTI.HI0_ */
            If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            Local0 = ObjectType (HI0)
            If ((C017 != Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local0, C017)
            }

            If (CondRefOf (\SSS0, Local0)){}
            Else
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\SSS0", 0x00)
                Return (0x01)
            }

            Local1 = 0x05
            While (Local1)
            {
                /* Repeated Load operator execution */

                Load (RFU0, HI1) /* \DTM0.TSTI.HI1_ */
                CH04 (Arg0, 0x00, 0x07, Z174, __LINE__, 0x05, Local1) /* AE_ALREADY_EXISTS */
                Local0 = ObjectType (HI1)
                If ((C009 != Local0))
                {
                    ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local0, C009)
                }

                Local1--
            }

            Unload (HI0)
            If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            If (CondRefOf (\SSS0, Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\SSS0", 0x01)
            }

            Return (0x00)
        }

        /* Exception when there already is an previously created Object */
        /* referred by the namepath of the new Object in the Table loaded */
        Method (TSTJ, 1, Serialized)
        {
            Name (HI0, 0x00)
            Name (HI1, 0x00)
            Concatenate (Arg0, "-tstj", Arg0)
            If (CondRefOf (\SSS0, Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\SSS0", 0x01)
                Return (0x01)
            }

            ^RFU0 = BUF0 /* \DTM0.BUF0 */
            /* Recalculate and save CheckSum */

            Local0 = ^RFU0 /* \DTM0.RFU0 */
            Store ((^SUM + CHSM (Local0, SizeOf (Local0))), ^SUM) /* \DTM0.SUM_ */
            If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            /* Load operator execution */

            Load (^RFU0, HI0) /* \DTM0.TSTJ.HI0_ */
            If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            Local0 = ObjectType (HI0)
            If ((C017 != Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local0, C017)
            }

            If (CondRefOf (\SSS0, Local0)){}
            Else
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\SSS0", 0x00)
                Return (0x01)
            }

            /* Load another table, containing declaration of \SSS0 */

            OperationRegion (IST0, SystemMemory, 0x80000000, 0x34)
            Field (IST0, ByteAcc, NoLock, Preserve)
            {
                RFU0,   416
            }

            Field (IST0, ByteAcc, NoLock, Preserve)
            {
                SIG,    32,
                LENG,   32,
                REV,    8,
                SUM,    8,
                OID,    48,
                OTID,   64,
                OREV,   32,
                CID,    32,
                CREV,   32,
                Offset (0x27),
                SSNM,   32,
                Offset (0x2F),
                SSRT,   32
            }

            RFU0 = BUF0 /* \DTM0.BUF0 */
            /* Modify Revision field of SSDT */

            Store ((CREV + 0x01), CREV) /* \DTM0.TSTJ.CREV */
            /* Recalculate and save CheckSum */

            Local0 = RFU0 /* \DTM0.TSTJ.RFU0 */
            Store ((SUM + CHSM (Local0, SizeOf (Local0))), SUM) /* \DTM0.TSTJ.SUM_ */
            Local1 = 0x05
            While (Local1)
            {
                /* Any next Load */

                Load (RFU0, HI1) /* \DTM0.TSTJ.HI1_ */
                CH04 (Arg0, 0x00, 0x07, Z174, __LINE__, 0x05, Local1) /* AE_ALREADY_EXISTS */
                Local0 = ObjectType (HI1)
                If ((C009 != Local0))
                {
                    ERR (Arg0, Z174, __LINE__, 0x00, 0x00, Local0, C009)
                }

                Local1--
            }

            Unload (HI0)
            If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            If (CondRefOf (\SSS0, Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\SSS0", 0x01)
            }

            Return (0x00)
        }

        /* Originated from ssdt5.asl: iasl -tc ssdt5.asl */

        Name (BUF5, Buffer (0x92)
        {
            /* 0000 */  0x53, 0x53, 0x44, 0x54, 0x92, 0x00, 0x00, 0x00,  // SSDT....
            /* 0008 */  0x02, 0xBA, 0x69, 0x41, 0x53, 0x4C, 0x54, 0x53,  // ..iASLTS
            /* 0010 */  0x4C, 0x54, 0x42, 0x4C, 0x30, 0x30, 0x30, 0x35,  // LTBL0005
            /* 0018 */  0x01, 0x00, 0x00, 0x00, 0x49, 0x4E, 0x54, 0x4C,  // ....INTL
            /* 0020 */  0x31, 0x08, 0x16, 0x20, 0x08, 0x44, 0x44, 0x42,  // 1.. .DDB
            /* 0028 */  0x58, 0x00, 0x08, 0x42, 0x55, 0x46, 0x58, 0x11,  // X..BUFX.
            /* 0030 */  0x37, 0x0A, 0x34, 0x53, 0x53, 0x44, 0x54, 0x34,  // 7.4SSDT4
            /* 0038 */  0x00, 0x00, 0x00, 0x02, 0x98, 0x49, 0x6E, 0x74,  // .....Int
            /* 0040 */  0x65, 0x6C, 0x00, 0x4D, 0x61, 0x6E, 0x79, 0x00,  // el.Many.
            /* 0048 */  0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x49,  // .......I
            /* 0050 */  0x4E, 0x54, 0x4C, 0x15, 0x12, 0x06, 0x20, 0x14,  // NTL... .
            /* 0058 */  0x0F, 0x5C, 0x53, 0x53, 0x53, 0x30, 0x00, 0xA4,  // .\SSS0..
            /* 0060 */  0x0D, 0x5C, 0x53, 0x53, 0x53, 0x30, 0x00, 0x5B,  // .\SSS0.[
            /* 0068 */  0x80, 0x49, 0x53, 0x54, 0x58, 0x00, 0x00, 0x0A,  // .ISTX...
            /* 0070 */  0x34, 0x5B, 0x81, 0x0C, 0x49, 0x53, 0x54, 0x58,  // 4[..ISTX
            /* 0078 */  0x01, 0x52, 0x46, 0x55, 0x58, 0x40, 0x1A, 0x70,  // .RFUX@.p
            /* 0080 */  0x42, 0x55, 0x46, 0x58, 0x52, 0x46, 0x55, 0x58,  // BUFXRFUX
            /* 0088 */  0x5B, 0x20, 0x52, 0x46, 0x55, 0x58, 0x44, 0x44,  // [ RFUXDD
            /* 0090 */  0x42, 0x58                                       // BX
        })
        OperationRegion (IST5, SystemMemory, 0x0600, 0x92)
        Field (IST5, ByteAcc, NoLock, Preserve)
        {
            RFU5,   1168
        }

        /* DDB Handle */

        External (\DDBX, UnknownObj)

        /* Recursive Load in module level code */

        Method (TSTK, 1, Serialized)
        {
            Name (DDBH, 0x00)
            Concatenate (Arg0, "-tstk", Arg0)
            If (CondRefOf (\DDBX, Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\DDBX", 0x01)
                Return (Zero)
            }

            If (CondRefOf (\SSS0, Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\SSS0", 0x01)
                Return (Zero)
            }

            RFU5 = BUF5 /* \DTM0.BUF5 */
            Load (RFU5, DDBH) /* \DTM0.TSTK.DDBH */
            If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            If (CondRefOf (\DDBX, Local0)){}
            Else
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\DDBX", 0x01)
                Return (Zero)
            }

            If (CondRefOf (\SSS0, Local0)){}
            Else
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\SSS0", 0x01)
                Return (Zero)
            }

            Unload (DDBX)
            If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            If (CondRefOf (\SSS0, Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\SSS0", 0x01)
                Return (Zero)
            }

            Unload (DDBH)
            If (CH03 (Arg0, Z174, __LINE__, 0x00, 0x00))
            {
                Return (0x01)
            }

            If (CondRefOf (\DDBX, Local0))
            {
                ERR (Arg0, Z174, __LINE__, 0x00, 0x00, "\\DDBX", 0x01)
                Return (Zero)
            }
        }

        /* Load a table and check to see if PAC0 is initialized properly */
        Method (TSTL, 1, Serialized)
        {
            Concatenate (Arg0, "-tstl", Arg0)
            CH03 (Arg0, Z174, __LINE__, 0x00, 0x00)
            External (SS01, methodobj)

            /* iasl -ts ssdt6.asl */

            Name (BUF1, Buffer()
            {
                0x53,0x53,0x44,0x54,0x3E,0x00,0x00,0x00,  /* 00000000    "SSDT>..." */
                0x02,0x80,0x49,0x6E,0x74,0x65,0x6C,0x00,  /* 00000008    "..Intel." */
                0x5F,0x42,0x33,0x30,0x37,0x00,0x00,0x00,  /* 00000010    "_B307..." */
                0x01,0x00,0x00,0x00,0x49,0x4E,0x54,0x4C,  /* 00000018    "....INTL" */
                0x27,0x04,0x18,0x20,0x14,0x0B,0x53,0x53,  /* 00000020    "'.. ..SS" */
                0x30,0x31,0x00,0xA4,0x50,0x4B,0x47,0x31,  /* 00000028    "01..PKG1" */
                0x08,0x50,0x4B,0x47,0x31,0x12,0x08,0x04,  /* 00000030    ".PKG1..." */
                0x00,0x01,0x0A,0x02,0x0A,0x03             /* 00000038    "......"   */
            })
            Name (DDBH, 0x00)
            Load (BUF1, DDBH)
            Local0 = SS01()
            Local1 = sizeof (Local0)
            if (Local1 != 0x4)
            {
                ERR (Arg0, ZFFF, __LINE__, 0x00, 0x00, Local1, 0x4)
            }
            Unload (DDBH)
            CH03 (Arg0, Z174, __LINE__, 0x00, 0x00)
        }
    }

    Method (TLD0, 0, Serialized)
    {
        /* Loading SSDT from a SystemMemory OpRegion, */
        /* different targets for DDBHandle */
        CH03 (__METHOD__, Z174, __LINE__, 0x00, 0x00)
        /* Named Objects */

        SRMT ("TLD0.tst0")
        \DTM0.TST0 (__METHOD__)
        CH03 (__METHOD__, Z174, __LINE__, 0x00, 0x00)
        /* LocalX Object */

        SRMT ("TLD0.tst1")
        \DTM0.TST1 (__METHOD__)
        CH03 (__METHOD__, Z174, __LINE__, 0x00, 0x00)
        /* Package element */

        SRMT ("TLD0.tst2")
        \DTM0.TST2 (__METHOD__)
        CH03 (__METHOD__, Z174, __LINE__, 0x00, 0x00)
        /* By Reference in ArgX */

        SRMT ("TLD0.tst3")
        \DTM0.TST3 (__METHOD__)
        /* Loading SSDT from a Field of an OpRegion of any type, */
        /* different targets for DDBHandle */
        CH03 (__METHOD__, Z174, __LINE__, 0x00, 0x00)
        /* SystemMemory Region */

        SRMT ("TLD0.tst4")
        \DTM0.TST4 (__METHOD__)
        CH03 (__METHOD__, Z174, __LINE__, 0x00, 0x00)
        /* SystemIO Region */

        SRMT ("TLD0.tst5")
        \DTM0.TST5 (__METHOD__)
        CH03 (__METHOD__, Z174, __LINE__, 0x00, 0x00)
        /* EmbeddedControl Region */

        SRMT ("TLD0.tst6")
        \DTM0.TST6 (__METHOD__)
        CH03 (__METHOD__, Z174, __LINE__, 0x00, 0x00)
        /* User defined Region */

        SRMT ("TLD0.tst7")
        \DTM0.TST7 (__METHOD__)
        CH03 (__METHOD__, Z174, __LINE__, 0x00, 0x00)
        /* Check that "namespace location to load the Definition Block */
        /* is relative to the current namespace" scope, */
        SRMT ("TLD0.tst8")
        \DTM0.TST8 (__METHOD__)
        CH03 (__METHOD__, Z174, __LINE__, 0x00, 0x00)
        /* Check global and dynamic declarations of OpRegions */
        /* and the appropriate _REG Methods invocation for the */
        /* loaded SSDT */
        SRMT ("TLD0.tst9")
        \DTM0.TST9 (__METHOD__)
        CH03 (__METHOD__, Z174, __LINE__, 0x00, 0x00)
        /* Object of any type can be used as the DDBHandle argument */

        SRMT ("TLD0.tstg")
        \DTM0.TSTG (__METHOD__)
        CH03 (__METHOD__, Z174, __LINE__, 0x00, 0x00)
        /* Loading a number of different SSDTs */

        SRMT ("TLD0.tsta")
        If (Y261)
        {
            \DTM0.TSTA (__METHOD__, 0xF0)
        }
        Else
        {
            BLCK ()
        }

        CH03 (__METHOD__, Z174, __LINE__, 0x00, 0x00)
        /* Recursive Load in module level */

        SRMT ("TLD0.tstk")
        \DTM0.TSTK (__METHOD__)
        CH03 (__METHOD__, Z174, __LINE__, 0x00, 0x00)

        SRMT ("TLD0.tstl")
        \DTM0.TSTL (__METHOD__)
        CH03 (__METHOD__, Z174, __LINE__, 0x00, 0x00)
    }

    /* Exceptional conditions */

    Method (TLD1, 0, Serialized)
    {
        /* Exceptions when the Object argument does not refer to */
        /* an operation region field or an operation region */
        SRMT ("TLD1.tstb")
        \DTM0.TSTB (__METHOD__)
        /* Exceptions when the an OpRegion passed as the Object */
        /* parameter of Load is not of SystemMemory type */
        SRMT ("TLD1.tstc")
        \DTM0.TSTC (__METHOD__)
        /* Exceptions when the table contained in an OpRegion */
        /* (Field) is not an SSDT */
        SRMT ("TLD1.tstd")
        \DTM0.TSTD (__METHOD__)
        /* Exceptions when the length of the supplied SSDT is greater */
        /* than the length of the respective OpRegion or Region Field, */
        SRMT ("TLD1.tste.0")
        If (Y284)
        {
            \DTM0.TSTE (__METHOD__, 0x00)
        }
        Else
        {
            BLCK ()
        }

        /* Exceptions when the length of the supplied SSDT is */
        /* less than the length of the Table Header */
        SRMT ("TLD1.tste.1")
        \DTM0.TSTE (__METHOD__, 0x01)
        /* Exceptions when the checksum of the supplied SSDT is invalid */

        SRMT ("TLD1.tstf")
        \DTM0.TSTF (__METHOD__)
        /* AE_OWNER_ID_LIMIT exception when too many Tables loaded */

        SRMT ("TLD1.tsth")
        If (Y294)
        {
            \DTM0.TSTH (__METHOD__, 0x00)
        }
        Else
        {
            BLCK ()
        }

        /* Exception when SSDT specified as the Object parameter */
        /* of the Load operator is already loaded */
        SRMT ("TLD1.tsti")
        \DTM0.TSTI (__METHOD__)
        /* Exception when there already is an previously created Object */
        /* referred by the namepath of the new Object in the Table loaded */
        SRMT ("TLD1.tstj")
        \DTM0.TSTJ (__METHOD__)
    }
