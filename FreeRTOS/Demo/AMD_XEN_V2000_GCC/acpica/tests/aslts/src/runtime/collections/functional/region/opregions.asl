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
     * Operation Region declarations
     */
    /*
     * On testing following issues should be covered:
     * - application of any allowed RegionSpace Keywords,
     * - Devices' _REG methods invocation during setup of Regions,
     * - global and dynamic Operation Region declarations,
     * - check of the Region Length on access to appropriate Fields,
     * - check that Region Offset and Length can be computational data.
     *
     * Can not be tested following issues:
     * - emulated Access to SystemCMOS, PciBarTarget, and UserDefRegionSpace
     *   (except 0x80) Operation Regions (there are no appropriate setup of them),
     * - Operation Region address range mapping to given Offset and Length,
     * - large values as Region Length,
     * - host OS providing of exclusive use of hardware registers in global
     *   Operation Region address range by ACPI control methods only.
     */
    Name (Z141, 0x8D)
    Name (NRSK, 0x0B)  /* Number of the specific RegionSpaceKeywords */
    Name (IRSK, 0x00)   /* Counter of the Invalid RSKs */
    Name (NFLG, 0x02)   /* Number of turn on/off Flag values */
    Name (IFLG, 0x00)   /* Counter of the Invalid Flags */
    Name (FRSK, 0x0101)   /* Some false RegionSpace Keyword */
    Name (PRSK, Package (NRSK)
    {
        0x0100,
        /* UserDefRegionSpace 0x80-0xFF: auxiliary */

        0x00,
        /* SystemMemory */

        0x01,
        /* SystemIO */

        0x02,
        /* PCI_Config */

        0x03,
        /* EmbeddedControl */

        0x04,
        /* SMBus */

        0x05,
        /* SystemCMOS */

        0x06,
        /* PciBarTarget */

        0x07,
        /* IPMI */

        0x08,
        /* GeneralPurposeIo */

        0x09
        /* GenericSerialBus */
    })
    /* DefaultAddressSpaces */

    Name (DRSK, Package (0x03)
    {
        0x00,
        /* SystemMemory */

        0x01,
        /* SystemIO */

        0x02
        /* PCI_Config */
    })
    Name (VRSK,       /* Counters of the Valid RSKs */Package (NRSK)
    {
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00
    })
    /* Expected Counters of the Valid RSKs */
    /* actually, not only default spaces are initialized */
    /* by ACPICA, but AcpiExec provided ones also, */
    /* from aeexec.c: */
    /*
     static ACPI_ADR_SPACE_TYPE  SpaceIdList[] =
     {
     ACPI_ADR_SPACE_EC,
     ACPI_ADR_SPACE_SMBUS,
     ACPI_ADR_SPACE_GSBUS,
     ACPI_ADR_SPACE_GPIO,
     ACPI_ADR_SPACE_PCI_BAR_TARGET,
     ACPI_ADR_SPACE_IPMI,
     ACPI_ADR_SPACE_FIXED_HARDWARE,
     ACPI_ADR_SPACE_USER_DEFINED1,
     ACPI_ADR_SPACE_USER_DEFINED2
     };
     */
    Name (ERSK,     /* 2 for \RGN0, \OPRK; 3 for \RGN0, \OPRI, and \OPRJ */

Package (NRSK)
    {
        0x01,
        0x02,
        0x03,
        0x01,
        0x01,
        0x01,
        0x00,
        0x00,
        0x00,
        0x00,
        0x00
    })
    Name (VFLG,       /* Counters of the Valid Flags */Package (NFLG)
    {
        0x00,
        0x00
    })
    /* Global Operation Regions availability notification Method */
    /* _REG(RegionSpaceKeyword, Flag) */
    /* RegionSpaceKeyword: */
    /*	     UserDefRegionSpace | SystemIO | SystemMemory | PCI_Config | */
    /*	     EmbeddedControl | SMBus | SystemCMOS | PciBarTarget | */
    /*       IPMI | GeneralPurposeIo | GenericSerialBus */
    /* Flag: 1/0 - turn on/off accessing operation regions of that Space */
    Method (_REG, 2, Serialized)  // _REG: Region Availability
    {
        Name (DBGF, 0x01)
        If (DBGF)
        {
            DNAM (Arg0, Arg1, "\\_REG")
        }

        Local0 = Match (PRSK, MEQ, Arg0, MTR, 0x00, 0x01)
        If (((Arg0 > 0x7F) && (Arg0 < 0x0100)))
        {
            Local0 = 0x00
        }

        If ((Local0 < NRSK))
        {
            Local1 = VRSK [Local0]
            Local2 = RefOf (Local1)
            DerefOf (Local2) = (DerefOf (Local1) + 0x01)
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

    /* Combination of the OperationRegion operator arguments */

    OperationRegion (RGN0, SystemMemory, 0x00, 0x0101)
    OperationRegion (RGN1, SystemIO, 0x0200, 0x0103)
    OperationRegion (RGN2, PCI_Config, 0x0400, 0x0105)
    OperationRegion (RGN3, EmbeddedControl, 0x0600, 0x0107)
    OperationRegion (RGN4, SMBus, 0x0800, 0x0109)
    OperationRegion (RGN5, SystemCMOS, 0x0A00, 0x010B)
    OperationRegion (RGN6, PCIBARTarget, 0x0C00, 0x010D)
    /* UserDefRegionSpace */

    OperationRegion (RGN7, 0x80, 0x0D00, 0x0117)
    OperationRegion (RGN8, 0xCF, 0x0E00, 0x0118)
    OperationRegion (RGN9, 0xFF, 0x0F00, 0x0119)
    /* ACPI 4/5 new space IDs */

    OperationRegion (RGNA, GeneralPurposeIo, 0x1100, 0x011A)
    /* NOTE: These spaces have special buffer protocols, can't be tested here */
    /*OperationRegion(RGNb, IPMI,             0x1000, 528) */
    /*OperationRegion(RGNc, GenericSerialBus, 0x1200, 272) */
    /* OpRegion Lengths checking task package: Name, SpaceID, Length */
    Name (P702, Package (0x21)
    {
        RGN0,
        0x00,
        0x0101,
        RGN1,
        0x01,
        0x0103,
        RGN2,
        0x02,
        0x0105,
        RGN3,
        0x03,
        0x0107,
        RGN4,
        0x04,
        0x0109,
        RGN5,
        0x05,
        0x010B,
        RGN6,
        0x06,
        0x010D,
        RGN7,
        0x80,
        0x0117,
        RGN8,
        0xCF,
        0x0118,
        RGN9,
        0xFF,
        0x0119,
        RGNA,
        0x08,
        0x011A
    })
    /* Region Space keyword strings */

    Name (NNAM, 0x0A)
    Name (RNAM, Package (NNAM)
    {
        /* 0x00 */

        "SystemMemory",
        /* 0x01 */

        "SystemIO",
        /* 0x02 */

        "PCI_Config",
        /* 0x03 */

        "EmbeddedControl",
        /* 0x04 */

        "SMBus",
        /* 0x05 */

        "SystemCMOS",
        /* 0x06 */

        "PciBarTarget",
        /* 0x07 */

        "IPMI",
        /* 0x08 */

        "GeneralPurposeIo",
        /* 0x09 */

        "GenericSerialBus"
    })
    /*
     * Display _REG method info
     */
    /* Arg0: SpaceID */
    /* Arg1: Enable/Disable flag */
    /* Arg2: _REG method name */
    Method (DNAM, 3, NotSerialized)
    {
        Concatenate ("Executing _REG method: ", Arg2, Local1)
        Concatenate (Local1, "  (", Local1)
        If ((Arg0 >= NNAM))
        {
            If ((Arg0 == 0x7E))
            {
                Concatenate (Local1, "Data Table", Local2)
            }
            Else
            {
                Concatenate (Local1, "User-defined or unknown SpaceId", Local2)
            }
        }
        Else
        {
            Concatenate (Local1, DerefOf (RNAM [Arg0]), Local2)
        }

        Concatenate (Local2, ")", Local2)
        Debug = Local2
        Debug = Arg0
        Debug = Arg1
    }

    Device (DOR0)
    {
        Name (IRSK, 0x00)   /* Counter of the Invalid RSKs */
        Name (IFLG, 0x00)   /* Counter of the Invalid Flags */
        Name (VRSK,       /* Counters of the Valid RSKs */Package (NRSK)
        {
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00
        })
        Name (ERSK,       /* Expected Counters of the Valid RSKs */Package (NRSK)
        {
            0x01,
            0x01,
            0x01,
            0x01,
            0x01,
            0x01,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00
        })
        Name (VFLG,       /* Counters of the Valid Flags */Package (NFLG)
        {
            0x00,
            0x00
        })
        /* Specific Operation Regions availability notification Method */
        /* \DOR0._REG(RegionSpaceKeyword, Flag) */
        Method (_REG, 2, Serialized)  // _REG: Region Availability
        {
            Name (DBGF, 0x01)
            If (DBGF)
            {
                DNAM (Arg0, Arg1, "\\DOR0._REG")
            }

            Local0 = Match (PRSK, MEQ, Arg0, MTR, 0x00, 0x01)
            If (((Arg0 > 0x7F) && (Arg0 < 0x0100)))
            {
                Local0 = 0x00
            }

            If ((Local0 < NRSK))
            {
                Local1 = VRSK [Local0]
                Local2 = RefOf (Local1)
                DerefOf (Local2) = (DerefOf (Local1) + 0x01)
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

        /* Combination of the OperationRegion operator arguments */

        OperationRegion (RGN0, SystemMemory, 0x1000, 0x0102)
        OperationRegion (RGN1, SystemIO, 0x1200, 0x0104)
        OperationRegion (RGN2, PCI_Config, 0x1400, 0x0106)
        OperationRegion (RGN3, EmbeddedControl, 0x1600, 0x0108)
        OperationRegion (RGN4, SMBus, 0x1800, 0x010A)
        OperationRegion (RGN5, SystemCMOS, 0x1A00, 0x010C)
        OperationRegion (RGN6, PCIBARTarget, 0x1C00, 0x010D)
        /* UserDefRegionSpace */

        OperationRegion (RGN7, 0x80, 0x00, 0x0127)
        OperationRegion (RGN8, 0xA5, 0x00, 0x0128)
        OperationRegion (RGN9, 0xFF, 0x00, 0x0129)
        /* ACPI 4/5 new space IDs */

        OperationRegion (RGNA, IPMI, 0x1E00, 0x010E)
        OperationRegion (RGNB, GeneralPurposeIo, 0x2000, 0x010F)
        OperationRegion (RGNC, GenericSerialBus, 0x2200, 0x0110)
    }

    Device (DOR1)
    {
        Name (IRSK, 0x00)   /* Counter of the Invalid RSKs */
        Name (IFLG, 0x00)   /* Counter of the Invalid Flags */
        Name (VRSK,       /* Counters of the Valid RSKs */Package (NRSK)
        {
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00
        })
        Name (ERSK,       /* Expected Counters of the Valid RSKs */Package (NRSK)
        {
            0x01,
            0x01,
            0x01,
            0x01,
            0x01,
            0x01,
            0x00,
            0x00,
            0x00,
            0x00,
            0x00
        })
        Name (VFLG,       /* Counters of the Valid Flags */Package (NFLG)
        {
            0x00,
            0x00
        })
        Name (IREG, 0x00)   /* Counter of the Invalid Calls to DOR1._REG */
        /* Specific Operation Regions availability notification Method */
        /* \DOR1._REG(RegionSpaceKeyword, Flag) */
        OperationRegion (JUNK, SystemMemory, 0x2000, 0x0100)
        Method (_REG, 2, Serialized)  // _REG: Region Availability
        {
            Name (DBGF, 0x01)
            If (DBGF)
            {
                DNAM (Arg0, Arg1, "\\DOR1._REG")
            }

            IREG++
        }

        Method (M000, 0, Serialized)
        {
            /* Dynamic Operation Regions availability notification Method */
            /* \DOR1.M000._REG(RegionSpaceKeyword, Flag) */
            Method (_REG, 2, Serialized)  // _REG: Region Availability
            {
                Name (DBGF, 0x01)
                If (DBGF)
                {
                    DNAM (Arg0, Arg1, "\\m701._REG")
                }

                Local0 = Match (PRSK, MEQ, Arg0, MTR, 0x00, 0x01)
                If (((Arg0 > 0x7F) && (Arg0 < 0x0100)))
                {
                    Local0 = 0x00
                }

                If ((Local0 < NRSK))
                {
                    Local1 = VRSK [Local0]
                    Local2 = RefOf (Local1)
                    DerefOf (Local2) = (DerefOf (Local1) + 0x01)
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

            /* Combination of the OperationRegion operator arguments */

            OperationRegion (RGN0, SystemMemory, 0x2000, 0x0100)
            OperationRegion (RGN1, SystemIO, 0x2200, 0x0300)
            OperationRegion (RGN2, PCI_Config, 0x2400, 0x0500)
            OperationRegion (RGN3, EmbeddedControl, 0x2600, 0x0700)
            OperationRegion (RGN4, SMBus, 0x2800, 0x0900)
            OperationRegion (RGN5, SystemCMOS, 0x2A00, 0x0B00)
            OperationRegion (RGN6, PCIBARTarget, 0x2C00, 0x0D00)
            /* UserDefRegionSpace */

            OperationRegion (RGN7, 0x80, 0x00, 0x0100)
            OperationRegion (RGN8, 0xA5, 0x00, 0x0100)
            OperationRegion (RGN9, 0xFF, 0x00, 0x0100)
            /* ACPI 4/5 new space IDs */

            OperationRegion (RGNA, IPMI, 0x2E00, 0x0F00)
            OperationRegion (RGNB, GeneralPurposeIo, 0x3000, 0x1100)
            OperationRegion (RGNC, GenericSerialBus, 0x3200, 0x1300)
            /* Incorrect call */

            _REG (FRSK, 0x02)
        }
    }

    /* Check Global OpRegions initialization */
    /* m700(CallChain) */
    /* CallChain: String */
    Method (M700, 1, NotSerialized)
    {
        Concatenate (Arg0, "-m700", Arg0)
        /* Check incorrect calls */

        If ((IRSK != 0x00))
        {
            ERR (Arg0, Z141, __LINE__, 0x00, 0x00, IRSK, 0x00)
        }

        If ((IFLG != 0x00))
        {
            ERR (Arg0, Z141, __LINE__, 0x00, 0x00, IFLG, 0x00)
        }

        If ((\DOR0.IRSK != 0x00))
        {
            ERR (Arg0, Z141, __LINE__, 0x00, 0x00, IRSK, 0x00)
        }

        If ((\DOR0.IFLG != 0x00))
        {
            ERR (Arg0, Z141, __LINE__, 0x00, 0x00, IFLG, 0x00)
        }

        /* Emulate and verify incorrect calls */

        _REG (FRSK, 0x02)
        \DOR0._REG (FRSK, 0x02)
        If ((IRSK != 0x01))
        {
            ERR (Arg0, Z141, __LINE__, 0x00, 0x00, IRSK, 0x01)
        }

        If ((IFLG != 0x01))
        {
            ERR (Arg0, Z141, __LINE__, 0x00, 0x00, IFLG, 0x01)
        }

        If ((\DOR0.IRSK != 0x01))
        {
            ERR (Arg0, Z141, __LINE__, 0x00, 0x00, IRSK, 0x01)
        }

        If ((\DOR0.IFLG != 0x01))
        {
            ERR (Arg0, Z141, __LINE__, 0x00, 0x00, IFLG, 0x01)
        }

        /* Check total calls to \_REG */

        If ((DerefOf (VFLG [0x01]) != 0x09))
        {
            ERR (Arg0, Z141, __LINE__, 0x00, 0x00, DerefOf (VFLG [0x01]), 0x09)
        }

        M70E (Arg0, 0x01, VRSK, ERSK, 0x0A)
        /* Check total calls to \DOR0._REG */

        If ((DerefOf (\DOR0.VFLG [0x01]) != 0x06))
        {
            ERR (Arg0, Z141, __LINE__, 0x00, 0x00, DerefOf (\DOR0.VFLG [0x01]), 0x06)
        }

        M70E (Arg0, 0x01, \DOR0.VRSK, \DOR0.ERSK, 0x0C)
    }

    /* Check Dynamic OpRegions initialization */
    /* m701(CallChain) */
    /* CallChain: String */
    Method (M701, 1, NotSerialized)
    {
        Concatenate (Arg0, "-m701", Arg0)
        If ((\DOR1.IREG != 0x00))
        {
            ERR (Arg0, Z141, __LINE__, 0x00, 0x00, \DOR1.IREG, 0x00)
        }

        If ((\DOR1.IRSK != 0x00))
        {
            ERR (Arg0, Z141, __LINE__, 0x00, 0x00, \DOR1.IRSK, 0x00)
        }

        If ((\DOR1.IFLG != 0x00))
        {
            ERR (Arg0, Z141, __LINE__, 0x00, 0x00, \DOR1.IFLG, 0x00)
        }

        If ((DerefOf (\DOR1.VFLG [0x01]) != 0x00))
        {
            ERR (Arg0, Z141, __LINE__, 0x00, 0x00, DerefOf (\DOR1.VFLG [0x01]), 0x00)
        }

        M70E (Arg0, 0x02, \DOR1.VRSK, 0x00, 0x11)
        \DOR1.M000 ()
        If ((\DOR1.IREG != 0x00))
        {
            ERR (Arg0, Z141, __LINE__, 0x00, 0x00, \DOR1.IREG, 0x01)
        }

        If ((\DOR1.IRSK != 0x01))
        {
            ERR (Arg0, Z141, __LINE__, 0x00, 0x00, \DOR1.IRSK, 0x01)
        }

        If ((\DOR1.IFLG != 0x01))
        {
            ERR (Arg0, Z141, __LINE__, 0x00, 0x00, \DOR1.IFLG, 0x01)
        }

        /* Check total calls to \DOR1._REG */

        If ((DerefOf (\DOR1.VFLG [0x01]) != 0x06))
        {
            ERR (Arg0, Z141, __LINE__, 0x00, 0x00, DerefOf (\DOR1.VFLG [0x01]), 0x06)
        }

        M70E (Arg0, 0x01, \DOR1.VRSK, \DOR1.ERSK, 0x16)
    }

    /* Check OpRegion Length restrictions */
    /* m702(CallChain) */
    /* CallChain: String */
    Method (M702, 1, NotSerialized)
    {
        Concatenate (Arg0, "-m702", Arg0)
        Local0 = SizeOf (P702)
        Local0 /= 0x03
        Local1 = 0x00
        While (Local0)
        {
            M70C (Arg0, P702, Local1)
            Local0--
            Local1++
        }
    }

    /* Check Overlapping of OpRegions */
    /* m703(CallChain) */
    /* CallChain: String */
    Method (M703, 1, Serialized)
    {
        Concatenate (Arg0, "-m703", Arg0)
        /* Overlap \RGN0 - \RGN9 */

        OperationRegion (RGN0, SystemMemory, 0x80, 0x0121)
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
        OperationRegion (RGNA, SystemMemory, 0x1090, 0x014A)
        /* Unsupported cases commented */

        M70F (Arg0, \RGN0, RGN0, 0x01, 0x00)
        M70F (Arg0, \RGN1, RGN1, 0x01, 0x01)
        /*  m70f(arg0, \RGN2, RGN2, 1, 2) */
        /*  m70f(arg0, \RGN3, RGN3, 1, 3) */
        /*  m70f(arg0, \RGN4, RGN4, 1, 4) */
        /*  m70f(arg0, \RGN5, RGN5, 1, 5) */
        /*  m70f(arg0, \RGN6, RGN6, 1, 6) */
        M70F (Arg0, \RGN7, RGN7, 0x01, 0x07)
        /*  m70f(arg0, \RGN8, RGN8, 1, 8) */
        /*  m70f(arg0, \RGN9, RGN9, 1, 9) */
        M70F (Arg0, \DOR0.RGN0, RGNA, 0x00, 0x0A)
    }

    /* Create Region Field about Region Length in length */
    /* and check possible exception */
    /* m70c(CallChain, Task, Index) */
    Method (M70C, 3, Serialized)
    {
        OperationRegion (OPRM, 0xFF, 0x00, 0x1000)
        Concatenate (Arg0, "-m70c", Arg0)
        Local4 = (Arg2 * 0x03)
        Local0 = (Local4 + 0x01)
        Local3 = DerefOf (Arg1 [Local0])
        Local0++
        Local2 = DerefOf (Arg1 [Local0])
        Local1 = (Local2 * 0x08)
        Name (B000, Buffer (0x0100){})
        CopyObject (DerefOf (Arg1 [Local4]), OPRM) /* \M70C.OPRM */
        Field (OPRM, ByteAcc, NoLock, Preserve)
        {
            FU01,   2048
        }

        Local6 = RefOf (FU01)
        Local5 = RefOf (Local6)
        M70D (Arg2, B000)
        If ((Local3 == 0x02)            /* PCI_Config */
            ){}
        ElseIf ((Local3 == 0x03)            /* EmbbededControl */
            ){}
        ElseIf ((Local3 == 0x04)            /* SMBus */
            ){}
        ElseIf ((Local3 == 0x05)            /* SystemCMOS */
            ){}
        ElseIf ((Local3 == 0x06)            /* PciBarTarget */
            ){}
        ElseIf ((Local3 == 0x07)            /* IPMI */
            ){}
        ElseIf ((Local3 == 0x08)            /* GeneralPurposeIo */
            ){}
        ElseIf ((Local3 > 0x80)            /* UserDefRegionSpace <> 0x80 */
            ){}
        Else
        {
            DerefOf (Local5) = B000 /* \M70C.B000 */
            CH03 (Arg0, Z141, __LINE__, 0x00, Local3)
            Local0 = ObjectType (DerefOf (Local6))
            Local1 = C00B /* \C00B */
            If ((Local0 != Local1))
            {
                ERR (Arg0, Z141, __LINE__, 0x00, 0x00, Local0, Local1)
            }
            Else
            {
                Local0 = DerefOf (Local6)
                If ((Local0 != B000))
                {
                    ERR (Arg0, Z141, __LINE__, Z141, Arg2, Local0, B000)
                }
            }
        }
    }

    /* Fill the buffer */
    /* m70d(Source, Target) */
    /* Source: 0x100 - index, else - this byte */
    /* Target: buffer for filling */
    Method (M70D, 2, Serialized)
    {
        Local0 = SizeOf (Arg1)
        While (Local0)
        {
            Local0--
            Switch (ToInteger (Arg0))
            {
                Case (0x0100)
                {
                    Arg1 [Local0] = Local0
                }
                Default
                {
                    Arg1 [Local0] = Arg0
                }

            }
        }
    }

    /* Processes the VRSK */
    /* m70e(CallChain, ToDo, Results, Benchmark, ErrId) */
    /* CallChain: String */
    /* ToDo:      0 - nullify, 1 - Check Values, 2 - check if null */
    /* Results:   actual VRSK Values */
    /* Benchmark: expected VRSK Values */
    /* ErrId:     index of the error */
    Method (M70E, 5, Serialized)
    {
        Concatenate (Arg0, "-m70e", Arg0)
        Local0 = NRSK /* \NRSK */
        While (Local0)
        {
            Local0--
            Local1 = Arg2 [Local0]
            Local2 = RefOf (Local1)
            Switch (ToInteger (Arg1))
            {
                Case (0x00)
                {
                    DerefOf (Local2) = 0x00
                }
                Case (0x01)
                {
                    Local3 = Arg3 [Local0]
                    If ((DerefOf (Local1) != DerefOf (Local3)))
                    {
                        ERR (Arg0, Z141, __LINE__, Z141, Local0, DerefOf (Local1), DerefOf (Local3))
                    }
                }
                Case (0x02)
                {
                    If ((DerefOf (Local1) != 0x00))
                    {
                        ERR (Arg0, Z141, __LINE__, Z141, Local0, DerefOf (Local1), 0x00)
                    }
                }

            }
        }
    }

    /* Create Region Fields in two overlapping Regions */
    /* and check overlapping parts to be shared */
    /* m70f(CallChain, OpRegion0, OpRegion1, RangeNum, ErrNum) */
    Method (M70F, 5, Serialized)
    {
        OperationRegion (OPRM, 0xFF, 0x00, 0x1000)
        OperationRegion (OPRN, 0xFF, 0x00, 0x1000)
        CopyObject (Arg1, OPRM) /* \M70F.OPRM */
        CopyObject (Arg2, OPRN) /* \M70F.OPRN */
        Field (OPRM, ByteAcc, NoLock, Preserve)
        {
            Offset (0x7D),
            FU00,   80,
            Offset (0x8D),
            FU02,   80
        }

        Field (OPRN, ByteAcc, NoLock, Preserve)
        {
            FU01,   80
        }

        Concatenate (Arg0, "-m70f", Arg0)
        Name (B000, Buffer (0x0A){})
        M70D (0x01, B000)
        If (Arg3)
        {
            FU00 = B000 /* \M70F.B000 */
        }
        Else
        {
            FU02 = B000 /* \M70F.B000 */
        }

        M70D (0x02, B000)
        FU01 = B000 /* \M70F.B000 */
        If (Arg3)
        {
            Local0 = FU00 /* \M70F.FU00 */
        }
        Else
        {
            Local0 = FU02 /* \M70F.FU02 */
        }

        Local1 = Buffer (0x0A)
            {
                /* 0000 */  0x01, 0x01, 0x01, 0x02, 0x02, 0x02, 0x02, 0x02,  // ........
                /* 0008 */  0x02, 0x02                                       // ..
            }
        If ((Local0 != Local1))
        {
            ERR (Arg0, Z141, __LINE__, Z141, Arg4, Local0, Local1)
        }
    }

    /* Check that the same ranges of different Address Spaces */
    /* actually refer the different locations */
    /* m704(CallChain) */
    /* CallChain: String */
    Method (M704, 1, Serialized)
    {
        Method (CHCK, 4, NotSerialized)
        {
            If ((Arg1 != Arg2))
            {
                ERR (Arg0, Z141, __LINE__, Z141, Arg3, Arg1, Arg2)
            }
        }

        OperationRegion (OPR0, SystemMemory, 0x00, 0x01)
        OperationRegion (OPR1, SystemIO, 0x00, 0x01)
        OperationRegion (OPR7, 0x80, 0x00, 0x01)
        Field (OPR0, ByteAcc, NoLock, Preserve)
        {
            F000,   8
        }

        Field (OPR1, ByteAcc, NoLock, Preserve)
        {
            F001,   8
        }

        Field (OPR7, ByteAcc, NoLock, Preserve)
        {
            F002,   8
        }

        Concatenate (Arg0, "-m704", Arg0)
        F000 = 0x5A
        CHCK (Arg0, F000, 0x5A, 0x00)
        F001 = 0xC3
        CHCK (Arg0, F001, 0xC3, 0x01)
        F002 = 0x96
        CHCK (Arg0, F002, 0x96, 0x02)
        CHCK (Arg0, F000, 0x5A, 0x03)
        CHCK (Arg0, F001, 0xC3, 0x04)
        CHCK (Arg0, F002, 0x96, 0x05)
    }

    /* Check non-constant OpRegion arguments */
    /* m705(CallChain) */
    /* CallChain: String */
    Method (M705, 1, Serialized)
    {
        Name (I000, 0x56)
        Name (I001, 0x78)
        Name (I002, 0x89ABCDEF)
        /* ArgX */

        Method (M000, 4, Serialized)
        {
            Switch (ToInteger (Arg1))
            {
                Case (0x00)
                {
                    OperationRegion (OPR0, SystemMemory, Arg2, Arg3)
                    Field (OPR0, ByteAcc, NoLock, Preserve)
                    {
                        F000,   32
                    }

                    Local5 = RefOf (F000)
                }
                Case (0x01)
                {
                    OperationRegion (OPR1, SystemIO, Arg2, Arg3)
                    Field (OPR1, ByteAcc, NoLock, Preserve)
                    {
                        F001,   32
                    }

                    Local5 = RefOf (F001)
                }
                Case (0x02)
                {
                    OperationRegion (OPR7, 0x80, Arg2, Arg3)
                    Field (OPR7, ByteAcc, NoLock, Preserve)
                    {
                        F007,   32
                    }

                    Local5 = RefOf (F007)
                }

            }

            Local6 = RefOf (Local5)
            DerefOf (Local6) = I002 /* \M705.I002 */
            Local7 = DerefOf (Local5)
            If ((I002 != Local7))
            {
                ERR (Arg0, Z141, __LINE__, Z141, Arg1, Local7, I002)
            }
        }

        /* Named */

        Method (M001, 2, Serialized)
        {
            Switch (ToInteger (Arg1))
            {
                Case (0x00)
                {
                    OperationRegion (OPR0, SystemMemory, I000, I001)
                    Field (OPR0, ByteAcc, NoLock, Preserve)
                    {
                        F000,   32
                    }

                    Local5 = RefOf (F000)
                }
                Case (0x01)
                {
                    OperationRegion (OPR1, SystemIO, I000, I001)
                    Field (OPR1, ByteAcc, NoLock, Preserve)
                    {
                        F001,   32
                    }

                    Local5 = RefOf (F001)
                }
                Case (0x02)
                {
                    OperationRegion (OPR7, 0x80, I000, I001)
                    Field (OPR7, ByteAcc, NoLock, Preserve)
                    {
                        F007,   32
                    }

                    Local5 = RefOf (F007)
                }

            }

            Local6 = RefOf (Local5)
            DerefOf (Local6) = I002 /* \M705.I002 */
            Local7 = DerefOf (Local5)
            If ((I002 != Local7))
            {
                ERR (Arg0, Z141, __LINE__, Z141, Arg1, Local7, I002)
            }
        }

        /* LocalX */

        Method (M002, 2, Serialized)
        {
            Local0 = I000 /* \M705.I000 */
            Local1 = I001 /* \M705.I001 */
            Switch (ToInteger (Arg1))
            {
                Case (0x00)
                {
                    OperationRegion (OPR0, SystemMemory, Local0, Local1)
                    Field (OPR0, ByteAcc, NoLock, Preserve)
                    {
                        F000,   32
                    }

                    Local5 = RefOf (F000)
                }
                Case (0x01)
                {
                    OperationRegion (OPR1, SystemIO, Local0, Local1)
                    Field (OPR1, ByteAcc, NoLock, Preserve)
                    {
                        F001,   32
                    }

                    Local5 = RefOf (F001)
                }
                Case (0x02)
                {
                    OperationRegion (OPR7, 0x80, Local0, Local1)
                    Field (OPR7, ByteAcc, NoLock, Preserve)
                    {
                        F007,   32
                    }

                    Local5 = RefOf (F007)
                }

            }

            Local6 = RefOf (Local5)
            DerefOf (Local6) = I002 /* \M705.I002 */
            Local7 = DerefOf (Local5)
            If ((I002 != Local7))
            {
                ERR (Arg0, Z141, __LINE__, Z141, Arg1, Local7, I002)
            }
        }

        /* Expression */

        Method (M003, 2, Serialized)
        {
            Local1 = I001 /* \M705.I001 */
            Switch (ToInteger (Arg1))
            {
                Case (0x00)
                {
                    OperationRegion (OPR0, SystemMemory, (I000 + 0x01), (Local1 - 0x01))
                    Field (OPR0, ByteAcc, NoLock, Preserve)
                    {
                        F000,   32
                    }

                    Local5 = RefOf (F000)
                }
                Case (0x01)
                {
                    OperationRegion (OPR1, SystemIO, (I000 + 0x01), (Local1 - 0x01))
                    Field (OPR1, ByteAcc, NoLock, Preserve)
                    {
                        F001,   32
                    }

                    Local5 = RefOf (F001)
                }
                Case (0x02)
                {
                    OperationRegion (OPR7, 0x80, (I000 + 0x01), (Local1 - 0x01))
                    Field (OPR7, ByteAcc, NoLock, Preserve)
                    {
                        F007,   32
                    }

                    Local5 = RefOf (F007)
                }

            }

            Local6 = RefOf (Local5)
            DerefOf (Local6) = I002 /* \M705.I002 */
            Local7 = DerefOf (Local5)
            If ((I002 != Local7))
            {
                ERR (Arg0, Z141, __LINE__, Z141, Arg1, Local7, I002)
            }
        }

        Concatenate (Arg0, "-m705", Arg0)
        M000 (Arg0, 0x00, 0x12, 0x34)
        M000 (Arg0, 0x01, 0x12, 0x34)
        M000 (Arg0, 0x02, 0x12, 0x34)
        M001 (Arg0, 0x00)
        M001 (Arg0, 0x01)
        M001 (Arg0, 0x02)
        M002 (Arg0, 0x00)
        M002 (Arg0, 0x01)
        M002 (Arg0, 0x02)
        M003 (Arg0, 0x00)
        M003 (Arg0, 0x01)
        M003 (Arg0, 0x02)
    }

    /* Check non-Integer OpRegion arguments */
    /* m706(CallChain) */
    /* CallChain: String */
    Method (M706, 1, Serialized)
    {
        Name (OFF0, 0xFEDCBA987654321F)
        Name (OFFB, Buffer (0x08)
        {
             0x1F, 0x32, 0x54, 0x76, 0x98, 0xBA, 0xDC, 0xFE   // .2Tv....
        })
        Name (OFFS, "7654321f")
        If (F64)
        {
            OFFS = "fedcba987654321f"
        }

        Name (LEN0, 0x0123)
        Name (LENB, Buffer (0x02)
        {
             0x23, 0x01                                       // #.
        })
        Name (LENS, "123")
        OperationRegion (OPR0, SystemMemory, 0xFEDCBA987654321F, 0x0123)
        OperationRegion (OPR1, SystemMemory, OFF0, LEN0)
        OperationRegion (OPR2, SystemMemory, OFFB, LENB)
        OperationRegion (OPR3, SystemMemory, OFFS, LENS)
        Field (OPR0, ByteAcc, NoLock, Preserve)
        {
            Offset (0x11F),
            FU00,   32
        }

        Field (OPR1, ByteAcc, NoLock, Preserve)
        {
            Offset (0x11F),
            FU01,   32
        }

        Field (OPR2, ByteAcc, NoLock, Preserve)
        {
            Offset (0x11F),
            FU02,   32
        }

        Field (OPR3, ByteAcc, NoLock, Preserve)
        {
            Offset (0x11F),
            FU03,   32
        }

        Name (I000, 0x12345678)
        Method (M000, 4, Serialized)
        {
            OperationRegion (OPR4, SystemMemory, Arg1, Arg2)
            Field (OPR4, AnyAcc, NoLock, Preserve)
            {
                Offset (0x11F),
                FU04,   32
            }

            If ((FU04 != I000))
            {
                ERR (Arg0, Z141, __LINE__, 0x00, 0x00, FU04, I000)
            }
        }

        Concatenate (Arg0, "-m706", Arg0)
        FU00 = I000 /* \M706.I000 */
        If ((FU00 != I000))
        {
            ERR (Arg0, Z141, __LINE__, 0x00, 0x00, FU00, I000)
        }

        If ((0xFEDCBA987654321F != OFF0))
        {
            ERR (Arg0, Z141, __LINE__, 0x00, 0x00, OFF0, 0xFEDCBA987654321F)
        }
        ElseIf ((0x0123 != LEN0))
        {
            ERR (Arg0, Z141, __LINE__, 0x00, 0x00, LEN0, 0x0123)
        }
        ElseIf ((FU01 != I000))
        {
            ERR (Arg0, Z141, __LINE__, 0x00, 0x00, FU00, I000)
        }

        If ((0xFEDCBA987654321F != OFFB))
        {
            ERR (Arg0, Z141, __LINE__, 0x00, 0x00, OFFB, 0xFEDCBA987654321F)
        }
        ElseIf ((0x0123 != LENB))
        {
            ERR (Arg0, Z141, __LINE__, 0x00, 0x00, LENB, 0x0123)
        }
        ElseIf ((FU02 != I000))
        {
            ERR (Arg0, Z141, __LINE__, 0x00, 0x00, FU00, I000)
        }

        If ((0xFEDCBA987654321F != OFFS))
        {
            Local0 = (OFFS + 0x00)
            ERR (Arg0, Z141, __LINE__, 0x00, 0x00, Local0, 0xFEDCBA987654321F)
        }
        ElseIf ((0x0123 != LENS))
        {
            Local0 = (LENS + 0x00)
            ERR (Arg0, Z141, __LINE__, 0x00, 0x00, Local0, 0x0123)
        }
        ElseIf ((FU03 != I000))
        {
            ERR (Arg0, Z141, __LINE__, 0x00, 0x00, FU00, I000)
        }

        M000 (Arg0, OFF0, LEN0, 0x2B)
        M000 (Arg0, OFFB, LENB, 0x2C)
        M000 (Arg0, OFFS, LENS, 0x2D)
    }

    /* Overlapping Operation Regions algorithm test */
    /* Test the 3 conditional cases of overlap */
    /* Test done only in SystemMemory */
    Method (M707, 1, Serialized)
    {
        OperationRegion (RGN0, SystemMemory, 0x0100, 0x08)
        OperationRegion (RGN1, SystemMemory, 0xFB, 0x08)
        OperationRegion (RGN2, SystemMemory, 0x0105, 0x08)
        OperationRegion (RGN3, SystemMemory, 0xF9, 0x16)
        OperationRegion (RGN4, SystemMemory, 0xF9, 0x16)
        /* Starting Field */

        Field (RGN0, ByteAcc, NoLock, Preserve)
        {
            Offset (0x01),
            FU00,   48
        }

        /* Overlap start of RGN0 */

        Field (RGN1, ByteAcc, NoLock, Preserve)
        {
            Offset (0x02),
            FU10,   48
        }

        /* Overlap end of RGN0 */

        Field (RGN2, ByteAcc, NoLock, Preserve)
        {
            FU20,   48
        }

        /* Overlap both start of RGN1 and end of RGN2 */

        Field (RGN3, ByteAcc, NoLock, Preserve)
        {
            FU30,   48,
            Offset (0x08),
            FU31,   16,
            Offset (0x0C),
            FU32,   16,
            Offset (0x10),
            FU33,   48
        }

        /* Single Field spanning RGN3 area */

        Field (RGN4, ByteAcc, NoLock, Preserve)
        {
            FU40,   176
        }

        Name (B000, Buffer (0x06){})
        Name (B001, Buffer (0x02){})
        /* Starting region write */

        M70D (0x01, B000)
        FU00 = B000 /* \M707.B000 */
        /* New region overlapping the left */

        M70D (0x02, B000)
        FU10 = B000 /* \M707.B000 */
        /* New region overlapping the right */

        M70D (0x03, B000)
        FU20 = B000 /* \M707.B000 */
        /* New region overlapping left and right with writes */
        /* at various locations */
        M70D (0x04, B000)
        FU30 = B000 /* \M707.B000 */
        M70D (0x05, B001)
        FU31 = B001 /* \M707.B001 */
        M70D (0x06, B001)
        FU32 = B001 /* \M707.B001 */
        M70D (0x07, B000)
        FU33 = B000 /* \M707.B000 */
        Local0 = FU40 /* \M707.FU40 */
        Local1 = Buffer (0x16)
            {
                /* 0000 */  0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x02, 0x02,  // ........
                /* 0008 */  0x05, 0x05, 0x01, 0x01, 0x06, 0x06, 0x03, 0x03,  // ........
                /* 0010 */  0x07, 0x07, 0x07, 0x07, 0x07, 0x07               // ......
            }
        If ((Local0 != Local1))
        {
            ERR (Arg0, Z141, __LINE__, 0x00, 0x00, Local0, Local1)
        }
    }

    Method (ORC0, 0, Serialized)
    {
        /* Global OpRegions */

        SRMT ("m700")
        If (Y220)
        {
            M700 (__METHOD__)
        }
        Else
        {
            BLCK ()
        }

        /* Dynamic OpRegions */

        SRMT ("m701")
        If (Y217)
        {
            M701 (__METHOD__)
        }
        Else
        {
            BLCK ()
        }

        /* OpRegion Lengths */

        SRMT ("m702")
        M702 (__METHOD__)
        /* Overlapping of OpRegions */

        SRMT ("m703")
        If (Y221)
        {
            M703 (__METHOD__)
        }
        Else
        {
            BLCK ()
        }

        /* The same ranges of different Address Spaces */

        SRMT ("m704")
        If (Y222)
        {
            M704 (__METHOD__)
        }
        Else
        {
            BLCK ()
        }

        /* Non-constant OpRegion arguments */

        SRMT ("m705")
        M705 (__METHOD__)
        /* Non-Integer OpRegion arguments */

        SRMT ("m706")
        M706 (__METHOD__)
        /* Overlapping OpRegions algorithm test */

        SRMT ("m707")
        M707 (__METHOD__)
    }
