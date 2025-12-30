/*
 * Intel ACPI Component Architecture
 * AML Disassembler version 20021002
 *
 * Disassembly of DSDT.AML, Wed Aug 30 20:30:19 2006
 */
DefinitionBlock ("DSDT.aml", "DSDT", 1, "IBM   ", "TP-T20  ", 100930080)
{
    Scope (\_PR)
    {
        Processor (CPU, 0x01, 0x00001010, 0x06) {}
    }

    Scope (\_SB)
    {
        Device (LNKA)
        {
            Name (_HID, EisaId ("PNP0C0F"))
            Name (_UID, 0x01)
            Method (_STA, 0, NotSerialized)
            {
                If (LNot (VPIR (\_SB.PCI0.ISA.PIRA)))
                {
                    Return (0x09)
                }
                Else
                {
                    Return (0x0B)
                }
            }

            Name (_PRS, ResourceTemplate ()
            {
                IRQ (Level, ActiveLow, Shared) {3,4,5,6,7,9,10,11}
            })
            Method (_DIS, 0, NotSerialized)
            {
                Or (\_SB.PCI0.ISA.PIRA, 0x80, \_SB.PCI0.ISA.PIRA)
            }

            Method (_CRS, 0, NotSerialized)
            {
                Name (BUFA, ResourceTemplate ()
                {
                    IRQ (Level, ActiveLow, Shared) {}
                })
                CreateWordField (BUFA, 0x01, IRA1)
                And (\_SB.PCI0.ISA.PIRA, 0x8F, Local0)
                If (VPIR (Local0))
                {
                    Store (ShiftLeft (One, Local0), IRA1)
                }

                Return (BUFA)
            }

            Method (_SRS, 1, NotSerialized)
            {
                CreateWordField (Arg0, 0x01, IRA2)
                FindSetRightBit (IRA2, Local0)
                And (\_SB.PCI0.ISA.PIRA, 0x70, Local1)
                Or (Local1, Decrement (Local0), Local1)
                Store (Local1, \_SB.PCI0.ISA.PIRA)
            }
        }

        Device (LNKB)
        {
            Name (_HID, EisaId ("PNP0C0F"))
            Name (_UID, 0x02)
            Method (_STA, 0, NotSerialized)
            {
                If (LNot (VPIR (\_SB.PCI0.ISA.PIRB)))
                {
                    Return (0x09)
                }
                Else
                {
                    Return (0x0B)
                }
            }

            Name (_PRS, ResourceTemplate ()
            {
                IRQ (Level, ActiveLow, Shared) {3,4,5,6,7,9,10,11}
            })
            Method (_DIS, 0, NotSerialized)
            {
                Or (\_SB.PCI0.ISA.PIRB, 0x80, \_SB.PCI0.ISA.PIRB)
            }

            Method (_CRS, 0, NotSerialized)
            {
                Name (BUFB, ResourceTemplate ()
                {
                    IRQ (Level, ActiveLow, Shared) {}
                })
                CreateWordField (BUFB, 0x01, IRB1)
                And (\_SB.PCI0.ISA.PIRB, 0x8F, Local0)
                If (VPIR (Local0))
                {
                    Store (ShiftLeft (One, Local0), IRB1)
                }

                Return (BUFB)
            }

            Method (_SRS, 1, NotSerialized)
            {
                CreateWordField (Arg0, 0x01, IRB2)
                FindSetRightBit (IRB2, Local0)
                And (\_SB.PCI0.ISA.PIRB, 0x70, Local1)
                Or (Local1, Decrement (Local0), Local1)
                Store (Local1, \_SB.PCI0.ISA.PIRB)
            }
        }

        Device (LNKC)
        {
            Name (_HID, EisaId ("PNP0C0F"))
            Name (_UID, 0x03)
            Method (_STA, 0, NotSerialized)
            {
                If (LNot (VPIR (\_SB.PCI0.ISA.PIRC)))
                {
                    Return (0x09)
                }
                Else
                {
                    Return (0x0B)
                }
            }

            Name (_PRS, ResourceTemplate ()
            {
                IRQ (Level, ActiveLow, Shared) {3,4,5,6,7,9,10,11}
            })
            Method (_DIS, 0, NotSerialized)
            {
                Or (\_SB.PCI0.ISA.PIRC, 0x80, \_SB.PCI0.ISA.PIRC)
            }

            Method (_CRS, 0, NotSerialized)
            {
                Name (BUFC, ResourceTemplate ()
                {
                    IRQ (Level, ActiveLow, Shared) {}
                })
                CreateWordField (BUFC, 0x01, IRC1)
                And (\_SB.PCI0.ISA.PIRC, 0x8F, Local0)
                If (VPIR (Local0))
                {
                    Store (ShiftLeft (One, Local0), IRC1)
                }

                Return (BUFC)
            }

            Method (_SRS, 1, NotSerialized)
            {
                CreateWordField (Arg0, 0x01, IRC2)
                FindSetRightBit (IRC2, Local0)
                And (\_SB.PCI0.ISA.PIRC, 0x70, Local1)
                Or (Local1, Decrement (Local0), Local1)
                Store (Local1, \_SB.PCI0.ISA.PIRC)
            }
        }

        Device (LNKD)
        {
            Name (_HID, EisaId ("PNP0C0F"))
            Name (_UID, 0x04)
            Method (_STA, 0, NotSerialized)
            {
                If (LNot (VPIR (\_SB.PCI0.ISA.PIRD)))
                {
                    Return (0x09)
                }
                Else
                {
                    Return (0x0B)
                }
            }

            Name (_PRS, ResourceTemplate ()
            {
                IRQ (Level, ActiveLow, Shared) {3,4,5,6,7,9,10,11}
            })
            Method (_DIS, 0, NotSerialized)
            {
                Or (\_SB.PCI0.ISA.PIRD, 0x80, \_SB.PCI0.ISA.PIRD)
            }

            Method (_CRS, 0, NotSerialized)
            {
                Name (BUFD, ResourceTemplate ()
                {
                    IRQ (Level, ActiveLow, Shared) {}
                })
                CreateWordField (BUFD, 0x01, IRD1)
                And (\_SB.PCI0.ISA.PIRD, 0x8F, Local0)
                If (VPIR (Local0))
                {
                    Store (ShiftLeft (One, Local0), IRD1)
                }

                Return (BUFD)
            }

            Method (_SRS, 1, NotSerialized)
            {
                CreateWordField (Arg0, 0x01, IRD2)
                FindSetRightBit (IRD2, Local0)
                And (\_SB.PCI0.ISA.PIRD, 0x70, Local1)
                Or (Local1, Decrement (Local0), Local1)
                Store (Local1, \_SB.PCI0.ISA.PIRD)
            }
        }

        Method (VPIR, 1, NotSerialized)
        {
            Store (One, Local0)
            If (And (Arg0, 0x80))
            {
                Store (Zero, Local0)
            }
            Else
            {
                And (Arg0, 0x0F, Local1)
                If (LLess (Local1, 0x03))
                {
                    Store (Zero, Local0)
                }
                Else
                {
                    If (LOr (LEqual (Local1, 0x08), LEqual (Local1, 0x0D)))
                    {
                        Store (Zero, Local0)
                    }
                }
            }

            Return (Local0)
        }

        Device (MEM)
        {
            Name (_HID, EisaId ("PNP0C01"))
            Name (ME98, ResourceTemplate ()
            {
                Memory32Fixed (ReadWrite, 0x00000000, 0x000A0000)
                Memory32Fixed (ReadOnly, 0x000E0000, 0x00020000)
                Memory32Fixed (ReadWrite, 0x00100000, 0x01EE0000)
                Memory32Fixed (ReadOnly, 0xFFF80000, 0x00080000)
            })
            CreateDWordField (ME98, 0x1C, MEB0)
            CreateDWordField (ME98, 0x20, MEL0)
            Name (MGAP, ResourceTemplate ()
            {
                Memory32Fixed (ReadOnly, 0x00000000, 0x00000000)
            })
            CreateDWordField (MGAP, 0x04, MGPB)
            CreateDWordField (MGAP, 0x08, MGPL)
            Name (MEMS, ResourceTemplate ()
            {
                Memory32Fixed (ReadWrite, 0x00000000, 0x000A0000)
                Memory32Fixed (ReadOnly, 0x000C0000, 0x00000000)
                Memory32Fixed (ReadOnly, 0x000C4000, 0x00000000)
                Memory32Fixed (ReadOnly, 0x000C8000, 0x00000000)
                Memory32Fixed (ReadOnly, 0x000CC000, 0x00000000)
                Memory32Fixed (ReadOnly, 0x000D0000, 0x00000000)
                Memory32Fixed (ReadOnly, 0x000D4000, 0x00000000)
                Memory32Fixed (ReadOnly, 0x000D8000, 0x00000000)
                Memory32Fixed (ReadOnly, 0x000DC000, 0x00000000)
                Memory32Fixed (ReadOnly, 0x000E0000, 0x00000000)
                Memory32Fixed (ReadOnly, 0x000E4000, 0x00000000)
                Memory32Fixed (ReadOnly, 0x000E8000, 0x00000000)
                Memory32Fixed (ReadOnly, 0x000EC000, 0x00000000)
                Memory32Fixed (ReadOnly, 0x000F0000, 0x00010000)
                Memory32Fixed (ReadWrite, 0x00100000, 0x01EE0000)
                Memory32Fixed (ReadOnly, 0xFFF80000, 0x00080000)
            })
            CreateDWordField (MEMS, 0x14, MC0L)
            CreateDWordField (MEMS, 0x20, MC4L)
            CreateDWordField (MEMS, 0x2C, MC8L)
            CreateDWordField (MEMS, 0x38, MCCL)
            CreateDWordField (MEMS, 0x44, MD0L)
            CreateDWordField (MEMS, 0x50, MD4L)
            CreateDWordField (MEMS, 0x5C, MD8L)
            CreateDWordField (MEMS, 0x68, MDCL)
            CreateDWordField (MEMS, 0x74, ME0L)
            CreateDWordField (MEMS, 0x80, ME4L)
            CreateDWordField (MEMS, 0x8C, ME8L)
            CreateDWordField (MEMS, 0x98, MECL)
            CreateBitField (MEMS, 0x78, MC0W)
            CreateBitField (MEMS, 0xD8, MC4W)
            CreateBitField (MEMS, 0x0138, MC8W)
            CreateBitField (MEMS, 0x0198, MCCW)
            CreateBitField (MEMS, 0x01F8, MD0W)
            CreateBitField (MEMS, 0x0258, MD4W)
            CreateBitField (MEMS, 0x02B8, MD8W)
            CreateBitField (MEMS, 0x0318, MDCW)
            CreateBitField (MEMS, 0x0378, ME0W)
            CreateBitField (MEMS, 0x03D8, ME4W)
            CreateBitField (MEMS, 0x0438, ME8W)
            CreateBitField (MEMS, 0x0498, MECW)
            CreateDWordField (MEMS, 0xAC, MEB1)
            CreateDWordField (MEMS, 0xB0, MEL1)
            Method (_CRS, 0, NotSerialized)
            {
                If (\W98F)
                {
                    Subtract (\MEMX, MEB0, MEL0)
                    Store (\GGAP (0x00), MGPB)
                    Store (\GGAP (0x01), MGPL)
                    If (LAnd (MGPB, MGPL))
                    {
                        Subtract (SizeOf (ME98), 0x02, Local0)
                        Name (MBF0, Buffer (Local0) {})
                        Add (Local0, SizeOf (MGAP), Local0)
                        Name (MBF1, Buffer (Local0) {})
                        Store (ME98, MBF0)
                        Concatenate (MBF0, MGAP, MBF1)
                        Return (MBF1)
                    }
                    Else
                    {
                        Return (ME98)
                    }
                }

                And (\_SB.PCI0.PAM1, 0x03, Local0)
                If (Local0)
                {
                    Store (0x4000, MC0L)
                    If (And (Local0, 0x02))
                    {
                        Store (0x01, MC0W)
                    }
                }

                And (\_SB.PCI0.PAM1, 0x30, Local0)
                If (Local0)
                {
                    Store (0x4000, MC4L)
                    If (And (Local0, 0x20))
                    {
                        Store (0x01, MC4W)
                    }
                }

                And (\_SB.PCI0.PAM2, 0x03, Local0)
                If (Local0)
                {
                    Store (0x4000, MC8L)
                    If (And (Local0, 0x02))
                    {
                        Store (0x01, MC8W)
                    }
                }

                And (\_SB.PCI0.PAM2, 0x30, Local0)
                If (Local0)
                {
                    Store (0x4000, MCCL)
                    If (And (Local0, 0x20))
                    {
                        Store (0x01, MCCW)
                    }
                }

                And (\_SB.PCI0.PAM3, 0x03, Local0)
                If (Local0)
                {
                    Store (0x4000, MD0L)
                    If (And (Local0, 0x02))
                    {
                        Store (0x01, MD0W)
                    }
                }

                And (\_SB.PCI0.PAM3, 0x30, Local0)
                If (Local0)
                {
                    Store (0x4000, MD4L)
                    If (And (Local0, 0x20))
                    {
                        Store (0x01, MD4W)
                    }
                }

                And (\_SB.PCI0.PAM4, 0x03, Local0)
                If (Local0)
                {
                    Store (0x4000, MD8L)
                    If (And (Local0, 0x02))
                    {
                        Store (0x01, MD8W)
                    }
                }

                And (\_SB.PCI0.PAM4, 0x30, Local0)
                If (Local0)
                {
                    Store (0x4000, MDCL)
                    If (And (Local0, 0x20))
                    {
                        Store (0x01, MDCW)
                    }
                }

                And (\_SB.PCI0.PAM5, 0x03, Local0)
                If (Local0)
                {
                    Store (0x4000, ME0L)
                    If (And (Local0, 0x02))
                    {
                        Store (0x01, ME0W)
                    }
                }

                And (\_SB.PCI0.PAM5, 0x30, Local0)
                If (Local0)
                {
                    Store (0x4000, ME4L)
                    If (And (Local0, 0x20))
                    {
                        Store (0x01, ME4W)
                    }
                }

                And (\_SB.PCI0.PAM6, 0x03, Local0)
                If (Local0)
                {
                    Store (0x4000, ME8L)
                    If (And (Local0, 0x02))
                    {
                        Store (0x01, ME8W)
                    }
                }

                And (\_SB.PCI0.PAM6, 0x30, Local0)
                If (Local0)
                {
                    Store (0x4000, MECL)
                    If (And (Local0, 0x20))
                    {
                        Store (0x01, MECW)
                    }
                }

                Subtract (\MEMX, MEB1, MEL1)
                Return (MEMS)
            }
        }

        Device (LID)
        {
            Name (_HID, EisaId ("PNP0C0D"))
            Method (_LID, 0, NotSerialized)
            {
                If (\H8DR)
                {
                    Return (\_SB.PCI0.ISA.EC.HPLD)
                }
                Else
                {
                    If (And (\RBEC (0x36), 0x04))
                    {
                        Return (0x01)
                    }
                    Else
                    {
                        Return (0x00)
                    }
                }
            }

            Method (_PRW, 0, NotSerialized)
            {
                If (LAnd (\W98F, LNot (\WMEF)))
                {
                    Return (Package (0x02)
                    {
                        0x0B,
                        0x04
                    })
                }
                Else
                {
                    Return (Package (0x02)
                    {
                        0x0B,
                        0x03
                    })
                }
            }

            Method (_PSW, 1, NotSerialized)
            {
                If (\H8DR)
                {
                    If (Arg0)
                    {
                        Store (One, \_SB.PCI0.ISA.EC.HWLO)
                    }
                    Else
                    {
                        Store (Zero, \_SB.PCI0.ISA.EC.HWLO)
                    }
                }
                Else
                {
                    If (Arg0)
                    {
                        \MBEC (0x32, 0xFF, 0x04)
                    }
                    Else
                    {
                        \MBEC (0x32, 0xFB, 0x00)
                    }
                }
            }
        }

        Device (SLPB)
        {
            Name (_HID, EisaId ("PNP0C0E"))
            Method (_PRW, 0, NotSerialized)
            {
                If (LAnd (\W98F, LNot (\WMEF)))
                {
                    Return (Package (0x02)
                    {
                        0x0B,
                        0x04
                    })
                }
                Else
                {
                    Return (Package (0x02)
                    {
                        0x0B,
                        0x03
                    })
                }
            }

            Method (_PSW, 1, NotSerialized)
            {
                If (\H8DR)
                {
                    If (Arg0)
                    {
                        Store (0x01, \_SB.PCI0.ISA.EC.HWFN)
                    }
                    Else
                    {
                        Store (0x00, \_SB.PCI0.ISA.EC.HWFN)
                    }
                }
                Else
                {
                    If (Arg0)
                    {
                        \MBEC (0x32, 0xFF, 0x10)
                    }
                    Else
                    {
                        \MBEC (0x32, 0xEF, 0x00)
                    }
                }
            }
        }

        Device (PCI0)
        {
            Name (_ADR, 0x00)
            Name (_HID, EisaId ("PNP0A03"))
            OperationRegion (X000, PCI_Config, 0x00, 0x0100)
            Field (X000, DWordAcc, NoLock, Preserve)
            {
                Offset (0x59),
                PAM0,   8,
                PAM1,   8,
                PAM2,   8,
                PAM3,   8,
                PAM4,   8,
                PAM5,   8,
                PAM6,   8,
                DRB0,   8,
                DRB1,   8,
                DRB2,   8,
                DRB3,   8,
                DRB4,   8,
                DRB5,   8,
                DRB6,   8,
                DRB7,   8,
                Offset (0x7A),
                CREN,   1,
                Offset (0x7B)
            }

            Name (_PRW, Package (0x02)
            {
                0x0B,
                0x04
            })
            Method (_PSW, 1, NotSerialized)
            {
                EPSW (0x01, Arg0)
            }

            Name (PMEE, 0x00)
            Method (EPSW, 2, NotSerialized)
            {
                If (Arg1)
                {
                    Or (PMEE, Arg0, Local0)
                }
                Else
                {
                    And (PMEE, Not (Arg0), Local0)
                }

                Store (Local0, PMEE)
                If (\H8DR)
                {
                    If (Local0)
                    {
                        Store (0x01, \_SB.PCI0.ISA.EC.HWPM)
                    }
                    Else
                    {
                        Store (0x00, \_SB.PCI0.ISA.EC.HWPM)
                    }
                }
                Else
                {
                    If (Local0)
                    {
                        \MBEC (0x32, 0xFF, 0x01)
                    }
                    Else
                    {
                        \MBEC (0x32, 0xFE, 0x00)
                    }
                }

                If (Local0)
                {
                    Store (0x01, \_SB.PCI0.ISA.WOLE)
                }
                Else
                {
                    Store (0x00, \_SB.PCI0.ISA.WOLE)
                }
            }

            Name (_CRS, ResourceTemplate ()
            {
                WordBusNumber (ResourceProducer, MinFixed, MaxFixed, PosDecode,
                    0x0000,
                    0x0000,
                    0x00FF,
                    0x0000,
                    0x0100)
                IO (Decode16, 0x0CF8, 0x0CF8, 0x01, 0x08)
                WordIO (ResourceProducer, MinFixed, MaxFixed, PosDecode, EntireRange,
                    0x0000,
                    0x0000,
                    0x0CF7,
                    0x0000,
                    0x0CF8)
                WordIO (ResourceProducer, MinFixed, MaxFixed, PosDecode, EntireRange,
                    0x0000,
                    0x0D00,
                    0xFFFF,
                    0x0000,
                    0xF300)
                DWordMemory (ResourceProducer, PosDecode, MinFixed, MaxFixed, Cacheable, ReadWrite,
                    0x00000000,
                    0x000A0000,
                    0x000BFFFF,
                    0x00000000,
                    0x00020000)
                DWordMemory (ResourceProducer, PosDecode, MinFixed, MaxFixed, Cacheable, ReadWrite,
                    0x00000000,
                    0x000C0000,
                    0x000C3FFF,
                    0x00000000,
                    0x00004000)
                DWordMemory (ResourceProducer, PosDecode, MinFixed, MaxFixed, Cacheable, ReadWrite,
                    0x00000000,
                    0x000C4000,
                    0x000C7FFF,
                    0x00000000,
                    0x00004000)
                DWordMemory (ResourceProducer, PosDecode, MinFixed, MaxFixed, Cacheable, ReadWrite,
                    0x00000000,
                    0x000C8000,
                    0x000CBFFF,
                    0x00000000,
                    0x00004000)
                DWordMemory (ResourceProducer, PosDecode, MinFixed, MaxFixed, Cacheable, ReadWrite,
                    0x00000000,
                    0x000CC000,
                    0x000CFFFF,
                    0x00000000,
                    0x00004000)
                DWordMemory (ResourceProducer, PosDecode, MinFixed, MaxFixed, Cacheable, ReadWrite,
                    0x00000000,
                    0x000D0000,
                    0x000D3FFF,
                    0x00000000,
                    0x00004000)
                DWordMemory (ResourceProducer, PosDecode, MinFixed, MaxFixed, Cacheable, ReadWrite,
                    0x00000000,
                    0x000D4000,
                    0x000D7FFF,
                    0x00000000,
                    0x00004000)
                DWordMemory (ResourceProducer, PosDecode, MinFixed, MaxFixed, Cacheable, ReadWrite,
                    0x00000000,
                    0x000D8000,
                    0x000DBFFF,
                    0x00000000,
                    0x00004000)
                DWordMemory (ResourceProducer, PosDecode, MinFixed, MaxFixed, Cacheable, ReadWrite,
                    0x00000000,
                    0x000DC000,
                    0x000DFFFF,
                    0x00000000,
                    0x00004000)
                DWordMemory (ResourceProducer, PosDecode, MinFixed, MaxFixed, Cacheable, ReadWrite,
                    0x00000000,
                    0x000E0000,
                    0x000E3FFF,
                    0x00000000,
                    0x00004000)
                DWordMemory (ResourceProducer, PosDecode, MinFixed, MaxFixed, Cacheable, ReadWrite,
                    0x00000000,
                    0x000E4000,
                    0x000E7FFF,
                    0x00000000,
                    0x00004000)
                DWordMemory (ResourceProducer, PosDecode, MinFixed, MaxFixed, Cacheable, ReadWrite,
                    0x00000000,
                    0x000E8000,
                    0x000EBFFF,
                    0x00000000,
                    0x00004000)
                DWordMemory (ResourceProducer, PosDecode, MinFixed, MaxFixed, Cacheable, ReadWrite,
                    0x00000000,
                    0x000EC000,
                    0x000EFFFF,
                    0x00000000,
                    0x00004000)
                DWordMemory (ResourceProducer, PosDecode, MinFixed, MaxFixed, Cacheable, ReadWrite,
                    0x00000000,
                    0x00100000,
                    0xFFDFFFFF,
                    0x00000000,
                    0xFFD00000)
            })
            CreateDWordField (_CRS, 0x68, C0LN)
            CreateDWordField (_CRS, 0x82, C4LN)
            CreateDWordField (_CRS, 0x9C, C8LN)
            CreateDWordField (_CRS, 0xB6, CCLN)
            CreateDWordField (_CRS, 0xD0, D0LN)
            CreateDWordField (_CRS, 0xEA, D4LN)
            CreateDWordField (_CRS, 0x0104, D8LN)
            CreateDWordField (_CRS, 0x011E, DCLN)
            CreateDWordField (_CRS, 0x0138, E0LN)
            CreateDWordField (_CRS, 0x0152, E4LN)
            CreateDWordField (_CRS, 0x016C, E8LN)
            CreateDWordField (_CRS, 0x0186, ECLN)
            CreateDWordField (_CRS, 0x0194, XXMN)
            CreateDWordField (_CRS, 0x0198, XXMX)
            CreateDWordField (_CRS, 0x01A0, XXLN)
            Method (_INI, 0, NotSerialized)
            {
                If (LEqual (\SCMP (\_OS, "Microsoft Windows"), Zero))
                {
                    Store (One, \W98F)
                }
                Else
                {
                    If (LEqual (\SCMP (\_OS, "Microsoft Windows NT"), Zero))
                    {
                        Store (One, \WNTF)
                    }
                    Else
                    {
                        If (LEqual (\SCMP (\_OS, "Microsoft WindowsME: Millennium Edition"), Zero))
                        {
                            Store (One, \WMEF)
                            Store (One, \W98F)
                        }
                    }
                }

                Multiply (DRB7, 0x00800000, Local0)
                Store (Local0, \MEMX)
                Store (Local0, XXMN)
                Add (Subtract (XXMX, XXMN), 0x01, XXLN)
                If (And (PAM1, 0x03))
                {
                    Store (0x00, C0LN)
                }

                If (And (PAM1, 0x30))
                {
                    Store (0x00, C4LN)
                }

                If (And (PAM2, 0x03))
                {
                    Store (0x00, C8LN)
                }

                If (And (PAM2, 0x30))
                {
                    Store (0x00, CCLN)
                }

                If (And (PAM3, 0x03))
                {
                    Store (0x00, D0LN)
                }

                If (And (PAM3, 0x30))
                {
                    Store (0x00, D4LN)
                }

                If (And (PAM4, 0x03))
                {
                    Store (0x00, D8LN)
                }

                If (And (PAM4, 0x30))
                {
                    Store (0x00, DCLN)
                }

                If (And (PAM5, 0x03))
                {
                    Store (0x00, E0LN)
                }

                If (And (PAM5, 0x30))
                {
                    Store (0x00, E4LN)
                }

                If (And (PAM6, 0x03))
                {
                    Store (0x00, E8LN)
                }

                If (And (PAM6, 0x30))
                {
                    Store (0x00, ECLN)
                }

                \_SB.PCI0.ISA.GPPM ()
                If (\GCHK ())
                {
                    Store (0x01, \GVEN)
                }
            }

            Name (_PRT, Package (0x07)
            {
                Package (0x04)
                {
                    0x0001FFFF,
                    0x00,
                    \_SB.LNKA,
                    0x00
                },

                Package (0x04)
                {
                    0x0002FFFF,
                    0x00,
                    \_SB.LNKA,
                    0x00
                },

                Package (0x04)
                {
                    0x0002FFFF,
                    0x01,
                    \_SB.LNKB,
                    0x00
                },

                Package (0x04)
                {
                    0x0003FFFF,
                    0x00,
                    \_SB.LNKC,
                    0x00
                },

                Package (0x04)
                {
                    0x0003FFFF,
                    0x01,
                    \_SB.LNKD,
                    0x00
                },

                Package (0x04)
                {
                    0x0005FFFF,
                    0x00,
                    \_SB.LNKA,
                    0x00
                },

                Package (0x04)
                {
                    0x0007FFFF,
                    0x03,
                    \_SB.LNKD,
                    0x00
                }
            })
            Device (IDE0)
            {
                Name (_ADR, 0x00070001)
                OperationRegion (X140, PCI_Config, 0x40, 0x10)
                Field (X140, DWordAcc, NoLock, Preserve)
                {
                    XPT0,   1,
                    XPI0,   1,
                    XPP0,   1,
                    XPD0,   1,
                    XPT1,   1,
                    XPI1,   1,
                    XPP1,   1,
                    XPD1,   1,
                    XPRT,   2,
                        ,   2,
                    XPIS,   2,
                    XPSE,   1,
                    XPE,    1,
                    XST0,   1,
                    XSI0,   1,
                    XSP0,   1,
                    XSD0,   1,
                    XST1,   1,
                    XSI1,   1,
                    XSP1,   1,
                    XSD1,   1,
                    XSRT,   2,
                        ,   2,
                    XSIS,   2,
                    XSSE,   1,
                    XSE,    1,
                    XVRT,   2,
                    XVIS,   2,
                    Offset (0x05),
                    Offset (0x08),
                    XEP0,   1,
                    XEP1,   1,
                    XES0,   1,
                    XES1,   1,
                    Offset (0x09),
                    Offset (0x0A),
                    XUP0,   2,
                        ,   2,
                    XUP1,   2,
                    Offset (0x0B),
                    XUS0,   2,
                        ,   2,
                    XUS1,   2,
                    Offset (0x0C)
                }

                Device (PRIM)
                {
                    Name (_ADR, 0x00)
                    Method (_GTM, 0, NotSerialized)
                    {
                        Subtract (0x05, XPIS, Local0)
                        Subtract (0x04, XPRT, Local1)
                        Add (Local0, Local1, Local0)
                        Multiply (0x1E, Local0, Local0)
                        If (LGreater (Local0, 0xF0))
                        {
                            Store (0x0384, Local0)
                        }

                        If (XEP0)
                        {
                            Store (0x11, Local4)
                            If (LEqual (XUP0, 0x00))
                            {
                                Store (0x78, Local1)
                            }
                            Else
                            {
                                If (LEqual (XUP0, 0x01))
                                {
                                    Store (0x50, Local1)
                                }
                                Else
                                {
                                    Store (0x3C, Local1)
                                }
                            }
                        }
                        Else
                        {
                            Store (0x10, Local4)
                            Store (Local0, Local1)
                        }

                        If (XPI0)
                        {
                            Or (Local4, 0x02, Local4)
                        }

                        If (XPSE)
                        {
                            Subtract (0x05, XVIS, Local2)
                            Subtract (0x04, XVRT, Local3)
                            Add (Local2, Local3, Local2)
                            Multiply (0x1E, Local2, Local2)
                            If (LGreater (Local2, 0xF0))
                            {
                                Store (0x0384, Local2)
                            }

                            If (XEP1)
                            {
                                Or (Local4, 0x04, Local4)
                                If (LEqual (XUP1, 0x00))
                                {
                                    Store (0x78, Local3)
                                }
                                Else
                                {
                                    If (LEqual (XUP1, 0x01))
                                    {
                                        Store (0x50, Local3)
                                    }
                                    Else
                                    {
                                        Store (0x3C, Local3)
                                    }
                                }
                            }
                            Else
                            {
                                Store (Local2, Local3)
                            }
                        }
                        Else
                        {
                            Store (0x00, Local2)
                            Store (0x00, Local3)
                        }

                        If (XPI1)
                        {
                            Or (Local4, 0x08, Local4)
                        }

                        Store (Local0, \GTP0)
                        Store (Local1, \GTD0)
                        Store (Local2, \GTP1)
                        Store (Local3, \GTD1)
                        Store (Local4, \GTMF)
                        Return (\BGTM)
                    }

                    Method (_STM, 3, NotSerialized)
                    {
                        CreateDWordField (Arg0, 0x00, STP0)
                        CreateDWordField (Arg0, 0x04, STD0)
                        CreateDWordField (Arg0, 0x08, STP1)
                        CreateDWordField (Arg0, 0x0C, STD1)
                        CreateDWordField (Arg0, 0x10, STMF)
                        If (SizeOf (Arg1))
                        {
                            CreateWordField (Arg1, 0x01, PMZR)
                            If (PMZR)
                            {
                                Store (One, Local5)
                            }
                            Else
                            {
                                Store (Zero, Local5)
                            }
                        }
                        Else
                        {
                            Store (Zero, Local5)
                        }

                        If (Local5)
                        {
                            If (\W98F)
                            {
                                CreateWordField (Arg1, 0x66, PM51)
                                CreateWordField (Arg1, 0x6A, PM53)
                                CreateWordField (Arg1, 0x7C, PM62)
                                CreateWordField (Arg1, 0x7E, PM63)
                                CreateWordField (Arg1, 0x80, PM64)
                                CreateWordField (Arg1, 0x82, PM65)
                                CreateWordField (Arg1, 0x88, PM68)
                                CreateWordField (Arg1, 0xB0, PM88)
                                Store (\UDMA (PM53, PM88), Local0)
                                If (LGreater (Local0, 0x03))
                                {
                                    Store (0x03, Local0)
                                }

                                Store (\MDMA (PM53, PM63, PM62, PM65), Local1)
                                Store (\MPIO (PM53, PM64, PM51, PM68), Local2)
                                Store (\MPI4 (Local1, Local2), Local3)
                            }
                            Else
                            {
                                Store (\MPIB (And (STMF, 0x02), STP0), Local2)
                                Store (\UDMB (And (STMF, 0x01), STD0), Local0)
                                Store (\MP4B (Local2), Local3)
                                Store (Local3, Local1)
                            }

                            Store (\MTIM (Local3, Local2, And (PMZR, 0x80)), Local4)
                            If (And (Local4, 0x01))
                            {
                                Store (One, XPT0)
                            }

                            If (And (Local4, 0x02))
                            {
                                Store (One, XPI0)
                            }

                            If (And (Local4, 0x04))
                            {
                                Store (One, XPP0)
                            }

                            If (And (Local4, 0x08))
                            {
                                Store (One, XPD0)
                            }

                            Store (\MISP (Local3), XPIS)
                            Store (\MRTC (Local3), XPRT)
                            If (Local0)
                            {
                                Store (One, XEP0)
                                Store (\MUCT (Local0), XUP0)
                            }
                            Else
                            {
                                Store (Zero, XEP0)
                                Store (Zero, XUP0)
                            }

                            Store (\MHDM (Local0, Local1), \HDM0)
                            Store (\MHPI (Local2), \HPI0)
                        }

                        If (SizeOf (Arg2))
                        {
                            CreateWordField (Arg2, 0x01, PS00)
                            If (PS00)
                            {
                                Store (One, Local5)
                            }
                            Else
                            {
                                Store (Zero, Local5)
                            }
                        }
                        Else
                        {
                            Store (Zero, Local5)
                        }

                        If (Local5)
                        {
                            If (\W98F)
                            {
                                CreateWordField (Arg2, 0x66, PS51)
                                CreateWordField (Arg2, 0x6A, PS53)
                                CreateWordField (Arg2, 0x7C, PS62)
                                CreateWordField (Arg2, 0x7E, PS63)
                                CreateWordField (Arg2, 0x80, PS64)
                                CreateWordField (Arg2, 0x82, PS65)
                                CreateWordField (Arg2, 0x88, PS68)
                                CreateWordField (Arg2, 0xB0, PS88)
                                Store (\UDMA (PS53, PS88), Local0)
                                If (LGreater (Local0, 0x03))
                                {
                                    Store (0x03, Local0)
                                }

                                Store (\MDMA (PS53, PS63, PS62, PS65), Local1)
                                Store (\MPIO (PS53, PS64, PS51, PS68), Local2)
                                Store (\MPI4 (Local1, Local2), Local3)
                            }
                            Else
                            {
                                Store (\MPIB (And (STMF, 0x08), STP1), Local2)
                                Store (\UDMB (And (STMF, 0x04), STD1), Local0)
                                Store (\MP4B (Local2), Local3)
                                Store (Local3, Local1)
                            }

                            Store (One, XPSE)
                            Store (\MTIM (Local3, Local2, And (PS00, 0x80)), Local4)
                            If (And (Local4, 0x01))
                            {
                                Store (One, XPT1)
                            }

                            If (And (Local4, 0x02))
                            {
                                Store (One, XPI1)
                            }

                            If (And (Local4, 0x04))
                            {
                                Store (One, XPP1)
                            }

                            If (And (Local4, 0x08))
                            {
                                Store (One, XPD1)
                            }

                            Store (\MISP (Local3), XVIS)
                            Store (\MRTC (Local3), XVRT)
                            If (Local0)
                            {
                                Store (One, XEP1)
                                Store (\MUCT (Local0), XUP1)
                            }
                            Else
                            {
                                Store (Zero, XEP1)
                                Store (Zero, XUP1)
                            }

                            Store (\MHDM (Local0, Local1), \HDM1)
                            Store (\MHDM (Local0, Local1), \CDM1)
                            Store (\MHPI (Local2), \HPI1)
                            Store (\MHPI (Local2), \CPI1)
                        }
                    }

                    Device (MSTR)
                    {
                        Name (_ADR, 0x00)
                        Method (_GTF, 0, NotSerialized)
                        {
                            Return (\ICM0)
                        }
                    }
                }

                Device (SCND)
                {
                    Name (_ADR, 0x01)
                    Method (_GTM, 0, NotSerialized)
                    {
                        Subtract (0x05, XSIS, Local0)
                        Subtract (0x04, XSRT, Local1)
                        Add (Local0, Local1, Local0)
                        Multiply (0x1E, Local0, Local0)
                        If (LGreater (Local0, 0xF0))
                        {
                            Store (0x0384, Local0)
                        }

                        If (XES0)
                        {
                            Store (0x11, Local2)
                            If (LEqual (XUS0, 0x00))
                            {
                                Store (0x78, Local1)
                            }
                            Else
                            {
                                If (LEqual (XUS0, 0x01))
                                {
                                    Store (0x50, Local1)
                                }
                                Else
                                {
                                    Store (0x3C, Local1)
                                }
                            }
                        }
                        Else
                        {
                            Store (0x10, Local2)
                            Store (Local0, Local1)
                        }

                        If (XSI0)
                        {
                            Or (Local2, 0x02, Local2)
                        }

                        Store (Local0, \GTP0)
                        Store (Local1, \GTD0)
                        Store (Zero, \GTP1)
                        Store (Zero, \GTD1)
                        Store (Local2, \GTMF)
                        Return (\BGTM)
                    }

                    Method (_STM, 3, NotSerialized)
                    {
                        CreateDWordField (Arg0, 0x00, STP0)
                        CreateDWordField (Arg0, 0x04, STD0)
                        CreateDWordField (Arg0, 0x08, STP1)
                        CreateDWordField (Arg0, 0x0C, STD1)
                        CreateDWordField (Arg0, 0x10, STMF)
                        If (SizeOf (Arg1))
                        {
                            CreateWordField (Arg1, 0x01, SM00)
                            If (SM00)
                            {
                                Store (One, Local5)
                            }
                            Else
                            {
                                Store (Zero, Local5)
                            }
                        }
                        Else
                        {
                            Store (Zero, Local5)
                        }

                        If (Local5)
                        {
                            If (\W98F)
                            {
                                CreateWordField (Arg1, 0x66, SM51)
                                CreateWordField (Arg1, 0x6A, SM53)
                                CreateWordField (Arg1, 0x7C, SM62)
                                CreateWordField (Arg1, 0x7E, SM63)
                                CreateWordField (Arg1, 0x80, SM64)
                                CreateWordField (Arg1, 0x82, SM65)
                                CreateWordField (Arg1, 0x88, SM68)
                                CreateWordField (Arg1, 0xB0, SM88)
                                Store (\UDMA (SM53, SM88), Local0)
                                If (LGreater (Local0, 0x03))
                                {
                                    Store (0x03, Local0)
                                }

                                Store (\MDMA (SM53, SM63, SM62, SM65), Local1)
                                Store (\MPIO (SM53, SM64, SM51, SM68), Local2)
                                Store (\MPI4 (Local1, Local2), Local3)
                            }
                            Else
                            {
                                Store (\MPIB (And (STMF, 0x02), STP0), Local2)
                                Store (\UDMB (And (STMF, 0x01), STD0), Local0)
                                Store (\MP4B (Local2), Local3)
                                Store (Local3, Local1)
                            }

                            Store (\MTIM (Local3, Local2, And (SM00, 0x80)), Local4)
                            If (And (Local4, 0x01))
                            {
                                Store (One, XST0)
                            }

                            If (And (Local4, 0x02))
                            {
                                Store (One, XSI0)
                            }

                            If (And (Local4, 0x04))
                            {
                                Store (One, XSP0)
                            }

                            If (And (Local4, 0x08))
                            {
                                Store (One, XSD0)
                            }

                            Store (\MISP (Local3), XSIS)
                            Store (\MRTC (Local3), XSRT)
                            If (Local0)
                            {
                                Store (One, XES0)
                                Store (\MUCT (Local0), XUS0)
                            }
                            Else
                            {
                                Store (Zero, XES0)
                                Store (Zero, XUS0)
                            }

                            Store (\MHDM (Local0, Local1), \HDM2)
                            Store (\MHDM (Local0, Local1), \CDM2)
                            Store (\MHPI (Local2), \HPI2)
                            Store (\MHPI (Local2), \CPI2)
                            Store (MHDM (Local0, Local1), \DDM2)
                            Store (MHPI (Local2), \DPI2)
                        }
                    }

                    Device (MSTR)
                    {
                        Name (_ADR, 0x00)
                        Method (_GTF, 0, NotSerialized)
                        {
                            Store (\_SB.PCI0.ISA.EC.GUID (), Local0)
                            If (LEqual (Local0, 0x06))
                            {
                                Return (\ICM2)
                            }

                            Store (Zero, Local1)
                            If (LEqual (Local0, 0x0B))
                            {
                                Store (One, Local1)
                            }

                            If (LEqual (Local0, 0x03))
                            {
                                Store (One, Local1)
                            }

                            If (LEqual (Local0, 0x0A))
                            {
                                Store (One, Local1)
                            }

                            If (Local1)
                            {
                                Store (\GCDT (0x00), \DTF2)
                                Store (\GCDT (0x01), \DTA2)
                                Return (\DCM2)
                            }
                            Else
                            {
                                Return (\ICC2)
                            }
                        }
                    }
                }
            }

            Device (PM00)
            {
                Name (_ADR, 0x00070003)
                OperationRegion (X3DR, PCI_Config, 0x5C, 0x20)
                Field (X3DR, DWordAcc, NoLock, Preserve)
                {
                        ,   1,
                        ,   2,
                        ,   1,
                        ,   1,
                        ,   2,
                    Offset (0x01),
                        ,   2,
                        ,   15,
                        ,   1,
                        ,   3,
                    XA0E,   1,
                    XM0E,   1,
                    XPE,    1,
                    X09A,   16,
                    X09M,   4,
                        ,   1,
                    X09E,   3,
                        ,   1,
                    XPA,    2,
                        ,   1,
                    XFA,    1,
                    XFE,    1,
                        ,   1,
                    Offset (0x08),
                    Offset (0x0B),
                    XU1A,   3,
                    XU1E,   1,
                    XU2A,   3,
                    XU2E,   1,
                    X12A,   16,
                    X12M,   4,
                    X12E,   1,
                    Offset (0x0F),
                    Offset (0x10),
                    X12O,   32,
                    X13A,   16,
                    X13M,   4,
                    X13E,   1,
                    Offset (0x17),
                    Offset (0x18),
                    X13O,   32,
                    Offset (0x20)
                }

                OperationRegion (SMBC, PCI_Config, 0xD2, 0x01)
                Field (SMBC, ByteAcc, NoLock, Preserve)
                {
                    SBHE,   1,
                    SBIS,   3
                }

                OperationRegion (GLEN, SystemIO, 0x1020, 0x02)
                Field (GLEN, WordAcc, NoLock, Preserve)
                {
                        ,   15,
                    BLEN,   1
                }
            }

            Device (USB)
            {
                Name (_ADR, 0x00070002)
                Method (_PSW, 1, NotSerialized)
                {
                    Noop
                }

                Name (_PRW, Package (0x02)
                {
                    0x08,
                    0x01
                })
            }

            Device (AGP)
            {
                Name (_ADR, 0x00010000)
                Name (_PRT, Package (0x02)
                {
                    Package (0x04)
                    {
                        0xFFFF,
                        0x00,
                        \_SB.LNKA,
                        0x00
                    },

                    Package (0x04)
                    {
                        0xFFFF,
                        0x01,
                        \_SB.LNKB,
                        0x00
                    }
                })
                Name (EDX1, Buffer (0x80)
                {
                    0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00,
                    0x24, 0x4D, 0x55, 0x0A, 0x01, 0x01, 0x01, 0x01,
                    0x23, 0x09, 0x01, 0x02, 0x80, 0x21, 0x18, 0x00,
                    0xEA, 0x0D, 0xFB, 0xA0, 0x57, 0x47, 0x98, 0x27,
                    0x12, 0x4D, 0x51, 0xA1, 0x08, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x64, 0x19,
                    0x00, 0x40, 0x41, 0x00, 0x26, 0x30, 0x18, 0x88,
                    0x36, 0x00, 0x0E, 0xCB, 0x10, 0x00, 0x00, 0x1A,
                    0x00, 0x00, 0x00, 0xFC, 0x00, 0x54, 0x68, 0x69,
                    0x6E, 0x6B, 0x50, 0x61, 0x64, 0x20, 0x4C, 0x43,
                    0x44, 0x20, 0x00, 0x00, 0x00, 0xFC, 0x00, 0x31,
                    0x30, 0x32, 0x34, 0x78, 0x37, 0x36, 0x38, 0x20,
                    0x20, 0x20, 0x20, 0x20, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x33
                })
                Name (EDX2, Buffer (0x0100)
                {
                    0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00,
                    0x24, 0x4D, 0x55, 0x0A, 0x01, 0x01, 0x01, 0x01,
                    0x23, 0x09, 0x01, 0x02, 0x80, 0x21, 0x18, 0x00,
                    0xEA, 0x0D, 0xFB, 0xA0, 0x57, 0x47, 0x98, 0x27,
                    0x12, 0x4D, 0x51, 0xA1, 0x08, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x64, 0x19,
                    0x00, 0x40, 0x41, 0x00, 0x26, 0x30, 0x18, 0x88,
                    0x36, 0x00, 0x0E, 0xCB, 0x10, 0x00, 0x00, 0x1A,
                    0x00, 0x00, 0x00, 0xFC, 0x00, 0x54, 0x68, 0x69,
                    0x6E, 0x6B, 0x50, 0x61, 0x64, 0x20, 0x4C, 0x43,
                    0x44, 0x20, 0x00, 0x00, 0x00, 0xFC, 0x00, 0x31,
                    0x30, 0x32, 0x34, 0x78, 0x37, 0x36, 0x38, 0x20,
                    0x20, 0x20, 0x20, 0x20, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x33,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
                })
                Name (EDT1, Buffer (0x80)
                {
                    0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00,
                    0xC1, 0xD0, 0xFE, 0x09, 0x01, 0x01, 0x01, 0x01,
                    0x23, 0x09, 0x01, 0x02, 0x00, 0x00, 0x00, 0x00,
                    0xEA, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0xA1, 0x08, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x31, 0x58, 0x1C, 0x20, 0x28, 0x80,
                    0x01, 0x00, 0xF6, 0xB8, 0x00, 0x00, 0x00, 0x1A,
                    0x00, 0x00, 0x00, 0xFC, 0x00, 0x54, 0x68, 0x69,
                    0x6E, 0x6B, 0x50, 0x61, 0x64, 0x20, 0x54, 0x56,
                    0x20, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x59
                })
                Name (EDT2, Buffer (0x0100)
                {
                    0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00,
                    0xC1, 0xD0, 0xFE, 0x09, 0x01, 0x01, 0x01, 0x01,
                    0x23, 0x09, 0x01, 0x02, 0x00, 0x00, 0x00, 0x00,
                    0xEA, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0xA1, 0x08, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x31, 0x58, 0x1C, 0x20, 0x28, 0x80,
                    0x01, 0x00, 0xF6, 0xB8, 0x00, 0x00, 0x00, 0x1A,
                    0x00, 0x00, 0x00, 0xFC, 0x00, 0x54, 0x68, 0x69,
                    0x6E, 0x6B, 0x50, 0x61, 0x64, 0x20, 0x54, 0x56,
                    0x20, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x59,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
                })
                Mutex (MDGS, 0x07)
                Name (VDEE, 0x01)
                Name (VDDA, Buffer (0x02) {})
                CreateBitField (VDDA, 0x00, VUPC)
                CreateBitField (VDDA, 0x01, VQDL)
                CreateBitField (VDDA, 0x02, VQDC)
                CreateBitField (VDDA, 0x03, VQDT)
                CreateBitField (VDDA, 0x04, VQDD)
                CreateBitField (VDDA, 0x05, VSDL)
                CreateBitField (VDDA, 0x06, VSDC)
                CreateBitField (VDDA, 0x07, VSDT)
                CreateBitField (VDDA, 0x08, VSDD)
                CreateBitField (VDDA, 0x0A, MSWT)
                CreateBitField (VDDA, 0x0B, VWST)
                CreateBitField (VDDA, 0x0D, VPWR)
                Device (VID)
                {
                    Name (_ADR, 0x00)
                    Name (_S1D, 0x01)
                    Name (_S3D, 0x03)
                    Method (_INI, 0, NotSerialized)
                    {
                        \VUPS (0x02)
                        Store (\VCDL, VQDL)
                        Store (\VCDC, VQDC)
                        Store (\VCDT, VQDT)
                        Store (\VCDD, VQDD)
                    }

                    Method (_PS0, 0, NotSerialized)
                    {
                        Store (0x01, VPWR)
                    }

                    Method (_PS1, 0, NotSerialized)
                    {
                        Store (0x00, VPWR)
                    }

                    Method (_PS2, 0, NotSerialized)
                    {
                        Store (0x00, VPWR)
                    }

                    Method (_PS3, 0, NotSerialized)
                    {
                        Store (0x00, VPWR)
                    }

                    Method (VSWT, 0, NotSerialized)
                    {
                        \VUPS (0x80)
                        If (LNot (\VCIN))
                        {
                            Store (0x01, Local0)
                            Store (0x00, Local2)
                            If (\VCDT)
                            {
                                Or (0x04, Local2, Local2)
                            }

                            If (\VCDL)
                            {
                                Add (0x01, Local0, Local0)
                            }

                            If (\VCDC)
                            {
                                Add (0x02, Local0, Local0)
                            }

                            If (LEqual (0x04, Local0))
                            {
                                Store (0x01, Local1)
                            }
                            Else
                            {
                                Store (Local0, Local1)
                            }

                            Or (Local2, Local1, Local1)
                            ASWT (Local1, 0x01)
                        }
                    }

                    Method (VLOC, 1, NotSerialized)
                    {
                        If (VPWR)
                        {
                            If (Arg0)
                            {
                                \VUPS (0x81)
                                If (LNot (VCSS))
                                {
                                    If (LNot (\VCDL))
                                    {
                                        ASWT (0x01, 0x00)
                                        \VNRS (0x01)
                                    }
                                }
                            }
                        }
                    }

                    Method (_DOS, 1, NotSerialized)
                    {
                        If (LEqual (Arg0, 0x02))
                        {
                            Store (0x01, Local0)
                            While (Local0)
                            {
                                Acquire (MDGS, 0xFFFF)
                                If (LEqual (0x00, MSWT))
                                {
                                    Store (0x01, MSWT)
                                    Store (0x00, Local0)
                                    Store (Arg0, VDEE)
                                }

                                Release (MDGS)
                                Sleep (0x01)
                            }
                        }
                        Else
                        {
                            Acquire (MDGS, 0xFFFF)
                            If (LEqual (VDEE, 0x02))
                            {
                                Store (0x00, MSWT)
                            }

                            If (LGreater (Arg0, 0x02))
                            {
                                Store (0x01, VDEE)
                            }
                            Else
                            {
                                Store (Arg0, VDEE)
                            }

                            Release (MDGS)
                        }
                    }

                    Method (_DOD, 0, NotSerialized)
                    {
                        Return (Package (0x03)
                        {
                            0x00010110,
                            0x00010100,
                            0x00010200
                        })
                    }

                    Method (ASWT, 2, NotSerialized)
                    {
                        If (LEqual (0x01, VDEE))
                        {
                            \VSDS (Arg0, 0x01)
                        }
                        Else
                        {
                            Store (0x01, Local0)
                            While (Local0)
                            {
                                Acquire (MDGS, 0xFFFF)
                                If (LEqual (0x00, MSWT))
                                {
                                    Store (0x00, Local0)
                                    If (And (0x01, Arg1))
                                    {
                                        Store (0x01, VUPC)
                                    }
                                    Else
                                    {
                                        Store (0x00, VUPC)
                                    }

                                    If (And (0x01, Arg0))
                                    {
                                        Store (0x01, VQDL)
                                    }
                                    Else
                                    {
                                        Store (0x00, VQDL)
                                    }

                                    If (And (0x02, Arg0))
                                    {
                                        Store (0x01, VQDC)
                                    }
                                    Else
                                    {
                                        Store (0x00, VQDC)
                                    }

                                    If (And (0x04, Arg0))
                                    {
                                        Store (0x01, VQDT)
                                    }
                                    Else
                                    {
                                        Store (0x00, VQDT)
                                    }
                                }

                                Release (MDGS)
                                Sleep (0x01)
                            }

                            If (And (0x02, Arg1))
                            {
                                Notify (\_SB.PCI0.AGP.VID, 0x81)
                            }
                            Else
                            {
                                Notify (\_SB.PCI0.AGP.VID, 0x80)
                            }
                        }
                    }

                    Method (VDSW, 1, NotSerialized)
                    {
                        If (LNot (Arg0))
                        {
                            ASWT (0x01, 0x00)
                            \VNRS (0x05)
                        }
                    }

                    Device (LCD0)
                    {
                        Name (_ADR, 0x0110)
                        Method (_DCS, 0, NotSerialized)
                        {
                            \VUPS (0x00)
                            If (\VCDL)
                            {
                                Return (0x1F)
                            }
                            Else
                            {
                                Return (0x1D)
                            }
                        }

                        Method (_DDC, 1, NotSerialized)
                        {
                            If (LEqual (\VLID, 0x02))
                            {
                                If (LEqual (Arg0, 0x01))
                                {
                                    Return (EDX1)
                                }
                                Else
                                {
                                    If (LEqual (Arg0, 0x02))
                                    {
                                        Return (EDX2)
                                    }
                                }
                            }
                        }

                        Method (_DGS, 0, NotSerialized)
                        {
                            Return (VQDL)
                        }

                        Method (_DSS, 1, NotSerialized)
                        {
                            And (Arg0, 0x01, VSDL)
                            If (And (Arg0, 0x80000000))
                            {
                                If (And (Arg0, 0x40000000))
                                {
                                    DSWT (0x02)
                                }
                                Else
                                {
                                    DSWT (0x01)
                                }
                            }
                        }
                    }

                    Device (CRT0)
                    {
                        Name (_ADR, 0x0100)
                        Method (_DCS, 0, NotSerialized)
                        {
                            \VUPS (0x01)
                            If (\VCSS)
                            {
                                If (\VCDC)
                                {
                                    Return (0x1F)
                                }
                                Else
                                {
                                    Return (0x1D)
                                }
                            }
                            Else
                            {
                                If (\VCDC)
                                {
                                    Return (0x0F)
                                }
                                Else
                                {
                                    Return (0x0D)
                                }
                            }
                        }

                        Method (_DDC, 1, NotSerialized)
                        {
                            \VDDC ()
                            If (LEqual (Arg0, 0x01))
                            {
                                Return (\DDC1)
                            }
                            Else
                            {
                                If (LEqual (Arg0, 0x02))
                                {
                                    Return (\DDC2)
                                }
                                Else
                                {
                                    Return (0x00)
                                }
                            }
                        }

                        Method (_DGS, 0, NotSerialized)
                        {
                            Return (VQDC)
                        }

                        Method (_DSS, 1, NotSerialized)
                        {
                            And (Arg0, 0x01, VSDC)
                            If (And (Arg0, 0x80000000))
                            {
                                If (And (Arg0, 0x40000000))
                                {
                                    DSWT (0x02)
                                }
                                Else
                                {
                                    DSWT (0x01)
                                }
                            }
                        }
                    }

                    Device (TV0)
                    {
                        Name (_ADR, 0x0200)
                        Method (_DCS, 0, NotSerialized)
                        {
                            \VUPS (0x00)
                            If (\VCDT)
                            {
                                Return (0x1F)
                            }
                            Else
                            {
                                Return (0x1D)
                            }
                        }

                        Method (_DDC, 1, NotSerialized)
                        {
                            If (LEqual (Arg0, 0x01))
                            {
                                Return (EDT1)
                            }
                            Else
                            {
                                If (LEqual (Arg0, 0x02))
                                {
                                    Return (EDT2)
                                }
                            }
                        }

                        Method (_DGS, 0, NotSerialized)
                        {
                            Return (VQDT)
                        }

                        Method (_DSS, 1, NotSerialized)
                        {
                            And (Arg0, 0x01, VSDT)
                            If (And (Arg0, 0x80000000))
                            {
                                If (And (Arg0, 0x40000000))
                                {
                                    DSWT (0x02)
                                }
                                Else
                                {
                                    DSWT (0x01)
                                }
                            }
                        }
                    }

                    Method (DSWT, 1, NotSerialized)
                    {
                        If (VSDL)
                        {
                            Store (0x01, Local0)
                        }
                        Else
                        {
                            Store (0x00, Local0)
                        }

                        If (VSDC)
                        {
                            Or (0x02, Local0, Local0)
                        }

                        If (Local0)
                        {
                            If (VUPC)
                            {
                                \VSDS (Local0, Arg0)
                            }
                        }
                        Else
                        {
                            Noop
                        }
                    }
                }
            }

            Device (ISA)
            {
                Name (_ADR, 0x00070000)
                OperationRegion (PIRQ, PCI_Config, 0x60, 0x60)
                Field (PIRQ, AnyAcc, NoLock, Preserve)
                {
                    PIRA,   8,
                    PIRB,   8,
                    PIRC,   8,
                    PIRD,   8,
                    SIRQ,   8,
                    Offset (0x16),
                    CH00,   3,
                        ,   4,
                    FE00,   1,
                    CH01,   3,
                        ,   4,
                    FE01,   1,
                    Offset (0x22),
                    P21E,   3,
                    Offset (0x23),
                    Offset (0x50),
                        ,   1,
                        ,   1,
                        ,   1,
                        ,   1,
                    GCR4,   1,
                        ,   1,
                        ,   1,
                    Offset (0x51),
                        ,   1,
                        ,   1,
                        ,   1,
                        ,   1,
                    GCRC,   1,
                        ,   1,
                        ,   1,
                    Offset (0x52),
                        ,   1,
                        ,   1,
                        ,   1,
                        ,   1,
                        ,   1,
                        ,   1,
                    SUS2,   1,
                    Offset (0x54),
                    Offset (0x60)
                }

                Device (SIO)
                {
                    Name (_HID, EisaId ("PNP0C02"))
                    Name (_UID, 0x00)
                    Name (_STA, 0x0B)
                    Name (_CRS, ResourceTemplate ()
                    {
                        IO (Decode16, 0x0022, 0x0022, 0x01, 0x01)
                        IO (Decode16, 0x0092, 0x0092, 0x01, 0x01)
                        IO (Decode16, 0x00B2, 0x00B2, 0x01, 0x02)
                        IO (Decode16, 0x1000, 0x1000, 0x01, 0x40)
                        IO (Decode16, 0x1040, 0x1040, 0x01, 0x10)
                        IO (Decode16, 0xFE00, 0xFE00, 0x01, 0x10)
                    })
                }

                Device (PIC)
                {
                    Name (_HID, EisaId ("PNP0000"))
                    Name (_CRS, ResourceTemplate ()
                    {
                        IO (Decode16, 0x0020, 0x0020, 0x01, 0x02)
                        IO (Decode16, 0x00A0, 0x00A0, 0x01, 0x02)
                        IO (Decode16, 0x04D0, 0x04D0, 0x01, 0x02)
                        IRQNoFlags () {2}
                    })
                }

                Device (TIMR)
                {
                    Name (_HID, EisaId ("PNP0100"))
                    Name (_CRS, ResourceTemplate ()
                    {
                        IO (Decode16, 0x0040, 0x0040, 0x01, 0x04)
                        IRQNoFlags () {0}
                    })
                }

                Device (DMAC)
                {
                    Name (_HID, EisaId ("PNP0200"))
                    Name (_CRS, ResourceTemplate ()
                    {
                        IO (Decode16, 0x0000, 0x0000, 0x01, 0x10)
                        IO (Decode16, 0x0080, 0x0080, 0x01, 0x10)
                        IO (Decode16, 0x00C0, 0x00C0, 0x01, 0x20)
                        DMA (Compatibility, BusMaster, Transfer8) {4}
                    })
                }

                Device (SPKR)
                {
                    Name (_HID, EisaId ("PNP0800"))
                    Name (_CRS, ResourceTemplate ()
                    {
                        IO (Decode16, 0x0061, 0x0061, 0x01, 0x01)
                    })
                }

                Device (FPU)
                {
                    Name (_HID, EisaId ("PNP0C04"))
                    Name (_CRS, ResourceTemplate ()
                    {
                        IO (Decode16, 0x00F0, 0x00F0, 0x01, 0x10)
                        IRQNoFlags () {13}
                    })
                }

                Device (RTC)
                {
                    Name (_HID, EisaId ("PNP0B00"))
                    Name (_CRS, ResourceTemplate ()
                    {
                        IO (Decode16, 0x0070, 0x0070, 0x01, 0x04)
                        IRQNoFlags () {8}
                    })
                }

                Device (KBD)
                {
                    Name (_HID, EisaId ("PNP0303"))
                    Name (_CRS, ResourceTemplate ()
                    {
                        IO (Decode16, 0x0060, 0x0060, 0x01, 0x01)
                        IO (Decode16, 0x0064, 0x0064, 0x01, 0x01)
                        IRQNoFlags () {1}
                    })
                }

                Device (MOU)
                {
                    Name (_HID, EisaId ("IBM3780"))
                    Name (_CID, 0x130FD041)
                    Name (_CRS, ResourceTemplate ()
                    {
                        IRQNoFlags () {12}
                    })
                }

                Device (PMGA)
                {
                    Name (_HID, EisaId ("PNP0C02"))
                    Name (_UID, 0x02)
                    Name (_STA, 0x0B)
                    Name (_CRS, ResourceTemplate ()
                    {
                        IO (Decode16, 0x15E0, 0x15E0, 0x01, 0x10)
                    })
                }

                OperationRegion (IMGA, SystemIO, 0x15EC, 0x04)
                Field (IMGA, ByteAcc, NoLock, Preserve)
                {
                    IND0,   8,
                    DAT0,   8,
                    IND1,   8,
                    DAT1,   8
                }

                IndexField (IND0, DAT0, ByteAcc, NoLock, Preserve)
                {
                    Offset (0x7F),
                    ACI,    8
                }

                IndexField (IND1, DAT1, ByteAcc, NoLock, Preserve)
                {
                        ,   4,
                    VDPW,   1,
                    CBPW,   1,
                    BREN,   1,
                    Offset (0x01),
                    Offset (0x07),
                        ,   2,
                    SSBY,   1,
                    Offset (0x08),
                    Offset (0x21),
                        ,   1,
                        ,   1,
                    BTON,   1,
                        ,   1,
                    Offset (0x22),
                    Offset (0x2D),
                    BUSC,   1,
                    BUSD,   1,
                    SCIS,   1,
                    SCIR,   2,
                    SLCK,   1,
                    WOLE,   1,
                    Offset (0x2E)
                }

                Method (HBEN, 0, NotSerialized)
                {
                    If (\GLPW ())
                    {
                        Store (0x01, BREN)
                    }
                }

                Method (HBDS, 0, NotSerialized)
                {
                    If (\GLPW ())
                    {
                        Store (0x00, BREN)
                    }
                }

                PowerResource (PSER, 0x00, 0x0000)
                {
                    Method (_STA, 0, NotSerialized)
                    {
                        Return (XOr (SSBY, 0x01))
                    }

                    Method (_ON, 0, NotSerialized)
                    {
                        Store (0x00, SSBY)
                    }

                    Method (_OFF, 0, NotSerialized)
                    {
                        Store (0x01, SSBY)
                    }
                }

                Device (SPIO)
                {
                    Name (_HID, EisaId ("PNP0C02"))
                    Name (_UID, 0x01)
                    Name (_STA, 0x0B)
                    Name (_CRS, ResourceTemplate ()
                    {
                        IO (Decode16, 0x002E, 0x002E, 0x01, 0x02)
                    })
                }

                OperationRegion (NCFG, SystemIO, 0x2E, 0x02)
                Field (NCFG, ByteAcc, NoLock, Preserve)
                {
                    INDX,   8,
                    DATA,   8
                }

                IndexField (INDX, DATA, ByteAcc, NoLock, Preserve)
                {
                    FER,    8,
                    FAR,    8,
                    PTR,    8,
                    FCR,    8,
                    PCR,    8,
                    Offset (0x06),
                    PMC,    8,
                    TUP,    8,
                    SID,    8,
                    ASC,    8,
                    S0LA,   8,
                    S0CF,   8,
                    S1LA,   8,
                    S1CF,   8,
                    Offset (0x10),
                    S0HA,   8,
                    S1HA,   8,
                    SCF0,   8,
                    Offset (0x18),
                    SCF1,   8,
                    Offset (0x1B),
                    PNP0,   8,
                    PNP1,   8,
                    Offset (0x40),
                    SCF2,   8,
                    PNP2,   8,
                    PBAL,   8,
                    PBAH,   8,
                    U1AL,   8,
                    U1AH,   8,
                    U2AL,   8,
                    U2AH,   8,
                    FBAL,   8,
                    FBAH,   8,
                    SBAL,   8,
                    SBAH,   8,
                    IRQ1,   8,
                    IRQ2,   8,
                    IRQ3,   8,
                    PNP3,   8,
                    SCF3,   8,
                    CLK,    8
                }

                PowerResource (PSIO, 0x00, 0x0000)
                {
                    Name (PSTS, 0x01)
                    Method (_STA, 0, NotSerialized)
                    {
                        Return (PSTS)
                    }

                    Method (_ON, 0, NotSerialized)
                    {
                        And (PTR, 0xFE, PTR)
                        Store (0x01, PSTS)
                    }

                    Method (_OFF, 0, NotSerialized)
                    {
                        Store (0x00, PSTS)
                    }
                }

                Device (FDC)
                {
                    Name (_HID, EisaId ("PNP0700"))
                    Name (_PR0, Package (0x01)
                    {
                        PSIO
                    })
                    Method (_STA, 0, NotSerialized)
                    {
                        Store (\_SB.PCI0.PM00.XFE, Local0)
                        If (Local0)
                        {
                            Return (0x0F)
                        }
                        Else
                        {
                            Return (0x0D)
                        }
                    }

                    Method (_DIS, 0, NotSerialized)
                    {
                        And (PNP2, 0x80, PNP2)
                        Store (Zero, \_SB.PCI0.PM00.XFE)
                    }

                    Name (_CRS, ResourceTemplate ()
                    {
                        IO (Decode16, 0x03F0, 0x03F0, 0x01, 0x06)
                        IO (Decode16, 0x03F7, 0x03F7, 0x01, 0x01)
                        IRQNoFlags () {6}
                        DMA (Compatibility, NotBusMaster, Transfer8) {2}
                    })
                    Name (_PRS, ResourceTemplate ()
                    {
                        IO (Decode16, 0x03F0, 0x03F0, 0x01, 0x06)
                        IO (Decode16, 0x03F7, 0x03F7, 0x01, 0x01)
                        IRQNoFlags () {6}
                        DMA (Compatibility, NotBusMaster, Transfer8) {2}
                    })
                    Method (_SRS, 1, NotSerialized)
                    {
                        And (FBAL, 0x01, Local0)
                        Or (Local0, 0xFC, FBAL)
                        And (FBAH, 0x03, FBAH)
                        And (PNP2, 0x80, Local0)
                        Or (Local0, 0x36, PNP2)
                        If (And (FER, 0x08, Local1)) {}
                        Else
                        {
                            Or (FER, 0x08, FER)
                        }

                        Store (Zero, \_SB.PCI0.PM00.XFA)
                        Store (One, \_SB.PCI0.PM00.XFE)
                        If (LEqual (\_SB.PCI0.ISA.EC.BDEV, 0x0D))
                        {
                            \SFDD (0x00)
                        }
                        Else
                        {
                            \SFDD (0x01)
                        }
                    }
                }

                Device (UART)
                {
                    Name (_HID, EisaId ("PNP0501"))
                    Name (_EJD, "_SB.PCI0.DOCK")
                    Name (_PR0, Package (0x02)
                    {
                        PSIO,
                        PSER
                    })
                    Name (_PRW, Package (0x02)
                    {
                        0x0B,
                        0x03
                    })
                    Method (_PSW, 1, NotSerialized)
                    {
                        If (\H8DR)
                        {
                            If (Arg0)
                            {
                                Store (0x01, \_SB.PCI0.ISA.EC.HWRI)
                            }
                            Else
                            {
                                Store (0x00, \_SB.PCI0.ISA.EC.HWRI)
                            }
                        }
                        Else
                        {
                            If (Arg0)
                            {
                                \MBEC (0x32, 0xFF, 0x40)
                            }
                            Else
                            {
                                \MBEC (0x32, 0xBF, 0x00)
                            }
                        }
                    }

                    Method (_STA, 0, NotSerialized)
                    {
                        If (And (FER, 0x02))
                        {
                            Return (0x0F)
                        }
                        Else
                        {
                            Return (0x0D)
                        }
                    }

                    Method (_DIS, 0, NotSerialized)
                    {
                        And (FER, 0xFD, FER)
                        Store (Zero, \_SB.PCI0.PM00.XU1E)
                    }

                    Method (_CRS, 0, NotSerialized)
                    {
                        Name (BUFF, ResourceTemplate ()
                        {
                            IO (Decode16, 0x03F8, 0x03F8, 0x01, 0x08)
                            IRQNoFlags () {4}
                        })
                        CreateWordField (BUFF, 0x02, U1MN)
                        CreateWordField (BUFF, 0x04, U1MX)
                        CreateWordField (BUFF, 0x09, U1IQ)
                        ShiftLeft (And (U1AL, 0xFE), 0x02, Local0)
                        Store (Local0, U1MN)
                        Store (Local0, U1MX)
                        If (And (PNP1, 0x01))
                        {
                            Store (0x08, U1IQ)
                        }

                        Return (BUFF)
                    }

                    Name (_PRS, ResourceTemplate ()
                    {
                        StartDependentFn (0x00, 0x00)
                        {
                            IO (Decode16, 0x03F8, 0x03F8, 0x01, 0x08)
                            IRQNoFlags () {4}
                        }
                        StartDependentFn (0x01, 0x00)
                        {
                            IO (Decode16, 0x02F8, 0x02F8, 0x01, 0x08)
                            IRQNoFlags () {3}
                        }
                        StartDependentFn (0x02, 0x00)
                        {
                            IO (Decode16, 0x03E8, 0x03E8, 0x01, 0x08)
                            IRQNoFlags () {4}
                        }
                        StartDependentFn (0x02, 0x00)
                        {
                            IO (Decode16, 0x02E8, 0x02E8, 0x01, 0x08)
                            IRQNoFlags () {3}
                        }
                        EndDependentFn ()
                    })
                    Method (_SRS, 1, NotSerialized)
                    {
                        CreateWordField (Arg0, 0x02, IOAR)
                        CreateWordField (Arg0, 0x09, IRQM)
                        If (LEqual (IOAR, 0x03F8))
                        {
                            Store (0xFE, Local0)
                            Store (0x00, Local1)
                        }
                        Else
                        {
                            If (LEqual (IOAR, 0x02F8))
                            {
                                Store (0xBE, Local0)
                                Store (0x01, Local1)
                            }
                            Else
                            {
                                If (LEqual (IOAR, 0x03E8))
                                {
                                    Store (0xFA, Local0)
                                    Store (0x07, Local1)
                                }
                                Else
                                {
                                    If (LEqual (IOAR, 0x02E8))
                                    {
                                        Store (0xBA, Local0)
                                        Store (0x05, Local1)
                                    }
                                    Else
                                    {
                                        Fatal (0x02, 0x90000002, 0x00)
                                    }
                                }
                            }
                        }

                        And (U1AH, 0x03, U1AH)
                        And (U1AL, 0x01, Local2)
                        Or (Local0, Local2, U1AL)
                        Store (Local1, \_SB.PCI0.PM00.XU1A)
                        And (PNP1, 0xF0, Local0)
                        If (LEqual (IRQM, 0x10))
                        {
                            Or (Local0, 0x04, Local0)
                        }
                        Else
                        {
                            If (LEqual (IRQM, 0x08))
                            {
                                Or (Local0, 0x03, Local0)
                            }
                            Else
                            {
                                Fatal (0x02, 0x90000002, 0x00)
                            }
                        }

                        Store (Local0, PNP1)
                        Or (FER, 0x02, FER)
                        Store (One, \_SB.PCI0.PM00.XU1E)
                    }
                }

                Name (PPMD, 0x00)
                Name (PPDR, 0x00)
                Method (GPPM, 0, NotSerialized)
                {
                    Store (\GPAR (), Local0)
                    And (Local0, 0x03, PPMD)
                    ShiftRight (And (Local0, 0x04), 0x02, PPDR)
                }

                Device (LPT)
                {
                    Name (_HID, EisaId ("PNP0400"))
                    Name (_EJD, "_SB.PCI0.DOCK")
                    Name (_PR0, Package (0x01)
                    {
                        PSIO
                    })
                    Method (_STA, 0, NotSerialized)
                    {
                        If (LEqual (PPMD, 0x03))
                        {
                            Return (Zero)
                        }
                        Else
                        {
                            If (And (FER, 0x01))
                            {
                                Return (0x0F)
                            }
                            Else
                            {
                                Return (0x0D)
                            }
                        }
                    }

                    Method (_DIS, 0, NotSerialized)
                    {
                        And (FER, 0xFE, FER)
                        Store (Zero, \_SB.PCI0.PM00.XPE)
                    }

                    Method (_CRS, 0, NotSerialized)
                    {
                        Name (BUFF, ResourceTemplate ()
                        {
                            IO (Decode16, 0x03BC, 0x03BC, 0x01, 0x04)
                            IRQNoFlags () {7}
                        })
                        CreateWordField (BUFF, 0x02, L1MN)
                        CreateWordField (BUFF, 0x04, L1MX)
                        CreateByteField (BUFF, 0x06, L1AL)
                        CreateByteField (BUFF, 0x07, L1LN)
                        CreateWordField (BUFF, 0x09, L1IQ)
                        If (LEqual (PPMD, 0x03))
                        {
                            Store (0x00, L1MN)
                            Store (0x00, L1MX)
                            Store (0x00, L1AL)
                            Store (0x00, L1LN)
                            Store (0x00, L1IQ)
                            Return (BUFF)
                        }

                        And (PBAL, 0xFF, Local0)
                        If (LEqual (Local0, 0xEF)) {}
                        Else
                        {
                            If (LEqual (Local0, 0xDE))
                            {
                                Store (0x0378, L1MN)
                                Store (0x0378, L1MX)
                                Store (0x08, L1LN)
                            }
                            Else
                            {
                                If (LEqual (Local0, 0x9E))
                                {
                                    Store (0x0278, L1MN)
                                    Store (0x0278, L1MX)
                                    Store (0x08, L1LN)
                                }
                            }
                        }

                        And (PNP0, 0xF0, Local1)
                        If (LEqual (Local1, 0x00))
                        {
                            Store (0x00, L1IQ)
                        }
                        Else
                        {
                            If (LEqual (Local1, 0x50))
                            {
                                Store (0x20, L1IQ)
                            }
                        }

                        Return (BUFF)
                    }

                    Method (_PRS, 0, NotSerialized)
                    {
                        If (PPMD)
                        {
                            Return (PEPP)
                        }
                        Else
                        {
                            Return (PLPT)
                        }
                    }

                    Name (PLPT, ResourceTemplate ()
                    {
                        StartDependentFnNoPri ()
                        {
                            IO (Decode16, 0x03BC, 0x03BC, 0x01, 0x04)
                            IRQNoFlags () {7}
                        }
                        StartDependentFnNoPri ()
                        {
                            IO (Decode16, 0x0378, 0x0378, 0x01, 0x08)
                            IRQNoFlags () {7}
                        }
                        StartDependentFnNoPri ()
                        {
                            IO (Decode16, 0x0278, 0x0278, 0x01, 0x08)
                            IRQNoFlags () {5}
                        }
                        StartDependentFnNoPri ()
                        {
                            IO (Decode16, 0x03BC, 0x03BC, 0x01, 0x04)
                            IRQNoFlags () {}
                        }
                        StartDependentFnNoPri ()
                        {
                            IO (Decode16, 0x0378, 0x0378, 0x01, 0x08)
                            IRQNoFlags () {}
                        }
                        StartDependentFnNoPri ()
                        {
                            IO (Decode16, 0x0278, 0x0278, 0x01, 0x08)
                            IRQNoFlags () {}
                        }
                        EndDependentFn ()
                    })
                    Name (PEPP, ResourceTemplate ()
                    {
                        StartDependentFnNoPri ()
                        {
                            IO (Decode16, 0x0378, 0x0378, 0x01, 0x08)
                            IRQNoFlags () {5,7}
                        }
                        StartDependentFnNoPri ()
                        {
                            IO (Decode16, 0x0278, 0x0278, 0x01, 0x08)
                            IRQNoFlags () {5,7}
                        }
                        EndDependentFn ()
                    })
                    Method (_SRS, 1, NotSerialized)
                    {
                        CreateWordField (Arg0, 0x02, IOAR)
                        CreateWordField (Arg0, 0x09, IRQM)
                        If (LEqual (IOAR, 0x03BC))
                        {
                            Store (0xEF, Local0)
                            Store (0x00, Local1)
                        }
                        Else
                        {
                            If (LEqual (IOAR, 0x0378))
                            {
                                Store (0xDE, Local0)
                                Store (0x01, Local1)
                            }
                            Else
                            {
                                If (LEqual (IOAR, 0x0278))
                                {
                                    Store (0x9E, Local0)
                                    Store (0x02, Local1)
                                }
                                Else
                                {
                                    Fatal (0x02, 0x90000002, 0x00)
                                }
                            }
                        }

                        And (PBAH, 0x03, Local2)
                        Store (Local2, PBAH)
                        Store (Local0, PBAL)
                        Store (Local1, \_SB.PCI0.PM00.XPA)
                        And (PNP0, 0x0F, Local0)
                        If (LEqual (IRQM, 0x20))
                        {
                            Or (Local0, 0x50, Local0)
                        }
                        Else
                        {
                            If (LEqual (IRQM, 0x80))
                            {
                                Or (Local0, 0x70, Local0)
                            }
                            Else
                            {
                                If (LEqual (IRQM, Zero)) {}
                            }
                        }

                        Store (Local0, PNP0)
                        If (LEqual (PPMD, 0x00))
                        {
                            And (PCR, 0xFA, Local0)
                            If (PPDR)
                            {
                                Or (PTR, 0x80, Local1)
                            }
                            Else
                            {
                                And (PTR, 0x7F, Local1)
                            }
                        }
                        Else
                        {
                            If (LEqual (PPMD, 0x01))
                            {
                                And (PCR, 0xF9, Local0)
                                Or (Local0, 0x01, Local0)
                            }
                            Else
                            {
                                And (PCR, 0xFB, Local0)
                                Or (Local0, 0x03, Local0)
                            }

                            And (PTR, 0x7F, Local1)
                        }

                        Store (Local0, PCR)
                        Store (Local1, PTR)
                        Or (FER, 0x01, FER)
                        Store (One, \_SB.PCI0.PM00.XPE)
                    }
                }

                Device (ECP)
                {
                    Name (_HID, EisaId ("PNP0401"))
                    Name (_EJD, "_SB.PCI0.DOCK")
                    Name (_PR0, Package (0x01)
                    {
                        PSIO
                    })
                    Method (_STA, 0, NotSerialized)
                    {
                        If (LEqual (PPMD, 0x03))
                        {
                            If (And (FER, 0x01))
                            {
                                Return (0x0F)
                            }
                            Else
                            {
                                Return (0x0D)
                            }
                        }
                        Else
                        {
                            Return (Zero)
                        }
                    }

                    Method (_DIS, 0, NotSerialized)
                    {
                        And (FER, 0xFE, FER)
                        Store (Zero, \_SB.PCI0.PM00.XPE)
                    }

                    Method (_CRS, 0, NotSerialized)
                    {
                        Name (BUFF, ResourceTemplate ()
                        {
                            IO (Decode16, 0x03BC, 0x03BC, 0x01, 0x04)
                            IO (Decode16, 0x07BC, 0x07BC, 0x01, 0x03)
                            IRQNoFlags () {7}
                            DMA (Compatibility, NotBusMaster, Transfer8) {3}
                        })
                        CreateWordField (BUFF, 0x02, ECN0)
                        CreateWordField (BUFF, 0x04, ECX0)
                        CreateByteField (BUFF, 0x06, ECA0)
                        CreateByteField (BUFF, 0x07, ECL0)
                        CreateWordField (BUFF, 0x0A, ECN1)
                        CreateWordField (BUFF, 0x0C, ECX1)
                        CreateByteField (BUFF, 0x0E, ECA1)
                        CreateByteField (BUFF, 0x0F, ECL1)
                        CreateWordField (BUFF, 0x11, ECIQ)
                        CreateWordField (BUFF, 0x14, ECDQ)
                        If (LNot (LEqual (PPMD, 0x03)))
                        {
                            Store (0x00, ECN0)
                            Store (0x00, ECX0)
                            Store (0x00, ECA0)
                            Store (0x00, ECL0)
                            Store (0x00, ECN1)
                            Store (0x00, ECX1)
                            Store (0x00, ECA1)
                            Store (0x00, ECL1)
                            Store (0x00, ECIQ)
                            Store (0x00, ECDQ)
                            Return (BUFF)
                        }

                        And (PBAL, 0xFF, Local0)
                        If (LEqual (Local0, 0xEF))
                        {
                            Store (0x03BC, Local1)
                        }
                        Else
                        {
                            If (LEqual (Local0, 0xDE))
                            {
                                Store (0x0378, Local1)
                                Store (0x08, ECL0)
                            }
                            Else
                            {
                                If (LEqual (Local0, 0x9E))
                                {
                                    Store (0x0278, Local1)
                                    Store (0x08, ECL0)
                                }
                            }
                        }

                        Store (Local1, ECN0)
                        Store (Local1, ECX0)
                        Add (Local1, 0x0400, ECN1)
                        Add (Local1, 0x0400, ECX1)
                        And (PNP0, 0xF0, Local1)
                        If (LEqual (Local1, 0x50))
                        {
                            Store (0x20, ECIQ)
                        }
                        Else
                        {
                            If (LEqual (Local1, 0x70)) {}
                            Else
                            {
                                Store (0x00, ECIQ)
                            }
                        }

                        And (SCF1, 0x38, Local2)
                        If (LEqual (Local2, 0x00))
                        {
                            Store (0x00, ECDQ)
                        }
                        Else
                        {
                            If (LEqual (Local2, 0x08))
                            {
                                Store (0x01, ECDQ)
                            }
                            Else
                            {
                                If (LEqual (Local2, 0x10))
                                {
                                    Store (0x02, ECDQ)
                                }
                                Else
                                {
                                    If (LEqual (Local2, 0x20)) {}
                                    Else
                                    {
                                        Store (0x00, ECDQ)
                                    }
                                }
                            }
                        }

                        Return (BUFF)
                    }

                    Name (_PRS, ResourceTemplate ()
                    {
                        StartDependentFnNoPri ()
                        {
                            IO (Decode16, 0x03BC, 0x03BC, 0x01, 0x04)
                            IO (Decode16, 0x07BC, 0x07BC, 0x01, 0x03)
                            IRQNoFlags () {7}
                            DMA (Compatibility, NotBusMaster, Transfer8) {0,1,3}
                        }
                        StartDependentFnNoPri ()
                        {
                            IO (Decode16, 0x0378, 0x0378, 0x01, 0x08)
                            IO (Decode16, 0x0778, 0x0778, 0x01, 0x03)
                            IRQNoFlags () {7}
                            DMA (Compatibility, NotBusMaster, Transfer8) {0,1,3}
                        }
                        StartDependentFnNoPri ()
                        {
                            IO (Decode16, 0x0278, 0x0278, 0x01, 0x08)
                            IO (Decode16, 0x0678, 0x0678, 0x01, 0x03)
                            IRQNoFlags () {5}
                            DMA (Compatibility, NotBusMaster, Transfer8) {0,1,3}
                        }
                        EndDependentFn ()
                    })
                    Method (_SRS, 1, NotSerialized)
                    {
                        CreateWordField (Arg0, 0x02, IOAR)
                        CreateWordField (Arg0, 0x11, IRQM)
                        CreateByteField (Arg0, 0x14, DMAM)
                        If (LEqual (IOAR, 0x03BC))
                        {
                            Store (0xEF, Local0)
                            Store (0x00, Local1)
                        }
                        Else
                        {
                            If (LEqual (IOAR, 0x0378))
                            {
                                Store (0xDE, Local0)
                                Store (0x01, Local1)
                            }
                            Else
                            {
                                If (LEqual (IOAR, 0x0278))
                                {
                                    Store (0x9E, Local0)
                                    Store (0x02, Local1)
                                }
                                Else
                                {
                                    Fatal (0x02, 0x90000002, 0x00)
                                }
                            }
                        }

                        And (PBAH, 0x03, Local2)
                        Store (Local2, PBAH)
                        Store (Local0, PBAL)
                        Store (Local1, \_SB.PCI0.PM00.XPA)
                        And (PNP0, 0x0F, Local0)
                        If (LEqual (IRQM, 0x20))
                        {
                            Or (Local0, 0x50, Local0)
                        }
                        Else
                        {
                            If (LEqual (IRQM, 0x80))
                            {
                                Or (Local0, 0x70, Local0)
                            }
                        }

                        Store (Local0, PNP0)
                        And (SCF1, 0xC7, Local1)
                        If (LEqual (DMAM, 0x01))
                        {
                            Or (Local1, 0x08, Local1)
                        }
                        Else
                        {
                            If (LEqual (DMAM, 0x02))
                            {
                                Or (Local1, 0x10, Local1)
                            }
                            Else
                            {
                                If (LEqual (DMAM, 0x08))
                                {
                                    Or (Local1, 0x20, Local1)
                                }
                            }
                        }

                        Store (Local1, SCF1)
                        And (PCR, 0xFE, Local0)
                        Or (Local0, 0x04, PCR)
                        Or (FER, 0x01, FER)
                        Store (One, \_SB.PCI0.PM00.XPE)
                        And (PCR, 0xFB, PCR)
                        \ECPP ()
                    }
                }

                Device (FIR)
                {
                    Name (_HID, EisaId ("IBM0071"))
                    Name (_CID, 0x1105D041)
                    Name (_PR0, Package (0x01)
                    {
                        PSIO
                    })
                    Method (_STA, 0, NotSerialized)
                    {
                        If (And (FER, 0x04))
                        {
                            Return (0x0F)
                        }
                        Else
                        {
                            Return (0x0D)
                        }
                    }

                    Method (_DIS, 0, NotSerialized)
                    {
                        And (SCF2, 0x5F, SCF2)
                        And (FER, 0xFB, FER)
                        Store (Zero, \_SB.PCI0.PM00.XU2E)
                    }

                    Method (_CRS, 0, NotSerialized)
                    {
                        Name (BUFF, ResourceTemplate ()
                        {
                            IO (Decode16, 0x03F8, 0x03F8, 0x01, 0x08)
                            IRQNoFlags () {4}
                            DMA (Compatibility, NotBusMaster, Transfer8) {3}
                        })
                        CreateWordField (BUFF, 0x02, IRMN)
                        CreateWordField (BUFF, 0x04, IRMX)
                        CreateWordField (BUFF, 0x09, IRIQ)
                        CreateByteField (BUFF, 0x0C, IRDR)
                        ShiftLeft (And (U2AL, 0xFE), 0x02, Local0)
                        Store (Local0, IRMN)
                        Store (Local0, IRMX)
                        If (LEqual (And (PNP1, 0xF0), 0x70))
                        {
                            Store (0x80, IRIQ)
                        }
                        Else
                        {
                            If (LEqual (And (PNP1, 0xF0), 0x50))
                            {
                                Store (0x20, IRIQ)
                            }
                            Else
                            {
                                If (LEqual (And (PNP1, 0xF0), 0x40))
                                {
                                    Store (0x10, IRIQ)
                                }
                                Else
                                {
                                    If (LEqual (And (PNP1, 0xF0), 0x30))
                                    {
                                        Store (0x08, IRIQ)
                                    }
                                    Else
                                    {
                                        Store (0x00, IRIQ)
                                    }
                                }
                            }
                        }

                        And (PNP3, 0x07, Local1)
                        If (LEqual (Local1, 0x00))
                        {
                            Store (0x00, IRDR)
                        }
                        Else
                        {
                            If (LEqual (Local1, 0x01))
                            {
                                Store (0x01, IRDR)
                            }
                            Else
                            {
                                If (LEqual (Local1, 0x02))
                                {
                                    Store (0x02, IRDR)
                                }
                                Else
                                {
                                    If (LEqual (Local1, 0x04))
                                    {
                                        Store (0x08, IRDR)
                                    }
                                    Else
                                    {
                                        Store (Zero, IRDR)
                                    }
                                }
                            }
                        }

                        Return (BUFF)
                    }

                    Name (_PRS, ResourceTemplate ()
                    {
                        StartDependentFn (0x00, 0x00)
                        {
                            IO (Decode16, 0x03F8, 0x03F8, 0x01, 0x08)
                            IRQNoFlags () {4}
                            DMA (Compatibility, NotBusMaster, Transfer8) {0,1,3}
                        }
                        StartDependentFn (0x01, 0x00)
                        {
                            IO (Decode16, 0x02F8, 0x02F8, 0x01, 0x08)
                            IRQNoFlags () {3}
                            DMA (Compatibility, NotBusMaster, Transfer8) {0,1,3}
                        }
                        StartDependentFn (0x02, 0x00)
                        {
                            IO (Decode16, 0x03E8, 0x03E8, 0x01, 0x08)
                            IRQNoFlags () {4}
                            DMA (Compatibility, NotBusMaster, Transfer8) {0,1,3}
                        }
                        StartDependentFn (0x02, 0x00)
                        {
                            IO (Decode16, 0x02E8, 0x02E8, 0x01, 0x08)
                            IRQNoFlags () {3}
                            DMA (Compatibility, NotBusMaster, Transfer8) {0,1,3}
                        }
                        StartDependentFn (0x02, 0x00)
                        {
                            IO (Decode16, 0x03F8, 0x03F8, 0x01, 0x08)
                            IRQNoFlags () {3,5,7}
                            DMA (Compatibility, NotBusMaster, Transfer8) {0,1,3}
                        }
                        StartDependentFn (0x02, 0x00)
                        {
                            IO (Decode16, 0x02F8, 0x02F8, 0x01, 0x08)
                            IRQNoFlags () {4,5,7}
                            DMA (Compatibility, NotBusMaster, Transfer8) {0,1,3}
                        }
                        StartDependentFn (0x02, 0x00)
                        {
                            IO (Decode16, 0x03E8, 0x03E8, 0x01, 0x08)
                            IRQNoFlags () {3,5,7}
                            DMA (Compatibility, NotBusMaster, Transfer8) {0,1,3}
                        }
                        StartDependentFn (0x02, 0x00)
                        {
                            IO (Decode16, 0x02E8, 0x02E8, 0x01, 0x08)
                            IRQNoFlags () {4,5,7}
                            DMA (Compatibility, NotBusMaster, Transfer8) {0,1,3}
                        }
                        StartDependentFn (0x02, 0x00)
                        {
                            IO (Decode16, 0x03F8, 0x03F8, 0x01, 0x08)
                            IRQNoFlags () {4}
                            DMA (Compatibility, NotBusMaster, Transfer8) {}
                        }
                        StartDependentFn (0x02, 0x00)
                        {
                            IO (Decode16, 0x02F8, 0x02F8, 0x01, 0x08)
                            IRQNoFlags () {3}
                            DMA (Compatibility, NotBusMaster, Transfer8) {}
                        }
                        StartDependentFn (0x02, 0x00)
                        {
                            IO (Decode16, 0x03E8, 0x03E8, 0x01, 0x08)
                            IRQNoFlags () {4}
                            DMA (Compatibility, NotBusMaster, Transfer8) {}
                        }
                        StartDependentFn (0x02, 0x00)
                        {
                            IO (Decode16, 0x02E8, 0x02E8, 0x01, 0x08)
                            IRQNoFlags () {3}
                            DMA (Compatibility, NotBusMaster, Transfer8) {}
                        }
                        StartDependentFn (0x02, 0x00)
                        {
                            IO (Decode16, 0x03F8, 0x03F8, 0x01, 0x08)
                            IRQNoFlags () {3,5,7}
                            DMA (Compatibility, NotBusMaster, Transfer8) {}
                        }
                        StartDependentFn (0x02, 0x00)
                        {
                            IO (Decode16, 0x02F8, 0x02F8, 0x01, 0x08)
                            IRQNoFlags () {4,5,7}
                            DMA (Compatibility, NotBusMaster, Transfer8) {}
                        }
                        StartDependentFn (0x02, 0x00)
                        {
                            IO (Decode16, 0x03E8, 0x03E8, 0x01, 0x08)
                            IRQNoFlags () {3,5,7}
                            DMA (Compatibility, NotBusMaster, Transfer8) {}
                        }
                        StartDependentFn (0x02, 0x00)
                        {
                            IO (Decode16, 0x02E8, 0x02E8, 0x01, 0x08)
                            IRQNoFlags () {4,5,7}
                            DMA (Compatibility, NotBusMaster, Transfer8) {}
                        }
                        EndDependentFn ()
                    })
                    Method (_SRS, 1, NotSerialized)
                    {
                        CreateWordField (Arg0, 0x02, IRIO)
                        CreateWordField (Arg0, 0x09, IRIQ)
                        CreateByteField (Arg0, 0x0C, IRDR)
                        If (LEqual (IRIO, 0x03F8))
                        {
                            Store (0xFE, Local0)
                            Store (0x00, Local1)
                        }
                        Else
                        {
                            If (LEqual (IRIO, 0x02F8))
                            {
                                Store (0xBE, Local0)
                                Store (0x01, Local1)
                            }
                            Else
                            {
                                If (LEqual (IRIO, 0x03E8))
                                {
                                    Store (0xFA, Local0)
                                    Store (0x07, Local1)
                                }
                                Else
                                {
                                    If (LEqual (IRIO, 0x02E8))
                                    {
                                        Store (0xBA, Local0)
                                        Store (0x05, Local1)
                                    }
                                    Else
                                    {
                                        Fatal (0x02, 0x90000002, 0x00)
                                    }
                                }
                            }
                        }

                        And (U2AH, 0x03, U2AH)
                        And (U2AL, 0x01, Local2)
                        Or (Local0, Local2, U2AL)
                        Store (Local1, \_SB.PCI0.PM00.XU2A)
                        And (PNP1, 0x0F, Local0)
                        If (LEqual (IRIQ, 0x80))
                        {
                            Or (Local0, 0x70, Local0)
                        }
                        Else
                        {
                            If (LEqual (IRIQ, 0x20))
                            {
                                Or (Local0, 0x50, Local0)
                            }
                            Else
                            {
                                If (LEqual (IRIQ, 0x10))
                                {
                                    Or (Local0, 0x40, Local0)
                                }
                                Else
                                {
                                    If (LEqual (IRIQ, 0x08))
                                    {
                                        Or (Local0, 0x30, Local0)
                                    }
                                    Else
                                    {
                                        Fatal (0x02, 0x90000002, 0x00)
                                    }
                                }
                            }
                        }

                        Store (Local0, PNP1)
                        If (LEqual (IRDR, 0x00))
                        {
                            Store (0x00, Local0)
                        }
                        Else
                        {
                            If (LEqual (IRDR, 0x01))
                            {
                                Store (0x01, Local0)
                            }
                            Else
                            {
                                If (LEqual (IRDR, 0x02))
                                {
                                    Store (0x02, Local0)
                                }
                                Else
                                {
                                    If (LEqual (IRDR, 0x08))
                                    {
                                        Store (0x04, Local0)
                                    }
                                    Else
                                    {
                                        Fatal (0x02, 0x90000002, 0x00)
                                    }
                                }
                            }
                        }

                        And (PNP3, 0xC0, Local1)
                        Or (Local1, Local0, PNP3)
                        Or (FER, 0x04, FER)
                        Store (One, \_SB.PCI0.PM00.XU2E)
                        Or (SCF2, 0xA0, SCF2)
                    }
                }

                Device (EC)
                {
                    Name (_HID, EisaId ("PNP0C09"))
                    Name (_GPE, 0x09)
                    Name (_GLK, 0x01)
                    Method (_REG, 2, NotSerialized)
                    {
                        If (LEqual (Arg0, 0x03))
                        {
                            Store (Arg1, \H8DR)
                        }
                    }

                    OperationRegion (ECOR, EmbeddedControl, 0x00, 0x0100)
                    Field (ECOR, ByteAcc, Lock, Preserve)
                    {
                            ,   1,
                        HCGA,   1,
                            ,   1,
                            ,   1,
                            ,   1,
                            ,   1,
                        HCAC,   1,
                        Offset (0x01),
                            ,   1,
                        BTCM,   1,
                            ,   1,
                            ,   1,
                            ,   1,
                        HCAD,   1,
                        BTPC,   1,
                        Offset (0x02),
                        Offset (0x03),
                        Offset (0x04),
                            ,   1,
                            ,   1,
                            ,   1,
                            ,   1,
                            ,   1,
                            ,   1,
                            ,   1,
                        Offset (0x05),
                        HSPA,   1,
                            ,   1,
                            ,   1,
                            ,   1,
                            ,   1,
                            ,   1,
                            ,   1,
                        Offset (0x06),
                        HSUN,   8,
                        HSRP,   8,
                        HACC,   8,
                        Offset (0x0A),
                        Offset (0x0B),
                        Offset (0x0C),
                        HLCL,   8,
                        HLBL,   8,
                        HLMS,   8,
                        HICA,   8,
                        HAM0,   8,
                        HAM1,   8,
                        HAM2,   8,
                        HAM3,   8,
                        HAM4,   8,
                        HAM5,   8,
                        HAM6,   8,
                        HAM7,   8,
                        HAM8,   8,
                        HAM9,   8,
                        HAMA,   8,
                        HAMB,   8,
                        HAMC,   8,
                        HAMD,   8,
                        HAME,   8,
                        HAMF,   8,
                        HT00,   1,
                        HT01,   1,
                        HT02,   1,
                            ,   4,
                        HT0E,   1,
                        HT10,   1,
                        HT11,   1,
                        HT12,   1,
                            ,   4,
                        HT1E,   1,
                        HT20,   1,
                        HT21,   1,
                        HT22,   1,
                            ,   4,
                        HT2E,   1,
                        HT30,   1,
                        HT31,   1,
                        HT32,   1,
                            ,   4,
                        HT3E,   1,
                        HT40,   1,
                        HT41,   1,
                        HT42,   1,
                            ,   4,
                        HT4E,   1,
                        HT50,   1,
                        HT51,   1,
                        HT52,   1,
                            ,   4,
                        HT5E,   1,
                        HT60,   1,
                        HT61,   1,
                        HT62,   1,
                            ,   4,
                        HT6E,   1,
                        HT70,   1,
                        HT71,   1,
                        HT72,   1,
                            ,   4,
                        HT7E,   1,
                        HDID,   8,
                        Offset (0x2A),
                        Offset (0x2B),
                        HT0H,   8,
                        HT0L,   8,
                        HT1H,   8,
                        HT1L,   8,
                        HFSP,   8,
                            ,   5,
                            ,   1,
                        HMUT,   1,
                        Offset (0x31),
                        Offset (0x32),
                        HWPM,   1,
                        HWLB,   1,
                        HWLO,   1,
                        HWDK,   1,
                        HWFN,   1,
                        HWBT,   1,
                        HWRI,   1,
                        HWBU,   1,
                        Offset (0x34),
                            ,   1,
                            ,   1,
                            ,   1,
                            ,   1,
                            ,   1,
                            ,   1,
                            ,   1,
                        Offset (0x35),
                        Offset (0x36),
                            ,   1,
                        BTWK,   1,
                        HPLD,   1,
                            ,   1,
                        HPAC,   1,
                        BTST,   1,
                        Offset (0x37),
                        HPBU,   1,
                            ,   1,
                            ,   1,
                            ,   1,
                            ,   1,
                            ,   1,
                            ,   1,
                        HPNF,   1,
                        HB0L,   4,
                            ,   1,
                        HB0C,   1,
                        HB0D,   1,
                        HB0A,   1,
                        HB1L,   4,
                            ,   1,
                        HB1C,   1,
                        HB1D,   1,
                        HB1A,   1,
                        HCMU,   1,
                            ,   1,
                            ,   1,
                            ,   1,
                        HCSL,   2,
                            ,   1,
                        Offset (0x3B),
                            ,   1,
                        KBLT,   1,
                        BTPW,   1,
                        BTDT,   1,
                        Offset (0x3C),
                        Offset (0x3D),
                        Offset (0x3E),
                        Offset (0x46),
                        Offset (0x47),
                            ,   4,
                            ,   1,
                            ,   1,
                            ,   1,
                        Offset (0x48),
                            ,   4,
                        Offset (0x49),
                        Offset (0x4A),
                        Offset (0x4C),
                        Offset (0x4E),
                        HWAK,   8,
                        Offset (0x50),
                        Offset (0x75),
                        Offset (0x78),
                        TMP0,   8,
                        TMP1,   8,
                        TMP2,   8,
                        TMP3,   8,
                        TMP4,   8,
                        TMP5,   8,
                        TMP6,   8,
                        TMP7,   8,
                        Offset (0x82),
                        CP4E,   8,
                        HFNI,   8,
                        HKBD,   1,
                        HPHT,   1,
                        Offset (0x85),
                        Offset (0xC0),
                        Offset (0xC2),
                        Offset (0xC4),
                        Offset (0xD0),
                        Offset (0xE0),
                        Offset (0xE8),
                        Offset (0xEA),
                        Offset (0xEB),
                        Offset (0xEC),
                            ,   1,
                            ,   1,
                            ,   2,
                            ,   1,
                            ,   1,
                            ,   1,
                        Offset (0xED),
                            ,   1,
                        Offset (0xEE),
                            ,   4,
                        Offset (0xEF),
                        Offset (0xF0),
                        Offset (0xF8),
                        Offset (0x100)
                    }

                    Method (_INI, 0, NotSerialized)
                    {
                        If (\H8DR)
                        {
                            Store (One, HCAC)
                            Store (Zero, HWFN)
                            Store (One, HWLB)
                            Store (Zero, HWLO)
                            And (HAM5, 0x3F, HAM5)
                        }
                        Else
                        {
                            \MBEC (0x00, 0xFF, 0x40)
                            \MBEC (0x32, 0xEB, 0x02)
                            \MBEC (0x15, 0x3F, 0x00)
                        }

                        If (\H8DR)
                        {
                            Store (0x00, HSPA)
                        }
                        Else
                        {
                            \MBEC (0x05, 0xFE, 0x00)
                        }

                        Store (GUID (), BDEV)
                        GHKS ()
                        \_SB.PCI0.ISA.EC.HKEY.BTIN ()
                    }

                    Name (_CRS, ResourceTemplate ()
                    {
                        IO (Decode16, 0x0062, 0x0062, 0x01, 0x01)
                        IO (Decode16, 0x0066, 0x0066, 0x01, 0x01)
                    })
                    Method (GUID, 0, NotSerialized)
                    {
                        Store (GDEV (0x00), Local0)
                        If (LEqual (Local0, 0x0F))
                        {
                            If (\H8DR)
                            {
                                If (HB1A)
                                {
                                    Store (0x10, Local0)
                                }
                            }
                            Else
                            {
                                If (And (\RBEC (0x39), 0x80))
                                {
                                    Store (0x10, Local0)
                                }
                            }
                        }

                        Return (Local0)
                    }

                    Mutex (MDEV, 0x07)
                    Method (GDEV, 1, NotSerialized)
                    {
                        Acquire (MDEV, 0xFFFF)
                        If (\H8DR)
                        {
                            And (HAM7, 0xFE, HAM7)
                        }
                        Else
                        {
                            \MBEC (0x17, 0xFE, 0x00)
                        }

                        And (Arg0, 0x03, \_SB.PCI0.PM00.EID)
                        And (ShiftRight (Arg0, 0x02), 0x01, \_SB.PCI0.PM00.EID2)
                        If (\H8DR)
                        {
                            Or (HDID, 0x80, HDID)
                            Store (0x20, Local1)
                            While (LAnd (Local1, And (HDID, 0x80)))
                            {
                                Sleep (0x01)
                                Decrement (Local1)
                            }

                            Store (HDID, Local2)
                        }
                        Else
                        {
                            \MBEC (0x28, 0xFF, 0x80)
                            Store (0x20, Local1)
                            While (LAnd (Local1, And (\RBEC (0x28), 0x80)))
                            {
                                Sleep (0x01)
                                Decrement (Local1)
                            }

                            Store (\RBEC (0x28), Local2)
                        }

                        If (And (Local2, 0x80))
                        {
                            Store (0xFF, Local2)
                        }

                        Store (0x00, \_SB.PCI0.PM00.EID)
                        Store (0x00, \_SB.PCI0.PM00.EID2)
                        Sleep (0x64)
                        If (\H8DR)
                        {
                            Or (HAM7, 0x01, HAM7)
                        }
                        Else
                        {
                            \MBEC (0x17, 0xFF, 0x01)
                        }

                        Release (MDEV)
                        Return (Local2)
                    }

                    Mutex (LEDM, 0x07)
                    Method (SYSL, 2, NotSerialized)
                    {
                        If (LEqual (Arg0, 0x00))
                        {
                            Store (0x01, Local0)
                        }
                        Else
                        {
                            If (LEqual (Arg0, 0x01))
                            {
                                Store (0x80, Local0)
                            }
                            Else
                            {
                                Return (0x00)
                            }
                        }

                        Acquire (LEDM, 0xFFFF)
                        If (LAnd (\H8DR, LNot (\W98F)))
                        {
                            Store (Local0, HLMS)
                            If (LEqual (Arg1, 0x00))
                            {
                                Store (0x00, HLBL)
                                Store (0x00, HLCL)
                            }
                            Else
                            {
                                If (LEqual (Arg1, 0x01))
                                {
                                    Store (0x00, HLBL)
                                    Store (Local0, HLCL)
                                }
                                Else
                                {
                                    If (LEqual (Arg1, 0x02))
                                    {
                                        Store (Local0, HLBL)
                                        Store (Local0, HLCL)
                                    }
                                    Else
                                    {
                                    }
                                }
                            }
                        }
                        Else
                        {
                            \WBEC (0x0E, Local0)
                            If (LEqual (Arg1, 0x00))
                            {
                                \WBEC (0x0D, 0x00)
                                \WBEC (0x0C, 0x00)
                            }
                            Else
                            {
                                If (LEqual (Arg1, 0x01))
                                {
                                    \WBEC (0x0D, 0x00)
                                    \WBEC (0x0C, Local0)
                                }
                                Else
                                {
                                    If (LEqual (Arg1, 0x02))
                                    {
                                        \WBEC (0x0D, Local0)
                                        \WBEC (0x0C, Local0)
                                    }
                                }
                            }
                        }

                        Sleep (0x0A)
                        Release (LEDM)
                    }

                    Name (BAON, 0x00)
                    Name (WBON, 0x00)
                    Method (BEEP, 1, NotSerialized)
                    {
                        If (LGreater (Arg0, 0x11))
                        {
                            Return (0x01)
                        }
                        Else
                        {
                            If (LAnd (\H8DR, LNot (\W98F)))
                            {
                                If (LEqual (Arg0, 0x00))
                                {
                                    If (BAON)
                                    {
                                        If (WBON)
                                        {
                                            Store (0x08, HSRP)
                                            Store (0x03, HSUN)
                                        }
                                        Else
                                        {
                                            Store (0x00, HSRP)
                                            Store (Arg0, HSUN)
                                        }

                                        Store (0x00, BAON)
                                    }
                                }
                                Else
                                {
                                    If (LEqual (Arg0, 0x0F))
                                    {
                                        Store (0x08, HSRP)
                                        Store (0x01, BAON)
                                        Store (Arg0, HSUN)
                                    }
                                    Else
                                    {
                                        If (BAON)
                                        {
                                            If (LEqual (Arg0, 0x11))
                                            {
                                                Store (0x00, WBON)
                                            }
                                            Else
                                            {
                                                If (LEqual (Arg0, 0x10))
                                                {
                                                    If (HMUT) {}
                                                    Else
                                                    {
                                                        Store (0x01, WBON)
                                                    }
                                                }
                                            }
                                        }
                                        Else
                                        {
                                            If (LEqual (Arg0, 0x11))
                                            {
                                                If (WBON)
                                                {
                                                    Store (0x00, HSRP)
                                                    Store (0x00, HSUN)
                                                    Store (0x00, WBON)
                                                }
                                            }
                                            Else
                                            {
                                                If (LEqual (Arg0, 0x10))
                                                {
                                                    If (HMUT) {}
                                                    Else
                                                    {
                                                        Store (0x01, WBON)
                                                        Store (0x08, HSRP)
                                                        Store (0x03, HSUN)
                                                    }
                                                }
                                                Else
                                                {
                                                    If (WBON)
                                                    {
                                                        If (LEqual (Arg0, 0x07))
                                                        {
                                                            Store (0x00, WBON)
                                                        }
                                                        Else
                                                        {
                                                            If (LEqual (Arg0, 0x03))
                                                            {
                                                                Store (0x00, WBON)
                                                                If (LEqual (\SPS, 0x04)) {}
                                                                Else
                                                                {
                                                                    Store (0x00, HSRP)
                                                                    Store (0x00, HSUN)
                                                                    Sleep (0x64)
                                                                    Store (0x07, HSUN)
                                                                    Sleep (0x012C)
                                                                }
                                                            }
                                                            Else
                                                            {
                                                                Store (0x00, HSRP)
                                                                Store (0x00, HSUN)
                                                                Sleep (0xC8)
                                                                Store (Arg0, HSUN)
                                                                Sleep (0xC8)
                                                                If (LEqual (Arg0, 0x04))
                                                                {
                                                                    Store (0x00, WBON)
                                                                }

                                                                If (LEqual (Arg0, 0x05))
                                                                {
                                                                    Store (0x00, WBON)
                                                                }

                                                                If (WBON)
                                                                {
                                                                    Store (0x08, HSRP)
                                                                    Store (0x03, HSUN)
                                                                }
                                                            }
                                                        }
                                                    }
                                                    Else
                                                    {
                                                        Store (Arg0, HSUN)
                                                        If (LEqual (Arg0, 0x03))
                                                        {
                                                            Sleep (0x012C)
                                                        }

                                                        If (LEqual (Arg0, 0x07))
                                                        {
                                                            Sleep (0x01F4)
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                            Else
                            {
                                If (LEqual (Arg0, 0x00))
                                {
                                    If (BAON)
                                    {
                                        If (WBON)
                                        {
                                            \WBEC (0x07, 0x08)
                                            \WBEC (0x06, 0x03)
                                        }
                                        Else
                                        {
                                            \WBEC (0x07, 0x00)
                                            \WBEC (0x06, Arg0)
                                        }

                                        Store (0x00, BAON)
                                    }
                                }
                                Else
                                {
                                    If (LEqual (Arg0, 0x0F))
                                    {
                                        \WBEC (0x07, 0x08)
                                        Store (0x01, BAON)
                                        \WBEC (0x06, Arg0)
                                    }
                                    Else
                                    {
                                        If (BAON)
                                        {
                                            If (LEqual (Arg0, 0x11))
                                            {
                                                Store (0x00, WBON)
                                            }
                                            Else
                                            {
                                                If (LEqual (Arg0, 0x10))
                                                {
                                                    If (HMUT) {}
                                                    Else
                                                    {
                                                        Store (0x01, WBON)
                                                    }
                                                }
                                            }
                                        }
                                        Else
                                        {
                                            If (LEqual (Arg0, 0x11))
                                            {
                                                If (WBON)
                                                {
                                                    \WBEC (0x07, 0x00)
                                                    \WBEC (0x06, 0x00)
                                                    Store (0x00, WBON)
                                                }
                                            }
                                            Else
                                            {
                                                If (LEqual (Arg0, 0x10))
                                                {
                                                    If (And (0x40, \RBEC (0x30))) {}
                                                    Else
                                                    {
                                                        Store (0x01, WBON)
                                                        \WBEC (0x07, 0x08)
                                                        \WBEC (0x06, 0x03)
                                                    }
                                                }
                                                Else
                                                {
                                                    If (WBON)
                                                    {
                                                        If (LEqual (Arg0, 0x07))
                                                        {
                                                            Store (0x00, WBON)
                                                        }
                                                        Else
                                                        {
                                                            If (LEqual (Arg0, 0x03))
                                                            {
                                                                Store (0x00, WBON)
                                                                If (LEqual (\SPS, 0x04)) {}
                                                                Else
                                                                {
                                                                    \WBEC (0x07, 0x00)
                                                                    \WBEC (0x06, 0x00)
                                                                    Sleep (0x64)
                                                                    \WBEC (0x06, 0x07)
                                                                    Sleep (0x012C)
                                                                }
                                                            }
                                                            Else
                                                            {
                                                                \WBEC (0x07, 0x00)
                                                                \WBEC (0x06, 0x00)
                                                                Sleep (0xC8)
                                                                \WBEC (0x06, Arg0)
                                                                Sleep (0xC8)
                                                                If (LEqual (Arg0, 0x04))
                                                                {
                                                                    Store (0x00, WBON)
                                                                }

                                                                If (LEqual (Arg0, 0x05))
                                                                {
                                                                    Store (0x00, WBON)
                                                                }

                                                                If (WBON)
                                                                {
                                                                    \WBEC (0x07, 0x08)
                                                                    \WBEC (0x06, 0x03)
                                                                }
                                                            }
                                                        }
                                                    }
                                                    Else
                                                    {
                                                        \WBEC (0x06, Arg0)
                                                        If (LEqual (Arg0, 0x03))
                                                        {
                                                            Sleep (0x012C)
                                                        }

                                                        If (LEqual (Arg0, 0x05))
                                                        {
                                                            Sleep (0xC8)
                                                        }

                                                        If (LEqual (Arg0, 0x07))
                                                        {
                                                            Sleep (0x01F4)
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }

                    Method (EVNT, 1, NotSerialized)
                    {
                        If (\H8DR)
                        {
                            If (Arg0)
                            {
                                Or (HAM7, 0x01, HAM7)
                                Or (HAM5, 0x04, HAM5)
                            }
                            Else
                            {
                                And (HAM7, 0xFE, HAM7)
                                And (HAM5, 0xFB, HAM5)
                            }
                        }
                        Else
                        {
                            If (Arg0)
                            {
                                \MBEC (0x17, 0xFF, 0x01)
                                \MBEC (0x15, 0xFF, 0x04)
                                If (\W98F)
                                {
                                    \WBEC (0x18, 0xFF)
                                }
                            }
                            Else
                            {
                                \MBEC (0x17, 0xFE, 0x00)
                                \MBEC (0x15, 0xFB, 0x00)
                                If (\W98F)
                                {
                                    \WBEC (0x18, 0x00)
                                }
                            }
                        }
                    }

                    Method (_Q12, 0, NotSerialized)
                    {
                        \_SB.PCI0.ISA.EC.HKEY.MHKQ (0x1003)
                    }

                    Method (_Q13, 0, NotSerialized)
                    {
                        If (\_SB.PCI0.ISA.EC.VDHK)
                        {
                            \_SB.PCI0.ISA.EC.HKEY.MHKQ (0x1004)
                        }
                        Else
                        {
                            Notify (\_SB.SLPB, 0x80)
                        }
                    }

                    Method (_Q16, 0, NotSerialized)
                    {
                        \_SB.PCI0.AGP.VID.VSWT ()
                    }

                    Method (_Q17, 0, NotSerialized)
                    {
                        If (LNot (\WNTF))
                        {
                            VEXP ()
                        }
                    }

                    Method (_Q1B, 0, NotSerialized)
                    {
                        \_SB.PCI0.ISA.EC.HKEY.MHKQ (0x100C)
                    }

                    Method (_Q1F, 0, NotSerialized)
                    {
                        \LGHT (0x02)
                    }

                    Method (_Q26, 0, NotSerialized)
                    {
                        \_SB.PCI0.ISA.HBDS ()
                        Sleep (0x01F4)
                        Notify (AC, 0x00)
                        Notify (\_TZ.THM0, 0x80)
                        If (\GVEN)
                        {
                            \GVIL (0x00)
                        }
                    }

                    Method (_Q27, 0, NotSerialized)
                    {
                        \_SB.PCI0.ISA.HBEN ()
                        Sleep (0x01F4)
                        Notify (AC, 0x00)
                        Notify (\_TZ.THM0, 0x80)
                        If (\GVEN)
                        {
                            \GVIL (0x01)
                        }
                    }

                    Method (_Q2A, 0, NotSerialized)
                    {
                        \_SB.PCI0.AGP.VID.VLOC (0x01)
                        \_SB.PCI0.ISA.EC.HKEY.MHKQ (0x5002)
                        Notify (\_SB.LID, 0x80)
                    }

                    Method (_Q2B, 0, NotSerialized)
                    {
                        \_SB.PCI0.ISA.EC.HKEY.MHKQ (0x5001)
                        \LGHT (0x00)
                        Notify (\_SB.LID, 0x80)
                    }

                    Method (_Q3D, 0, NotSerialized)
                    {
                        \FERR ()
                    }

                    Method (_Q48, 0, NotSerialized)
                    {
                        If (\GVEN)
                        {
                            \GVIL (0x04)
                        }
                    }

                    Method (_Q49, 0, NotSerialized)
                    {
                        If (\GVEN)
                        {
                            \GVIL (0x05)
                        }
                    }

                    Method (_Q7F, 0, NotSerialized)
                    {
                        Fatal (0x01, 0x80000001, 0x00)
                    }

                    Method (_Q20, 0, NotSerialized)
                    {
                        Notify (BAT0, 0x80)
                        Notify (BAT1, 0x80)
                    }

                    Method (_Q21, 0, NotSerialized)
                    {
                        Notify (BAT0, 0x80)
                        Notify (BAT1, 0x80)
                    }

                    Method (_Q22, 0, NotSerialized)
                    {
                        Notify (BAT0, 0x80)
                        Notify (BAT1, 0x80)
                    }

                    Method (_Q23, 0, NotSerialized)
                    {
                        Store (HB0A, Local0)
                        If (XOr (^BAT0.B0ST, Local0))
                        {
                            Store (Local0, ^BAT0.B0ST)
                            Notify (BAT0, 0x81)
                        }
                        Else
                        {
                            Notify (BAT0, 0x80)
                        }

                        Store (HB1A, Local0)
                        If (XOr (^BAT1.B1ST, Local0))
                        {
                            Store (Local0, ^BAT1.B1ST)
                            _Q38 ()
                        }
                        Else
                        {
                            If (LAnd (^BAT1.XB1S, Local0))
                            {
                                Notify (BAT1, 0x80)
                            }
                        }
                    }

                    Method (_Q24, 0, NotSerialized)
                    {
                        Notify (BAT0, 0x80)
                    }

                    Method (_Q25, 0, NotSerialized)
                    {
                        Notify (BAT1, 0x80)
                    }

                    Name (BT0I, Package (0x0D)
                    {
                        0x00,
                        0x00,
                        0x00,
                        0x01,
                        0x2A30,
                        0x00,
                        0x00,
                        0x01,
                        0x01,
                        "ThinkPad Battery",
                        "",
                        "LION",
                        "IBM Corporation "
                    })
                    Name (BT0P, Package (0x04) {})
                    Name (BT0J, 0x00)
                    Device (BAT0)
                    {
                        Name (_HID, EisaId ("PNP0C0A"))
                        Name (_UID, 0x00)
                        Name (_PCL, Package (0x01)
                        {
                            \_SB
                        })
                        Name (B0ST, 0x00)
                        Method (_STA, 0, NotSerialized)
                        {
                            If (\H8DR)
                            {
                                Store (HB0A, B0ST)
                            }
                            Else
                            {
                                If (And (\RBEC (0x38), 0x80))
                                {
                                    Store (0x01, B0ST)
                                }
                                Else
                                {
                                    Store (0x00, B0ST)
                                }
                            }

                            If (B0ST)
                            {
                                Return (0x1F)
                            }
                            Else
                            {
                                Return (0x0F)
                            }
                        }

                        Method (_BIF, 0, NotSerialized)
                        {
                            AI2C ()
                            Store (0x0A, Local6)
                            Store (0x01, Local5)
                            While (LAnd (Local5, Local6))
                            {
                                If (HB0A)
                                {
                                    Store (I2RB (Zero, 0x01, 0x10), Local7)
                                    If (LOr (LEqual (HMBC, 0x1C), Local7))
                                    {
                                        Store (0x00, Local5)
                                    }
                                    Else
                                    {
                                        Sleep (0x03E8)
                                        Decrement (Local6)
                                        Store (0x8080, Local7)
                                    }
                                }
                                Else
                                {
                                    Store (0x00, Local6)
                                    Store (0x00, Local7)
                                }
                            }

                            If (LOr (Local7, Local5))
                            {
                                Store (0x00, Index (BT0I, 0x00))
                                Store (0xFFFFFFFF, Index (BT0I, 0x01))
                                Store (0x00, Index (BT0I, 0x05))
                                Store (0x00, Index (BT0I, 0x06))
                                Store (0xFFFFFFFF, Index (BT0I, 0x02))
                            }
                            Else
                            {
                                Store (HBPU, Index (BT0I, 0x00))
                                Store (HBRC, Local0)
                                Store (Local0, Index (BT0I, 0x01))
                                Store (Divide (Local0, 0x14, ), Index (BT0I, 0x05))
                                Store (Divide (Local0, 0x64, ), Index (BT0I, 0x06))
                                Store (HBFC, Index (BT0I, 0x02))
                                Store (Divide (HBFC, 0x64, ), BT0J)
                            }

                            RI2C ()
                            If (Local7) {}
                            Return (BT0I)
                        }

                        Method (_BST, 0, NotSerialized)
                        {
                            AI2C ()
                            Store (I2RB (Zero, 0x01, 0x10), Local7)
                            If (LOr (LNot (LEqual (HMBC, 0x1C)), Local7))
                            {
                                Store (0x00, Index (BT0P, 0x03))
                                Store (0x00, Index (BT0P, 0x02))
                                Store (0x00, Index (BT0P, 0x01))
                                Store (0x04, Index (BT0P, 0x00))
                            }
                            Else
                            {
                                Store (HBVL, Local0)
                                Store (Local0, Index (BT0P, 0x03))
                                Store (Add (HBCC, BT0J), Local1)
                                If (LNot (LLess (Local1, HBFC)))
                                {
                                    Store (HBFC, Index (BT0P, 0x02))
                                }
                                Else
                                {
                                    Store (Local1, Index (BT0P, 0x02))
                                }

                                Store (HBEC, Local1)
                                If (LNot (LLess (Local1, 0x8000)))
                                {
                                    Store (Subtract (0x00010000, Local1), Local2)
                                }
                                Else
                                {
                                    Store (Local1, Local2)
                                }

                                If (HBPU)
                                {
                                    Store (Local2, Index (BT0P, 0x01))
                                }
                                Else
                                {
                                    Multiply (Local0, Local2, Local1)
                                    Store (Divide (Local1, 0x03E8, ), Index (BT0P, 0x01))
                                }

                                If (HB0C)
                                {
                                    Store (0x02, Index (BT0P, 0x00))
                                }
                                Else
                                {
                                    If (HB0D)
                                    {
                                        Store (0x01, Index (BT0P, 0x00))
                                    }
                                    Else
                                    {
                                        Store (0x00, Index (BT0P, 0x00))
                                    }
                                }

                                If (HB0L) {}
                                Else
                                {
                                    Or (DerefOf (Index (BT0P, 0x00)), 0x04, Index (BT0P, 0x00))
                                }
                            }

                            RI2C ()
                            Return (BT0P)
                        }

                        Method (_BTP, 1, NotSerialized)
                        {
                            And (HAM4, 0xEF, HAM4)
                            If (Arg0)
                            {
                                Subtract (Arg0, BT0J, Local1)
                                If (LNot (DerefOf (Index (BT0I, 0x00))))
                                {
                                    Divide (Local1, 0x0A, Local0, Local1)
                                }

                                And (Local1, 0xFF, HT0L)
                                And (ShiftRight (Local1, 0x08), 0xFF, HT0H)
                                Or (HAM4, 0x10, HAM4)
                            }
                        }
                    }

                    Name (BT1I, Package (0x0D)
                    {
                        0x00,
                        0x00,
                        0x00,
                        0x01,
                        0x2A30,
                        0x00,
                        0x00,
                        0x01,
                        0x01,
                        "ThinkPad Battery",
                        "",
                        "LION",
                        "IBM Corporation "
                    })
                    Name (BT1P, Package (0x04) {})
                    Name (BT1J, 0x00)
                    Device (BAT1)
                    {
                        Name (_HID, EisaId ("PNP0C0A"))
                        Name (_UID, 0x01)
                        Name (_PCL, Package (0x01)
                        {
                            \_SB
                        })
                        Name (B1ST, 0x00)
                        Name (XB1S, 0x01)
                        Method (_STA, 0, NotSerialized)
                        {
                            If (\H8DR)
                            {
                                Store (HB1A, B1ST)
                            }
                            Else
                            {
                                If (And (\RBEC (0x39), 0x80))
                                {
                                    Store (0x01, B1ST)
                                }
                                Else
                                {
                                    Store (0x00, B1ST)
                                }
                            }

                            If (B1ST)
                            {
                                If (XB1S)
                                {
                                    Return (0x1F)
                                }
                                Else
                                {
                                    If (\WNTF)
                                    {
                                        Return (0x00)
                                    }
                                    Else
                                    {
                                        Return (0x1F)
                                    }
                                }

                                Return (0x1F)
                            }
                            Else
                            {
                                If (\WNTF)
                                {
                                    Return (0x00)
                                }
                                Else
                                {
                                    Return (0x0F)
                                }
                            }
                        }

                        Method (_BIF, 0, NotSerialized)
                        {
                            AI2C ()
                            Store (0x0A, Local6)
                            Store (0x01, Local5)
                            While (LAnd (Local5, Local6))
                            {
                                If (HB1A)
                                {
                                    Store (I2RB (Zero, 0x01, 0x11), Local7)
                                    If (LOr (LEqual (HMBC, 0x1C), Local7))
                                    {
                                        Store (0x00, Local5)
                                    }
                                    Else
                                    {
                                        Sleep (0x03E8)
                                        Decrement (Local6)
                                        Store (0x8080, Local7)
                                    }
                                }
                                Else
                                {
                                    Store (0x00, Local6)
                                    Store (0x00, Local7)
                                }
                            }

                            If (LOr (Local7, Local5))
                            {
                                Store (0x00, Index (BT1I, 0x00))
                                Store (0xFFFFFFFF, Index (BT1I, 0x01))
                                Store (0x00, Index (BT1I, 0x05))
                                Store (0x00, Index (BT1I, 0x06))
                                Store (0xFFFFFFFF, Index (BT1I, 0x02))
                            }
                            Else
                            {
                                Store (HBPU, Index (BT1I, 0x00))
                                Store (HBRC, Local0)
                                Store (Local0, Index (BT1I, 0x01))
                                Store (Divide (Local0, 0x14, ), Index (BT1I, 0x05))
                                Store (Divide (Local0, 0x64, ), Index (BT1I, 0x06))
                                Store (HBFC, Index (BT1I, 0x02))
                                Store (Divide (HBFC, 0x64, ), BT1J)
                            }

                            RI2C ()
                            If (Local7) {}
                            Return (BT1I)
                        }

                        Method (_BST, 0, NotSerialized)
                        {
                            AI2C ()
                            Store (I2RB (Zero, 0x01, 0x11), Local7)
                            If (LOr (LNot (LEqual (HMBC, 0x1C)), Local7))
                            {
                                Store (0x00, Index (BT1P, 0x03))
                                Store (0x00, Index (BT1P, 0x02))
                                Store (0x00, Index (BT1P, 0x01))
                                Store (0x04, Index (BT1P, 0x00))
                            }
                            Else
                            {
                                Store (HBVL, Local0)
                                Store (Local0, Index (BT1P, 0x03))
                                Store (Add (HBCC, BT1J), Local1)
                                If (LNot (LLess (Local1, HBFC)))
                                {
                                    Store (HBFC, Index (BT1P, 0x02))
                                }
                                Else
                                {
                                    Store (Local1, Index (BT1P, 0x02))
                                }

                                Store (HBEC, Local1)
                                If (LNot (LLess (Local1, 0x8000)))
                                {
                                    Store (Subtract (0x00010000, Local1), Local2)
                                }
                                Else
                                {
                                    Store (Local1, Local2)
                                }

                                If (HBPU)
                                {
                                    Store (Local2, Index (BT1P, 0x01))
                                }
                                Else
                                {
                                    Multiply (Local0, Local2, Local1)
                                    Store (Divide (Local1, 0x03E8, ), Index (BT1P, 0x01))
                                }

                                If (HB1C)
                                {
                                    Store (0x02, Index (BT1P, 0x00))
                                }
                                Else
                                {
                                    If (HB1D)
                                    {
                                        Store (0x01, Index (BT1P, 0x00))
                                    }
                                    Else
                                    {
                                        Store (0x00, Index (BT1P, 0x00))
                                    }
                                }

                                If (HB1L) {}
                                Else
                                {
                                    Or (DerefOf (Index (BT1P, 0x00)), 0x04, Index (BT1P, 0x00))
                                }
                            }

                            RI2C ()
                            Return (BT1P)
                        }

                        Method (_BTP, 1, NotSerialized)
                        {
                            And (HAM4, 0xDF, HAM4)
                            If (Arg0)
                            {
                                Subtract (Arg0, BT1J, Local1)
                                If (LNot (DerefOf (Index (BT1I, 0x00))))
                                {
                                    Divide (Local1, 0x0A, Local0, Local1)
                                }

                                And (Local1, 0xFF, HT1L)
                                And (ShiftRight (Local1, 0x08), 0xFF, HT1H)
                                Or (HAM4, 0x20, HAM4)
                            }
                        }
                    }

                    Device (AC)
                    {
                        Name (_HID, "ACPI0003")
                        Name (_UID, 0x00)
                        Name (_PCL, Package (0x01)
                        {
                            \_SB
                        })
                        Method (_PSR, 0, NotSerialized)
                        {
                            Return (HPAC)
                        }

                        Method (_STA, 0, NotSerialized)
                        {
                            Return (0x0F)
                        }
                    }

                    Scope (\_SB.PCI0.ISA.EC)
                    {
                        Field (ECOR, ByteAcc, Lock, Preserve)
                        {
                            Offset (0x50),
                            HMPR,   8,
                            HMST,   5,
                                ,   1,
                            HMAR,   1,
                            HMDN,   1,
                            HMAD,   8,
                            HMCM,   8,
                            HMDT,   8,
                            Offset (0x74),
                            HMBC,   8
                        }

                        Field (ECOR, ByteAcc, Lock, Preserve)
                        {
                            Offset (0x54),
                            HBPU,   8,
                            Offset (0x56),
                            HBST,   8,
                            HBID,   4,
                            Offset (0x58),
                            HBRC,   32,
                            HBFC,   32,
                            HBCC,   32,
                            HBVL,   16,
                            HBEC,   16,
                            HBBT,   16,
                            HBNF,   16,
                            HBTC,   16,
                            HBCT,   16,
                            Offset (0x74),
                            Offset (0x100)
                        }

                        Field (ECOR, ByteAcc, Lock, Preserve)
                        {
                            Offset (0x54),
                            HBTS,   8,
                            HBAF,   1,
                            Offset (0x56),
                            HBSD,   16,
                            HBDT,   16,
                            HBH0,   16,
                            HBL0,   16,
                            HBH1,   16,
                            HBL1,   16,
                            HBH2,   16,
                            HBL2,   16
                        }

                        Field (ECOR, ByteAcc, Lock, Preserve)
                        {
                            Offset (0x54),
                            HF_Z,   8,
                            HF_D,   8,
                            HZIP,   8,
                            HDVD,   8,
                            HHFD,   8,
                            HF_H,   8,
                            HHDD,   8,
                            HADP,   8,
                            HLS,    8,
                            HF_C,   8,
                            HCRW,   8,
                            HCD,    8,
                            HR01,   8,
                            HFDD,   8,
                            HIMP,   8,
                            HNON,   8
                        }

                        Mutex (I2CM, 0x07)
                        Method (AI2C, 0, NotSerialized)
                        {
                            Return (Acquire (I2CM, 0xFFFF))
                        }

                        Method (RI2C, 0, NotSerialized)
                        {
                            Release (I2CM)
                        }

                        Method (I2CR, 3, NotSerialized)
                        {
                            AI2C ()
                            Store (Arg0, HCSL)
                            If (HCAD)
                            {
                                Or (ShiftLeft (Arg1, 0x01), 0x01, HMAD)
                            }
                            Else
                            {
                                Store (Arg1, HMAD)
                            }

                            Store (Arg2, HMCM)
                            Store (0x07, HMPR)
                            Store (CHKS (), Local7)
                            If (Local7)
                            {
                                Store (Local7, Local0)
                            }
                            Else
                            {
                                Store (HMDT, Local0)
                            }

                            RI2C ()
                            Return (Local0)
                        }

                        Method (I2CW, 4, NotSerialized)
                        {
                            AI2C ()
                            Store (Arg0, HCSL)
                            If (HCAD)
                            {
                                Or (ShiftLeft (Arg1, 0x01), 0x01, HMAD)
                            }
                            Else
                            {
                                Store (Arg1, HMAD)
                            }

                            Store (Arg2, HMCM)
                            Store (Arg3, HMDT)
                            Store (0x06, HMPR)
                            Store (CHKS (), Local0)
                            RI2C ()
                            Return (Local0)
                        }

                        Method (I2RB, 3, NotSerialized)
                        {
                            Store (Arg0, HCSL)
                            If (HCAD)
                            {
                                Store (ShiftLeft (Arg1, 0x01), HMAD)
                            }
                            Else
                            {
                                Store (Arg1, HMAD)
                            }

                            Store (Arg2, HMCM)
                            Store (0x0B, HMPR)
                            Return (CHKS ())
                        }

                        Method (I2WB, 4, NotSerialized)
                        {
                            Store (Arg0, HCSL)
                            If (HCAD)
                            {
                                Store (ShiftLeft (Arg1, 0x01), HMAD)
                            }
                            Else
                            {
                                Store (Arg1, HMAD)
                            }

                            Store (Arg2, HMCM)
                            Store (Arg3, HMBC)
                            Store (0x0A, HMPR)
                            Return (CHKS ())
                        }

                        Method (CHKS, 0, NotSerialized)
                        {
                            Store (0x03E8, Local0)
                            While (HMPR)
                            {
                                Sleep (0x01)
                                Decrement (Local0)
                                If (LNot (Local0))
                                {
                                    Return (0x8080)
                                }
                            }

                            If (HMDN)
                            {
                                If (HMST)
                                {
                                    Return (Or (0x8000, HMST))
                                }
                                Else
                                {
                                    Return (Zero)
                                }
                            }
                            Else
                            {
                                Return (0x8081)
                            }
                        }
                    }

                    Name (VDHK, 0x00)
                    Method (GHKS, 0, NotSerialized)
                    {
                        Store (\GHKY (), VDHK)
                    }

                    Device (HKEY)
                    {
                        Name (_HID, EisaId ("IBM0068"))
                        Method (_STA, 0, NotSerialized)
                        {
                            If (VDHK)
                            {
                                Return (0x0F)
                            }
                            Else
                            {
                                Return (0x00)
                            }
                        }

                        Name (DHKC, 0x00)
                        Name (DHKB, 0x01)
                        Mutex (XDHK, 0x07)
                        Name (DHKH, 0x00)
                        Name (DHKW, 0x00)
                        Name (DHKS, 0x00)
                        Name (DHKD, 0x00)
                        Method (MHKS, 0, NotSerialized)
                        {
                            Notify (\_SB.SLPB, 0x80)
                        }

                        Method (MHKC, 1, NotSerialized)
                        {
                            Store (Arg0, DHKC)
                        }

                        Method (MHKP, 0, NotSerialized)
                        {
                            Acquire (XDHK, 0xFFFF)
                            If (DHKW)
                            {
                                Store (DHKW, Local1)
                                Store (Zero, DHKW)
                            }
                            Else
                            {
                                If (DHKD)
                                {
                                    Store (DHKD, Local1)
                                    Store (Zero, DHKD)
                                }
                                Else
                                {
                                    If (DHKS)
                                    {
                                        Store (DHKS, Local1)
                                        Store (Zero, DHKS)
                                    }
                                    Else
                                    {
                                        Store (DHKH, Local1)
                                        Store (Zero, DHKH)
                                    }
                                }
                            }

                            Release (XDHK)
                            Return (Local1)
                        }

                        Method (MHKE, 1, NotSerialized)
                        {
                            Store (Arg0, DHKB)
                            Acquire (XDHK, 0xFFFF)
                            Store (Zero, DHKH)
                            Store (Zero, DHKW)
                            Store (Zero, DHKS)
                            Store (Zero, DHKD)
                            Release (XDHK)
                        }

                        Method (MHKQ, 1, NotSerialized)
                        {
                            If (DHKB)
                            {
                                If (DHKC)
                                {
                                    Acquire (XDHK, 0xFFFF)
                                    If (LLess (Arg0, 0x1000)) {}
                                    Else
                                    {
                                        If (LLess (Arg0, 0x2000))
                                        {
                                            Store (Arg0, DHKH)
                                        }
                                        Else
                                        {
                                            If (LLess (Arg0, 0x3000))
                                            {
                                                Store (Arg0, DHKW)
                                            }
                                            Else
                                            {
                                                If (LLess (Arg0, 0x4000))
                                                {
                                                    Store (Arg0, DHKS)
                                                }
                                                Else
                                                {
                                                    If (LLess (Arg0, 0x5000))
                                                    {
                                                        Store (Arg0, DHKD)
                                                    }
                                                    Else
                                                    {
                                                        If (LLess (Arg0, 0x6000))
                                                        {
                                                            Store (Arg0, DHKH)
                                                        }
                                                        Else
                                                        {
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }

                                    Release (XDHK)
                                    If (LEqual (DHKH, 0x1003))
                                    {
                                        \LGHT (0x00)
                                    }

                                    Notify (HKEY, 0x80)
                                }
                                Else
                                {
                                    If (LEqual (Arg0, 0x1004))
                                    {
                                        Notify (\_SB.SLPB, 0x80)
                                    }
                                }
                            }
                        }

                        Method (XGWT, 0, NotSerialized)
                        {
                            \VUPS (0x80)
                            If (\WNTF)
                            {
                                Store (0x00, Local0)
                                If (\VCDL)
                                {
                                    Or (0x01, Local0, Local0)
                                }

                                If (\VCDC)
                                {
                                    Or (0x02, Local0, Local0)
                                }

                                If (\VCDT)
                                {
                                    Or (0x04, Local0, Local0)
                                }

                                Return (Local0)
                            }
                            Else
                            {
                                Return (0xFFFF)
                            }
                        }

                        Method (XSWT, 1, NotSerialized)
                        {
                            If (\WNTF)
                            {
                                And (0x03, Arg0, Local0)
                                If (Local0)
                                {
                                    \_SB.PCI0.AGP.VID.ASWT (Local0, 0x01)
                                }
                            }
                            Else
                            {
                                Return (0xFFFF)
                            }
                        }

                        Method (MHKB, 1, NotSerialized)
                        {
                            If (LEqual (Arg0, 0x00))
                            {
                                \_SB.PCI0.ISA.EC.BEEP (0x11)
                            }
                            Else
                            {
                                If (LEqual (Arg0, 0x01))
                                {
                                    \_SB.PCI0.ISA.EC.BEEP (0x10)
                                }
                                Else
                                {
                                }
                            }
                        }

                        Method (MHKX, 0, NotSerialized)
                        {
                            If (\_SB.PCI0.ISA.FDC.DCFD)
                            {
                                Return (0x01)
                            }
                            Else
                            {
                                Return (0x03)
                            }
                        }
                    }
                }
            }

            Device (CBS0)
            {
                Name (_ADR, 0x00020000)
                OperationRegion (CBUS, PCI_Config, 0x00, 0x0100)
                Field (CBUS, DWordAcc, NoLock, Preserve)
                {
                    Offset (0x40),
                    SVID,   16,
                    SSID,   16,
                    LGDC,   32,
                    Offset (0x80),
                    SYSC,   32,
                    MCTL,   8,
                    Offset (0x91),
                    CCTL,   8,
                    Offset (0x93),
                    DIAG,   8
                }

                Method (_INI, 0, NotSerialized)
                {
                    Store (Zero, LGDC)
                    And (CCTL, 0x7F, CCTL)
                    Or (SYSC, 0x01, SYSC)
                    If (LNot (And (_ADR, 0xFFFF)))
                    {
                        And (MCTL, 0x83, BMCL)
                    }
                }

                Name (BMCL, 0x00)
                Name (PWRS, 0x00)
                Method (_PSC, 0, NotSerialized)
                {
                    Return (PWRS)
                }

                Method (_PS0, 0, NotSerialized)
                {
                    PWUP ()
                    Store (0x00, PWRS)
                }

                Method (_PS3, 0, NotSerialized)
                {
                    Store (0x03, PWRS)
                    PWDN ()
                }

                Method (PWDN, 0, NotSerialized)
                {
                    If (LAnd (\_SB.PCI0.CBS0.PWRS, \_SB.PCI0.CBS1.PWRS))
                    {
                        If (LNot (And (_ADR, 0xFFFF)))
                        {
                            And (MCTL, 0x83, BMCL)
                            And (MCTL, 0xFC, Local0)
                            Or (Local0, 0x80, MCTL)
                        }
                        Else
                        {
                            \_SB.PCI0.CBS0.PWDN ()
                        }
                    }
                }

                Method (PWUP, 0, NotSerialized)
                {
                    If (LAnd (\_SB.PCI0.CBS0.PWRS, \_SB.PCI0.CBS1.PWRS))
                    {
                        If (LNot (And (_ADR, 0xFFFF)))
                        {
                            And (MCTL, 0x7C, Local0)
                            Or (Local0, BMCL, MCTL)
                        }
                        Else
                        {
                            \_SB.PCI0.CBS0.PWUP ()
                        }
                    }
                }
            }

            Device (CBS1)
            {
                Name (_ADR, 0x00020001)
                OperationRegion (CBUS, PCI_Config, 0x00, 0x0100)
                Field (CBUS, DWordAcc, NoLock, Preserve)
                {
                    Offset (0x40),
                    SVID,   16,
                    SSID,   16,
                    LGDC,   32,
                    Offset (0x80),
                    SYSC,   32,
                    MCTL,   8,
                    Offset (0x91),
                    CCTL,   8,
                    Offset (0x93),
                    DIAG,   8
                }

                Method (_INI, 0, NotSerialized)
                {
                    Store (Zero, LGDC)
                    And (CCTL, 0x7F, CCTL)
                    Or (SYSC, 0x01, SYSC)
                    If (LNot (And (_ADR, 0xFFFF)))
                    {
                        And (MCTL, 0x83, BMCL)
                    }
                }

                Name (BMCL, 0x00)
                Name (PWRS, 0x00)
                Method (_PSC, 0, NotSerialized)
                {
                    Return (PWRS)
                }

                Method (_PS0, 0, NotSerialized)
                {
                    PWUP ()
                    Store (0x00, PWRS)
                }

                Method (_PS3, 0, NotSerialized)
                {
                    Store (0x03, PWRS)
                    PWDN ()
                }

                Method (PWDN, 0, NotSerialized)
                {
                    If (LAnd (\_SB.PCI0.CBS0.PWRS, \_SB.PCI0.CBS1.PWRS))
                    {
                        If (LNot (And (_ADR, 0xFFFF)))
                        {
                            And (MCTL, 0x83, BMCL)
                            And (MCTL, 0xFC, Local0)
                            Or (Local0, 0x80, MCTL)
                        }
                        Else
                        {
                            \_SB.PCI0.CBS0.PWDN ()
                        }
                    }
                }

                Method (PWUP, 0, NotSerialized)
                {
                    If (LAnd (\_SB.PCI0.CBS0.PWRS, \_SB.PCI0.CBS1.PWRS))
                    {
                        If (LNot (And (_ADR, 0xFFFF)))
                        {
                            And (MCTL, 0x7C, Local0)
                            Or (Local0, BMCL, MCTL)
                        }
                        Else
                        {
                            \_SB.PCI0.CBS0.PWUP ()
                        }
                    }
                }
            }

            Device (DOCK)
            {
                Name (_ADR, 0x00040000)
                Method (_BDN, 0, NotSerialized)
                {
                    Return (GDID ())
                }

                Method (_UID, 0, NotSerialized)
                {
                    Return (GDSR ())
                }

                Name (_PRT, Package (0x06)
                {
                    Package (0x04)
                    {
                        0xFFFF,
                        0x00,
                        \_SB.LNKA,
                        0x00
                    },

                    Package (0x04)
                    {
                        0xFFFF,
                        0x01,
                        \_SB.LNKB,
                        0x00
                    },

                    Package (0x04)
                    {
                        0xFFFF,
                        0x02,
                        \_SB.LNKC,
                        0x00
                    },

                    Package (0x04)
                    {
                        0xFFFF,
                        0x03,
                        \_SB.LNKD,
                        0x00
                    },

                    Package (0x04)
                    {
                        0x0001FFFF,
                        0x00,
                        \_SB.LNKB,
                        0x00
                    },

                    Package (0x04)
                    {
                        0x0002FFFF,
                        0x00,
                        \_SB.LNKC,
                        0x00
                    }
                })
                Method (_REG, 2, NotSerialized)
                {
                    If (LEqual (Arg0, 0x02))
                    {
                        If (Arg1)
                        {
                            Sleep (0x19)
                            And (\_SB.PCI0.ISA.SIRQ, 0x3F, \_SB.PCI0.ISA.SIRQ)
                        }

                        \_SB.PCI0.DOCK.CBS2.DREG (0x02, Arg1)
                        \_SB.PCI0.DOCK.CBS3.DREG (0x02, Arg1)
                        \_SB.PCI0.DOCK.IDE1.DREG (0x02, Arg1)
                        If (Arg1)
                        {
                            Or (\_SB.PCI0.ISA.SIRQ, 0xC0, \_SB.PCI0.ISA.SIRQ)
                            Stall (0x64)
                            And (\_SB.PCI0.ISA.SIRQ, 0xBF, \_SB.PCI0.ISA.SIRQ)
                            LTCY ()
                        }
                    }
                }

                Method (_INI, 0, NotSerialized)
                {
                    If (GDID ())
                    {
                        PPEN (0x00)
                        PPIN ()
                        PPEN (0x01)
                        If (\W98F)
                        {
                            _REG (0x02, 0x01)
                        }

                        DATT (0x00, 0x00)
                        DATT (0x01, 0x01)
                    }
                    Else
                    {
                        DATT (0x00, 0x01)
                        DATT (0x01, 0x00)
                    }

                    DDWK (0x00)
                }

                Method (_STA, 0, NotSerialized)
                {
                    If (\W98F)
                    {
                        If (DFLG (0x02, 0x08))
                        {
                            \_SB.PCI0.ISA.EC.HKEY.MHKQ (DHKE)
                            Notify (\_SB.PCI0.DOCK, 0x01)
                            DFLG (0x01, 0x08)
                        }
                    }

                    \_SB.PCI0.DOCK.WURQ ()
                    If (LEqual (GDID (), 0x4A004D24))
                    {
                        Store (0x0F, Local0)
                    }
                    Else
                    {
                        If (LNot (\W98F))
                        {
                            Store (0x00, Local0)
                        }
                        Else
                        {
                            Store (0x0C, Local0)
                        }
                    }

                    Return (Local0)
                }

                Name (_PRW, Package (0x02)
                {
                    0x0B,
                    0x04
                })
                Method (_PSW, 1, NotSerialized)
                {
                    EPSW (0x02, Arg0)
                }

                Name (DIDB, 0xFFFFFFFF)
                Method (DPTS, 1, NotSerialized)
                {
                    If (LAnd (LNot (LLess (Arg0, 0x01)), LNot (LGreater (Arg0, 0x04))))
                    {
                        DFLG (0x00, 0x0100)
                        Store (0x00, DHKE)
                        If (DFLG (0x02, 0x02))
                        {
                            Store (0x00, DOID)
                            DFLG (0x01, 0x02)
                        }

                        If (GDID ())
                        {
                            DDWK (0x01)
                            If (LEqual (Arg0, 0x01))
                            {
                                SSU2 (0x01)
                            }

                            If (LEqual (Arg0, 0x04))
                            {
                                Store (0x01, \_SB.PCI0.ISA.SLCK)
                            }
                        }
                        Else
                        {
                            DDWK (0x00)
                        }

                        Store (GDID (), DIDB)
                    }
                }

                Method (DWAK, 1, NotSerialized)
                {
                    Store (0xFFFFFFFF, DOID)
                    If (LAnd (LNot (LLess (Arg0, 0x01)), LNot (LGreater (Arg0, 0x04))))
                    {
                        If (LNot (LEqual (DIDB, 0x00)))
                        {
                            If (LNot (LEqual (GDID (), 0x00)))
                            {
                                PPEN (0x00)
                                PPIN ()
                                If (\W98F)
                                {
                                    _REG (0x02, 0x01)
                                    PPEN (0x01)
                                }

                                ShiftLeft (Arg0, 0x08, DHKE)
                                If (DFLG (0x02, 0x08))
                                {
                                    Or (DHKE, 0x2004, DHKE)
                                    If (LNot (\W98F))
                                    {
                                        \_SB.PCI0.ISA.EC.HKEY.MHKQ (DHKE)
                                        Notify (\_SB.PCI0.DOCK, 0x03)
                                        DFLG (0x01, 0x08)
                                    }
                                }
                                Else
                                {
                                    If (LEqual (\_SB.PCI0.DOCK.GDID (), 0x4A004D24))
                                    {
                                        Notify (\_SB.PCI0.DOCK.IDE1, 0x00)
                                    }

                                    If (LEqual (Arg0, 0x04))
                                    {
                                        \DHDP (0x03)
                                    }
                                }
                            }
                            Else
                            {
                                Notify (\_SB.PCI0.DOCK, 0x00)
                                \DHDP (0x00)
                            }
                        }
                        Else
                        {
                            If (LNot (LEqual (GDID (), 0x00)))
                            {
                                If (\_SB.PCI0.ISA.BUSC)
                                {
                                    _INI ()
                                    If (LNot (\W98F))
                                    {
                                        PPEN (0x00)
                                    }
                                }

                                Notify (\_SB.PCI0.DOCK, 0x00)
                            }
                        }

                        DDWK (0x00)
                        Store (0x00, \_SB.PCI0.ISA.SLCK)
                        DFLG (0x01, 0x0100)
                        If (LEqual (Arg0, 0x01))
                        {
                            SSU2 (0x00)
                        }

                        If (\WMEF)
                        {
                            DFLG (0x01, 0x02)
                        }
                    }
                }

                Method (_DCK, 1, NotSerialized)
                {
                    If (Arg0)
                    {
                        BCON (0x01)
                        Sleep (0x4B)
                        PPIN ()
                        If (LEqual (\_SB.PCI0.DOCK.GDID (), 0x4A004D24))
                        {
                            If (\W98F)
                            {
                                \DHDP (0x01)
                            }
                            Else
                            {
                                \DHDP (0x04)
                            }
                        }

                        If (\W98F)
                        {
                            PPEN (0x01)
                            _REG (0x02, 0x01)
                        }

                        DATT (0x00, 0x00)
                        DATT (0x01, 0x01)
                        If (\GVEN)
                        {
                            \GVIL (0x02)
                        }
                    }
                    Else
                    {
                        DFLG (0x00, 0x02)
                        \DHDP (0x00)
                        If (\W98F)
                        {
                            _REG (0x02, 0x00)
                        }

                        PPUB (0x00)
                        DATT (0x00, 0x01)
                        DATT (0x01, 0x00)
                        If (\GVEN)
                        {
                            \GVIL (0x03)
                        }
                    }

                    \_SB.PCI0.AGP.VID.VDSW (Arg0)
                    Return (0x01)
                }

                Method (_EJ0, 1, NotSerialized)
                {
                    If (DFLG (0x02, 0x02))
                    {
                        If (Arg0)
                        {
                            BCON (0x00)
                            WUIN ()
                            Store (0x00, DOID)
                            Store (0x00, \_SB.PCI0.ISA.FDC.DCFD)
                            Store (0x01, \_SB.PCI0.ISA.FDC.XFDS)
                        }

                        DFLG (0x01, 0x02)
                    }
                }

                Method (_EJ4, 1, NotSerialized)
                {
                    Store (0x00, \_SB.PCI0.ISA.FDC.DCFD)
                }

                Name (DOID, 0xFFFFFFFF)
                Name (DHKE, 0x00)
                Name (WUCT, 0x00)
                Mutex (WUDM, 0x07)
                Method (WURQ, 0, NotSerialized)
                {
                    If (And (DHKE, 0x2004))
                    {
                        If (LEqual (GDID (), 0x00))
                        {
                            Acquire (WUDM, 0xFFFF)
                            If (LNot (Decrement (WUCT)))
                            {
                                Store (0x01, Local0)
                            }
                            Else
                            {
                                Store (0x00, Local0)
                            }

                            Release (WUDM)
                            If (Local0)
                            {
                                Store (0x00, DHKE)
                                \_SB.PCI0.ISA.EC.HKEY.MHKQ (0x4003)
                            }
                        }
                    }
                }

                Method (WUIN, 0, NotSerialized)
                {
                    Acquire (WUDM, 0xFFFF)
                    If (\WNTF)
                    {
                        Store (0x21, WUCT)
                    }
                    Else
                    {
                        Store (0x01, WUCT)
                    }

                    Release (WUDM)
                }

                Method (GDID, 0, NotSerialized)
                {
                    If (LEqual (DOID, 0xFFFFFFFF))
                    {
                        Store (RDID (), DOID)
                    }

                    If (\WMEF)
                    {
                        Store (DOID, DIDB)
                    }

                    Return (DOID)
                }

                Method (GDSR, 0, NotSerialized)
                {
                    Return (RDSR ())
                }

                Method (RDID, 0, NotSerialized)
                {
                    Store (\_SB.PCI0.ISA.EC.GDEV (0x02), Local0)
                    If (And (Local0, 0x07))
                    {
                        Return (0x00)
                    }

                    If (LNot (\H8DR))
                    {
                        Return (\GDCK (0x02))
                    }

                    Store (0x10, Local0)
                    Store (0x00, Local1)
                    Store (0x00, Local2)
                    Store (0x00, Local3)
                    Store (0x00, Local4)
                    While (Local0)
                    {
                        Store (EEPR (Local2), Local1)
                        If (LAnd (LNot (LEqual (Local1, 0x8080)), LNot (LEqual (Local1, 0x8018))))
                        {
                            If (LEqual (And (Local1, 0x8000), 0x8000))
                            {
                                Return (0x00)
                            }
                            Else
                            {
                                If (LLess (Local2, 0x09))
                                {
                                    If (LAnd (LLess (Local2, 0x08), LGreater (Local2, 0x03)))
                                    {
                                        Or (Local3, ShiftLeft (Local1, Multiply (Subtract (Local2, 0x04), 0x08)), Local3)
                                    }

                                    Add (Local4, Local1, Local4)
                                    Store (0x10, Local0)
                                    Increment (Local2)
                                }
                                Else
                                {
                                    If (LEqual (Local2, 0x09))
                                    {
                                        If (LNot (And (Add (Local4, Local1), 0xFF)))
                                        {
                                            Return (Local3)
                                        }
                                        Else
                                        {
                                            Return (0x00)
                                        }
                                    }
                                }
                            }
                        }

                        Decrement (Local0)
                    }

                    Return (0x00)
                }

                Method (RDSR, 0, NotSerialized)
                {
                    If (LEqual (GDID (), 0x00))
                    {
                        Return (0x00)
                    }

                    If (LNot (\H8DR))
                    {
                        Return (\GDCK (0x01))
                    }

                    Store (0x10, Local0)
                    Store (0x00, Local1)
                    Store (0x00, Local2)
                    Store (0x00, Local3)
                    Store (0x00, Local4)
                    While (Local0)
                    {
                        Store (EEPR (Local2), Local1)
                        If (LAnd (LNot (LEqual (Local1, 0x8080)), LNot (LEqual (Local1, 0x8018))))
                        {
                            If (LEqual (And (Local1, 0x8000), 0x8000))
                            {
                                Return (0x00)
                            }
                            Else
                            {
                                If (LLess (Local2, 0x09))
                                {
                                    If (LLess (Local2, 0x04))
                                    {
                                        Or (Local3, ShiftLeft (Local1, Multiply (Local2, 0x08)), Local3)
                                    }

                                    Add (Local4, Local1, Local4)
                                    Store (0x10, Local0)
                                    Increment (Local2)
                                }
                                Else
                                {
                                    If (LEqual (Local2, 0x09))
                                    {
                                        If (LNot (And (Add (Local4, Local1), 0xFF)))
                                        {
                                            Return (Local3)
                                        }
                                        Else
                                        {
                                            Return (0x00)
                                        }
                                    }
                                }
                            }
                        }

                        Decrement (Local0)
                    }

                    Return (0x00)
                }

                Method (EEPR, 1, NotSerialized)
                {
                    Store (0x00, \_SB.PCI0.ISA.EC.HCAC)
                    Or (\_SB.PCI0.ISA.ACI, 0x01, \_SB.PCI0.ISA.ACI)
                    Store (\_SB.PCI0.ISA.EC.I2CR (0x00, 0x51, Arg0), Local0)
                    And (\_SB.PCI0.ISA.ACI, 0xFE, \_SB.PCI0.ISA.ACI)
                    Store (0x01, \_SB.PCI0.ISA.EC.HCAC)
                    Return (Local0)
                }

                Name (FLAG, 0x00)
                Method (DFLG, 2, NotSerialized)
                {
                    If (LEqual (Arg0, 0x00))
                    {
                        Or (FLAG, Arg1, FLAG)
                    }

                    If (LEqual (Arg0, 0x01))
                    {
                        And (FLAG, Not (Arg1), FLAG)
                    }

                    If (And (FLAG, Arg1))
                    {
                        Return (0x01)
                    }
                    Else
                    {
                        Return (0x00)
                    }
                }

                Method (DATT, 2, NotSerialized)
                {
                    Store (0x00, Local0)
                    If (LEqual (Arg0, 0x00))
                    {
                        If (LEqual (Arg1, 0x01))
                        {
                            If (\H8DR)
                            {
                                Or (\_SB.PCI0.ISA.EC.HAM6, 0x80, \_SB.PCI0.ISA.EC.HAM6)
                            }
                            Else
                            {
                                \MBEC (0x16, 0xFF, 0x80)
                            }
                        }

                        If (LEqual (Arg1, 0x00))
                        {
                            If (\H8DR)
                            {
                                And (\_SB.PCI0.ISA.EC.HAM6, 0x7F, \_SB.PCI0.ISA.EC.HAM6)
                            }
                            Else
                            {
                                \MBEC (0x16, 0x7F, 0x00)
                            }
                        }

                        If (LEqual (Arg1, 0x02))
                        {
                            If (\H8DR)
                            {
                                If (And (\_SB.PCI0.ISA.EC.HAM6, 0x80))
                                {
                                    Store (0x01, Local0)
                                }
                            }
                            Else
                            {
                                If (And (\RBEC (0x16), 0x80))
                                {
                                    Store (0x01, Local0)
                                }
                            }
                        }
                    }

                    If (LEqual (Arg0, 0x01))
                    {
                        If (LEqual (Arg1, 0x01))
                        {
                            If (\H8DR)
                            {
                                Or (\_SB.PCI0.ISA.EC.HAMA, 0x01, \_SB.PCI0.ISA.EC.HAMA)
                            }
                            Else
                            {
                                \MBEC (0x1A, 0xFF, 0x01)
                            }
                        }

                        If (LEqual (Arg1, 0x00))
                        {
                            If (\H8DR)
                            {
                                And (\_SB.PCI0.ISA.EC.HAMA, 0xFE, \_SB.PCI0.ISA.EC.HAMA)
                            }
                            Else
                            {
                                \MBEC (0x1A, 0xFE, 0x00)
                            }
                        }

                        If (LEqual (Arg1, 0x02))
                        {
                            If (\H8DR)
                            {
                                If (And (\_SB.PCI0.ISA.EC.HAMA, 0x01))
                                {
                                    Store (0x01, Local0)
                                }
                            }
                            Else
                            {
                                If (And (\RBEC (0x1A), 0x01))
                                {
                                    Store (0x01, Local0)
                                }
                            }
                        }
                    }

                    Return (Local0)
                }

                Method (DDWK, 1, NotSerialized)
                {
                    Store (0x00, Local0)
                    If (LEqual (Arg0, 0x01))
                    {
                        If (\H8DR)
                        {
                            Store (One, \_SB.PCI0.ISA.EC.HWDK)
                        }
                        Else
                        {
                            \MBEC (0x32, 0xFF, 0x08)
                        }
                    }

                    If (LEqual (Arg0, 0x00))
                    {
                        If (\H8DR)
                        {
                            Store (Zero, \_SB.PCI0.ISA.EC.HWDK)
                        }
                        Else
                        {
                            \MBEC (0x32, 0xF7, 0x00)
                        }
                    }

                    If (LEqual (Arg0, 0x02))
                    {
                        If (\H8DR)
                        {
                            If (\_SB.PCI0.ISA.EC.HWDK)
                            {
                                Store (0x01, Local0)
                            }
                        }
                        Else
                        {
                            If (And (\RBEC (0x32), 0x08))
                            {
                                Store (0x01, Local0)
                            }
                        }
                    }

                    Return (Local0)
                }

                Method (DGPE, 0, NotSerialized)
                {
                    If (\WMEF)
                    {
                        DFLG (0x00, 0x0100)
                    }

                    If (DFLG (0x02, 0x0100))
                    {
                        DFLG (0x00, 0x08)
                    }
                    Else
                    {
                        Or (DHKE, 0x2004, DHKE)
                        If (\W98F)
                        {
                            Notify (\_SB.PCI0.DOCK, 0x01)
                        }
                        Else
                        {
                            \_SB.PCI0.ISA.EC.HKEY.MHKQ (DHKE)
                            Notify (\_SB.PCI0.DOCK, 0x03)
                        }
                    }
                }

                Event (DEVT)
                Method (BCON, 1, NotSerialized)
                {
                    If (LAnd (Arg0, \_SB.PCI0.ISA.BUSC))
                    {
                        Return (0x00)
                    }

                    If (LAnd (LNot (Arg0), \_SB.PCI0.ISA.BUSD))
                    {
                        Return (0x00)
                    }

                    Store (DATT (0x00, 0x02), Local0)
                    DATT (0x00, 0x01)
                    Reset (DEVT)
                    If (Arg0)
                    {
                        Sleep (0xC8)
                        Store (0x00, \_SB.PCI0.ISA.BUSD)
                        Store (0x01, \_SB.PCI0.ISA.BUSC)
                    }
                    Else
                    {
                        Store (0x00, \_SB.PCI0.ISA.BUSC)
                        Store (0x01, \_SB.PCI0.ISA.BUSD)
                    }

                    Wait (DEVT, 0xFFFF)
                    If (LNot (Local0))
                    {
                        DATT (0x00, 0x00)
                    }
                }

                Method (LTCY, 0, NotSerialized)
                {
                    If (LEqual (GDID (), 0x4A004D24))
                    {
                        LDEV (0x00)
                        LDEV (0x01)
                        LCBS (0x02)
                    }
                }

                Method (LDEV, 1, NotSerialized)
                {
                    Or (0x80000000, ShiftLeft (\RPCI (0x80002019), 0x10), Local0)
                    Or (Local0, ShiftLeft (Arg0, 0x0B), Local0)
                    Store (0x00, Local1)
                    While (LLess (Local1, 0x08))
                    {
                        Or (Local0, ShiftLeft (Local1, 0x08), Local2)
                        Store (\RPCI (Or (Local2, 0x02)), Local3)
                        Store (\RPCI (Or (Local2, 0x03)), Local4)
                        If (LOr (LNot (LEqual (Local3, 0xFF)), LNot (LEqual (Local4, 0xFF))))
                        {
                            Store (\RPCI (Or (Local2, 0x0E)), Local5)
                            If (LNot (Local5))
                            {
                                Store (\RPCI (Or (Local2, 0x3E)), Local6)
                                If (LNot (LGreater (Local6, 0x08)))
                                {
                                    Store (0x40, Local7)
                                }
                                Else
                                {
                                    If (LNot (LGreater (Local6, 0x1F)))
                                    {
                                        Store (Multiply (Local6, 0x08), Local7)
                                    }
                                    Else
                                    {
                                        Store (0xD0, Local7)
                                    }
                                }

                                \WPCI (Or (Local2, 0x0D), Local7)
                                \WPCI (Or (Local2, 0x0C), 0x08)
                            }
                        }

                        Increment (Local1)
                    }
                }

                Method (LCBS, 1, NotSerialized)
                {
                    Or (0x80000000, ShiftLeft (\RPCI (0x80002019), 0x10), Local0)
                    Or (Local0, ShiftLeft (Arg0, 0x0B), Local0)
                    Store (0x00, Local1)
                    While (LLess (Local1, 0x02))
                    {
                        Or (Local0, ShiftLeft (Local1, 0x08), Local2)
                        \WPCI (Or (Local2, 0x0C), 0x08)
                        \WPCI (Or (Local2, 0x0D), 0x40)
                        \WPCI (Or (Local2, 0x1B), 0x80)
                        Increment (Local1)
                    }
                }

                Method (SSU2, 1, NotSerialized)
                {
                    If (Arg0)
                    {
                        Store (0x01, \_SB.PCI0.PM00.S2DS)
                        Store (0x01, \_SB.PCI0.ISA.SUS2)
                    }
                    Else
                    {
                        Store (0x00, \_SB.PCI0.ISA.SUS2)
                        Store (0x00, \_SB.PCI0.PM00.S2DS)
                    }
                }

                Scope (\_SB.PCI0.ISA.EC)
                {
                    Method (_Q37, 0, NotSerialized)
                    {
                        If (\_SB.PCI0.ISA.SCIS)
                        {
                            Store (\_SB.PCI0.ISA.SCIR, Local0)
                            If (LEqual (Local0, 0x00))
                            {
                                If (LNot (\_SB.PCI0.DOCK.GDID ()))
                                {
                                    Store (0xFFFFFFFF, \_SB.PCI0.DOCK.DOID)
                                    Notify (\_SB.PCI0.DOCK, 0x00)
                                }
                            }

                            If (LAnd (LEqual (Local0, 0x02), \_SB.PCI0.ISA.BUSC))
                            {
                                Signal (\_SB.PCI0.DOCK.DEVT)
                            }

                            If (LAnd (LEqual (Local0, 0x03), \_SB.PCI0.ISA.BUSD))
                            {
                                Signal (\_SB.PCI0.DOCK.DEVT)
                            }

                            Store (0x00, \_SB.PCI0.ISA.SCIS)
                        }
                    }

                    Method (_Q50, 0, NotSerialized)
                    {
                        If (\_SB.PCI0.DOCK.GDID ())
                        {
                            If (\W98F)
                            {
                                Notify (\_SB.PCI0.DOCK, 0x01)
                            }
                            Else
                            {
                                Notify (\_SB.PCI0.DOCK, 0x03)
                            }
                        }
                    }
                }

                OperationRegion (PPBR, PCI_Config, 0x00, 0x0100)
                Field (PPBR, DWordAcc, NoLock, Preserve)
                {
                    Offset (0x40),
                    SVID,   16,
                    SSID,   16,
                    Offset (0x66),
                    SDCL,   8,
                    PDCL,   8,
                    Offset (0x6C),
                    SCAD,   8,
                    BUFC,   8,
                    Offset (0x6F),
                    CLKR,   8,
                    Offset (0x76),
                    PG0D,   1,
                    PG1D,   1,
                    PG2D,   1,
                    PG3D,   1,
                    SG0D,   1,
                    SG1D,   1,
                    SG2D,   1,
                    SG3D,   1,
                    PG0O,   1,
                    PG1O,   1,
                    PG2O,   1,
                    PG3O,   1,
                    SG0O,   1,
                    SG1O,   1,
                    SG2O,   1,
                    SG3O,   1,
                    Offset (0x79),
                    SIRQ,   8,
                    ARMK,   8
                }

                Method (PPIN, 0, NotSerialized)
                {
                    Or (ShiftRight (0x00040000, 0x05), 0x80000000, Local0)
                    Store (\RPCI (Or (Local0, 0x84)), Local1)
                    If (LAnd (Local1, 0x03))
                    {
                        \WPCI (Or (Local0, 0x84), And (Local1, 0xFC))
                        Sleep (0x0A)
                    }

                    If (\W98F)
                    {
                        \WPCI (Or (Local0, 0x1C), 0xF0)
                        \WPCI (Or (Local0, 0x1D), 0x00)
                        \WPCI (Or (Local0, 0x20), 0xF0)
                        \WPCI (Or (Local0, 0x21), 0xFF)
                        \WPCI (Or (Local0, 0x22), 0x00)
                        \WPCI (Or (Local0, 0x23), 0x00)
                        \WPCI (Or (Local0, 0x24), 0xF0)
                        \WPCI (Or (Local0, 0x25), 0xFF)
                        \WPCI (Or (Local0, 0x26), 0x00)
                        \WPCI (Or (Local0, 0x27), 0x00)
                    }

                    \WPCI (Or (Local0, 0x19), 0x08)
                    \WPCI (Or (Local0, 0x1A), 0x0E)
                    \WPCI (Or (Local0, 0x0C), 0x08)
                    \WPCI (Or (Local0, 0x0D), 0x40)
                    \WPCI (Or (Local0, 0x1B), 0x44)
                    Store (0x1014, SVID)
                    Store (0xE3, SSID)
                    Or (And (SDCL, 0x00), 0x01, SDCL)
                    Or (And (PDCL, 0x00), 0x01, PDCL)
                    Or (And (SCAD, 0x02), 0xB0, SCAD)
                    Or (And (BUFC, 0x00), 0x1F, BUFC)
                    Or (And (CLKR, 0x00), 0x0C, CLKR)
                    Or (And (SIRQ, 0x00), 0x23, SIRQ)
                    Or (And (ARMK, 0x00), 0x38, ARMK)
                    PPFD ()
                    PPUB (0x01)
                    PPMX ()
                }

                Method (PPEN, 1, NotSerialized)
                {
                    Or (0x80000000, ShiftRight (0x00040000, 0x05), Local0)
                    If (Arg0)
                    {
                        \MPCI (Or (Local0, 0x04), 0xFF, 0x07)
                    }
                    Else
                    {
                        \MPCI (Or (Local0, 0x04), 0xF8, 0x00)
                    }
                }

                Method (PPRS, 0, NotSerialized)
                {
                    Or (0x80000000, ShiftRight (0x00040000, 0x05), Local0)
                    \MPCI (Or (Local0, 0x3E), 0xFF, 0x40)
                    Sleep (0x64)
                    \MPCI (Or (Local0, 0x3E), 0xBF, 0x00)
                }

                Method (PPFD, 0, NotSerialized)
                {
                    Store (0x01, SG1D)
                    If (LEqual (\_SB.PCI0.ISA.EC.GDEV (0x03), 0x0D))
                    {
                        Store (0x01, \_SB.PCI0.ISA.FDC.DCFD)
                        Store (0x01, SG1O)
                    }
                    Else
                    {
                        Store (0x00, \_SB.PCI0.ISA.FDC.DCFD)
                        Store (0x00, SG1O)
                    }
                }

                Method (PPUB, 1, NotSerialized)
                {
                    Store (0x00, SG3D)
                    If (Arg0)
                    {
                        Store (0x00, PG3O)
                    }
                    Else
                    {
                        Store (0x01, PG3O)
                    }

                    Store (0x01, PG3D)
                }

                Method (PPMX, 0, NotSerialized)
                {
                    Store (\RPCI (Or (0x80000019, ShiftRight (0x00040000, 0x05))), Local0)
                    Or (0x80000000, ShiftLeft (Local0, 0x10), Local0)
                    Store (0x04, Local1)
                    Store (0x00, Local2)
                    While (Local1)
                    {
                        Decrement (Local1)
                        ShiftLeft (Local2, 0x08, Local2)
                        Or (Local2, \RPCI (Or (Local0, Local1)), Local2)
                    }

                    If (LEqual (Local2, 0x00213388))
                    {
                        Or (SDCL, 0x04, SDCL)
                    }
                }

                Device (IDE1)
                {
                    Name (_ADR, 0x00010000)
                    OperationRegion (IDEC, PCI_Config, 0x00, 0x0100)
                    Field (IDEC, DWordAcc, NoLock, Preserve)
                    {
                        Offset (0x4F),
                            ,   2,
                        ENCL,   1,
                        Offset (0x50),
                        Offset (0x51),
                            ,   2,
                        PRMC,   1,
                        SNDC,   1,
                        Offset (0x52),
                        XCMT,   8,
                            ,   6,
                        XAR0,   2,
                        XDRR,   4,
                        XDRW,   4,
                        Offset (0x73),
                        XUDM,   1,
                            ,   1,
                        XUDC,   1,
                            ,   1,
                        XUDT,   2,
                        Offset (0x74)
                    }

                    Method (DREG, 2, NotSerialized)
                    {
                        If (LEqual (Arg0, 0x02))
                        {
                            If (Arg1)
                            {
                                If (LEqual (\_SB.PCI0.DOCK.GDID (), 0x4A004D24))
                                {
                                    If (LNot (And (\_SB.PCI0.DOCK.SCAD, 0x02)))
                                    {
                                        Store (0x01, PRMC)
                                        Store (0x01, SNDC)
                                    }
                                }

                                If (\W98F)
                                {
                                    RAID ()
                                }
                            }
                        }
                    }

                    Method (RAID, 0, NotSerialized)
                    {
                        Store (0x01, ENCL)
                        Store (\RPCI (Or (0x80000019, ShiftRight (0x00040000, 0x05))), Local0)
                        Or (0x80000000, ShiftLeft (Local0, 0x10), Local0)
                        Or (Local0, ShiftRight (_ADR, 0x05), Local0)
                        Or (Local0, ShiftLeft (And (_ADR, 0x07), 0x08), Local0)
                        \WPCI (Or (Local0, 0x0A), 0x04)
                        Store (0x00, ENCL)
                    }

                    Method (_STA, 0, NotSerialized)
                    {
                        Store (0x00, Local0)
                        If (LEqual (\_SB.PCI0.DOCK.GDID (), 0x4A004D24))
                        {
                            If (LNot (And (\_SB.PCI0.DOCK.SCAD, 0x02)))
                            {
                                Store (0x0F, Local0)
                            }
                        }

                        Return (Local0)
                    }

                    Device (PRIM)
                    {
                        Name (_ADR, 0x00)
                        Method (_GTM, 0, NotSerialized)
                        {
                            Store (0x12, Local4)
                            If (XCMT)
                            {
                                If (XDRR)
                                {
                                    If (LEqual (XDRR, 0x0F))
                                    {
                                        Store (0x01, Local0)
                                    }
                                    Else
                                    {
                                        Add (0x01, XDRR, Local0)
                                    }
                                }
                                Else
                                {
                                    Store (0x10, Local0)
                                }

                                If (XDRW)
                                {
                                    Store (XDRW, Local1)
                                }
                                Else
                                {
                                    Store (0x10, Local1)
                                }

                                Add (Local0, Local1, Local0)
                                Multiply (0x1E, Local0, Local0)
                                If (LGreater (Local0, 0xF0))
                                {
                                    Store (0x0384, Local0)
                                }

                                Store (Local0, Local1)
                            }
                            Else
                            {
                                Store (0x00, Local0)
                            }

                            Store (Local0, Local1)
                            If (XUDM)
                            {
                                Or (Local4, 0x01, Local4)
                                If (XUDC)
                                {
                                    Add (XUDT, 0x01, Local1)
                                    Multiply (0x0F, Local1, Local1)
                                }
                                Else
                                {
                                    Add (XUDT, 0x01, Local1)
                                    Multiply (0x1E, Local1, Local1)
                                    If (LEqual (Local1, 0x5A))
                                    {
                                        Store (0x50, Local1)
                                    }
                                }
                            }

                            Store (Local0, \GTP0)
                            Store (Local1, \GTD0)
                            Store (0x00, \GTP1)
                            Store (0x00, \GTD1)
                            Store (Local4, \GTMF)
                            Return (\BGTM)
                        }

                        Method (_STM, 3, NotSerialized)
                        {
                            CreateDWordField (Arg0, 0x00, STP0)
                            CreateDWordField (Arg0, 0x04, STD0)
                            CreateDWordField (Arg0, 0x08, STP1)
                            CreateDWordField (Arg0, 0x0C, STD1)
                            CreateDWordField (Arg0, 0x10, STMF)
                            If (SizeOf (Arg1))
                            {
                                CreateWordField (Arg1, 0x01, DM00)
                                If (DM00)
                                {
                                    Store (One, Local5)
                                }
                                Else
                                {
                                    Store (Zero, Local5)
                                }
                            }
                            Else
                            {
                                Store (Zero, Local5)
                            }

                            If (Local5)
                            {
                                If (W98F)
                                {
                                    CreateWordField (Arg1, 0x66, DM51)
                                    CreateWordField (Arg1, 0x6A, DM53)
                                    CreateWordField (Arg1, 0x7C, DM62)
                                    CreateWordField (Arg1, 0x7E, DM63)
                                    CreateWordField (Arg1, 0x80, DM64)
                                    CreateWordField (Arg1, 0x82, DM65)
                                    CreateWordField (Arg1, 0x88, DM68)
                                    CreateWordField (Arg1, 0xB0, DM88)
                                    Store (\UDMA (DM53, DM88), Local0)
                                    Store (\MDMA (DM53, DM63, DM62, DM65), Local1)
                                    Store (\MPIO (DM53, DM64, DM51, DM68), Local2)
                                }
                                Else
                                {
                                    Store (\MPIB (And (STMF, 0x02), STP0), Local2)
                                    Store (\UDMB (And (STMF, 0x01), STD0), Local0)
                                    Store (\MDMB (STD0), Local1)
                                }

                                Store (And (DM00, 0x80), \IDKS)
                                Store (\CART (Local2), XAR0)
                                Store (\CCMD (Local2), XCMT)
                                Store (\CDRW (Local1, Local2), Local3)
                                And (Local3, 0x0F, XDRR)
                                ShiftRight (Local3, 0x04, XDRW)
                                If (Local0)
                                {
                                    Store (0x01, XUDM)
                                    If (LNot (LGreater (Local0, 0x03)))
                                    {
                                        Store (0x00, XUDC)
                                    }
                                    Else
                                    {
                                        Store (0x01, XUDC)
                                    }

                                    Store (\CUDC (Local0), XUDT)
                                }

                                Store (\MHDM (Local0, Local1), \HDM3)
                                Store (\MHDM (Local0, Local1), \CDM3)
                                Store (\MHPI (Local2), \HPI3)
                                Store (\MHPI (Local2), \CPI3)
                            }
                        }

                        Device (MSTR)
                        {
                            Name (_ADR, 0x00)
                            Method (_GTF, 0, NotSerialized)
                            {
                                If (\IDKS)
                                {
                                    Return (\ICC3)
                                }
                                Else
                                {
                                    Return (\ICM3)
                                }
                            }
                        }
                    }
                }

                Device (CBS2)
                {
                    Name (_ADR, 0x00020000)
                    Method (_STA, 0, NotSerialized)
                    {
                        If (LEqual (\_SB.PCI0.DOCK.GDID (), 0x4A004D24))
                        {
                            Return (0x0F)
                        }
                        Else
                        {
                            Return (0x00)
                        }
                    }

                    Method (DREG, 2, NotSerialized)
                    {
                        If (LAnd (LEqual (Arg0, 0x02), LEqual (Arg1, 0x01)))
                        {
                            If (LEqual (\_SB.PCI0.DOCK.GDID (), 0x4A004D24))
                            {
                                ICFG ()
                            }
                        }
                    }

                    OperationRegion (CBUS, PCI_Config, 0x00, 0x0100)
                    Field (CBUS, DWordAcc, NoLock, Preserve)
                    {
                        Offset (0x44),
                        LGDC,   32,
                        Offset (0x80),
                        SYSC,   32,
                        Offset (0x8C),
                        MULR,   32,
                        RSTS,   8,
                        CCTL,   8,
                        DCTL,   8,
                        DIAG,   8
                    }

                    Method (ICFG, 0, NotSerialized)
                    {
                        Store (RPCI (Or (0x80000019, ShiftRight (0x00040000, 0x05))), Local0)
                        Or (0x80000000, ShiftLeft (Local0, 0x10), Local0)
                        Or (Local0, ShiftRight (_ADR, 0x05), Local0)
                        Or (Local0, ShiftLeft (And (_ADR, 0x07), 0x08), Local0)
                        \WPCI (Or (Local0, 0x0C), 0x08)
                        \WPCI (Or (Local0, 0x0D), 0xA8)
                        \WPCI (Or (Local0, 0x1B), 0x80)
                        Or (And (LGDC, 0x00), 0x00, LGDC)
                        Or (And (SYSC, 0x00FFFF00), 0x2864C077, SYSC)
                        Or (And (MULR, 0x00), 0x1002, MULR)
                        Or (And (RSTS, 0x00), 0xC0, RSTS)
                        Or (And (CCTL, 0x7B), 0x02, CCTL)
                        Or (And (DCTL, 0x00), 0x66, DCTL)
                        Or (And (DIAG, 0x1E), 0x40, DIAG)
                    }
                }

                Device (CBS3)
                {
                    Name (_ADR, 0x00020001)
                    Method (_STA, 0, NotSerialized)
                    {
                        If (LEqual (\_SB.PCI0.DOCK.GDID (), 0x4A004D24))
                        {
                            Return (0x0F)
                        }
                        Else
                        {
                            Return (0x00)
                        }
                    }

                    Method (DREG, 2, NotSerialized)
                    {
                        If (LAnd (LEqual (Arg0, 0x02), LEqual (Arg1, 0x01)))
                        {
                            If (LEqual (\_SB.PCI0.DOCK.GDID (), 0x4A004D24))
                            {
                                ICFG ()
                            }
                        }
                    }

                    OperationRegion (CBUS, PCI_Config, 0x00, 0x0100)
                    Field (CBUS, DWordAcc, NoLock, Preserve)
                    {
                        Offset (0x44),
                        LGDC,   32,
                        Offset (0x80),
                        SYSC,   32,
                        Offset (0x8C),
                        MULR,   32,
                        RSTS,   8,
                        CCTL,   8,
                        DCTL,   8,
                        DIAG,   8
                    }

                    Method (ICFG, 0, NotSerialized)
                    {
                        Store (RPCI (Or (0x80000019, ShiftRight (0x00040000, 0x05))), Local0)
                        Or (0x80000000, ShiftLeft (Local0, 0x10), Local0)
                        Or (Local0, ShiftRight (_ADR, 0x05), Local0)
                        Or (Local0, ShiftLeft (And (_ADR, 0x07), 0x08), Local0)
                        \WPCI (Or (Local0, 0x0C), 0x08)
                        \WPCI (Or (Local0, 0x0D), 0xA8)
                        \WPCI (Or (Local0, 0x1B), 0x80)
                        Or (And (LGDC, 0x00), 0x00, LGDC)
                        Or (And (SYSC, 0x00FFFF00), 0x2864C077, SYSC)
                        Or (And (MULR, 0x00), 0x1002, MULR)
                        Or (And (RSTS, 0x00), 0xC0, RSTS)
                        Or (And (CCTL, 0x7B), 0x02, CCTL)
                        Or (And (DCTL, 0x00), 0x66, DCTL)
                        Or (And (DIAG, 0x1E), 0x40, DIAG)
                    }
                }
            }
        }

        Scope (\_SB.PCI0.ISA.EC)
        {
            Name (BDEV, 0x00)
            Name (BSTS, 0x00)
            Name (BHKE, 0x00)
            Name (BXCN, 0x00)
            Method (_Q2C, 0, NotSerialized)
            {
                If (LEqual (BSTS, 0x00))
                {
                    Store (GUID (), BDEV)
                    If (BXCN)
                    {
                        NXRE (BDEV)
                    }
                    Else
                    {
                        NBRE (BDEV)
                    }
                }
            }

            Method (_Q2D, 0, NotSerialized)
            {
                Store (GUID (), BDEV)
                If (BXCN)
                {
                    NXRC (BDEV)
                }
                Else
                {
                    NBIN (BDEV)
                }
            }

            Method (_Q38, 0, NotSerialized)
            {
                Store (GUID (), Local0)
                If (LAnd (BDEV, LNot (LEqual (Local0, BDEV))))
                {
                    If (LEqual (Local0, 0x0F))
                    {
                        BDIS ()
                        If (BXCN)
                        {
                            Store (BDEV, Local0)
                            Store (0x0F, BDEV)
                            NXEJ (Local0)
                        }
                        Else
                        {
                            NBEJ (BDEV)
                            Store (Local0, BDEV)
                        }
                    }
                    Else
                    {
                        If (HPBU)
                        {
                            If (BXCN)
                            {
                                Store (Local0, BDEV)
                                NXIN (Local0)
                            }
                        }
                        Else
                        {
                            Store (Local0, BDEV)
                            If (BXCN)
                            {
                                NXRC (Local0)
                            }
                            Else
                            {
                                NBIN (Local0)
                            }
                        }
                    }
                }
            }

            Method (NBRE, 1, NotSerialized)
            {
                If (LEqual (Arg0, 0x0D))
                {
                    Notify (\_SB.PCI0.ISA.FDC.FDD0, 0x03)
                }

                If (LLess (Arg0, 0x0C))
                {
                    Notify (\_SB.PCI0.IDE0.SCND.MSTR, 0x03)
                }

                If (LEqual (Arg0, 0x10))
                {
                    If (LOr (HPAC, HB0A))
                    {
                        If (\WNTF)
                        {
                            Notify (\_SB.PCI0.ISA.EC.BAT1, 0x03)
                        }
                    }
                    Else
                    {
                        BLED (0x02, 0x01)
                        BEEP (0x0F)
                        Store (0x02, BSTS)
                    }
                }
            }

            Method (NBEJ, 1, NotSerialized)
            {
                If (LEqual (BSTS, 0x00))
                {
                    If (LEqual (Arg0, 0x0D))
                    {
                        Notify (\_SB.PCI0.ISA.FDC.FDD0, 0x01)
                    }

                    If (LLess (Arg0, 0x0C))
                    {
                        Notify (\_SB.PCI0.IDE0.SCND.MSTR, 0x01)
                    }

                    If (LEqual (Arg0, 0x10))
                    {
                        If (\WNTF)
                        {
                            Notify (\_SB.PCI0.ISA.EC.BAT1, 0x01)
                        }
                        Else
                        {
                            Notify (\_SB.PCI0.ISA.EC.BAT1, 0x81)
                        }
                    }
                }

                BLED (0x00, 0x00)
                BEEP (0x00)
                Store (0x00, BSTS)
            }

            Method (NBIN, 1, NotSerialized)
            {
                If (LEqual (Arg0, 0x0D))
                {
                    BEN (0x00)
                    \SFDD (0x00)
                    BLED (0x02, 0x00)
                    Notify (\_SB.PCI0.ISA.FDC.FDD0, 0x01)
                }

                If (LLess (Arg0, 0x0C))
                {
                    If (LEqual (Arg0, 0x06))
                    {
                        BEN (0x02)
                    }
                    Else
                    {
                        BEN (0x01)
                    }

                    BLED (0x02, 0x00)
                    Notify (\_SB.PCI0.IDE0.SCND.MSTR, 0x01)
                }

                If (LEqual (Arg0, 0x10))
                {
                    BLED (0x02, 0x00)
                    If (\WNTF)
                    {
                        Store (0x01, \_SB.PCI0.ISA.EC.BAT1.XB1S)
                        Notify (\_SB.PCI0.ISA.EC.BAT1, 0x01)
                    }
                    Else
                    {
                        Notify (\_SB.PCI0.ISA.EC.BAT1, 0x81)
                    }
                }

                BEEP (0x00)
                Store (0x00, BSTS)
            }

            Method (BEJ0, 1, NotSerialized)
            {
                If (Arg0)
                {
                    BDIS ()
                    BLED (0x00, 0x00)
                    \BHDP (0x00)
                    Store (0x01, BSTS)
                    If (BHKE)
                    {
                        Store (0x00, BHKE)
                        \_SB.PCI0.ISA.EC.HKEY.MHKQ (0x3003)
                    }
                }
                Else
                {
                    BLED (0x02, 0x00)
                    Store (0x00, BSTS)
                }
            }

            Method (BEJ3, 1, NotSerialized)
            {
                If (Arg0)
                {
                    Store (0x83, BF_Z)
                    Store (0x83, BF_D)
                    Store (0x83, BZIP)
                    Store (0x83, BDVD)
                    Store (0x83, BHFD)
                    Store (0x83, BF_H)
                    Store (0x83, BHDD)
                    Store (0x83, BLS)
                    Store (0x83, BF_C)
                    Store (0x83, BCRW)
                    Store (0x83, BCD)
                    Store (0x83, BFDD)
                    BDIS ()
                    Store (0x01, BSTS)
                }
                Else
                {
                    Store (0x81, BF_Z)
                    Store (0x81, BF_D)
                    Store (0x81, BZIP)
                    Store (0x81, BDVD)
                    Store (0x81, BHFD)
                    Store (0x81, BF_H)
                    Store (0x81, BHDD)
                    Store (0x81, BLS)
                    Store (0x81, BF_C)
                    Store (0x81, BCRW)
                    Store (0x81, BCD)
                    Store (0x81, BFDD)
                    Store (0x00, BSTS)
                }
            }

            Method (BPTS, 1, NotSerialized)
            {
                If (LOr (LEqual (Arg0, 0x00), LNot (LLess (Arg0, 0x05)))) {}
                Else
                {
                    If (LNot (LEqual (BSTS, 0x00)))
                    {
                        Store (0x0F, BDEV)
                        Store (0x00, BSTS)
                    }

                    Store (0x00, BHKE)
                    If (LNot (LEqual (BDEV, 0x0F)))
                    {
                        BLDT (0x00)
                        BUWK (0x01)
                    }
                    Else
                    {
                        BLDT (0x01)
                        BUWK (0x00)
                    }
                }
            }

            Method (BWAK, 1, NotSerialized)
            {
                If (LOr (LEqual (Arg0, 0x00), LNot (LLess (Arg0, 0x05)))) {}
                Else
                {
                    BUWK (0x00)
                    Store (GUID (), Local0)
                    If (LGreater (Local0, 0x0E))
                    {
                        BDIS ()
                    }

                    \_SB.PCI0.ISA.FDC._INI ()
                    If (LNot (LEqual (Local0, 0x0D)))
                    {
                        If (LEqual (\_SB.PCI0.ISA.FDC.FD0S, \_SB.PCI0.ISA.EC.HPNF))
                        {
                            Notify (\_SB.PCI0.ISA.FDC.FDD0, 0x01)
                        }
                    }

                    If (LEqual (BSTS, 0x00))
                    {
                        If (LNot (LEqual (Local0, BDEV)))
                        {
                            If (BXCN)
                            {
                                Store (Local0, BDEV)
                                NXRC (Local0)
                            }
                            Else
                            {
                                NBEJ (BDEV)
                                Store (Local0, BDEV)
                                NBIN (Local0)
                            }
                        }
                        Else
                        {
                            If (LNot (LEqual (Local0, 0x0F)))
                            {
                                BLED (0x02, 0x00)
                                If (HPBU)
                                {
                                    Or (ShiftLeft (Arg0, 0x08), 0x2005, BHKE)
                                    \_SB.PCI0.ISA.EC.HKEY.MHKQ (BHKE)
                                    If (LNot (LGreater (Arg0, 0x02))) {}
                                    Else
                                    {
                                        If (BXCN)
                                        {
                                            NXRE (Local0)
                                        }
                                        Else
                                        {
                                            NBRE (Local0)
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }

            Method (BDIS, 0, NotSerialized)
            {
                \SFDD (0x01)
                Store (0x00, \_SB.PCI0.IDE0.XSI0)
                Store (0x01, \_SB.PCI0.ISA.GCRC)
                Store (0x01, \_SB.PCI0.PM00.ULON)
                Store (0x01, \_SB.PCI0.PM00.CSON)
            }

            Method (BEN, 1, NotSerialized)
            {
                If (LNot (LOr (\_SB.PCI0.PM00.ULON, \_SB.PCI0.PM00.CSON)))
                {
                    Return (0x00)
                }

                If (Arg0)
                {
                    Store (0x00, \_SB.PCI0.IDE0.XSE)
                    Stall (0x05)
                }

                Store (0x00, \_SB.PCI0.PM00.URST)
                Store (0x00, \_SB.PCI0.PM00.ULON)
                Store (0x00, \_SB.PCI0.PM00.CSON)
                Sleep (0x0F)
                If (Arg0)
                {
                    Store (0x00, \_SB.PCI0.ISA.GCRC)
                    Store (0x01, \_SB.PCI0.IDE0.XSE)
                    Stall (0x2D)
                }

                Store (0x01, \_SB.PCI0.PM00.URST)
                Sleep (0x14)
                If (Arg0)
                {
                    Sleep (0x0190)
                    If (LEqual (Arg0, 0x02))
                    {
                        Sleep (0x07D0)
                    }
                }
            }

            Method (BSTA, 1, NotSerialized)
            {
                If (\_SB.PCI0.PM00.CSON)
                {
                    Return (0x00)
                }

                Store (GUID (), Local0)
                If (LEqual (Arg0, 0x00))
                {
                    Return (LEqual (Local0, 0x0D))
                }

                If (LEqual (Arg0, 0x01))
                {
                    Return (LLess (Local0, 0x0D))
                }

                Return (0x00)
            }

            Method (BLED, 2, NotSerialized)
            {
                If (\H8DR)
                {
                    Acquire (LEDM, 0xFFFF)
                    Store (0x18, HLMS)
                    If (Arg1)
                    {
                        Store (0x18, HLBL)
                    }
                    Else
                    {
                        Store (0x00, HLBL)
                    }

                    If (LEqual (Arg0, 0x00))
                    {
                        Store (0x00, HLCL)
                    }
                    Else
                    {
                        If (LEqual (Arg0, 0x01))
                        {
                            Store (0x08, HLCL)
                        }
                        Else
                        {
                            If (LEqual (Arg0, 0x02))
                            {
                                Store (0x10, HLCL)
                            }
                            Else
                            {
                            }
                        }
                    }

                    Sleep (0x0A)
                    Release (LEDM)
                }
            }

            Name (BF_Z, 0x83)
            Name (BF_D, 0x83)
            Name (BZIP, 0x83)
            Name (BDVD, 0x83)
            Name (BHFD, 0x83)
            Name (BF_H, 0x83)
            Name (BHDD, 0x83)
            Name (BADP, 0x00)
            Name (BLS, 0x83)
            Name (BF_C, 0x83)
            Name (BCRW, 0x83)
            Name (BCD, 0x83)
            Name (BR01, 0x00)
            Name (BFDD, 0x83)
            Name (BIMP, 0x00)
            Name (BNON, 0x83)
            Method (BLDT, 1, NotSerialized)
            {
                AI2C ()
                If (Arg0)
                {
                    Store (BF_Z, HF_Z)
                    Store (BF_D, HF_D)
                    Store (BZIP, HZIP)
                    Store (BDVD, HDVD)
                    Store (BHFD, HHFD)
                    Store (BF_H, HF_H)
                    Store (BHDD, HHDD)
                    Store (BADP, HADP)
                    Store (BLS, HLS)
                    Store (BF_C, HF_C)
                    Store (BCRW, HCRW)
                    Store (BCD, HCD)
                    Store (BR01, HR01)
                    Store (BFDD, HFDD)
                    Store (BIMP, HIMP)
                    Store (BNON, HNON)
                }
                Else
                {
                    Store (0x81, HF_Z)
                    Store (0x81, HF_D)
                    Store (0x81, HZIP)
                    Store (0x81, HDVD)
                    Store (0x81, HHFD)
                    Store (0x81, HF_H)
                    Store (0x81, HHDD)
                    Store (0x00, HADP)
                    Store (0x81, HLS)
                    Store (0x81, HF_C)
                    Store (0x81, HCRW)
                    Store (0x81, HCD)
                    Store (0x00, HR01)
                    Store (0x81, HFDD)
                    Store (0x00, HIMP)
                    Store (0x81, HNON)
                }

                Store (I2WB (Zero, 0x01, 0x09, 0x10), Local7)
                RI2C ()
                If (Local7)
                {
                    Fatal (0x01, 0x80000003, Local7)
                }
            }

            Method (BUWK, 1, NotSerialized)
            {
                If (\H8DR)
                {
                    If (Arg0)
                    {
                        Store (0x01, \_SB.PCI0.ISA.EC.HWBU)
                    }
                    Else
                    {
                        Store (0x00, \_SB.PCI0.ISA.EC.HWBU)
                    }
                }
                Else
                {
                    If (Arg0)
                    {
                        \MBEC (0x32, 0xFF, 0x80)
                    }
                    Else
                    {
                        \MBEC (0x32, 0x7F, 0x00)
                    }
                }
            }

            Method (NXRE, 1, NotSerialized)
            {
                If (LEqual (Arg0, 0x0F))
                {
                    BLED (0x00, 0x00)
                    Store (0x00, BSTS)
                }

                If (LEqual (Arg0, 0x0D))
                {
                    BLED (0x02, 0x01)
                    Notify (\_SB.SWAP, 0x83)
                }

                If (LLess (Arg0, 0x0C))
                {
                    BLED (0x02, 0x01)
                    Notify (\_SB.SWAP, 0x83)
                }

                If (LEqual (Arg0, 0x10))
                {
                    If (LOr (HPAC, HB0A))
                    {
                        BLED (0x02, 0x01)
                        Notify (\_SB.SWAP, 0x83)
                    }
                    Else
                    {
                        BLED (0x02, 0x01)
                        BEEP (0x0F)
                        Store (0x02, BSTS)
                    }
                }
            }

            Method (NXRC, 1, NotSerialized)
            {
                If (LEqual (Arg0, 0x0D))
                {
                    BLED (0x02, 0x00)
                    BEN (0x00)
                    \SFDD (0x00)
                    Notify (\_SB.SWAP, 0x80)
                }

                If (LLess (Arg0, 0x0C))
                {
                    BLED (0x02, 0x00)
                    If (LEqual (Arg0, 0x06))
                    {
                        BEN (0x02)
                    }
                    Else
                    {
                        BEN (0x01)
                    }

                    Notify (\_SB.SWAP, 0x80)
                }

                If (LEqual (Arg0, 0x10))
                {
                    Notify (\_SB.PCI0.ISA.EC.BAT1, 0x81)
                    BLED (0x02, 0x00)
                    Notify (\_SB.SWAP, 0x80)
                }

                BEEP (0x00)
                Store (0x00, BSTS)
            }

            Method (NXEJ, 1, NotSerialized)
            {
                If (LEqual (Arg0, 0x10))
                {
                    Notify (\_SB.PCI0.ISA.EC.BAT1, 0x81)
                }

                Notify (\_SB.SWAP, 0x82)
                BLED (0x00, 0x00)
                BEEP (0x00)
                Store (0x00, BSTS)
            }

            Method (NXIN, 1, NotSerialized)
            {
                Notify (\_SB.SWAP, 0x81)
            }
        }

        Scope (\_SB)
        {
            Device (SWAP)
            {
                Name (_HID, EisaId ("IBM0069"))
                Method (_STA, 0, NotSerialized)
                {
                    If (\WMEF)
                    {
                        Return (0x0F)
                    }
                    Else
                    {
                        Return (0x00)
                    }
                }

                Method (XCNN, 1, NotSerialized)
                {
                    Store (Arg0, \_SB.PCI0.ISA.EC.BXCN)
                    Return (0x09)
                }

                Method (XSWP, 0, NotSerialized)
                {
                    Return (0x01)
                }

                Method (XEJ0, 1, NotSerialized)
                {
                    Store (0x00, \_SB.PCI0.ISA.EC.BAT1.B1ST)
                    \_SB.PCI0.ISA.EC.BEJ0 (Arg0)
                }

                Method (XEJ3, 1, NotSerialized)
                {
                    Store (0x00, \_SB.PCI0.ISA.EC.BAT1.B1ST)
                    \_SB.PCI0.ISA.EC.BEJ3 (Arg0)
                }

                Method (XDID, 0, NotSerialized)
                {
                    Name (XPCK, Package (0x06)
                    {
                        0x00,
                        0x00,
                        0xFFFFFFFF,
                        0xFFFFFFFF,
                        0xFFFFFFFF,
                        0x00
                    })
                    Store (\_SB.PCI0.ISA.EC.BDEV, Local0)
                    Store (Local0, Index (XPCK, 0x00))
                    If (LLess (Local0, 0x0C))
                    {
                        Store (\_SB.PCI0.IDE0._ADR, Index (XPCK, 0x02))
                        Store (\_SB.PCI0.IDE0.SCND._ADR, Index (XPCK, 0x03))
                        Store (\_SB.PCI0.IDE0.SCND.MSTR._ADR, Index (XPCK, 0x04))
                    }

                    If (LEqual (Local0, 0x0D))
                    {
                        Store (\_SB.PCI0.ISA.FDC._HID, Index (XPCK, 0x02))
                        Store (\_SB.PCI0.ISA.FDC.FDD0._ADR, Index (XPCK, 0x04))
                    }

                    If (LEqual (Local0, 0x10))
                    {
                        Store (\_SB.PCI0.ISA.EC.BAT1._HID, Index (XPCK, 0x02))
                        Store (\_SB.PCI0.ISA.EC.BAT1._UID, Index (XPCK, 0x04))
                    }

                    Store (XOr (\_SB.PCI0.PM00.CSON, 0x01), Index (XPCK, 0x05))
                    Return (XPCK)
                }

                Method (XSTM, 1, NotSerialized)
                {
                    Name (XDMY, Buffer (0x14) {})
                    \_SB.PCI0.IDE0.SCND._STM (XDMY, Arg0, 0x00)
                }

                Method (XGTF, 0, NotSerialized)
                {
                    Return (\_SB.PCI0.IDE0.SCND.MSTR._GTF ())
                }
            }
        }

        Scope (\_SB.PCI0.IDE0.SCND.MSTR)
        {
            Method (_EJ0, 1, NotSerialized)
            {
                \_SB.PCI0.ISA.EC.BEJ0 (Arg0)
            }

            Method (_STA, 0, NotSerialized)
            {
                If (\_SB.PCI0.ISA.EC.BSTA (0x01))
                {
                    Return (0x0F)
                }
                Else
                {
                    Return (0x00)
                }
            }
        }

        Scope (\_SB.PCI0.ISA.FDC)
        {
            Method (_INI, 0, NotSerialized)
            {
                Store (0x00, \_SB.PCI0.ISA.FDC.XFDS)
                If (\H8DR)
                {
                    Or (\_SB.PCI0.ISA.EC.HAMA, 0x0C, \_SB.PCI0.ISA.EC.HAMA)
                }
                Else
                {
                    \MBEC (0x1A, 0xFF, 0x0C)
                }
            }

            Name (FDEB, Buffer (0x14)
            {
                0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x02, 0x00, 0x00, 0x00
            })
            CreateByteField (FDEB, 0x00, FD0S)
            Name (XFDS, 0x00)
            Name (DCFD, 0x00)
            Method (_FDE, 0, NotSerialized)
            {
                If (LOr (\_SB.PCI0.ISA.EC.BSTA (0x00), DCFD))
                {
                    Store (0x01, FD0S)
                }
                Else
                {
                    If (LOr (\_SB.PCI0.ISA.EC.HPNF, XFDS))
                    {
                        Store (0x00, FD0S)
                    }
                    Else
                    {
                        Store (0x01, FD0S)
                    }
                }

                Return (FDEB)
            }

            Device (FDD0)
            {
                Name (_ADR, 0x00)
                Name (_EJD, "_SB.PCI0.DOCK")
                Method (_EJ0, 1, NotSerialized)
                {
                    If (\_SB.PCI0.ISA.EC.BSTA (0x00))
                    {
                        \_SB.PCI0.ISA.EC.BEJ0 (Arg0)
                    }
                    Else
                    {
                        If (DCFD) {}
                        Else
                        {
                            Store (0x01, XFDS)
                        }
                    }
                }

                Name (_FDI, Package (0x10)
                {
                    0x00,
                    0x04,
                    0x4F,
                    0x12,
                    0x01,
                    0xDF,
                    0x02,
                    0x25,
                    0x02,
                    0x12,
                    0x1B,
                    0xFF,
                    0x6C,
                    0xF6,
                    0x0F,
                    0x05
                })
            }
        }

        Scope (\_SB.PCI0.ISA.EC)
        {
            Method (_Q52, 0, NotSerialized)
            {
                If (\_SB.PCI0.ISA.FDC.XFDS)
                {
                    Store (0x00, \_SB.PCI0.ISA.FDC.XFDS)
                }
                Else
                {
                    If (LOr (\_SB.PCI0.ISA.EC.BSTA (0x00), \_SB.PCI0.ISA.FDC.DCFD)) {}
                    Else
                    {
                        Notify (\_SB.PCI0.ISA.FDC.FDD0, 0x01)
                    }
                }
            }

            Method (_Q53, 0, NotSerialized)
            {
                Store (0x00, \_SB.PCI0.ISA.FDC.XFDS)
                If (LOr (\_SB.PCI0.ISA.EC.BSTA (0x00), \_SB.PCI0.ISA.FDC.DCFD)) {}
                Else
                {
                    Notify (\_SB.PCI0.ISA.FDC.FDD0, 0x01)
                }
            }
        }

        Scope (\_SB.PCI0.ISA.EC.BAT1)
        {
            Method (_EJ0, 1, NotSerialized)
            {
                Store (0x00, B1ST)
                Store (0x00, XB1S)
                \_SB.PCI0.ISA.EC.BEJ0 (Arg0)
            }
        }

        Scope (\_SB.PCI0.ISA.EC)
        {
            Method (_Q1C, 0, NotSerialized)
            {
                \VOLD ()
            }

            Method (_Q1D, 0, NotSerialized)
            {
                \VOLU ()
            }

            Method (_Q1E, 0, NotSerialized)
            {
                \VOLM ()
            }
        }

        Scope (\_SB.PCI0.ISA.EC)
        {
            Method (_Q14, 0, NotSerialized)
            {
                \BRIU ()
            }

            Method (_Q15, 0, NotSerialized)
            {
                \BRID ()
            }
        }

        Scope (\_SB.PCI0.ISA.EC)
        {
            Method (_Q19, 0, NotSerialized)
            {
                \TPKY ()
            }
        }

        Scope (\_SB.PCI0.ISA.EC.HKEY)
        {
            Name (BTID, 0x00)
            Name (BTFG, 0x00)
            Method (GULP, 0, NotSerialized)
            {
                Store (0x00, Local0)
                If (LEqual (BTID, 0x01))
                {
                    Or (Local0, 0x01, Local0)
                }

                If (PWRS ())
                {
                    Or (Local0, 0x02, Local0)
                }

                If (And (BTFG, 0x01))
                {
                    Or (Local0, 0x04, Local0)
                }

                Return (Local0)
            }

            Method (SULP, 1, NotSerialized)
            {
                If (And (Arg0, 0x02))
                {
                    PWRC (0x01)
                }
                Else
                {
                    PWRC (0x00)
                }

                If (And (Arg0, 0x04))
                {
                    Or (BTFG, 0x01, BTFG)
                    \GBTH (0x02)
                }
                Else
                {
                    And (BTFG, Not (0x01), BTFG)
                    \GBTH (0x03)
                }

                Return (GULP ())
            }

            Method (BTIN, 0, NotSerialized)
            {
                Store (\GBTH (0x00), BTID)
                If (\GBTH (0x01))
                {
                    Or (BTFG, 0x01, BTFG)
                }

                ATCH (0x01)
                PBTN (0x01)
                MODE (0x01)
            }

            Method (BTPS, 1, NotSerialized)
            {
                PBTN (0x00)
                If (LEqual (BTID, 0x01))
                {
                    If (LNot (And (BTFG, 0x01)))
                    {
                        PWRC (0x00)
                    }
                }

                If (PWRS ())
                {
                    Or (BTFG, 0x02, BTFG)
                }
                Else
                {
                    And (BTFG, Not (0x02), BTFG)
                }
            }

            Method (BTWK, 1, NotSerialized)
            {
                PBTN (0x01)
                If (And (BTFG, 0x02))
                {
                    PWRC (0x01)
                }
            }

            Method (PWRC, 1, NotSerialized)
            {
                If (Arg0)
                {
                    If (\H8DR)
                    {
                        Store (One, \_SB.PCI0.ISA.EC.BTPW)
                    }
                    Else
                    {
                        \MBEC (0x3B, 0xFF, 0x04)
                    }
                }
                Else
                {
                    If (\H8DR)
                    {
                        Store (Zero, \_SB.PCI0.ISA.EC.BTPW)
                    }
                    Else
                    {
                        \MBEC (0x3B, 0xFB, 0x00)
                    }
                }
            }

            Method (ATCH, 1, NotSerialized)
            {
                If (Arg0)
                {
                    If (\H8DR)
                    {
                        Store (Zero, \_SB.PCI0.ISA.EC.BTDT)
                    }
                    Else
                    {
                        \MBEC (0x3B, 0xF7, 0x00)
                    }
                }
                Else
                {
                    If (\H8DR)
                    {
                        Store (One, \_SB.PCI0.ISA.EC.BTDT)
                    }
                    Else
                    {
                        \MBEC (0x3B, 0xFF, 0x08)
                    }
                }
            }

            Method (MODE, 1, NotSerialized)
            {
                If (Arg0)
                {
                    If (\H8DR)
                    {
                        Store (One, \_SB.PCI0.ISA.EC.BTCM)
                    }
                    Else
                    {
                        \MBEC (0x01, 0xFF, 0x02)
                    }
                }
                Else
                {
                    If (\H8DR)
                    {
                        Store (Zero, \_SB.PCI0.ISA.EC.BTCM)
                    }
                    Else
                    {
                        \MBEC (0x01, 0xFD, 0x00)
                    }
                }
            }

            Method (PBTN, 1, NotSerialized)
            {
                If (Arg0)
                {
                    If (\H8DR)
                    {
                        Store (One, \_SB.PCI0.ISA.EC.BTPC)
                    }
                    Else
                    {
                        \MBEC (0x01, 0xFF, 0x40)
                    }
                }
                Else
                {
                    If (\H8DR)
                    {
                        Store (Zero, \_SB.PCI0.ISA.EC.BTPC)
                    }
                    Else
                    {
                        \MBEC (0x01, 0xBF, 0x00)
                    }
                }
            }

            Method (PWRS, 0, NotSerialized)
            {
                If (\H8DR)
                {
                    Store (\_SB.PCI0.ISA.EC.BTPW, Local0)
                }
                Else
                {
                    Store (ShiftRight (And (\RBEC (0x3B), 0x04), 0x02), Local0)
                }

                Return (Local0)
            }

            Method (ATCS, 0, NotSerialized)
            {
                If (\H8DR)
                {
                    Store (\_SB.PCI0.ISA.EC.BTDT, Local0)
                }
                Else
                {
                    Store (ShiftRight (And (\RBEC (0x3B), 0x08), 0x03), Local0)
                }

                XOr (Local0, 0x01, Local0)
                Return (Local0)
            }

            Method (WAKS, 0, NotSerialized)
            {
                If (\H8DR)
                {
                    Store (\_SB.PCI0.ISA.EC.BTWK, Local0)
                }
                Else
                {
                    Store (ShiftRight (And (\RBEC (0x36), 0x02), 0x01), Local0)
                }

                Return (Local0)
            }

            Method (BTAT, 2, NotSerialized)
            {
                Store (0x00, Local0)
                If (LEqual (Arg0, 0x00))
                {
                    If (LEqual (Arg1, 0x01))
                    {
                        If (\H8DR)
                        {
                            Or (\_SB.PCI0.ISA.EC.HAMA, 0x10, \_SB.PCI0.ISA.EC.HAMA)
                        }
                        Else
                        {
                            \MBEC (0x1A, 0xFF, 0x10)
                        }
                    }

                    If (LEqual (Arg1, 0x00))
                    {
                        If (\H8DR)
                        {
                            And (\_SB.PCI0.ISA.EC.HAMA, 0xEF, \_SB.PCI0.ISA.EC.HAMA)
                        }
                        Else
                        {
                            \MBEC (0x1A, 0xEF, 0x00)
                        }
                    }

                    If (LEqual (Arg1, 0x02))
                    {
                        If (\H8DR)
                        {
                            If (And (\_SB.PCI0.ISA.EC.HAMA, 0x10))
                            {
                                Store (0x01, Local0)
                            }
                        }
                        Else
                        {
                            If (And (\RBEC (0x1A), 0x10))
                            {
                                Store (0x01, Local0)
                            }
                        }
                    }
                }

                If (LEqual (Arg0, 0x01))
                {
                    If (LEqual (Arg1, 0x01))
                    {
                        If (\H8DR)
                        {
                            Or (\_SB.PCI0.ISA.EC.HAMA, 0x20, \_SB.PCI0.ISA.EC.HAMA)
                        }
                        Else
                        {
                            \MBEC (0x1A, 0xFF, 0x20)
                        }
                    }

                    If (LEqual (Arg1, 0x00))
                    {
                        If (\H8DR)
                        {
                            And (\_SB.PCI0.ISA.EC.HAMA, 0xDF, \_SB.PCI0.ISA.EC.HAMA)
                        }
                        Else
                        {
                            \MBEC (0x1A, 0xDF, 0x00)
                        }
                    }

                    If (LEqual (Arg1, 0x02))
                    {
                        If (\H8DR)
                        {
                            If (And (\_SB.PCI0.ISA.EC.HAMA, 0x20))
                            {
                                Store (0x01, Local0)
                            }
                        }
                        Else
                        {
                            If (And (\RBEC (0x1A), 0x20))
                            {
                                Store (0x01, Local0)
                            }
                        }
                    }
                }

                Return (Local0)
            }
        }
    }

    Name (\_S0, Package (0x04)
    {
        0x05,
        0x05,
        0x00,
        0x00
    })
    Name (\_S1, Package (0x04)
    {
        0x04,
        0x04,
        0x00,
        0x00
    })
    Name (\_S3, Package (0x04)
    {
        0x01,
        0x01,
        0x00,
        0x00
    })
    Name (\_S4, Package (0x04)
    {
        0x07,
        0x07,
        0x00,
        0x00
    })
    Name (\_S5, Package (0x04)
    {
        0x07,
        0x07,
        0x00,
        0x00
    })
    Method (\_PTS, 1, NotSerialized)
    {
        If (LEqual (Arg0, \SPS))
        {
            Store (0x00, Local0)
        }
        Else
        {
            If (LOr (LEqual (Arg0, 0x00), LNot (LLess (Arg0, 0x06))))
            {
                Store (0x00, Local0)
            }
            Else
            {
                Store (0x01, Local0)
            }
        }

        If (Local0)
        {
            Store (Arg0, \SPS)
            \_SB.PCI0.ISA.EC.HKEY.MHKE (0x00)
            \_SB.PCI0.ISA.EC.EVNT (0x00)
            If (\_SB.PCI0.ISA.EC.KBLT)
            {
                \LGHT (0x00)
            }

            If (LEqual (Arg0, 0x01))
            {
                Store (0x01, \_SB.PCI0.PM00.BLEN)
                Store (0x00, \_SB.PCI0.ISA.EC.HCAC)
                Or (\_SB.PCI0.ISA.ACI, 0x01, \_SB.PCI0.ISA.ACI)
                Store (\_SB.PCI0.ISA.EC.HFNI, \FNID)
                Store (0x00, \_SB.PCI0.ISA.EC.HFNI)
            }

            If (LEqual (Arg0, 0x02))
            {
                Store (One, \_SB.PCI0.PM00.BLEN)
                Store (One, \_SB.PCI0.CREN)
            }

            If (LEqual (Arg0, 0x03))
            {
                \VVPD ()
                Store (One, \_SB.PCI0.PM00.BLEN)
            }

            If (LEqual (Arg0, 0x04))
            {
                \WOLP ()
                \TRAP (0x04, 0x01)
            }

            If (LEqual (Arg0, 0x05))
            {
                \TRAP (0x05, 0x01)
            }

            If (LNot (LEqual (Arg0, 0x05)))
            {
                Store (One, \_SB.PCI0.ISA.EC.HCMU)
                Store (0x00, \_SB.PCI0.ISA.EC.HFSP)
                \_SB.PCI0.DOCK.DPTS (Arg0)
                \_SB.PCI0.ISA.EC.BPTS (Arg0)
            }

            \_SB.PCI0.ISA.EC.HKEY.BTPS (Arg0)
        }
    }

    Name (WAKI, Package (0x02)
    {
        0x00,
        0x00
    })
    Method (\_WAK, 1, NotSerialized)
    {
        If (LOr (LEqual (Arg0, 0x00), LNot (LLess (Arg0, 0x05))))
        {
            Return (WAKI)
        }

        Store (Zero, \SPS)
        Store (Zero, \_SB.PCI0.PM00.BLEN)
        Store (Zero, \_SB.PCI0.CREN)
        Store (Zero, \_SB.PCI0.ISA.EC.HCMU)
        Store (0x80, \_SB.PCI0.ISA.EC.HFSP)
        \_SB.PCI0.ISA.EC.EVNT (0x01)
        \_SB.PCI0.ISA.EC.HKEY.MHKE (0x01)
        If (LEqual (Arg0, 0x01))
        {
            And (\_SB.PCI0.ISA.ACI, 0xFE, \_SB.PCI0.ISA.ACI)
            Store (0x01, \_SB.PCI0.ISA.EC.HCAC)
            Store (\_SB.PCI0.ISA.EC.HFNI, \FNID)
        }

        If (LEqual (Arg0, 0x02)) {}
        If (LEqual (Arg0, 0x03)) {}
        If (LEqual (Arg0, 0x04))
        {
            If (\W98F)
            {
                Notify (\_SB.SLPB, 0x02)
            }

            If (\WMEF)
            {
                \_SB.PCI0.ISA.EC.BEEP (0x05)
            }

            If (LNot (\W98F))
            {
                Store (0x00, \_SB.PCI0.ISA.EC.HSPA)
            }
        }

        \_SB.PCI0.DOCK.DWAK (Arg0)
        \_SB.PCI0.ISA.EC.BWAK (Arg0)
        \_SB.PCI0.ISA.EC.HKEY.BTWK (Arg0)
        Notify (\_TZ.THM0, 0x80)
        \VNRS (0x01)
        \VSLD (\_SB.LID._LID ())
        If (LAnd (\W98F, LNot (\WMEF)))
        {
            Notify (\_SB.PCI0.USB, 0x01)
        }

        If (LLess (Arg0, 0x04))
        {
            If (LOr (And (\_SB.PCI0.ISA.EC.CP4E, 0x02), And (\RRBF, 0x02)))
            {
                ShiftLeft (Arg0, 0x08, Local0)
                Store (Or (0x2013, Local0), Local0)
                \_SB.PCI0.ISA.EC.HKEY.MHKQ (Local0)
            }
        }

        Store (Zero, \RRBF)
        Return (WAKI)
    }

    Scope (\_SI)
    {
        Method (_SST, 1, NotSerialized)
        {
            If (LEqual (Arg0, 0x00))
            {
                \_SB.PCI0.ISA.EC.SYSL (0x00, 0x00)
                \_SB.PCI0.ISA.EC.SYSL (0x01, 0x00)
            }

            If (LEqual (Arg0, 0x01))
            {
                If (LOr (\SPS, \WNTF))
                {
                    \_SB.PCI0.ISA.EC.BEEP (0x05)
                }

                \_SB.PCI0.ISA.EC.SYSL (0x00, 0x01)
                \_SB.PCI0.ISA.EC.SYSL (0x01, 0x00)
            }

            If (LEqual (Arg0, 0x02))
            {
                \_SB.PCI0.ISA.EC.SYSL (0x00, 0x01)
                \_SB.PCI0.ISA.EC.SYSL (0x01, 0x02)
            }

            If (LEqual (Arg0, 0x03))
            {
                If (LGreater (\SPS, 0x03))
                {
                    \_SB.PCI0.ISA.EC.BEEP (0x07)
                }
                Else
                {
                    If (LEqual (\SPS, 0x03))
                    {
                        \_SB.PCI0.ISA.EC.BEEP (0x03)
                    }
                    Else
                    {
                        \_SB.PCI0.ISA.EC.BEEP (0x04)
                    }
                }

                If (LEqual (\SPS, 0x03))
                {
                    \_SB.PCI0.ISA.EC.SYSL (0x00, 0x00)
                }
                Else
                {
                    \_SB.PCI0.ISA.EC.SYSL (0x00, 0x01)
                }

                \_SB.PCI0.ISA.EC.SYSL (0x01, 0x01)
            }

            If (LEqual (Arg0, 0x04))
            {
                \_SB.PCI0.ISA.EC.BEEP (0x03)
                \_SB.PCI0.ISA.EC.SYSL (0x01, 0x02)
            }
        }
    }

    Scope (\_GPE)
    {
        Method (_L0B, 0, NotSerialized)
        {
            Store (\_SB.PCI0.ISA.EC.HWAK, Local0)
            Sleep (0x0A)
            Store (Local0, \RRBF)
            If (And (Local0, 0x01))
            {
                If (And (\_SB.PCI0.PMEE, 0x01))
                {
                    Notify (\_SB.PCI0, 0x02)
                }

                If (And (\_SB.PCI0.PMEE, 0x02))
                {
                    Notify (\_SB.PCI0.DOCK, 0x02)
                }
            }

            If (And (Local0, 0x02)) {}
            If (And (Local0, 0x04))
            {
                If (\W98F)
                {
                    Notify (\_SB.SLPB, 0x02)
                }
                Else
                {
                    Notify (\_SB.LID, 0x02)
                }
            }

            If (And (Local0, 0x08))
            {
                \_SB.PCI0.DOCK.DGPE ()
                Notify (\_SB.SLPB, 0x02)
            }

            If (And (Local0, 0x10))
            {
                Notify (\_SB.SLPB, 0x02)
            }

            If (And (Local0, 0x40))
            {
                Notify (\_SB.PCI0.ISA.UART, 0x02)
            }

            If (And (Local0, 0x80))
            {
                Notify (\_SB.SLPB, 0x02)
            }
        }
    }

    Scope (\_TZ)
    {
        ThermalZone (THM0)
        {
            Name (_CRT, 0x0E76)
            Name (_PSL, Package (0x01)
            {
                \_PR.CPU
            })
            Name (_PSV, 0x0E3F)
            Name (_TC1, 0x05)
            Name (_TC2, 0x02)
            Name (_TSP, 0x0258)
            Method (_TMP, 0, NotSerialized)
            {
                If (\H8DR)
                {
                    Store (\_SB.PCI0.ISA.EC.TMP0, Local0)
                }
                Else
                {
                    Store (\RBEC (0x78), Local0)
                }

                Return (C2K (Local0))
            }
        }

        Method (C2K, 1, NotSerialized)
        {
            Add (Multiply (Arg0, 0x0A), 0x0AAC, Local0)
            If (LNot (LGreater (Local0, 0x0AAC)))
            {
                Store (0x0BB8, Local0)
            }

            If (LNot (LLess (Local0, 0x0FAC)))
            {
                Store (0x0BB8, Local0)
            }

            Return (Local0)
        }
    }

    Scope (\_SB.PCI0.ISA.EC)
    {
        Method (_Q40, 0, NotSerialized)
        {
            Notify (\_TZ.THM0, 0x80)
        }
    }

    OperationRegion (MNVS, SystemMemory, 0x0FFFF000, 0x1000)
    Field (MNVS, DWordAcc, NoLock, Preserve)
    {
        Offset (0xF00),
        HDHD,   8,
        HDSE,   8,
        Offset (0xF03),
        Offset (0xF04),
        Offset (0xF08),
        Offset (0xF0C),
        Offset (0xF10),
        VCDL,   1,
        VCDC,   1,
        VCDT,   1,
        VCDD,   1,
            ,   1,
        VCSS,   1,
        VCDB,   1,
        VCIN,   1,
        Offset (0xF12),
        VLID,   4,
        Offset (0xF14)
    }

    Field (MNVS, ByteAcc, NoLock, Preserve)
    {
        Offset (0xE00),
        DDC1,   1024,
        Offset (0xF00)
    }

    Field (MNVS, ByteAcc, NoLock, Preserve)
    {
        Offset (0xE00),
        DDC2,   2048
    }

    OperationRegion (SMI0, SystemIO, 0xFE00, 0x02)
    Field (SMI0, ByteAcc, NoLock, Preserve)
    {
        APMC,   8
    }

    Field (MNVS, AnyAcc, NoLock, Preserve)
    {
        Offset (0xFC0),
        CMD,    8,
        ERR,    32,
        PAR0,   32,
        PAR1,   32,
        PAR2,   32,
        PAR3,   32
    }

    Mutex (MSMI, 0x07)
    Method (SMI, 5, NotSerialized)
    {
        Acquire (MSMI, 0xFFFF)
        Store (Arg0, CMD)
        Store (Arg1, PAR0)
        Store (Arg2, PAR1)
        Store (Arg3, PAR2)
        Store (Arg4, PAR3)
        Store (0x00, APMC)
        While (LEqual (ERR, 0x01))
        {
            Sleep (0x64)
            Store (0x00, APMC)
        }

        Store (PAR0, Local0)
        Release (MSMI)
        Return (Local0)
    }

    Method (RPCI, 1, NotSerialized)
    {
        Return (SMI (0x80, 0x00, Arg0, 0x00, 0x00))
    }

    Method (WPCI, 2, NotSerialized)
    {
        SMI (0x80, 0x01, Arg0, Arg1, 0x00)
    }

    Method (MPCI, 3, NotSerialized)
    {
        SMI (0x80, 0x02, Arg0, Arg1, Arg2)
    }

    Method (RBEC, 1, NotSerialized)
    {
        Return (SMI (0x81, 0x00, Arg0, 0x00, 0x00))
    }

    Method (WBEC, 2, NotSerialized)
    {
        SMI (0x81, 0x01, Arg0, Arg1, 0x00)
    }

    Method (MBEC, 3, NotSerialized)
    {
        SMI (0x81, 0x02, Arg0, Arg1, Arg2)
    }

    Method (TRAP, 2, NotSerialized)
    {
        SMI (0x82, Arg0, Arg1, 0x00, 0x00)
    }

    Method (FERR, 0, NotSerialized)
    {
        SMI (0x83, 0x00, 0x00, 0x00, 0x00)
    }

    Method (GFDD, 0, NotSerialized)
    {
        Return (SMI (0x84, 0x00, 0x00, 0x00, 0x00))
    }

    Method (SFDD, 1, NotSerialized)
    {
        SMI (0x84, 0x01, Arg0, 0x00, 0x00)
    }

    Method (DHDP, 1, NotSerialized)
    {
        Return (SMI (0x85, Arg0, 0x00, 0x00, 0x00))
    }

    Method (VOLU, 0, NotSerialized)
    {
        SMI (0x86, 0x00, 0x00, 0x00, 0x00)
    }

    Method (VOLD, 0, NotSerialized)
    {
        SMI (0x86, 0x01, 0x00, 0x00, 0x00)
    }

    Method (VOLM, 0, NotSerialized)
    {
        SMI (0x86, 0x02, 0x00, 0x00, 0x00)
    }

    Method (TPKY, 0, NotSerialized)
    {
        SMI (0x86, 0x03, 0x00, 0x00, 0x00)
    }

    Method (BRIU, 0, NotSerialized)
    {
        SMI (0x86, 0x04, 0x00, 0x00, 0x00)
    }

    Method (BRID, 0, NotSerialized)
    {
        SMI (0x86, 0x05, 0x00, 0x00, 0x00)
    }

    Method (SNMB, 0, NotSerialized)
    {
        SMI (0x86, 0x06, 0x00, 0x00, 0x00)
    }

    Method (SMUT, 0, NotSerialized)
    {
        SMI (0x86, 0x07, 0x00, 0x00, 0x00)
    }

    Method (ESYB, 1, NotSerialized)
    {
        If (LEqual (Arg0, 0x00))
        {
            SMI (0x86, 0x03, 0x00, 0x00, 0x00)
        }
        Else
        {
            SMI (0x86, 0x08, Decrement (Arg0), 0x00, 0x00)
        }
    }

    Method (DSEP, 0, NotSerialized)
    {
        SMI (0x86, 0x09, 0x00, 0x00, 0x00)
    }

    Method (VEXP, 0, NotSerialized)
    {
        SMI (0x87, 0x00, 0x00, 0x00, 0x00)
    }

    Method (VUPS, 1, NotSerialized)
    {
        SMI (0x88, Arg0, 0x00, 0x00, 0x00)
    }

    Method (VSDS, 2, NotSerialized)
    {
        SMI (0x89, Arg0, Arg1, 0x00, 0x00)
    }

    Method (VDDC, 0, NotSerialized)
    {
        SMI (0x8A, 0x00, 0x00, 0x00, 0x00)
    }

    Method (VVPD, 0, NotSerialized)
    {
        SMI (0x94, 0x00, 0x00, 0x00, 0x00)
    }

    Method (GVIL, 1, NotSerialized)
    {
        SMI (0x8B, Arg0, 0x00, 0x00, 0x00)
    }

    Method (GCHK, 0, NotSerialized)
    {
        Return (SMI (0x8B, 0x06, 0x00, 0x00, 0x00))
    }

    Method (LGHT, 1, NotSerialized)
    {
        SMI (0x8C, Arg0, 0x00, 0x00, 0x00)
    }

    Method (GPAR, 0, NotSerialized)
    {
        Return (SMI (0x8D, 0x00, 0x00, 0x00, 0x00))
    }

    Method (GDCK, 1, NotSerialized)
    {
        \_SB.PCI0.ISA.EC.AI2C ()
        Store (SMI (0x8E, Arg0, 0x00, 0x00, 0x00), Local0)
        \_SB.PCI0.ISA.EC.RI2C ()
        Return (Local0)
    }

    Method (GGAP, 1, NotSerialized)
    {
        Return (SMI (0x8F, Arg0, 0x00, 0x00, 0x00))
    }

    Method (GHKY, 0, NotSerialized)
    {
        Store (SMI (0x90, 0x00, 0x00, 0x00, 0x00), Local0)
        Return (And (ShiftRight (Local0, 0x04), 0x01))
    }

    Method (GCDT, 1, NotSerialized)
    {
        Return (SMI (0x91, Arg0, 0x00, 0x00, 0x00))
    }

    Method (GBTH, 1, NotSerialized)
    {
        Return (SMI (0x92, Arg0, 0x00, 0x00, 0x00))
    }

    Method (BHDP, 1, NotSerialized)
    {
        Return (SMI (0x93, Arg0, 0x00, 0x00, 0x00))
    }

    Method (VNRS, 1, NotSerialized)
    {
        Return (SMI (0x95, Arg0, 0x00, 0x00, 0x00))
    }

    Method (GLPW, 0, NotSerialized)
    {
        Return (SMI (0x96, 0x00, 0x00, 0x00, 0x00))
    }

    Method (GTPS, 0, NotSerialized)
    {
        Return (SMI (0x97, 0x00, 0x00, 0x00, 0x00))
    }

    Method (VSLD, 1, NotSerialized)
    {
        Return (SMI (0x99, Arg0, 0x00, 0x00, 0x00))
    }

    Method (CBRI, 0, NotSerialized)
    {
        SMI (0x9A, 0x00, 0x00, 0x00, 0x00)
    }

    Method (WOLP, 0, NotSerialized)
    {
        SMI (0x9B, 0x00, 0x00, 0x00, 0x00)
    }

    Method (ECPP, 0, NotSerialized)
    {
        SMI (0x9C, 0x00, 0x00, 0x00, 0x00)
    }

    Scope (\_SB.PCI0.PM00)
    {
        OperationRegion (GPOR, SystemIO, 0x1034, 0x04)
        Field (GPOR, ByteAcc, NoLock, Preserve)
        {
                ,   1,
            Offset (0x01),
            MSON,   1,
                ,   1,
            URST,   1,
            EID2,   1,
            EID,    2,
            CSON,   1,
                ,   4,
            IPDR,   1,
                ,   1,
            S2DS,   1,
                ,   1,
            ULON,   1,
                ,   7
        }
    }

    Name (ICM0, Buffer (0x1C)
    {
        0x02, 0x00, 0x00, 0x00, 0x00, 0xA0, 0xEF, 0x00,
        0x00, 0x00, 0x00, 0x00, 0xA0, 0xF5, 0x03, 0x00,
        0x00, 0x00, 0x00, 0xA0, 0xEF, 0x03, 0x00, 0x00,
        0x00, 0x00, 0xA0, 0xEF
    })
    CreateByteField (ICM0, 0x0F, HDM0)
    CreateByteField (ICM0, 0x16, HPI0)
    Name (ICM1, Buffer (0x1C)
    {
        0x02, 0x00, 0x00, 0x00, 0x00, 0xB0, 0xEF, 0x00,
        0x00, 0x00, 0x00, 0x00, 0xB0, 0xF5, 0x03, 0x00,
        0x00, 0x00, 0x00, 0xB0, 0xEF, 0x03, 0x00, 0x00,
        0x00, 0x00, 0xB0, 0xEF
    })
    CreateByteField (ICM1, 0x0F, HDM1)
    CreateByteField (ICM1, 0x16, HPI1)
    Name (ICC1, Buffer (0x0E)
    {
        0x03, 0x00, 0x00, 0x00, 0x00, 0xB0, 0xEF, 0x03,
        0x00, 0x00, 0x00, 0x00, 0xB0, 0xEF
    })
    CreateByteField (ICC1, 0x01, CDM1)
    CreateByteField (ICC1, 0x08, CPI1)
    Name (IDKM, 0x00)
    Name (ICM2, Buffer (0x1C)
    {
        0x02, 0x00, 0x00, 0x00, 0x00, 0xA0, 0xEF, 0x00,
        0x00, 0x00, 0x00, 0x00, 0xA0, 0xF5, 0x03, 0x00,
        0x00, 0x00, 0x00, 0xA0, 0xEF, 0x03, 0x00, 0x00,
        0x00, 0x00, 0xA0, 0xEF
    })
    CreateByteField (ICM2, 0x0F, HDM2)
    CreateByteField (ICM2, 0x16, HPI2)
    Name (ICC2, Buffer (0x0E)
    {
        0x03, 0x00, 0x00, 0x00, 0x00, 0xA0, 0xEF, 0x03,
        0x00, 0x00, 0x00, 0x00, 0xA0, 0xEF
    })
    CreateByteField (ICC2, 0x01, CDM2)
    CreateByteField (ICC2, 0x08, CPI2)
    Name (DCM2, Buffer (0x1C)
    {
        0x03, 0x00, 0x00, 0x00, 0x00, 0xA0, 0xEF, 0x03,
        0x00, 0x00, 0x00, 0x00, 0xA0, 0xEF, 0x00, 0x00,
        0x00, 0x00, 0x00, 0xA0, 0xE3, 0x00, 0x00, 0x00,
        0x00, 0x00, 0xA0, 0xE3
    })
    CreateByteField (DCM2, 0x01, DDM2)
    CreateByteField (DCM2, 0x08, DPI2)
    CreateByteField (DCM2, 0x0F, DTA2)
    CreateByteField (DCM2, 0x16, DTF2)
    Name (IDKS, 0x00)
    Name (ICM3, Buffer (0x1C)
    {
        0x02, 0x00, 0x00, 0x00, 0x00, 0xA0, 0xEF, 0x00,
        0x00, 0x00, 0x00, 0x00, 0xA0, 0xF5, 0x03, 0x00,
        0x00, 0x00, 0x00, 0xA0, 0xEF, 0x03, 0x00, 0x00,
        0x00, 0x00, 0xA0, 0xEF
    })
    CreateByteField (ICM3, 0x0F, HDM3)
    CreateByteField (ICM3, 0x16, HPI3)
    Name (ICC3, Buffer (0x0E)
    {
        0x03, 0x00, 0x00, 0x00, 0x00, 0xA0, 0xEF, 0x03,
        0x00, 0x00, 0x00, 0x00, 0xA0, 0xEF
    })
    CreateByteField (ICC3, 0x01, CDM3)
    CreateByteField (ICC3, 0x08, CPI3)
    Name (BGTM, Buffer (0x14) {})
    CreateDWordField (BGTM, 0x00, GTP0)
    CreateDWordField (BGTM, 0x04, GTD0)
    CreateDWordField (BGTM, 0x08, GTP1)
    CreateDWordField (BGTM, 0x0C, GTD1)
    CreateDWordField (BGTM, 0x10, GTMF)
    Method (UDMA, 2, NotSerialized)
    {
        If (And (Arg0, 0x04))
        {
            If (And (Arg1, 0x10))
            {
                Return (0x05)
            }
            Else
            {
                If (And (Arg1, 0x08))
                {
                    Return (0x04)
                }
                Else
                {
                    If (And (Arg1, 0x04))
                    {
                        Return (0x03)
                    }
                    Else
                    {
                        If (And (Arg1, 0x02))
                        {
                            Return (0x02)
                        }
                        Else
                        {
                            If (And (Arg1, 0x01))
                            {
                                Return (0x01)
                            }
                            Else
                            {
                                Return (0x00)
                            }
                        }
                    }
                }
            }
        }
        Else
        {
            Return (0x00)
        }
    }

    Method (UDMB, 2, NotSerialized)
    {
        If (Arg0)
        {
            If (LGreater (Arg1, 0x1E))
            {
                If (LGreater (Arg1, 0x2D))
                {
                    If (LGreater (Arg1, 0x3C))
                    {
                        If (LGreater (Arg1, 0x50))
                        {
                            Return (0x01)
                        }
                        Else
                        {
                            Return (0x02)
                        }
                    }
                    Else
                    {
                        Return (0x03)
                    }
                }
                Else
                {
                    Return (0x04)
                }
            }
            Else
            {
                Return (0x05)
            }
        }
        Else
        {
            Return (0x00)
        }
    }

    Method (MDMA, 4, NotSerialized)
    {
        If (And (Arg0, 0x02))
        {
            If (And (Arg1, 0x04))
            {
                If (LNot (LGreater (Arg3, 0x78)))
                {
                    Return (0x03)
                }
                Else
                {
                    If (LNot (LGreater (Arg3, 0xB4)))
                    {
                        Return (0x02)
                    }
                    Else
                    {
                        If (LNot (LGreater (Arg3, 0xF0)))
                        {
                            Return (0x01)
                        }
                        Else
                        {
                            Return (0x00)
                        }
                    }
                }
            }
            Else
            {
                If (And (Arg1, 0x02))
                {
                    If (LNot (LGreater (Arg3, 0xB4)))
                    {
                        Return (0x02)
                    }
                    Else
                    {
                        If (LNot (LGreater (Arg3, 0xF0)))
                        {
                            Return (0x01)
                        }
                        Else
                        {
                            Return (0x00)
                        }
                    }
                }
                Else
                {
                    If (And (Arg2, 0x04))
                    {
                        If (LNot (LGreater (Arg3, 0xF0)))
                        {
                            Return (0x01)
                        }
                        Else
                        {
                            Return (0x00)
                        }
                    }
                    Else
                    {
                        Return (0x00)
                    }
                }
            }
        }
        Else
        {
            Return (0x00)
        }
    }

    Method (MDMB, 1, NotSerialized)
    {
        If (LGreater (Arg0, 0x78))
        {
            If (LGreater (Arg0, 0x96))
            {
                Return (0x01)
            }
            Else
            {
                Return (0x02)
            }
        }
        Else
        {
            Return (0x03)
        }
    }

    Method (MPIO, 4, NotSerialized)
    {
        If (And (Arg0, 0x02))
        {
            If (And (Arg1, 0x02))
            {
                If (LNot (LGreater (Arg3, 0x78)))
                {
                    Return (0x04)
                }
                Else
                {
                    If (LNot (LGreater (Arg3, 0xB4)))
                    {
                        Return (0x03)
                    }
                    Else
                    {
                        If (LNot (LGreater (Arg3, 0xF0)))
                        {
                            Return (0x02)
                        }
                        Else
                        {
                            Return (0x00)
                        }
                    }
                }
            }
            Else
            {
                If (And (Arg1, 0x01))
                {
                    If (LNot (LGreater (Arg3, 0xB4)))
                    {
                        Return (0x03)
                    }
                    Else
                    {
                        If (LNot (LGreater (Arg3, 0xF0)))
                        {
                            Return (0x02)
                        }
                        Else
                        {
                            Return (0x00)
                        }
                    }
                }
                Else
                {
                    If (LEqual (Arg2, 0x02))
                    {
                        Return (0x01)
                    }
                    Else
                    {
                        Return (0x00)
                    }
                }
            }
        }
        Else
        {
            If (LEqual (Arg2, 0x02))
            {
                Return (0x01)
            }
            Else
            {
                Return (0x00)
            }
        }
    }

    Method (MPIB, 2, NotSerialized)
    {
        If (LGreater (Arg1, 0x78))
        {
            If (LGreater (Arg1, 0xB4))
            {
                If (LGreater (Arg1, 0xF0))
                {
                    Return (0x00)
                }
                Else
                {
                    If (Arg0)
                    {
                        Return (0x02)
                    }
                    Else
                    {
                        Return (0x01)
                    }
                }
            }
            Else
            {
                Return (0x03)
            }
        }
        Else
        {
            Return (0x04)
        }
    }

    Method (MPI4, 2, NotSerialized)
    {
        If (Arg0)
        {
            If (LEqual (Arg0, 0x01))
            {
                Return (0x01)
            }
            Else
            {
                If (LEqual (Arg0, 0x02))
                {
                    Return (0x02)
                }
                Else
                {
                    If (LEqual (Arg1, 0x03))
                    {
                        Return (0x02)
                    }
                    Else
                    {
                        Return (0x03)
                    }
                }
            }
        }
        Else
        {
            If (LLess (Arg1, 0x02))
            {
                Return (Arg1)
            }
            Else
            {
                Return (Decrement (Arg1))
            }
        }
    }

    Method (MP4B, 1, NotSerialized)
    {
        If (LNot (LGreater (Arg0, 0x01)))
        {
            Return (Arg0)
        }
        Else
        {
            Return (Decrement (Arg0))
        }
    }

    Method (MTIM, 3, NotSerialized)
    {
        If (LEqual (Arg0, 0x00))
        {
            Store (0x00, Local5)
        }
        Else
        {
            If (LEqual (Arg0, 0x01))
            {
                If (LLess (Arg1, 0x02))
                {
                    Store (0x01, Local5)
                }
                Else
                {
                    Store (0x03, Local5)
                }
            }
            Else
            {
                If (LEqual (Arg0, 0x02))
                {
                    Store (0x03, Local5)
                }
                Else
                {
                    Store (0x03, Local5)
                }
            }

            If (LEqual (Arg1, 0x00))
            {
                Or (Local5, 0x08, Local5)
            }
        }

        If (Arg2)
        {
            And (Local5, 0xFB, Local5)
        }
        Else
        {
            Or (Local5, 0x04, Local5)
        }

        Return (Local5)
    }

    Method (MISP, 1, NotSerialized)
    {
        If (LEqual (Arg0, 0x00))
        {
            Return (0x00)
        }
        Else
        {
            If (LEqual (Arg0, 0x01))
            {
                Return (0x01)
            }
            Else
            {
                If (LEqual (Arg0, 0x02))
                {
                    Return (0x02)
                }
                Else
                {
                    Return (0x02)
                }
            }
        }
    }

    Method (MRTC, 1, NotSerialized)
    {
        If (LEqual (Arg0, 0x00))
        {
            Return (0x00)
        }
        Else
        {
            If (LEqual (Arg0, 0x01))
            {
                Return (0x00)
            }
            Else
            {
                If (LEqual (Arg0, 0x02))
                {
                    Return (0x01)
                }
                Else
                {
                    Return (0x03)
                }
            }
        }
    }

    Method (MUCT, 1, NotSerialized)
    {
        If (LEqual (Arg0, 0x00))
        {
            Return (0x00)
        }
        Else
        {
            If (LEqual (Arg0, 0x01))
            {
                Return (0x00)
            }
            Else
            {
                If (LEqual (Arg0, 0x02))
                {
                    Return (0x01)
                }
                Else
                {
                    Return (0x02)
                }
            }
        }
    }

    Method (CART, 1, NotSerialized)
    {
        If (LEqual (Arg0, 0x00))
        {
            Return (0x02)
        }
        Else
        {
            Return (0x01)
        }
    }

    Method (CCMD, 1, NotSerialized)
    {
        If (LEqual (Arg0, 0x04))
        {
            Return (0x3F)
        }
        Else
        {
            If (LEqual (Arg0, 0x03))
            {
                Return (0x32)
            }
            Else
            {
                If (LEqual (Arg0, 0x02))
                {
                    Return (0xAF)
                }
                Else
                {
                    If (LEqual (Arg0, 0x01))
                    {
                        Return (0xA2)
                    }
                    Else
                    {
                        Return (0xA9)
                    }
                }
            }
        }
    }

    Method (CDRW, 2, NotSerialized)
    {
        If (LEqual (Arg0, 0x01))
        {
            Store (0x88, Local0)
        }
        Else
        {
            If (LEqual (Arg0, 0x02))
            {
                Store (0x31, Local0)
            }
            Else
            {
                If (LEqual (Arg0, 0x03))
                {
                    Store (0x3F, Local0)
                }
                Else
                {
                    Store (0xFFFFFFFF, Local0)
                }
            }
        }

        If (LEqual (Arg1, 0x00))
        {
            Store (0x6D, Local1)
        }
        Else
        {
            If (LEqual (Arg1, 0x01))
            {
                Store (0x43, Local1)
            }
            Else
            {
                If (LEqual (Arg1, 0x02))
                {
                    Store (0x43, Local1)
                }
                Else
                {
                    If (LEqual (Arg1, 0x03))
                    {
                        Store (0x32, Local1)
                    }
                    Else
                    {
                        Store (0x3F, Local1)
                    }
                }
            }
        }

        If (LGreater (CCYC (Local0), CCYC (Local1)))
        {
            Return (Local0)
        }
        Else
        {
            Return (Local1)
        }
    }

    Method (CCYC, 1, NotSerialized)
    {
        And (Arg0, 0x0F, Local0)
        ShiftRight (Arg0, 0x04, Local1)
        If (Local0)
        {
            If (LEqual (Local0, 0x0F))
            {
                Store (0x01, Local0)
            }
            Else
            {
                Increment (Local0)
            }
        }
        Else
        {
            Store (0x10, Local0)
        }

        If (LNot (Local1))
        {
            Store (0x10, Local1)
        }

        Add (Local0, Local1, Local0)
        Multiply (Local0, 0x1E, Local0)
        Return (Local0)
    }

    Method (CUDC, 1, NotSerialized)
    {
        If (LEqual (Arg0, 0x01))
        {
            Return (0x03)
        }
        Else
        {
            If (LEqual (Arg0, 0x02))
            {
                Return (0x02)
            }
            Else
            {
                If (LEqual (Arg0, 0x03))
                {
                    Return (0x01)
                }
                Else
                {
                    If (LEqual (Arg0, 0x04))
                    {
                        Return (0x02)
                    }
                    Else
                    {
                        Return (0x01)
                    }
                }
            }
        }
    }

    Method (MHDM, 2, NotSerialized)
    {
        If (LEqual (Arg0, 0x00))
        {
            If (LEqual (Arg1, 0x00))
            {
                Return (0x00)
            }
            Else
            {
                If (LEqual (Arg1, 0x01))
                {
                    Return (0x12)
                }
                Else
                {
                    If (LEqual (Arg1, 0x02))
                    {
                        Return (0x21)
                    }
                    Else
                    {
                        Return (0x22)
                    }
                }
            }
        }
        Else
        {
            If (LEqual (Arg0, 0x01))
            {
                Return (0x40)
            }
            Else
            {
                If (LEqual (Arg0, 0x02))
                {
                    Return (0x41)
                }
                Else
                {
                    If (LEqual (Arg0, 0x03))
                    {
                        Return (0x42)
                    }
                    Else
                    {
                        If (LEqual (Arg0, 0x04))
                        {
                            Return (0x43)
                        }
                        Else
                        {
                            Return (0x44)
                        }
                    }
                }
            }
        }
    }

    Method (MHPI, 1, NotSerialized)
    {
        If (LEqual (Arg0, 0x00))
        {
            Return (0x00)
        }
        Else
        {
            If (LEqual (Arg0, 0x01))
            {
                Return (0x01)
            }
            Else
            {
                If (LEqual (Arg0, 0x02))
                {
                    Return (0x00)
                }
                Else
                {
                    If (LEqual (Arg0, 0x03))
                    {
                        Return (0x0B)
                    }
                    Else
                    {
                        Return (0x0C)
                    }
                }
            }
        }
    }

    Method (MIN, 2, NotSerialized)
    {
        If (LLess (Arg0, Arg1))
        {
            Return (Arg0)
        }
        Else
        {
            Return (Arg1)
        }
    }

    Method (SLEN, 1, NotSerialized)
    {
        Return (SizeOf (Arg0))
    }

    Method (S2BF, 1, Serialized)
    {
        Add (SLEN (Arg0), One, Local0)
        Name (BUFF, Buffer (Local0) {})
        Store (Arg0, BUFF)
        Return (BUFF)
    }

    Method (SCMP, 2, NotSerialized)
    {
        Store (S2BF (Arg0), Local0)
        Store (S2BF (Arg1), Local1)
        Store (Zero, Local4)
        Store (SLEN (Arg0), Local5)
        Store (SLEN (Arg1), Local6)
        Store (MIN (Local5, Local6), Local7)
        While (LLess (Local4, Local7))
        {
            Store (DerefOf (Index (Local0, Local4)), Local2)
            Store (DerefOf (Index (Local1, Local4)), Local3)
            If (LGreater (Local2, Local3))
            {
                Return (One)
            }
            Else
            {
                If (LLess (Local2, Local3))
                {
                    Return (Ones)
                }
            }

            Increment (Local4)
        }

        If (LLess (Local4, Local5))
        {
            Return (One)
        }
        Else
        {
            If (LLess (Local4, Local6))
            {
                Return (Ones)
            }
            Else
            {
                Return (Zero)
            }
        }
    }

    Name (SPS, 0x00)
    Name (W98F, 0x00)
    Name (WNTF, 0x00)
    Name (WMEF, 0x00)
    Name (H8DR, 0x00)
    Name (MEMX, 0x00)
    Name (GVEN, 0x00)
    Name (FNID, 0x00)
    Name (RRBF, 0x00)
}
