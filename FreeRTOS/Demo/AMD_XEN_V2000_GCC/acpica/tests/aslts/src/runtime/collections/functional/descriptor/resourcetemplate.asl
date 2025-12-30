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
     * Resource Descriptor macros
     *
     * Resource To Buffer Conversion Macro
     */
    Name (P438, Package (0x03)
    {
        Buffer (0x02)
        {
             0x79, 0x00                                       // y.
        },

        ResourceTemplate ()
        {
            IRQ (Level, ActiveHigh, Exclusive, )
                {0}
            IRQNoFlags ()
                {1}
            DMA (Compatibility, NotBusMaster, Transfer16, )
                {2}
            IO (Decode16,
                0xF0F1,             // Range Minimum
                0xF2F3,             // Range Maximum
                0xF4,               // Alignment
                0xF5,               // Length
                )
            FixedIO (
                0x03F1,             // Address
                0xF2,               // Length
                )
            VendorShort ()      // Length = 0x07
            {
                 0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
            }
            Memory24 (ReadWrite,
                0xF0F1,             // Range Minimum
                0xF2F3,             // Range Maximum
                0xF4F5,             // Alignment
                0xF6F7,             // Length
                )
            Memory32 (ReadWrite,
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Alignment
                0xFCFDFEFF,         // Length
                )
            Memory32Fixed (ReadOnly,
                0xF0F1F2F3,         // Address Base
                0xF4F5F6F7,         // Address Length
                )
            VendorLong  ()      // Length = 0x15
            {
                /* 0000 */  0x9F, 0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6,  // ........
                /* 0008 */  0xF7, 0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE,  // ........
                /* 0010 */  0xFF, 0x00, 0x01, 0x02, 0x03                     // .....
            }
            QWordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
            DWordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
            WordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0xF6F7,             // Granularity
                0xF8F9,             // Range Minimum
                0xFAFB,             // Range Maximum
                0xFCFD,             // Translation Offset
                0xFEFF,             // Length
                0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
            QWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                0xFF, "PATHPATHPATH", , AddressRangeACPI, TypeTranslation)
            DWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                0xFF, "PATHPATHPATH", , AddressRangeACPI, TypeTranslation)
            WordBusNumber (ResourceConsumer, MinFixed, MaxFixed, SubDecode,
                0xF6F7,             // Granularity
                0xF8F9,             // Range Minimum
                0xFAFB,             // Range Maximum
                0xFCFD,             // Translation Offset
                0xFEFF,             // Length
                0xFF, "PATHPATHPATH", )
            Interrupt (ResourceConsumer, Edge, ActiveLow, Shared, 0xFF, "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*", )
            {
                0x00000001,
                0x00000002,
                0x00000003,
                0x00000004,
                0x00000005,
                0x00000006,
                0x00000007,
                0x00000008,
                0x00000009,
                0x0000000A,
                0x0000000B,
                0x0000000C,
                0x0000000D,
                0x0000000E,
                0x0000000F,
                0x00000010,
                0x00000011,
                0x00000012,
                0x00000013,
                0x00000014,
                0x00000015,
                0x00000016,
                0x00000017,
                0x00000018,
                0x00000019,
                0x0000001A,
                0x0000001B,
                0x0000001C,
                0x0000001D,
                0x0000001E,
                0x0000001F,
                0x00000020,
                0x00000021,
                0x00000022,
                0x00000023,
                0x00000024,
                0x00000025,
                0x00000026,
                0x00000027,
                0x00000028,
                0x00000029,
                0x0000002A,
                0x0000002B,
                0x0000002C,
                0x0000002D,
                0x0000002E,
                0x0000002F,
                0x00000030,
                0x00000031,
                0x00000032,
                0x00000033,
                0x00000034,
                0x00000035,
                0x00000036,
                0x00000037,
                0x00000038,
                0x00000039,
                0x0000003A,
                0x0000003B,
                0x0000003C,
                0x0000003D,
                0x0000003E,
                0x0000003F,
                0x00000040,
                0x00000041,
                0x00000042,
                0x00000043,
                0x00000044,
                0x00000045,
                0x00000046,
                0x00000047,
                0x00000048,
                0x00000049,
                0x0000004A,
                0x0000004B,
                0x0000004C,
                0x0000004D,
                0x0000004E,
                0x0000004F,
                0x00000050,
                0x00000051,
                0x00000052,
                0x00000053,
                0x00000054,
                0x00000055,
                0x00000056,
                0x00000057,
                0x00000058,
                0x00000059,
                0x0000005A,
                0x0000005B,
                0x0000005C,
                0x0000005D,
                0x0000005E,
                0x0000005F,
                0x00000060,
                0x00000061,
                0x00000062,
                0x00000063,
                0x00000064,
                0x00000065,
                0x00000066,
                0x00000067,
                0x00000068,
                0x00000069,
                0x0000006A,
                0x0000006B,
                0x0000006C,
                0x0000006D,
                0x0000006E,
                0x0000006F,
                0x00000070,
                0x00000071,
                0x00000072,
                0x00000073,
                0x00000074,
                0x00000075,
                0x00000076,
                0x00000077,
                0x00000078,
                0x00000079,
                0x0000007A,
                0x0000007B,
                0x0000007C,
                0x0000007D,
                0x0000007E,
                0x0000007F,
                0x00000080,
                0x00000081,
                0x00000082,
                0x00000083,
                0x00000084,
                0x00000085,
                0x00000086,
                0x00000087,
                0x00000088,
                0x00000089,
                0x0000008A,
                0x0000008B,
                0x0000008C,
                0x0000008D,
                0x0000008E,
                0x0000008F,
                0x00000090,
                0x00000091,
                0x00000092,
                0x00000093,
                0x00000094,
                0x00000095,
                0x00000096,
                0x00000097,
                0x00000098,
                0x00000099,
                0x0000009A,
                0x0000009B,
                0x0000009C,
                0x0000009D,
                0x0000009E,
                0x0000009F,
                0x000000A0,
                0x000000A1,
                0x000000A2,
                0x000000A3,
                0x000000A4,
                0x000000A5,
                0x000000A6,
                0x000000A7,
                0x000000A8,
                0x000000A9,
                0x000000AA,
                0x000000AB,
                0x000000AC,
                0x000000AD,
                0x000000AE,
                0x000000AF,
                0x000000B0,
                0x000000B1,
                0x000000B2,
                0x000000B3,
                0x000000B4,
                0x000000B5,
                0x000000B6,
                0x000000B7,
                0x000000B8,
                0x000000B9,
                0x000000BA,
                0x000000BB,
                0x000000BC,
                0x000000BD,
                0x000000BE,
                0x000000BF,
                0x000000C0,
                0x000000C1,
                0x000000C2,
                0x000000C3,
                0x000000C4,
                0x000000C5,
                0x000000C6,
                0x000000C7,
                0x000000C8,
                0x000000C9,
                0x000000CA,
                0x000000CB,
                0x000000CC,
                0x000000CD,
                0x000000CE,
                0x000000CF,
                0x000000D0,
                0x000000D1,
                0x000000D2,
                0x000000D3,
                0x000000D4,
                0x000000D5,
                0x000000D6,
                0x000000D7,
                0x000000D8,
                0x000000D9,
                0x000000DA,
                0x000000DB,
                0x000000DC,
                0x000000DD,
                0x000000DE,
                0x000000DF,
                0x000000E0,
                0x000000E1,
                0x000000E2,
                0x000000E3,
                0x000000E4,
                0x000000E5,
                0x000000E6,
                0x000000E7,
                0x000000E8,
                0x000000E9,
                0x000000EA,
                0x000000EB,
                0x000000EC,
                0x000000ED,
                0x000000EE,
                0x000000EF,
                0x000000F0,
                0x000000F1,
                0x000000F2,
                0x000000F3,
                0x000000F4,
                0x000000F5,
                0x000000F6,
                0x000000F7,
                0x000000F8,
                0x000000F9,
                0x000000FA,
                0x000000FB,
                0x000000FC,
                0x000000FD,
                0x000000FE,
                0x000000FF,
            }
            Register (FFixedHW,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                ,)
            ExtendedIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0xD0D1D2D3D4D5D6D7, // Granularity
                0xD8D9DADBDCDDDEDF, // Range Minimum
                0xE0E1E2E3E4E5E6E7, // Range Maximum
                0xE8E9EAEBECEDEEEF, // Translation Offset
                0xF0F1F2F3F4F5F6F7, // Length
                0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                , TypeTranslation, SparseTranslation)
            ExtendedMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                0xD0D1D2D3D4D5D6D7, // Granularity
                0xD8D9DADBDCDDDEDF, // Range Minimum
                0xE0E1E2E3E4E5E6E7, // Range Maximum
                0xE8E9EAEBECEDEEEF, // Translation Offset
                0xF0F1F2F3F4F5F6F7, // Length
                0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                , AddressRangeACPI, TypeTranslation)
            ExtendedSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                0xD0D1D2D3D4D5D6D7, // Granularity
                0xD8D9DADBDCDDDEDF, // Range Minimum
                0xE0E1E2E3E4E5E6E7, // Range Maximum
                0xE8E9EAEBECEDEEEF, // Translation Offset
                0xF0F1F2F3F4F5F6F7, // Length
                0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                )
            DWordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                0xFF, "PATHPATHPATH", )
            QWordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                0xFF, "PATHPATHPATH", )
            WordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                0xF6F7,             // Granularity
                0xF8F9,             // Range Minimum
                0xFAFB,             // Range Maximum
                0xFCFD,             // Translation Offset
                0xFEFF,             // Length
                0xFF, "PATHPATHPATH", )
        },

        ResourceTemplate ()
        {
            StartDependentFnNoPri ()
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
            }
            StartDependentFnNoPri ()
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
            }
            StartDependentFn (0x00, 0x00)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
            }
            StartDependentFn (0x00, 0x01)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
            }
            StartDependentFn (0x00, 0x02)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
            }
            StartDependentFn (0x01, 0x00)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
            }
            StartDependentFn (0x01, 0x01)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
                Memory32 (ReadWrite,
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Alignment
                    0xFCFDFEFF,         // Length
                    )
            }
            StartDependentFn (0x01, 0x01)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
                Memory32 (ReadWrite,
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Alignment
                    0xFCFDFEFF,         // Length
                    )
                Memory32Fixed (ReadOnly,
                    0xF0F1F2F3,         // Address Base
                    0xF4F5F6F7,         // Address Length
                    )
                VendorLong  ()      // Length = 0x15
                {
                    /* 0000 */  0x9F, 0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6,  // ........
                    /* 0008 */  0xF7, 0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE,  // ........
                    /* 0010 */  0xFF, 0x00, 0x01, 0x02, 0x03                     // .....
                }
                QWordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                    0xD8D9DADBDCDDDEDF, // Granularity
                    0xE0E1E2E3E4E5E6E7, // Range Minimum
                    0xE8E9EAEBECEDEEEF, // Range Maximum
                    0xF0F1F2F3F4F5F6F7, // Translation Offset
                    0xF8F9FAFBFCFDFEFF, // Length
                    0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
                DWordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                    0xECEDEEEF,         // Granularity
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Translation Offset
                    0xFCFDFEFF,         // Length
                    0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
                WordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                    0xF6F7,             // Granularity
                    0xF8F9,             // Range Minimum
                    0xFAFB,             // Range Maximum
                    0xFCFD,             // Translation Offset
                    0xFEFF,             // Length
                    0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
                QWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                    0xD8D9DADBDCDDDEDF, // Granularity
                    0xE0E1E2E3E4E5E6E7, // Range Minimum
                    0xE8E9EAEBECEDEEEF, // Range Maximum
                    0xF0F1F2F3F4F5F6F7, // Translation Offset
                    0xF8F9FAFBFCFDFEFF, // Length
                    0xFF, "PATHPATHPATH", , AddressRangeACPI, TypeTranslation)
                DWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                    0xECEDEEEF,         // Granularity
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Translation Offset
                    0xFCFDFEFF,         // Length
                    0xFF, "PATHPATHPATH", , AddressRangeACPI, TypeTranslation)
                WordBusNumber (ResourceConsumer, MinFixed, MaxFixed, SubDecode,
                    0xF6F7,             // Granularity
                    0xF8F9,             // Range Minimum
                    0xFAFB,             // Range Maximum
                    0xFCFD,             // Translation Offset
                    0xFEFF,             // Length
                    0xFF, "PATHPATHPATH", )
                Interrupt (ResourceConsumer, Edge, ActiveLow, Shared, 0xFF, "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*", )
                {
                    0x00000001,
                    0x00000002,
                    0x00000003,
                    0x00000004,
                    0x00000005,
                    0x00000006,
                    0x00000007,
                    0x00000008,
                    0x00000009,
                    0x0000000A,
                    0x0000000B,
                    0x0000000C,
                    0x0000000D,
                    0x0000000E,
                    0x0000000F,
                    0x00000010,
                    0x00000011,
                    0x00000012,
                    0x00000013,
                    0x00000014,
                    0x00000015,
                    0x00000016,
                    0x00000017,
                    0x00000018,
                    0x00000019,
                    0x0000001A,
                    0x0000001B,
                    0x0000001C,
                    0x0000001D,
                    0x0000001E,
                    0x0000001F,
                    0x00000020,
                    0x00000021,
                    0x00000022,
                    0x00000023,
                    0x00000024,
                    0x00000025,
                    0x00000026,
                    0x00000027,
                    0x00000028,
                    0x00000029,
                    0x0000002A,
                    0x0000002B,
                    0x0000002C,
                    0x0000002D,
                    0x0000002E,
                    0x0000002F,
                    0x00000030,
                    0x00000031,
                    0x00000032,
                    0x00000033,
                    0x00000034,
                    0x00000035,
                    0x00000036,
                    0x00000037,
                    0x00000038,
                    0x00000039,
                    0x0000003A,
                    0x0000003B,
                    0x0000003C,
                    0x0000003D,
                    0x0000003E,
                    0x0000003F,
                    0x00000040,
                    0x00000041,
                    0x00000042,
                    0x00000043,
                    0x00000044,
                    0x00000045,
                    0x00000046,
                    0x00000047,
                    0x00000048,
                    0x00000049,
                    0x0000004A,
                    0x0000004B,
                    0x0000004C,
                    0x0000004D,
                    0x0000004E,
                    0x0000004F,
                    0x00000050,
                    0x00000051,
                    0x00000052,
                    0x00000053,
                    0x00000054,
                    0x00000055,
                    0x00000056,
                    0x00000057,
                    0x00000058,
                    0x00000059,
                    0x0000005A,
                    0x0000005B,
                    0x0000005C,
                    0x0000005D,
                    0x0000005E,
                    0x0000005F,
                    0x00000060,
                    0x00000061,
                    0x00000062,
                    0x00000063,
                    0x00000064,
                    0x00000065,
                    0x00000066,
                    0x00000067,
                    0x00000068,
                    0x00000069,
                    0x0000006A,
                    0x0000006B,
                    0x0000006C,
                    0x0000006D,
                    0x0000006E,
                    0x0000006F,
                    0x00000070,
                    0x00000071,
                    0x00000072,
                    0x00000073,
                    0x00000074,
                    0x00000075,
                    0x00000076,
                    0x00000077,
                    0x00000078,
                    0x00000079,
                    0x0000007A,
                    0x0000007B,
                    0x0000007C,
                    0x0000007D,
                    0x0000007E,
                    0x0000007F,
                    0x00000080,
                    0x00000081,
                    0x00000082,
                    0x00000083,
                    0x00000084,
                    0x00000085,
                    0x00000086,
                    0x00000087,
                    0x00000088,
                    0x00000089,
                    0x0000008A,
                    0x0000008B,
                    0x0000008C,
                    0x0000008D,
                    0x0000008E,
                    0x0000008F,
                    0x00000090,
                    0x00000091,
                    0x00000092,
                    0x00000093,
                    0x00000094,
                    0x00000095,
                    0x00000096,
                    0x00000097,
                    0x00000098,
                    0x00000099,
                    0x0000009A,
                    0x0000009B,
                    0x0000009C,
                    0x0000009D,
                    0x0000009E,
                    0x0000009F,
                    0x000000A0,
                    0x000000A1,
                    0x000000A2,
                    0x000000A3,
                    0x000000A4,
                    0x000000A5,
                    0x000000A6,
                    0x000000A7,
                    0x000000A8,
                    0x000000A9,
                    0x000000AA,
                    0x000000AB,
                    0x000000AC,
                    0x000000AD,
                    0x000000AE,
                    0x000000AF,
                    0x000000B0,
                    0x000000B1,
                    0x000000B2,
                    0x000000B3,
                    0x000000B4,
                    0x000000B5,
                    0x000000B6,
                    0x000000B7,
                    0x000000B8,
                    0x000000B9,
                    0x000000BA,
                    0x000000BB,
                    0x000000BC,
                    0x000000BD,
                    0x000000BE,
                    0x000000BF,
                    0x000000C0,
                    0x000000C1,
                    0x000000C2,
                    0x000000C3,
                    0x000000C4,
                    0x000000C5,
                    0x000000C6,
                    0x000000C7,
                    0x000000C8,
                    0x000000C9,
                    0x000000CA,
                    0x000000CB,
                    0x000000CC,
                    0x000000CD,
                    0x000000CE,
                    0x000000CF,
                    0x000000D0,
                    0x000000D1,
                    0x000000D2,
                    0x000000D3,
                    0x000000D4,
                    0x000000D5,
                    0x000000D6,
                    0x000000D7,
                    0x000000D8,
                    0x000000D9,
                    0x000000DA,
                    0x000000DB,
                    0x000000DC,
                    0x000000DD,
                    0x000000DE,
                    0x000000DF,
                    0x000000E0,
                    0x000000E1,
                    0x000000E2,
                    0x000000E3,
                    0x000000E4,
                    0x000000E5,
                    0x000000E6,
                    0x000000E7,
                    0x000000E8,
                    0x000000E9,
                    0x000000EA,
                    0x000000EB,
                    0x000000EC,
                    0x000000ED,
                    0x000000EE,
                    0x000000EF,
                    0x000000F0,
                    0x000000F1,
                    0x000000F2,
                    0x000000F3,
                    0x000000F4,
                    0x000000F5,
                    0x000000F6,
                    0x000000F7,
                    0x000000F8,
                    0x000000F9,
                    0x000000FA,
                    0x000000FB,
                    0x000000FC,
                    0x000000FD,
                    0x000000FE,
                    0x000000FF,
                }
                Register (FFixedHW,
                    0xF0,               // Bit Width
                    0xF1,               // Bit Offset
                    0xF2F3F4F5F6F7F8F9, // Address
                    ,)
                ExtendedIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                    0xD0D1D2D3D4D5D6D7, // Granularity
                    0xD8D9DADBDCDDDEDF, // Range Minimum
                    0xE0E1E2E3E4E5E6E7, // Range Maximum
                    0xE8E9EAEBECEDEEEF, // Translation Offset
                    0xF0F1F2F3F4F5F6F7, // Length
                    0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                    , TypeTranslation, SparseTranslation)
                ExtendedMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                    0xD0D1D2D3D4D5D6D7, // Granularity
                    0xD8D9DADBDCDDDEDF, // Range Minimum
                    0xE0E1E2E3E4E5E6E7, // Range Maximum
                    0xE8E9EAEBECEDEEEF, // Translation Offset
                    0xF0F1F2F3F4F5F6F7, // Length
                    0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                    , AddressRangeACPI, TypeTranslation)
                ExtendedSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                    0xD0D1D2D3D4D5D6D7, // Granularity
                    0xD8D9DADBDCDDDEDF, // Range Minimum
                    0xE0E1E2E3E4E5E6E7, // Range Maximum
                    0xE8E9EAEBECEDEEEF, // Translation Offset
                    0xF0F1F2F3F4F5F6F7, // Length
                    0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                    )
                DWordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                    0xECEDEEEF,         // Granularity
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Translation Offset
                    0xFCFDFEFF,         // Length
                    0xFF, "PATHPATHPATH", )
                QWordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                    0xD8D9DADBDCDDDEDF, // Granularity
                    0xE0E1E2E3E4E5E6E7, // Range Minimum
                    0xE8E9EAEBECEDEEEF, // Range Maximum
                    0xF0F1F2F3F4F5F6F7, // Translation Offset
                    0xF8F9FAFBFCFDFEFF, // Length
                    0xFF, "PATHPATHPATH", )
                WordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                    0xF6F7,             // Granularity
                    0xF8F9,             // Range Minimum
                    0xFAFB,             // Range Maximum
                    0xFCFD,             // Translation Offset
                    0xFEFF,             // Length
                    0xFF, "PATHPATHPATH", )
            }
            StartDependentFn (0x01, 0x02)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
                Memory32 (ReadWrite,
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Alignment
                    0xFCFDFEFF,         // Length
                    )
                Memory32Fixed (ReadOnly,
                    0xF0F1F2F3,         // Address Base
                    0xF4F5F6F7,         // Address Length
                    )
            }
            StartDependentFn (0x02, 0x00)
            {
            }
            StartDependentFn (0x02, 0x01)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
                Memory32 (ReadWrite,
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Alignment
                    0xFCFDFEFF,         // Length
                    )
                Memory32Fixed (ReadOnly,
                    0xF0F1F2F3,         // Address Base
                    0xF4F5F6F7,         // Address Length
                    )
                VendorLong  ()      // Length = 0x15
                {
                    /* 0000 */  0x9F, 0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6,  // ........
                    /* 0008 */  0xF7, 0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE,  // ........
                    /* 0010 */  0xFF, 0x00, 0x01, 0x02, 0x03                     // .....
                }
            }
            StartDependentFn (0x02, 0x02)
            {
            }
            EndDependentFn ()
        }
    })
    /* Complex test data */

    Name (P445, Package (0x02)
    {
        ResourceTemplate ()
        {
            IRQ (Level, ActiveHigh, Exclusive, )
                {0}
            IRQNoFlags ()
                {1}
            DMA (Compatibility, NotBusMaster, Transfer16, )
                {2}
            IO (Decode16,
                0xF0F1,             // Range Minimum
                0xF2F3,             // Range Maximum
                0xF4,               // Alignment
                0xF5,               // Length
                )
            FixedIO (
                0x03F1,             // Address
                0xF2,               // Length
                )
            VendorShort ()      // Length = 0x07
            {
                 0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
            }
            Memory24 (ReadWrite,
                0xF0F1,             // Range Minimum
                0xF2F3,             // Range Maximum
                0xF4F5,             // Alignment
                0xF6F7,             // Length
                )
            Memory32 (ReadWrite,
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Alignment
                0xFCFDFEFF,         // Length
                )
            Memory32Fixed (ReadOnly,
                0xF0F1F2F3,         // Address Base
                0xF4F5F6F7,         // Address Length
                )
            VendorLong  ()      // Length = 0x15
            {
                /* 0000 */  0x9F, 0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6,  // ........
                /* 0008 */  0xF7, 0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE,  // ........
                /* 0010 */  0xFF, 0x00, 0x01, 0x02, 0x03                     // .....
            }
            QWordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
            DWordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
            WordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0xF6F7,             // Granularity
                0xF8F9,             // Range Minimum
                0xFAFB,             // Range Maximum
                0xFCFD,             // Translation Offset
                0xFEFF,             // Length
                0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
            QWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                0xFF, "PATHPATHPATH", , AddressRangeACPI, TypeTranslation)
            DWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                0xFF, "PATHPATHPATH", , AddressRangeACPI, TypeTranslation)
            WordBusNumber (ResourceConsumer, MinFixed, MaxFixed, SubDecode,
                0xF6F7,             // Granularity
                0xF8F9,             // Range Minimum
                0xFAFB,             // Range Maximum
                0xFCFD,             // Translation Offset
                0xFEFF,             // Length
                0xFF, "PATHPATHPATH", )
            Interrupt (ResourceConsumer, Edge, ActiveLow, Shared, 0xFF, "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*", )
            {
                0x00000001,
                0x00000002,
                0x00000003,
                0x00000004,
                0x00000005,
                0x00000006,
                0x00000007,
                0x00000008,
                0x00000009,
                0x0000000A,
                0x0000000B,
                0x0000000C,
                0x0000000D,
                0x0000000E,
                0x0000000F,
                0x00000010,
                0x00000011,
                0x00000012,
                0x00000013,
                0x00000014,
                0x00000015,
                0x00000016,
                0x00000017,
                0x00000018,
                0x00000019,
                0x0000001A,
                0x0000001B,
                0x0000001C,
                0x0000001D,
                0x0000001E,
                0x0000001F,
                0x00000020,
                0x00000021,
                0x00000022,
                0x00000023,
                0x00000024,
                0x00000025,
                0x00000026,
                0x00000027,
                0x00000028,
                0x00000029,
                0x0000002A,
                0x0000002B,
                0x0000002C,
                0x0000002D,
                0x0000002E,
                0x0000002F,
                0x00000030,
                0x00000031,
                0x00000032,
                0x00000033,
                0x00000034,
                0x00000035,
                0x00000036,
                0x00000037,
                0x00000038,
                0x00000039,
                0x0000003A,
                0x0000003B,
                0x0000003C,
                0x0000003D,
                0x0000003E,
                0x0000003F,
                0x00000040,
                0x00000041,
                0x00000042,
                0x00000043,
                0x00000044,
                0x00000045,
                0x00000046,
                0x00000047,
                0x00000048,
                0x00000049,
                0x0000004A,
                0x0000004B,
                0x0000004C,
                0x0000004D,
                0x0000004E,
                0x0000004F,
                0x00000050,
                0x00000051,
                0x00000052,
                0x00000053,
                0x00000054,
                0x00000055,
                0x00000056,
                0x00000057,
                0x00000058,
                0x00000059,
                0x0000005A,
                0x0000005B,
                0x0000005C,
                0x0000005D,
                0x0000005E,
                0x0000005F,
                0x00000060,
                0x00000061,
                0x00000062,
                0x00000063,
                0x00000064,
                0x00000065,
                0x00000066,
                0x00000067,
                0x00000068,
                0x00000069,
                0x0000006A,
                0x0000006B,
                0x0000006C,
                0x0000006D,
                0x0000006E,
                0x0000006F,
                0x00000070,
                0x00000071,
                0x00000072,
                0x00000073,
                0x00000074,
                0x00000075,
                0x00000076,
                0x00000077,
                0x00000078,
                0x00000079,
                0x0000007A,
                0x0000007B,
                0x0000007C,
                0x0000007D,
                0x0000007E,
                0x0000007F,
                0x00000080,
                0x00000081,
                0x00000082,
                0x00000083,
                0x00000084,
                0x00000085,
                0x00000086,
                0x00000087,
                0x00000088,
                0x00000089,
                0x0000008A,
                0x0000008B,
                0x0000008C,
                0x0000008D,
                0x0000008E,
                0x0000008F,
                0x00000090,
                0x00000091,
                0x00000092,
                0x00000093,
                0x00000094,
                0x00000095,
                0x00000096,
                0x00000097,
                0x00000098,
                0x00000099,
                0x0000009A,
                0x0000009B,
                0x0000009C,
                0x0000009D,
                0x0000009E,
                0x0000009F,
                0x000000A0,
                0x000000A1,
                0x000000A2,
                0x000000A3,
                0x000000A4,
                0x000000A5,
                0x000000A6,
                0x000000A7,
                0x000000A8,
                0x000000A9,
                0x000000AA,
                0x000000AB,
                0x000000AC,
                0x000000AD,
                0x000000AE,
                0x000000AF,
                0x000000B0,
                0x000000B1,
                0x000000B2,
                0x000000B3,
                0x000000B4,
                0x000000B5,
                0x000000B6,
                0x000000B7,
                0x000000B8,
                0x000000B9,
                0x000000BA,
                0x000000BB,
                0x000000BC,
                0x000000BD,
                0x000000BE,
                0x000000BF,
                0x000000C0,
                0x000000C1,
                0x000000C2,
                0x000000C3,
                0x000000C4,
                0x000000C5,
                0x000000C6,
                0x000000C7,
                0x000000C8,
                0x000000C9,
                0x000000CA,
                0x000000CB,
                0x000000CC,
                0x000000CD,
                0x000000CE,
                0x000000CF,
                0x000000D0,
                0x000000D1,
                0x000000D2,
                0x000000D3,
                0x000000D4,
                0x000000D5,
                0x000000D6,
                0x000000D7,
                0x000000D8,
                0x000000D9,
                0x000000DA,
                0x000000DB,
                0x000000DC,
                0x000000DD,
                0x000000DE,
                0x000000DF,
                0x000000E0,
                0x000000E1,
                0x000000E2,
                0x000000E3,
                0x000000E4,
                0x000000E5,
                0x000000E6,
                0x000000E7,
                0x000000E8,
                0x000000E9,
                0x000000EA,
                0x000000EB,
                0x000000EC,
                0x000000ED,
                0x000000EE,
                0x000000EF,
                0x000000F0,
                0x000000F1,
                0x000000F2,
                0x000000F3,
                0x000000F4,
                0x000000F5,
                0x000000F6,
                0x000000F7,
                0x000000F8,
                0x000000F9,
                0x000000FA,
                0x000000FB,
                0x000000FC,
                0x000000FD,
                0x000000FE,
                0x000000FF,
            }
            Register (FFixedHW,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                ,)
            ExtendedIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0xD0D1D2D3D4D5D6D7, // Granularity
                0xD8D9DADBDCDDDEDF, // Range Minimum
                0xE0E1E2E3E4E5E6E7, // Range Maximum
                0xE8E9EAEBECEDEEEF, // Translation Offset
                0xF0F1F2F3F4F5F6F7, // Length
                0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                , TypeTranslation, SparseTranslation)
            ExtendedMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                0xD0D1D2D3D4D5D6D7, // Granularity
                0xD8D9DADBDCDDDEDF, // Range Minimum
                0xE0E1E2E3E4E5E6E7, // Range Maximum
                0xE8E9EAEBECEDEEEF, // Translation Offset
                0xF0F1F2F3F4F5F6F7, // Length
                0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                , AddressRangeACPI, TypeTranslation)
            ExtendedSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                0xD0D1D2D3D4D5D6D7, // Granularity
                0xD8D9DADBDCDDDEDF, // Range Minimum
                0xE0E1E2E3E4E5E6E7, // Range Maximum
                0xE8E9EAEBECEDEEEF, // Translation Offset
                0xF0F1F2F3F4F5F6F7, // Length
                0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                )
            DWordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                0xFF, "PATHPATHPATH", )
            QWordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                0xFF, "PATHPATHPATH", )
            WordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                0xF6F7,             // Granularity
                0xF8F9,             // Range Minimum
                0xFAFB,             // Range Maximum
                0xFCFD,             // Translation Offset
                0xFEFF,             // Length
                0xFF, "PATHPATHPATH", )
            IRQ (Level, ActiveHigh, Exclusive, )
                {0}
            IRQNoFlags ()
                {1}
            DMA (Compatibility, NotBusMaster, Transfer16, )
                {2}
            IO (Decode16,
                0xF0F1,             // Range Minimum
                0xF2F3,             // Range Maximum
                0xF4,               // Alignment
                0xF5,               // Length
                )
            FixedIO (
                0x03F1,             // Address
                0xF2,               // Length
                )
            VendorShort ()      // Length = 0x07
            {
                 0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
            }
            Memory24 (ReadWrite,
                0xF0F1,             // Range Minimum
                0xF2F3,             // Range Maximum
                0xF4F5,             // Alignment
                0xF6F7,             // Length
                )
            Memory32 (ReadWrite,
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Alignment
                0xFCFDFEFF,         // Length
                )
            Memory32Fixed (ReadOnly,
                0xF0F1F2F3,         // Address Base
                0xF4F5F6F7,         // Address Length
                )
            VendorLong  ()      // Length = 0x15
            {
                /* 0000 */  0x9F, 0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6,  // ........
                /* 0008 */  0xF7, 0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE,  // ........
                /* 0010 */  0xFF, 0x00, 0x01, 0x02, 0x03                     // .....
            }
            QWordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
            DWordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
            WordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0xF6F7,             // Granularity
                0xF8F9,             // Range Minimum
                0xFAFB,             // Range Maximum
                0xFCFD,             // Translation Offset
                0xFEFF,             // Length
                0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
            QWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                0xFF, "PATHPATHPATH", , AddressRangeACPI, TypeTranslation)
            DWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                0xFF, "PATHPATHPATH", , AddressRangeACPI, TypeTranslation)
            WordBusNumber (ResourceConsumer, MinFixed, MaxFixed, SubDecode,
                0xF6F7,             // Granularity
                0xF8F9,             // Range Minimum
                0xFAFB,             // Range Maximum
                0xFCFD,             // Translation Offset
                0xFEFF,             // Length
                0xFF, "PATHPATHPATH", )
            Interrupt (ResourceConsumer, Edge, ActiveLow, Shared, 0xFF, "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*", )
            {
                0x00000001,
                0x00000002,
                0x00000003,
                0x00000004,
                0x00000005,
                0x00000006,
                0x00000007,
                0x00000008,
                0x00000009,
                0x0000000A,
                0x0000000B,
                0x0000000C,
                0x0000000D,
                0x0000000E,
                0x0000000F,
                0x00000010,
                0x00000011,
                0x00000012,
                0x00000013,
                0x00000014,
                0x00000015,
                0x00000016,
                0x00000017,
                0x00000018,
                0x00000019,
                0x0000001A,
                0x0000001B,
                0x0000001C,
                0x0000001D,
                0x0000001E,
                0x0000001F,
                0x00000020,
                0x00000021,
                0x00000022,
                0x00000023,
                0x00000024,
                0x00000025,
                0x00000026,
                0x00000027,
                0x00000028,
                0x00000029,
                0x0000002A,
                0x0000002B,
                0x0000002C,
                0x0000002D,
                0x0000002E,
                0x0000002F,
                0x00000030,
                0x00000031,
                0x00000032,
                0x00000033,
                0x00000034,
                0x00000035,
                0x00000036,
                0x00000037,
                0x00000038,
                0x00000039,
                0x0000003A,
                0x0000003B,
                0x0000003C,
                0x0000003D,
                0x0000003E,
                0x0000003F,
                0x00000040,
                0x00000041,
                0x00000042,
                0x00000043,
                0x00000044,
                0x00000045,
                0x00000046,
                0x00000047,
                0x00000048,
                0x00000049,
                0x0000004A,
                0x0000004B,
                0x0000004C,
                0x0000004D,
                0x0000004E,
                0x0000004F,
                0x00000050,
                0x00000051,
                0x00000052,
                0x00000053,
                0x00000054,
                0x00000055,
                0x00000056,
                0x00000057,
                0x00000058,
                0x00000059,
                0x0000005A,
                0x0000005B,
                0x0000005C,
                0x0000005D,
                0x0000005E,
                0x0000005F,
                0x00000060,
                0x00000061,
                0x00000062,
                0x00000063,
                0x00000064,
                0x00000065,
                0x00000066,
                0x00000067,
                0x00000068,
                0x00000069,
                0x0000006A,
                0x0000006B,
                0x0000006C,
                0x0000006D,
                0x0000006E,
                0x0000006F,
                0x00000070,
                0x00000071,
                0x00000072,
                0x00000073,
                0x00000074,
                0x00000075,
                0x00000076,
                0x00000077,
                0x00000078,
                0x00000079,
                0x0000007A,
                0x0000007B,
                0x0000007C,
                0x0000007D,
                0x0000007E,
                0x0000007F,
                0x00000080,
                0x00000081,
                0x00000082,
                0x00000083,
                0x00000084,
                0x00000085,
                0x00000086,
                0x00000087,
                0x00000088,
                0x00000089,
                0x0000008A,
                0x0000008B,
                0x0000008C,
                0x0000008D,
                0x0000008E,
                0x0000008F,
                0x00000090,
                0x00000091,
                0x00000092,
                0x00000093,
                0x00000094,
                0x00000095,
                0x00000096,
                0x00000097,
                0x00000098,
                0x00000099,
                0x0000009A,
                0x0000009B,
                0x0000009C,
                0x0000009D,
                0x0000009E,
                0x0000009F,
                0x000000A0,
                0x000000A1,
                0x000000A2,
                0x000000A3,
                0x000000A4,
                0x000000A5,
                0x000000A6,
                0x000000A7,
                0x000000A8,
                0x000000A9,
                0x000000AA,
                0x000000AB,
                0x000000AC,
                0x000000AD,
                0x000000AE,
                0x000000AF,
                0x000000B0,
                0x000000B1,
                0x000000B2,
                0x000000B3,
                0x000000B4,
                0x000000B5,
                0x000000B6,
                0x000000B7,
                0x000000B8,
                0x000000B9,
                0x000000BA,
                0x000000BB,
                0x000000BC,
                0x000000BD,
                0x000000BE,
                0x000000BF,
                0x000000C0,
                0x000000C1,
                0x000000C2,
                0x000000C3,
                0x000000C4,
                0x000000C5,
                0x000000C6,
                0x000000C7,
                0x000000C8,
                0x000000C9,
                0x000000CA,
                0x000000CB,
                0x000000CC,
                0x000000CD,
                0x000000CE,
                0x000000CF,
                0x000000D0,
                0x000000D1,
                0x000000D2,
                0x000000D3,
                0x000000D4,
                0x000000D5,
                0x000000D6,
                0x000000D7,
                0x000000D8,
                0x000000D9,
                0x000000DA,
                0x000000DB,
                0x000000DC,
                0x000000DD,
                0x000000DE,
                0x000000DF,
                0x000000E0,
                0x000000E1,
                0x000000E2,
                0x000000E3,
                0x000000E4,
                0x000000E5,
                0x000000E6,
                0x000000E7,
                0x000000E8,
                0x000000E9,
                0x000000EA,
                0x000000EB,
                0x000000EC,
                0x000000ED,
                0x000000EE,
                0x000000EF,
                0x000000F0,
                0x000000F1,
                0x000000F2,
                0x000000F3,
                0x000000F4,
                0x000000F5,
                0x000000F6,
                0x000000F7,
                0x000000F8,
                0x000000F9,
                0x000000FA,
                0x000000FB,
                0x000000FC,
                0x000000FD,
                0x000000FE,
                0x000000FF,
            }
            Register (FFixedHW,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                ,)
            ExtendedIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0xD0D1D2D3D4D5D6D7, // Granularity
                0xD8D9DADBDCDDDEDF, // Range Minimum
                0xE0E1E2E3E4E5E6E7, // Range Maximum
                0xE8E9EAEBECEDEEEF, // Translation Offset
                0xF0F1F2F3F4F5F6F7, // Length
                0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                , TypeTranslation, SparseTranslation)
            ExtendedMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                0xD0D1D2D3D4D5D6D7, // Granularity
                0xD8D9DADBDCDDDEDF, // Range Minimum
                0xE0E1E2E3E4E5E6E7, // Range Maximum
                0xE8E9EAEBECEDEEEF, // Translation Offset
                0xF0F1F2F3F4F5F6F7, // Length
                0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                , AddressRangeACPI, TypeTranslation)
            ExtendedSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                0xD0D1D2D3D4D5D6D7, // Granularity
                0xD8D9DADBDCDDDEDF, // Range Minimum
                0xE0E1E2E3E4E5E6E7, // Range Maximum
                0xE8E9EAEBECEDEEEF, // Translation Offset
                0xF0F1F2F3F4F5F6F7, // Length
                0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                )
            DWordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                0xFF, "PATHPATHPATH", )
            QWordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                0xFF, "PATHPATHPATH", )
            WordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                0xF6F7,             // Granularity
                0xF8F9,             // Range Minimum
                0xFAFB,             // Range Maximum
                0xFCFD,             // Translation Offset
                0xFEFF,             // Length
                0xFF, "PATHPATHPATH", )
        },

        ResourceTemplate ()
        {
            StartDependentFnNoPri ()
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
            }
            StartDependentFnNoPri ()
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
            }
            StartDependentFn (0x00, 0x00)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
            }
            StartDependentFn (0x00, 0x01)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
            }
            StartDependentFn (0x00, 0x02)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
            }
            StartDependentFn (0x01, 0x00)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
            }
            StartDependentFn (0x01, 0x01)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
                Memory32 (ReadWrite,
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Alignment
                    0xFCFDFEFF,         // Length
                    )
            }
            StartDependentFn (0x01, 0x01)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
                Memory32 (ReadWrite,
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Alignment
                    0xFCFDFEFF,         // Length
                    )
                Memory32Fixed (ReadOnly,
                    0xF0F1F2F3,         // Address Base
                    0xF4F5F6F7,         // Address Length
                    )
                VendorLong  ()      // Length = 0x15
                {
                    /* 0000 */  0x9F, 0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6,  // ........
                    /* 0008 */  0xF7, 0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE,  // ........
                    /* 0010 */  0xFF, 0x00, 0x01, 0x02, 0x03                     // .....
                }
                QWordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                    0xD8D9DADBDCDDDEDF, // Granularity
                    0xE0E1E2E3E4E5E6E7, // Range Minimum
                    0xE8E9EAEBECEDEEEF, // Range Maximum
                    0xF0F1F2F3F4F5F6F7, // Translation Offset
                    0xF8F9FAFBFCFDFEFF, // Length
                    0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
                DWordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                    0xECEDEEEF,         // Granularity
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Translation Offset
                    0xFCFDFEFF,         // Length
                    0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
                WordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                    0xF6F7,             // Granularity
                    0xF8F9,             // Range Minimum
                    0xFAFB,             // Range Maximum
                    0xFCFD,             // Translation Offset
                    0xFEFF,             // Length
                    0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
                QWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                    0xD8D9DADBDCDDDEDF, // Granularity
                    0xE0E1E2E3E4E5E6E7, // Range Minimum
                    0xE8E9EAEBECEDEEEF, // Range Maximum
                    0xF0F1F2F3F4F5F6F7, // Translation Offset
                    0xF8F9FAFBFCFDFEFF, // Length
                    0xFF, "PATHPATHPATH", , AddressRangeACPI, TypeTranslation)
                DWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                    0xECEDEEEF,         // Granularity
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Translation Offset
                    0xFCFDFEFF,         // Length
                    0xFF, "PATHPATHPATH", , AddressRangeACPI, TypeTranslation)
                WordBusNumber (ResourceConsumer, MinFixed, MaxFixed, SubDecode,
                    0xF6F7,             // Granularity
                    0xF8F9,             // Range Minimum
                    0xFAFB,             // Range Maximum
                    0xFCFD,             // Translation Offset
                    0xFEFF,             // Length
                    0xFF, "PATHPATHPATH", )
                Interrupt (ResourceConsumer, Edge, ActiveLow, Shared, 0xFF, "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*", )
                {
                    0x00000001,
                    0x00000002,
                    0x00000003,
                    0x00000004,
                    0x00000005,
                    0x00000006,
                    0x00000007,
                    0x00000008,
                    0x00000009,
                    0x0000000A,
                    0x0000000B,
                    0x0000000C,
                    0x0000000D,
                    0x0000000E,
                    0x0000000F,
                    0x00000010,
                    0x00000011,
                    0x00000012,
                    0x00000013,
                    0x00000014,
                    0x00000015,
                    0x00000016,
                    0x00000017,
                    0x00000018,
                    0x00000019,
                    0x0000001A,
                    0x0000001B,
                    0x0000001C,
                    0x0000001D,
                    0x0000001E,
                    0x0000001F,
                    0x00000020,
                    0x00000021,
                    0x00000022,
                    0x00000023,
                    0x00000024,
                    0x00000025,
                    0x00000026,
                    0x00000027,
                    0x00000028,
                    0x00000029,
                    0x0000002A,
                    0x0000002B,
                    0x0000002C,
                    0x0000002D,
                    0x0000002E,
                    0x0000002F,
                    0x00000030,
                    0x00000031,
                    0x00000032,
                    0x00000033,
                    0x00000034,
                    0x00000035,
                    0x00000036,
                    0x00000037,
                    0x00000038,
                    0x00000039,
                    0x0000003A,
                    0x0000003B,
                    0x0000003C,
                    0x0000003D,
                    0x0000003E,
                    0x0000003F,
                    0x00000040,
                    0x00000041,
                    0x00000042,
                    0x00000043,
                    0x00000044,
                    0x00000045,
                    0x00000046,
                    0x00000047,
                    0x00000048,
                    0x00000049,
                    0x0000004A,
                    0x0000004B,
                    0x0000004C,
                    0x0000004D,
                    0x0000004E,
                    0x0000004F,
                    0x00000050,
                    0x00000051,
                    0x00000052,
                    0x00000053,
                    0x00000054,
                    0x00000055,
                    0x00000056,
                    0x00000057,
                    0x00000058,
                    0x00000059,
                    0x0000005A,
                    0x0000005B,
                    0x0000005C,
                    0x0000005D,
                    0x0000005E,
                    0x0000005F,
                    0x00000060,
                    0x00000061,
                    0x00000062,
                    0x00000063,
                    0x00000064,
                    0x00000065,
                    0x00000066,
                    0x00000067,
                    0x00000068,
                    0x00000069,
                    0x0000006A,
                    0x0000006B,
                    0x0000006C,
                    0x0000006D,
                    0x0000006E,
                    0x0000006F,
                    0x00000070,
                    0x00000071,
                    0x00000072,
                    0x00000073,
                    0x00000074,
                    0x00000075,
                    0x00000076,
                    0x00000077,
                    0x00000078,
                    0x00000079,
                    0x0000007A,
                    0x0000007B,
                    0x0000007C,
                    0x0000007D,
                    0x0000007E,
                    0x0000007F,
                    0x00000080,
                    0x00000081,
                    0x00000082,
                    0x00000083,
                    0x00000084,
                    0x00000085,
                    0x00000086,
                    0x00000087,
                    0x00000088,
                    0x00000089,
                    0x0000008A,
                    0x0000008B,
                    0x0000008C,
                    0x0000008D,
                    0x0000008E,
                    0x0000008F,
                    0x00000090,
                    0x00000091,
                    0x00000092,
                    0x00000093,
                    0x00000094,
                    0x00000095,
                    0x00000096,
                    0x00000097,
                    0x00000098,
                    0x00000099,
                    0x0000009A,
                    0x0000009B,
                    0x0000009C,
                    0x0000009D,
                    0x0000009E,
                    0x0000009F,
                    0x000000A0,
                    0x000000A1,
                    0x000000A2,
                    0x000000A3,
                    0x000000A4,
                    0x000000A5,
                    0x000000A6,
                    0x000000A7,
                    0x000000A8,
                    0x000000A9,
                    0x000000AA,
                    0x000000AB,
                    0x000000AC,
                    0x000000AD,
                    0x000000AE,
                    0x000000AF,
                    0x000000B0,
                    0x000000B1,
                    0x000000B2,
                    0x000000B3,
                    0x000000B4,
                    0x000000B5,
                    0x000000B6,
                    0x000000B7,
                    0x000000B8,
                    0x000000B9,
                    0x000000BA,
                    0x000000BB,
                    0x000000BC,
                    0x000000BD,
                    0x000000BE,
                    0x000000BF,
                    0x000000C0,
                    0x000000C1,
                    0x000000C2,
                    0x000000C3,
                    0x000000C4,
                    0x000000C5,
                    0x000000C6,
                    0x000000C7,
                    0x000000C8,
                    0x000000C9,
                    0x000000CA,
                    0x000000CB,
                    0x000000CC,
                    0x000000CD,
                    0x000000CE,
                    0x000000CF,
                    0x000000D0,
                    0x000000D1,
                    0x000000D2,
                    0x000000D3,
                    0x000000D4,
                    0x000000D5,
                    0x000000D6,
                    0x000000D7,
                    0x000000D8,
                    0x000000D9,
                    0x000000DA,
                    0x000000DB,
                    0x000000DC,
                    0x000000DD,
                    0x000000DE,
                    0x000000DF,
                    0x000000E0,
                    0x000000E1,
                    0x000000E2,
                    0x000000E3,
                    0x000000E4,
                    0x000000E5,
                    0x000000E6,
                    0x000000E7,
                    0x000000E8,
                    0x000000E9,
                    0x000000EA,
                    0x000000EB,
                    0x000000EC,
                    0x000000ED,
                    0x000000EE,
                    0x000000EF,
                    0x000000F0,
                    0x000000F1,
                    0x000000F2,
                    0x000000F3,
                    0x000000F4,
                    0x000000F5,
                    0x000000F6,
                    0x000000F7,
                    0x000000F8,
                    0x000000F9,
                    0x000000FA,
                    0x000000FB,
                    0x000000FC,
                    0x000000FD,
                    0x000000FE,
                    0x000000FF,
                }
                Register (FFixedHW,
                    0xF0,               // Bit Width
                    0xF1,               // Bit Offset
                    0xF2F3F4F5F6F7F8F9, // Address
                    ,)
                ExtendedIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                    0xD0D1D2D3D4D5D6D7, // Granularity
                    0xD8D9DADBDCDDDEDF, // Range Minimum
                    0xE0E1E2E3E4E5E6E7, // Range Maximum
                    0xE8E9EAEBECEDEEEF, // Translation Offset
                    0xF0F1F2F3F4F5F6F7, // Length
                    0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                    , TypeTranslation, SparseTranslation)
                ExtendedMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                    0xD0D1D2D3D4D5D6D7, // Granularity
                    0xD8D9DADBDCDDDEDF, // Range Minimum
                    0xE0E1E2E3E4E5E6E7, // Range Maximum
                    0xE8E9EAEBECEDEEEF, // Translation Offset
                    0xF0F1F2F3F4F5F6F7, // Length
                    0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                    , AddressRangeACPI, TypeTranslation)
                ExtendedSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                    0xD0D1D2D3D4D5D6D7, // Granularity
                    0xD8D9DADBDCDDDEDF, // Range Minimum
                    0xE0E1E2E3E4E5E6E7, // Range Maximum
                    0xE8E9EAEBECEDEEEF, // Translation Offset
                    0xF0F1F2F3F4F5F6F7, // Length
                    0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                    )
                DWordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                    0xECEDEEEF,         // Granularity
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Translation Offset
                    0xFCFDFEFF,         // Length
                    0xFF, "PATHPATHPATH", )
                QWordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                    0xD8D9DADBDCDDDEDF, // Granularity
                    0xE0E1E2E3E4E5E6E7, // Range Minimum
                    0xE8E9EAEBECEDEEEF, // Range Maximum
                    0xF0F1F2F3F4F5F6F7, // Translation Offset
                    0xF8F9FAFBFCFDFEFF, // Length
                    0xFF, "PATHPATHPATH", )
                WordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                    0xF6F7,             // Granularity
                    0xF8F9,             // Range Minimum
                    0xFAFB,             // Range Maximum
                    0xFCFD,             // Translation Offset
                    0xFEFF,             // Length
                    0xFF, "PATHPATHPATH", )
            }
            StartDependentFn (0x01, 0x02)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
                Memory32 (ReadWrite,
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Alignment
                    0xFCFDFEFF,         // Length
                    )
                Memory32Fixed (ReadOnly,
                    0xF0F1F2F3,         // Address Base
                    0xF4F5F6F7,         // Address Length
                    )
            }
            StartDependentFn (0x02, 0x00)
            {
            }
            StartDependentFn (0x02, 0x01)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
                Memory32 (ReadWrite,
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Alignment
                    0xFCFDFEFF,         // Length
                    )
                Memory32Fixed (ReadOnly,
                    0xF0F1F2F3,         // Address Base
                    0xF4F5F6F7,         // Address Length
                    )
                VendorLong  ()      // Length = 0x15
                {
                    /* 0000 */  0x9F, 0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6,  // ........
                    /* 0008 */  0xF7, 0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE,  // ........
                    /* 0010 */  0xFF, 0x00, 0x01, 0x02, 0x03                     // .....
                }
            }
            StartDependentFn (0x02, 0x02)
            {
            }
            EndDependentFn ()
            StartDependentFnNoPri ()
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
            }
            StartDependentFnNoPri ()
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
            }
            StartDependentFn (0x00, 0x00)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
            }
            StartDependentFn (0x00, 0x01)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
            }
            StartDependentFn (0x00, 0x02)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
            }
            StartDependentFn (0x01, 0x00)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
            }
            StartDependentFn (0x01, 0x01)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
                Memory32 (ReadWrite,
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Alignment
                    0xFCFDFEFF,         // Length
                    )
            }
            StartDependentFn (0x01, 0x01)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
                Memory32 (ReadWrite,
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Alignment
                    0xFCFDFEFF,         // Length
                    )
                Memory32Fixed (ReadOnly,
                    0xF0F1F2F3,         // Address Base
                    0xF4F5F6F7,         // Address Length
                    )
                VendorLong  ()      // Length = 0x15
                {
                    /* 0000 */  0x9F, 0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6,  // ........
                    /* 0008 */  0xF7, 0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE,  // ........
                    /* 0010 */  0xFF, 0x00, 0x01, 0x02, 0x03                     // .....
                }
                QWordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                    0xD8D9DADBDCDDDEDF, // Granularity
                    0xE0E1E2E3E4E5E6E7, // Range Minimum
                    0xE8E9EAEBECEDEEEF, // Range Maximum
                    0xF0F1F2F3F4F5F6F7, // Translation Offset
                    0xF8F9FAFBFCFDFEFF, // Length
                    0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
                DWordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                    0xECEDEEEF,         // Granularity
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Translation Offset
                    0xFCFDFEFF,         // Length
                    0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
                WordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                    0xF6F7,             // Granularity
                    0xF8F9,             // Range Minimum
                    0xFAFB,             // Range Maximum
                    0xFCFD,             // Translation Offset
                    0xFEFF,             // Length
                    0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
                QWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                    0xD8D9DADBDCDDDEDF, // Granularity
                    0xE0E1E2E3E4E5E6E7, // Range Minimum
                    0xE8E9EAEBECEDEEEF, // Range Maximum
                    0xF0F1F2F3F4F5F6F7, // Translation Offset
                    0xF8F9FAFBFCFDFEFF, // Length
                    0xFF, "PATHPATHPATH", , AddressRangeACPI, TypeTranslation)
                DWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                    0xECEDEEEF,         // Granularity
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Translation Offset
                    0xFCFDFEFF,         // Length
                    0xFF, "PATHPATHPATH", , AddressRangeACPI, TypeTranslation)
                WordBusNumber (ResourceConsumer, MinFixed, MaxFixed, SubDecode,
                    0xF6F7,             // Granularity
                    0xF8F9,             // Range Minimum
                    0xFAFB,             // Range Maximum
                    0xFCFD,             // Translation Offset
                    0xFEFF,             // Length
                    0xFF, "PATHPATHPATH", )
                Interrupt (ResourceConsumer, Edge, ActiveLow, Shared, 0xFF, "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*", )
                {
                    0x00000001,
                    0x00000002,
                    0x00000003,
                    0x00000004,
                    0x00000005,
                    0x00000006,
                    0x00000007,
                    0x00000008,
                    0x00000009,
                    0x0000000A,
                    0x0000000B,
                    0x0000000C,
                    0x0000000D,
                    0x0000000E,
                    0x0000000F,
                    0x00000010,
                    0x00000011,
                    0x00000012,
                    0x00000013,
                    0x00000014,
                    0x00000015,
                    0x00000016,
                    0x00000017,
                    0x00000018,
                    0x00000019,
                    0x0000001A,
                    0x0000001B,
                    0x0000001C,
                    0x0000001D,
                    0x0000001E,
                    0x0000001F,
                    0x00000020,
                    0x00000021,
                    0x00000022,
                    0x00000023,
                    0x00000024,
                    0x00000025,
                    0x00000026,
                    0x00000027,
                    0x00000028,
                    0x00000029,
                    0x0000002A,
                    0x0000002B,
                    0x0000002C,
                    0x0000002D,
                    0x0000002E,
                    0x0000002F,
                    0x00000030,
                    0x00000031,
                    0x00000032,
                    0x00000033,
                    0x00000034,
                    0x00000035,
                    0x00000036,
                    0x00000037,
                    0x00000038,
                    0x00000039,
                    0x0000003A,
                    0x0000003B,
                    0x0000003C,
                    0x0000003D,
                    0x0000003E,
                    0x0000003F,
                    0x00000040,
                    0x00000041,
                    0x00000042,
                    0x00000043,
                    0x00000044,
                    0x00000045,
                    0x00000046,
                    0x00000047,
                    0x00000048,
                    0x00000049,
                    0x0000004A,
                    0x0000004B,
                    0x0000004C,
                    0x0000004D,
                    0x0000004E,
                    0x0000004F,
                    0x00000050,
                    0x00000051,
                    0x00000052,
                    0x00000053,
                    0x00000054,
                    0x00000055,
                    0x00000056,
                    0x00000057,
                    0x00000058,
                    0x00000059,
                    0x0000005A,
                    0x0000005B,
                    0x0000005C,
                    0x0000005D,
                    0x0000005E,
                    0x0000005F,
                    0x00000060,
                    0x00000061,
                    0x00000062,
                    0x00000063,
                    0x00000064,
                    0x00000065,
                    0x00000066,
                    0x00000067,
                    0x00000068,
                    0x00000069,
                    0x0000006A,
                    0x0000006B,
                    0x0000006C,
                    0x0000006D,
                    0x0000006E,
                    0x0000006F,
                    0x00000070,
                    0x00000071,
                    0x00000072,
                    0x00000073,
                    0x00000074,
                    0x00000075,
                    0x00000076,
                    0x00000077,
                    0x00000078,
                    0x00000079,
                    0x0000007A,
                    0x0000007B,
                    0x0000007C,
                    0x0000007D,
                    0x0000007E,
                    0x0000007F,
                    0x00000080,
                    0x00000081,
                    0x00000082,
                    0x00000083,
                    0x00000084,
                    0x00000085,
                    0x00000086,
                    0x00000087,
                    0x00000088,
                    0x00000089,
                    0x0000008A,
                    0x0000008B,
                    0x0000008C,
                    0x0000008D,
                    0x0000008E,
                    0x0000008F,
                    0x00000090,
                    0x00000091,
                    0x00000092,
                    0x00000093,
                    0x00000094,
                    0x00000095,
                    0x00000096,
                    0x00000097,
                    0x00000098,
                    0x00000099,
                    0x0000009A,
                    0x0000009B,
                    0x0000009C,
                    0x0000009D,
                    0x0000009E,
                    0x0000009F,
                    0x000000A0,
                    0x000000A1,
                    0x000000A2,
                    0x000000A3,
                    0x000000A4,
                    0x000000A5,
                    0x000000A6,
                    0x000000A7,
                    0x000000A8,
                    0x000000A9,
                    0x000000AA,
                    0x000000AB,
                    0x000000AC,
                    0x000000AD,
                    0x000000AE,
                    0x000000AF,
                    0x000000B0,
                    0x000000B1,
                    0x000000B2,
                    0x000000B3,
                    0x000000B4,
                    0x000000B5,
                    0x000000B6,
                    0x000000B7,
                    0x000000B8,
                    0x000000B9,
                    0x000000BA,
                    0x000000BB,
                    0x000000BC,
                    0x000000BD,
                    0x000000BE,
                    0x000000BF,
                    0x000000C0,
                    0x000000C1,
                    0x000000C2,
                    0x000000C3,
                    0x000000C4,
                    0x000000C5,
                    0x000000C6,
                    0x000000C7,
                    0x000000C8,
                    0x000000C9,
                    0x000000CA,
                    0x000000CB,
                    0x000000CC,
                    0x000000CD,
                    0x000000CE,
                    0x000000CF,
                    0x000000D0,
                    0x000000D1,
                    0x000000D2,
                    0x000000D3,
                    0x000000D4,
                    0x000000D5,
                    0x000000D6,
                    0x000000D7,
                    0x000000D8,
                    0x000000D9,
                    0x000000DA,
                    0x000000DB,
                    0x000000DC,
                    0x000000DD,
                    0x000000DE,
                    0x000000DF,
                    0x000000E0,
                    0x000000E1,
                    0x000000E2,
                    0x000000E3,
                    0x000000E4,
                    0x000000E5,
                    0x000000E6,
                    0x000000E7,
                    0x000000E8,
                    0x000000E9,
                    0x000000EA,
                    0x000000EB,
                    0x000000EC,
                    0x000000ED,
                    0x000000EE,
                    0x000000EF,
                    0x000000F0,
                    0x000000F1,
                    0x000000F2,
                    0x000000F3,
                    0x000000F4,
                    0x000000F5,
                    0x000000F6,
                    0x000000F7,
                    0x000000F8,
                    0x000000F9,
                    0x000000FA,
                    0x000000FB,
                    0x000000FC,
                    0x000000FD,
                    0x000000FE,
                    0x000000FF,
                }
                Register (FFixedHW,
                    0xF0,               // Bit Width
                    0xF1,               // Bit Offset
                    0xF2F3F4F5F6F7F8F9, // Address
                    ,)
                ExtendedIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                    0xD0D1D2D3D4D5D6D7, // Granularity
                    0xD8D9DADBDCDDDEDF, // Range Minimum
                    0xE0E1E2E3E4E5E6E7, // Range Maximum
                    0xE8E9EAEBECEDEEEF, // Translation Offset
                    0xF0F1F2F3F4F5F6F7, // Length
                    0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                    , TypeTranslation, SparseTranslation)
                ExtendedMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                    0xD0D1D2D3D4D5D6D7, // Granularity
                    0xD8D9DADBDCDDDEDF, // Range Minimum
                    0xE0E1E2E3E4E5E6E7, // Range Maximum
                    0xE8E9EAEBECEDEEEF, // Translation Offset
                    0xF0F1F2F3F4F5F6F7, // Length
                    0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                    , AddressRangeACPI, TypeTranslation)
                ExtendedSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                    0xD0D1D2D3D4D5D6D7, // Granularity
                    0xD8D9DADBDCDDDEDF, // Range Minimum
                    0xE0E1E2E3E4E5E6E7, // Range Maximum
                    0xE8E9EAEBECEDEEEF, // Translation Offset
                    0xF0F1F2F3F4F5F6F7, // Length
                    0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                    )
                DWordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                    0xECEDEEEF,         // Granularity
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Translation Offset
                    0xFCFDFEFF,         // Length
                    0xFF, "PATHPATHPATH", )
                QWordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                    0xD8D9DADBDCDDDEDF, // Granularity
                    0xE0E1E2E3E4E5E6E7, // Range Minimum
                    0xE8E9EAEBECEDEEEF, // Range Maximum
                    0xF0F1F2F3F4F5F6F7, // Translation Offset
                    0xF8F9FAFBFCFDFEFF, // Length
                    0xFF, "PATHPATHPATH", )
                WordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                    0xF6F7,             // Granularity
                    0xF8F9,             // Range Minimum
                    0xFAFB,             // Range Maximum
                    0xFCFD,             // Translation Offset
                    0xFEFF,             // Length
                    0xFF, "PATHPATHPATH", )
            }
            StartDependentFn (0x01, 0x02)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
                Memory32 (ReadWrite,
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Alignment
                    0xFCFDFEFF,         // Length
                    )
                Memory32Fixed (ReadOnly,
                    0xF0F1F2F3,         // Address Base
                    0xF4F5F6F7,         // Address Length
                    )
            }
            StartDependentFn (0x02, 0x00)
            {
            }
            StartDependentFn (0x02, 0x01)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
                Memory32 (ReadWrite,
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Alignment
                    0xFCFDFEFF,         // Length
                    )
                Memory32Fixed (ReadOnly,
                    0xF0F1F2F3,         // Address Base
                    0xF4F5F6F7,         // Address Length
                    )
                VendorLong  ()      // Length = 0x15
                {
                    /* 0000 */  0x9F, 0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6,  // ........
                    /* 0008 */  0xF7, 0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE,  // ........
                    /* 0010 */  0xFF, 0x00, 0x01, 0x02, 0x03                     // .....
                }
            }
            StartDependentFn (0x02, 0x02)
            {
            }
            EndDependentFn ()
        }
    })
    /*
     ACPI Specification, Revision 3.0, September 2, 2004
     6.4.2.8   End Tag
     Type 0, Small Item Name 0xF, Length = 1
     The End tag identifies an end of resource data.
     Note: If the checksum field is zero, the resource data is treated as if the checksum
     operation succeeded. Configuration proceeds normally.
     Table 6-31   End Tag Definition
     Offset	Field Name
     Byte 0	Value = 01111001B (0x79) (Type = 0, small item name = 0xF, length = 1)
     Byte 1	Checksum covering all resource data after the serial identifier. This checksum is
     generated such that adding it to the sum of all the data bytes will produce a zero sum.
     The End Tag is automatically generated by the ASL compiler at the end of the ResourceTemplate
     statement.
     */
    Name (P439, Package (0x03)
    {
        Buffer (0x02)
        {
             0x79, 0x00                                       // y.
        },

        ResourceTemplate ()
        {
            IRQ (Level, ActiveHigh, Exclusive, )
                {0}
            IRQNoFlags ()
                {1}
            DMA (Compatibility, NotBusMaster, Transfer16, )
                {2}
            IO (Decode16,
                0xF0F1,             // Range Minimum
                0xF2F3,             // Range Maximum
                0xF4,               // Alignment
                0xF5,               // Length
                )
            FixedIO (
                0x03F1,             // Address
                0xF2,               // Length
                )
            VendorShort ()      // Length = 0x07
            {
                 0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
            }
            Memory24 (ReadWrite,
                0xF0F1,             // Range Minimum
                0xF2F3,             // Range Maximum
                0xF4F5,             // Alignment
                0xF6F7,             // Length
                )
            Memory32 (ReadWrite,
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Alignment
                0xFCFDFEFF,         // Length
                )
            Memory32Fixed (ReadOnly,
                0xF0F1F2F3,         // Address Base
                0xF4F5F6F7,         // Address Length
                )
            VendorLong  ()      // Length = 0x15
            {
                /* 0000 */  0x9F, 0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6,  // ........
                /* 0008 */  0xF7, 0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE,  // ........
                /* 0010 */  0xFF, 0x00, 0x01, 0x02, 0x03                     // .....
            }
            QWordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
            DWordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
            WordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0xF6F7,             // Granularity
                0xF8F9,             // Range Minimum
                0xFAFB,             // Range Maximum
                0xFCFD,             // Translation Offset
                0xFEFF,             // Length
                0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
            QWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                0xFF, "PATHPATHPATH", , AddressRangeACPI, TypeTranslation)
            DWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                0xFF, "PATHPATHPATH", , AddressRangeACPI, TypeTranslation)
            WordBusNumber (ResourceConsumer, MinFixed, MaxFixed, SubDecode,
                0xF6F7,             // Granularity
                0xF8F9,             // Range Minimum
                0xFAFB,             // Range Maximum
                0xFCFD,             // Translation Offset
                0xFEFF,             // Length
                0xFF, "PATHPATHPATH", )
            Interrupt (ResourceConsumer, Edge, ActiveLow, Shared, 0xFF, "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*", )
            {
                0x00000001,
                0x00000002,
                0x00000003,
                0x00000004,
                0x00000005,
                0x00000006,
                0x00000007,
                0x00000008,
                0x00000009,
                0x0000000A,
                0x0000000B,
                0x0000000C,
                0x0000000D,
                0x0000000E,
                0x0000000F,
                0x00000010,
                0x00000011,
                0x00000012,
                0x00000013,
                0x00000014,
                0x00000015,
                0x00000016,
                0x00000017,
                0x00000018,
                0x00000019,
                0x0000001A,
                0x0000001B,
                0x0000001C,
                0x0000001D,
                0x0000001E,
                0x0000001F,
                0x00000020,
                0x00000021,
                0x00000022,
                0x00000023,
                0x00000024,
                0x00000025,
                0x00000026,
                0x00000027,
                0x00000028,
                0x00000029,
                0x0000002A,
                0x0000002B,
                0x0000002C,
                0x0000002D,
                0x0000002E,
                0x0000002F,
                0x00000030,
                0x00000031,
                0x00000032,
                0x00000033,
                0x00000034,
                0x00000035,
                0x00000036,
                0x00000037,
                0x00000038,
                0x00000039,
                0x0000003A,
                0x0000003B,
                0x0000003C,
                0x0000003D,
                0x0000003E,
                0x0000003F,
                0x00000040,
                0x00000041,
                0x00000042,
                0x00000043,
                0x00000044,
                0x00000045,
                0x00000046,
                0x00000047,
                0x00000048,
                0x00000049,
                0x0000004A,
                0x0000004B,
                0x0000004C,
                0x0000004D,
                0x0000004E,
                0x0000004F,
                0x00000050,
                0x00000051,
                0x00000052,
                0x00000053,
                0x00000054,
                0x00000055,
                0x00000056,
                0x00000057,
                0x00000058,
                0x00000059,
                0x0000005A,
                0x0000005B,
                0x0000005C,
                0x0000005D,
                0x0000005E,
                0x0000005F,
                0x00000060,
                0x00000061,
                0x00000062,
                0x00000063,
                0x00000064,
                0x00000065,
                0x00000066,
                0x00000067,
                0x00000068,
                0x00000069,
                0x0000006A,
                0x0000006B,
                0x0000006C,
                0x0000006D,
                0x0000006E,
                0x0000006F,
                0x00000070,
                0x00000071,
                0x00000072,
                0x00000073,
                0x00000074,
                0x00000075,
                0x00000076,
                0x00000077,
                0x00000078,
                0x00000079,
                0x0000007A,
                0x0000007B,
                0x0000007C,
                0x0000007D,
                0x0000007E,
                0x0000007F,
                0x00000080,
                0x00000081,
                0x00000082,
                0x00000083,
                0x00000084,
                0x00000085,
                0x00000086,
                0x00000087,
                0x00000088,
                0x00000089,
                0x0000008A,
                0x0000008B,
                0x0000008C,
                0x0000008D,
                0x0000008E,
                0x0000008F,
                0x00000090,
                0x00000091,
                0x00000092,
                0x00000093,
                0x00000094,
                0x00000095,
                0x00000096,
                0x00000097,
                0x00000098,
                0x00000099,
                0x0000009A,
                0x0000009B,
                0x0000009C,
                0x0000009D,
                0x0000009E,
                0x0000009F,
                0x000000A0,
                0x000000A1,
                0x000000A2,
                0x000000A3,
                0x000000A4,
                0x000000A5,
                0x000000A6,
                0x000000A7,
                0x000000A8,
                0x000000A9,
                0x000000AA,
                0x000000AB,
                0x000000AC,
                0x000000AD,
                0x000000AE,
                0x000000AF,
                0x000000B0,
                0x000000B1,
                0x000000B2,
                0x000000B3,
                0x000000B4,
                0x000000B5,
                0x000000B6,
                0x000000B7,
                0x000000B8,
                0x000000B9,
                0x000000BA,
                0x000000BB,
                0x000000BC,
                0x000000BD,
                0x000000BE,
                0x000000BF,
                0x000000C0,
                0x000000C1,
                0x000000C2,
                0x000000C3,
                0x000000C4,
                0x000000C5,
                0x000000C6,
                0x000000C7,
                0x000000C8,
                0x000000C9,
                0x000000CA,
                0x000000CB,
                0x000000CC,
                0x000000CD,
                0x000000CE,
                0x000000CF,
                0x000000D0,
                0x000000D1,
                0x000000D2,
                0x000000D3,
                0x000000D4,
                0x000000D5,
                0x000000D6,
                0x000000D7,
                0x000000D8,
                0x000000D9,
                0x000000DA,
                0x000000DB,
                0x000000DC,
                0x000000DD,
                0x000000DE,
                0x000000DF,
                0x000000E0,
                0x000000E1,
                0x000000E2,
                0x000000E3,
                0x000000E4,
                0x000000E5,
                0x000000E6,
                0x000000E7,
                0x000000E8,
                0x000000E9,
                0x000000EA,
                0x000000EB,
                0x000000EC,
                0x000000ED,
                0x000000EE,
                0x000000EF,
                0x000000F0,
                0x000000F1,
                0x000000F2,
                0x000000F3,
                0x000000F4,
                0x000000F5,
                0x000000F6,
                0x000000F7,
                0x000000F8,
                0x000000F9,
                0x000000FA,
                0x000000FB,
                0x000000FC,
                0x000000FD,
                0x000000FE,
                0x000000FF,
            }
            Register (FFixedHW,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                ,)
            ExtendedIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0xD0D1D2D3D4D5D6D7, // Granularity
                0xD8D9DADBDCDDDEDF, // Range Minimum
                0xE0E1E2E3E4E5E6E7, // Range Maximum
                0xE8E9EAEBECEDEEEF, // Translation Offset
                0xF0F1F2F3F4F5F6F7, // Length
                0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                , TypeTranslation, SparseTranslation)
            ExtendedMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                0xD0D1D2D3D4D5D6D7, // Granularity
                0xD8D9DADBDCDDDEDF, // Range Minimum
                0xE0E1E2E3E4E5E6E7, // Range Maximum
                0xE8E9EAEBECEDEEEF, // Translation Offset
                0xF0F1F2F3F4F5F6F7, // Length
                0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                , AddressRangeACPI, TypeTranslation)
            ExtendedSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                0xD0D1D2D3D4D5D6D7, // Granularity
                0xD8D9DADBDCDDDEDF, // Range Minimum
                0xE0E1E2E3E4E5E6E7, // Range Maximum
                0xE8E9EAEBECEDEEEF, // Translation Offset
                0xF0F1F2F3F4F5F6F7, // Length
                0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                )
            DWordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                0xFF, "PATHPATHPATH", )
            QWordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                0xFF, "PATHPATHPATH", )
            WordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                0xF6F7,             // Granularity
                0xF8F9,             // Range Minimum
                0xFAFB,             // Range Maximum
                0xFCFD,             // Translation Offset
                0xFEFF,             // Length
                0xFF, "PATHPATHPATH", )
        },

        ResourceTemplate ()
        {
            StartDependentFnNoPri ()
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
            }
            StartDependentFnNoPri ()
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
            }
            StartDependentFn (0x00, 0x00)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
            }
            StartDependentFn (0x00, 0x01)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
            }
            StartDependentFn (0x00, 0x02)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
            }
            StartDependentFn (0x01, 0x00)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
            }
            StartDependentFn (0x01, 0x01)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
                Memory32 (ReadWrite,
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Alignment
                    0xFCFDFEFF,         // Length
                    )
            }
            StartDependentFn (0x01, 0x01)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
                Memory32 (ReadWrite,
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Alignment
                    0xFCFDFEFF,         // Length
                    )
                Memory32Fixed (ReadOnly,
                    0xF0F1F2F3,         // Address Base
                    0xF4F5F6F7,         // Address Length
                    )
                VendorLong  ()      // Length = 0x15
                {
                    /* 0000 */  0x9F, 0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6,  // ........
                    /* 0008 */  0xF7, 0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE,  // ........
                    /* 0010 */  0xFF, 0x00, 0x01, 0x02, 0x03                     // .....
                }
                QWordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                    0xD8D9DADBDCDDDEDF, // Granularity
                    0xE0E1E2E3E4E5E6E7, // Range Minimum
                    0xE8E9EAEBECEDEEEF, // Range Maximum
                    0xF0F1F2F3F4F5F6F7, // Translation Offset
                    0xF8F9FAFBFCFDFEFF, // Length
                    0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
                DWordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                    0xECEDEEEF,         // Granularity
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Translation Offset
                    0xFCFDFEFF,         // Length
                    0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
                WordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                    0xF6F7,             // Granularity
                    0xF8F9,             // Range Minimum
                    0xFAFB,             // Range Maximum
                    0xFCFD,             // Translation Offset
                    0xFEFF,             // Length
                    0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
                QWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                    0xD8D9DADBDCDDDEDF, // Granularity
                    0xE0E1E2E3E4E5E6E7, // Range Minimum
                    0xE8E9EAEBECEDEEEF, // Range Maximum
                    0xF0F1F2F3F4F5F6F7, // Translation Offset
                    0xF8F9FAFBFCFDFEFF, // Length
                    0xFF, "PATHPATHPATH", , AddressRangeACPI, TypeTranslation)
                DWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                    0xECEDEEEF,         // Granularity
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Translation Offset
                    0xFCFDFEFF,         // Length
                    0xFF, "PATHPATHPATH", , AddressRangeACPI, TypeTranslation)
                WordBusNumber (ResourceConsumer, MinFixed, MaxFixed, SubDecode,
                    0xF6F7,             // Granularity
                    0xF8F9,             // Range Minimum
                    0xFAFB,             // Range Maximum
                    0xFCFD,             // Translation Offset
                    0xFEFF,             // Length
                    0xFF, "PATHPATHPATH", )
                Interrupt (ResourceConsumer, Edge, ActiveLow, Shared, 0xFF, "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*", )
                {
                    0x00000001,
                    0x00000002,
                    0x00000003,
                    0x00000004,
                    0x00000005,
                    0x00000006,
                    0x00000007,
                    0x00000008,
                    0x00000009,
                    0x0000000A,
                    0x0000000B,
                    0x0000000C,
                    0x0000000D,
                    0x0000000E,
                    0x0000000F,
                    0x00000010,
                    0x00000011,
                    0x00000012,
                    0x00000013,
                    0x00000014,
                    0x00000015,
                    0x00000016,
                    0x00000017,
                    0x00000018,
                    0x00000019,
                    0x0000001A,
                    0x0000001B,
                    0x0000001C,
                    0x0000001D,
                    0x0000001E,
                    0x0000001F,
                    0x00000020,
                    0x00000021,
                    0x00000022,
                    0x00000023,
                    0x00000024,
                    0x00000025,
                    0x00000026,
                    0x00000027,
                    0x00000028,
                    0x00000029,
                    0x0000002A,
                    0x0000002B,
                    0x0000002C,
                    0x0000002D,
                    0x0000002E,
                    0x0000002F,
                    0x00000030,
                    0x00000031,
                    0x00000032,
                    0x00000033,
                    0x00000034,
                    0x00000035,
                    0x00000036,
                    0x00000037,
                    0x00000038,
                    0x00000039,
                    0x0000003A,
                    0x0000003B,
                    0x0000003C,
                    0x0000003D,
                    0x0000003E,
                    0x0000003F,
                    0x00000040,
                    0x00000041,
                    0x00000042,
                    0x00000043,
                    0x00000044,
                    0x00000045,
                    0x00000046,
                    0x00000047,
                    0x00000048,
                    0x00000049,
                    0x0000004A,
                    0x0000004B,
                    0x0000004C,
                    0x0000004D,
                    0x0000004E,
                    0x0000004F,
                    0x00000050,
                    0x00000051,
                    0x00000052,
                    0x00000053,
                    0x00000054,
                    0x00000055,
                    0x00000056,
                    0x00000057,
                    0x00000058,
                    0x00000059,
                    0x0000005A,
                    0x0000005B,
                    0x0000005C,
                    0x0000005D,
                    0x0000005E,
                    0x0000005F,
                    0x00000060,
                    0x00000061,
                    0x00000062,
                    0x00000063,
                    0x00000064,
                    0x00000065,
                    0x00000066,
                    0x00000067,
                    0x00000068,
                    0x00000069,
                    0x0000006A,
                    0x0000006B,
                    0x0000006C,
                    0x0000006D,
                    0x0000006E,
                    0x0000006F,
                    0x00000070,
                    0x00000071,
                    0x00000072,
                    0x00000073,
                    0x00000074,
                    0x00000075,
                    0x00000076,
                    0x00000077,
                    0x00000078,
                    0x00000079,
                    0x0000007A,
                    0x0000007B,
                    0x0000007C,
                    0x0000007D,
                    0x0000007E,
                    0x0000007F,
                    0x00000080,
                    0x00000081,
                    0x00000082,
                    0x00000083,
                    0x00000084,
                    0x00000085,
                    0x00000086,
                    0x00000087,
                    0x00000088,
                    0x00000089,
                    0x0000008A,
                    0x0000008B,
                    0x0000008C,
                    0x0000008D,
                    0x0000008E,
                    0x0000008F,
                    0x00000090,
                    0x00000091,
                    0x00000092,
                    0x00000093,
                    0x00000094,
                    0x00000095,
                    0x00000096,
                    0x00000097,
                    0x00000098,
                    0x00000099,
                    0x0000009A,
                    0x0000009B,
                    0x0000009C,
                    0x0000009D,
                    0x0000009E,
                    0x0000009F,
                    0x000000A0,
                    0x000000A1,
                    0x000000A2,
                    0x000000A3,
                    0x000000A4,
                    0x000000A5,
                    0x000000A6,
                    0x000000A7,
                    0x000000A8,
                    0x000000A9,
                    0x000000AA,
                    0x000000AB,
                    0x000000AC,
                    0x000000AD,
                    0x000000AE,
                    0x000000AF,
                    0x000000B0,
                    0x000000B1,
                    0x000000B2,
                    0x000000B3,
                    0x000000B4,
                    0x000000B5,
                    0x000000B6,
                    0x000000B7,
                    0x000000B8,
                    0x000000B9,
                    0x000000BA,
                    0x000000BB,
                    0x000000BC,
                    0x000000BD,
                    0x000000BE,
                    0x000000BF,
                    0x000000C0,
                    0x000000C1,
                    0x000000C2,
                    0x000000C3,
                    0x000000C4,
                    0x000000C5,
                    0x000000C6,
                    0x000000C7,
                    0x000000C8,
                    0x000000C9,
                    0x000000CA,
                    0x000000CB,
                    0x000000CC,
                    0x000000CD,
                    0x000000CE,
                    0x000000CF,
                    0x000000D0,
                    0x000000D1,
                    0x000000D2,
                    0x000000D3,
                    0x000000D4,
                    0x000000D5,
                    0x000000D6,
                    0x000000D7,
                    0x000000D8,
                    0x000000D9,
                    0x000000DA,
                    0x000000DB,
                    0x000000DC,
                    0x000000DD,
                    0x000000DE,
                    0x000000DF,
                    0x000000E0,
                    0x000000E1,
                    0x000000E2,
                    0x000000E3,
                    0x000000E4,
                    0x000000E5,
                    0x000000E6,
                    0x000000E7,
                    0x000000E8,
                    0x000000E9,
                    0x000000EA,
                    0x000000EB,
                    0x000000EC,
                    0x000000ED,
                    0x000000EE,
                    0x000000EF,
                    0x000000F0,
                    0x000000F1,
                    0x000000F2,
                    0x000000F3,
                    0x000000F4,
                    0x000000F5,
                    0x000000F6,
                    0x000000F7,
                    0x000000F8,
                    0x000000F9,
                    0x000000FA,
                    0x000000FB,
                    0x000000FC,
                    0x000000FD,
                    0x000000FE,
                    0x000000FF,
                }
                Register (FFixedHW,
                    0xF0,               // Bit Width
                    0xF1,               // Bit Offset
                    0xF2F3F4F5F6F7F8F9, // Address
                    ,)
                ExtendedIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                    0xD0D1D2D3D4D5D6D7, // Granularity
                    0xD8D9DADBDCDDDEDF, // Range Minimum
                    0xE0E1E2E3E4E5E6E7, // Range Maximum
                    0xE8E9EAEBECEDEEEF, // Translation Offset
                    0xF0F1F2F3F4F5F6F7, // Length
                    0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                    , TypeTranslation, SparseTranslation)
                ExtendedMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                    0xD0D1D2D3D4D5D6D7, // Granularity
                    0xD8D9DADBDCDDDEDF, // Range Minimum
                    0xE0E1E2E3E4E5E6E7, // Range Maximum
                    0xE8E9EAEBECEDEEEF, // Translation Offset
                    0xF0F1F2F3F4F5F6F7, // Length
                    0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                    , AddressRangeACPI, TypeTranslation)
                ExtendedSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                    0xD0D1D2D3D4D5D6D7, // Granularity
                    0xD8D9DADBDCDDDEDF, // Range Minimum
                    0xE0E1E2E3E4E5E6E7, // Range Maximum
                    0xE8E9EAEBECEDEEEF, // Translation Offset
                    0xF0F1F2F3F4F5F6F7, // Length
                    0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                    )
                DWordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                    0xECEDEEEF,         // Granularity
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Translation Offset
                    0xFCFDFEFF,         // Length
                    0xFF, "PATHPATHPATH", )
                QWordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                    0xD8D9DADBDCDDDEDF, // Granularity
                    0xE0E1E2E3E4E5E6E7, // Range Minimum
                    0xE8E9EAEBECEDEEEF, // Range Maximum
                    0xF0F1F2F3F4F5F6F7, // Translation Offset
                    0xF8F9FAFBFCFDFEFF, // Length
                    0xFF, "PATHPATHPATH", )
                WordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                    0xF6F7,             // Granularity
                    0xF8F9,             // Range Minimum
                    0xFAFB,             // Range Maximum
                    0xFCFD,             // Translation Offset
                    0xFEFF,             // Length
                    0xFF, "PATHPATHPATH", )
            }
            StartDependentFn (0x01, 0x02)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
                Memory32 (ReadWrite,
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Alignment
                    0xFCFDFEFF,         // Length
                    )
                Memory32Fixed (ReadOnly,
                    0xF0F1F2F3,         // Address Base
                    0xF4F5F6F7,         // Address Length
                    )
            }
            StartDependentFn (0x02, 0x00)
            {
            }
            StartDependentFn (0x02, 0x01)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
                Memory32 (ReadWrite,
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Alignment
                    0xFCFDFEFF,         // Length
                    )
                Memory32Fixed (ReadOnly,
                    0xF0F1F2F3,         // Address Base
                    0xF4F5F6F7,         // Address Length
                    )
                VendorLong  ()      // Length = 0x15
                {
                    /* 0000 */  0x9F, 0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6,  // ........
                    /* 0008 */  0xF7, 0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE,  // ........
                    /* 0010 */  0xFF, 0x00, 0x01, 0x02, 0x03                     // .....
                }
            }
            StartDependentFn (0x02, 0x02)
            {
            }
            EndDependentFn ()
        }
    })
    /* Complex test data */

    Name (P446, Package (0x02)
    {
        ResourceTemplate ()
        {
            IRQ (Level, ActiveHigh, Exclusive, )
                {0}
            IRQNoFlags ()
                {1}
            DMA (Compatibility, NotBusMaster, Transfer16, )
                {2}
            IO (Decode16,
                0xF0F1,             // Range Minimum
                0xF2F3,             // Range Maximum
                0xF4,               // Alignment
                0xF5,               // Length
                )
            FixedIO (
                0x03F1,             // Address
                0xF2,               // Length
                )
            VendorShort ()      // Length = 0x07
            {
                 0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
            }
            Memory24 (ReadWrite,
                0xF0F1,             // Range Minimum
                0xF2F3,             // Range Maximum
                0xF4F5,             // Alignment
                0xF6F7,             // Length
                )
            Memory32 (ReadWrite,
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Alignment
                0xFCFDFEFF,         // Length
                )
            Memory32Fixed (ReadOnly,
                0xF0F1F2F3,         // Address Base
                0xF4F5F6F7,         // Address Length
                )
            VendorLong  ()      // Length = 0x15
            {
                /* 0000 */  0x9F, 0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6,  // ........
                /* 0008 */  0xF7, 0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE,  // ........
                /* 0010 */  0xFF, 0x00, 0x01, 0x02, 0x03                     // .....
            }
            QWordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
            DWordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
            WordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0xF6F7,             // Granularity
                0xF8F9,             // Range Minimum
                0xFAFB,             // Range Maximum
                0xFCFD,             // Translation Offset
                0xFEFF,             // Length
                0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
            QWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                0xFF, "PATHPATHPATH", , AddressRangeACPI, TypeTranslation)
            DWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                0xFF, "PATHPATHPATH", , AddressRangeACPI, TypeTranslation)
            WordBusNumber (ResourceConsumer, MinFixed, MaxFixed, SubDecode,
                0xF6F7,             // Granularity
                0xF8F9,             // Range Minimum
                0xFAFB,             // Range Maximum
                0xFCFD,             // Translation Offset
                0xFEFF,             // Length
                0xFF, "PATHPATHPATH", )
            Interrupt (ResourceConsumer, Edge, ActiveLow, Shared, 0xFF, "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*", )
            {
                0x00000001,
                0x00000002,
                0x00000003,
                0x00000004,
                0x00000005,
                0x00000006,
                0x00000007,
                0x00000008,
                0x00000009,
                0x0000000A,
                0x0000000B,
                0x0000000C,
                0x0000000D,
                0x0000000E,
                0x0000000F,
                0x00000010,
                0x00000011,
                0x00000012,
                0x00000013,
                0x00000014,
                0x00000015,
                0x00000016,
                0x00000017,
                0x00000018,
                0x00000019,
                0x0000001A,
                0x0000001B,
                0x0000001C,
                0x0000001D,
                0x0000001E,
                0x0000001F,
                0x00000020,
                0x00000021,
                0x00000022,
                0x00000023,
                0x00000024,
                0x00000025,
                0x00000026,
                0x00000027,
                0x00000028,
                0x00000029,
                0x0000002A,
                0x0000002B,
                0x0000002C,
                0x0000002D,
                0x0000002E,
                0x0000002F,
                0x00000030,
                0x00000031,
                0x00000032,
                0x00000033,
                0x00000034,
                0x00000035,
                0x00000036,
                0x00000037,
                0x00000038,
                0x00000039,
                0x0000003A,
                0x0000003B,
                0x0000003C,
                0x0000003D,
                0x0000003E,
                0x0000003F,
                0x00000040,
                0x00000041,
                0x00000042,
                0x00000043,
                0x00000044,
                0x00000045,
                0x00000046,
                0x00000047,
                0x00000048,
                0x00000049,
                0x0000004A,
                0x0000004B,
                0x0000004C,
                0x0000004D,
                0x0000004E,
                0x0000004F,
                0x00000050,
                0x00000051,
                0x00000052,
                0x00000053,
                0x00000054,
                0x00000055,
                0x00000056,
                0x00000057,
                0x00000058,
                0x00000059,
                0x0000005A,
                0x0000005B,
                0x0000005C,
                0x0000005D,
                0x0000005E,
                0x0000005F,
                0x00000060,
                0x00000061,
                0x00000062,
                0x00000063,
                0x00000064,
                0x00000065,
                0x00000066,
                0x00000067,
                0x00000068,
                0x00000069,
                0x0000006A,
                0x0000006B,
                0x0000006C,
                0x0000006D,
                0x0000006E,
                0x0000006F,
                0x00000070,
                0x00000071,
                0x00000072,
                0x00000073,
                0x00000074,
                0x00000075,
                0x00000076,
                0x00000077,
                0x00000078,
                0x00000079,
                0x0000007A,
                0x0000007B,
                0x0000007C,
                0x0000007D,
                0x0000007E,
                0x0000007F,
                0x00000080,
                0x00000081,
                0x00000082,
                0x00000083,
                0x00000084,
                0x00000085,
                0x00000086,
                0x00000087,
                0x00000088,
                0x00000089,
                0x0000008A,
                0x0000008B,
                0x0000008C,
                0x0000008D,
                0x0000008E,
                0x0000008F,
                0x00000090,
                0x00000091,
                0x00000092,
                0x00000093,
                0x00000094,
                0x00000095,
                0x00000096,
                0x00000097,
                0x00000098,
                0x00000099,
                0x0000009A,
                0x0000009B,
                0x0000009C,
                0x0000009D,
                0x0000009E,
                0x0000009F,
                0x000000A0,
                0x000000A1,
                0x000000A2,
                0x000000A3,
                0x000000A4,
                0x000000A5,
                0x000000A6,
                0x000000A7,
                0x000000A8,
                0x000000A9,
                0x000000AA,
                0x000000AB,
                0x000000AC,
                0x000000AD,
                0x000000AE,
                0x000000AF,
                0x000000B0,
                0x000000B1,
                0x000000B2,
                0x000000B3,
                0x000000B4,
                0x000000B5,
                0x000000B6,
                0x000000B7,
                0x000000B8,
                0x000000B9,
                0x000000BA,
                0x000000BB,
                0x000000BC,
                0x000000BD,
                0x000000BE,
                0x000000BF,
                0x000000C0,
                0x000000C1,
                0x000000C2,
                0x000000C3,
                0x000000C4,
                0x000000C5,
                0x000000C6,
                0x000000C7,
                0x000000C8,
                0x000000C9,
                0x000000CA,
                0x000000CB,
                0x000000CC,
                0x000000CD,
                0x000000CE,
                0x000000CF,
                0x000000D0,
                0x000000D1,
                0x000000D2,
                0x000000D3,
                0x000000D4,
                0x000000D5,
                0x000000D6,
                0x000000D7,
                0x000000D8,
                0x000000D9,
                0x000000DA,
                0x000000DB,
                0x000000DC,
                0x000000DD,
                0x000000DE,
                0x000000DF,
                0x000000E0,
                0x000000E1,
                0x000000E2,
                0x000000E3,
                0x000000E4,
                0x000000E5,
                0x000000E6,
                0x000000E7,
                0x000000E8,
                0x000000E9,
                0x000000EA,
                0x000000EB,
                0x000000EC,
                0x000000ED,
                0x000000EE,
                0x000000EF,
                0x000000F0,
                0x000000F1,
                0x000000F2,
                0x000000F3,
                0x000000F4,
                0x000000F5,
                0x000000F6,
                0x000000F7,
                0x000000F8,
                0x000000F9,
                0x000000FA,
                0x000000FB,
                0x000000FC,
                0x000000FD,
                0x000000FE,
                0x000000FF,
            }
            Register (FFixedHW,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                ,)
            ExtendedIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0xD0D1D2D3D4D5D6D7, // Granularity
                0xD8D9DADBDCDDDEDF, // Range Minimum
                0xE0E1E2E3E4E5E6E7, // Range Maximum
                0xE8E9EAEBECEDEEEF, // Translation Offset
                0xF0F1F2F3F4F5F6F7, // Length
                0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                , TypeTranslation, SparseTranslation)
            ExtendedMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                0xD0D1D2D3D4D5D6D7, // Granularity
                0xD8D9DADBDCDDDEDF, // Range Minimum
                0xE0E1E2E3E4E5E6E7, // Range Maximum
                0xE8E9EAEBECEDEEEF, // Translation Offset
                0xF0F1F2F3F4F5F6F7, // Length
                0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                , AddressRangeACPI, TypeTranslation)
            ExtendedSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                0xD0D1D2D3D4D5D6D7, // Granularity
                0xD8D9DADBDCDDDEDF, // Range Minimum
                0xE0E1E2E3E4E5E6E7, // Range Maximum
                0xE8E9EAEBECEDEEEF, // Translation Offset
                0xF0F1F2F3F4F5F6F7, // Length
                0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                )
            DWordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                0xFF, "PATHPATHPATH", )
            QWordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                0xFF, "PATHPATHPATH", )
            WordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                0xF6F7,             // Granularity
                0xF8F9,             // Range Minimum
                0xFAFB,             // Range Maximum
                0xFCFD,             // Translation Offset
                0xFEFF,             // Length
                0xFF, "PATHPATHPATH", )
            IRQ (Level, ActiveHigh, Exclusive, )
                {0}
            IRQNoFlags ()
                {1}
            DMA (Compatibility, NotBusMaster, Transfer16, )
                {2}
            IO (Decode16,
                0xF0F1,             // Range Minimum
                0xF2F3,             // Range Maximum
                0xF4,               // Alignment
                0xF5,               // Length
                )
            FixedIO (
                0x03F1,             // Address
                0xF2,               // Length
                )
            VendorShort ()      // Length = 0x07
            {
                 0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
            }
            Memory24 (ReadWrite,
                0xF0F1,             // Range Minimum
                0xF2F3,             // Range Maximum
                0xF4F5,             // Alignment
                0xF6F7,             // Length
                )
            Memory32 (ReadWrite,
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Alignment
                0xFCFDFEFF,         // Length
                )
            Memory32Fixed (ReadOnly,
                0xF0F1F2F3,         // Address Base
                0xF4F5F6F7,         // Address Length
                )
            VendorLong  ()      // Length = 0x15
            {
                /* 0000 */  0x9F, 0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6,  // ........
                /* 0008 */  0xF7, 0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE,  // ........
                /* 0010 */  0xFF, 0x00, 0x01, 0x02, 0x03                     // .....
            }
            QWordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
            DWordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
            WordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0xF6F7,             // Granularity
                0xF8F9,             // Range Minimum
                0xFAFB,             // Range Maximum
                0xFCFD,             // Translation Offset
                0xFEFF,             // Length
                0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
            QWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                0xFF, "PATHPATHPATH", , AddressRangeACPI, TypeTranslation)
            DWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                0xFF, "PATHPATHPATH", , AddressRangeACPI, TypeTranslation)
            WordBusNumber (ResourceConsumer, MinFixed, MaxFixed, SubDecode,
                0xF6F7,             // Granularity
                0xF8F9,             // Range Minimum
                0xFAFB,             // Range Maximum
                0xFCFD,             // Translation Offset
                0xFEFF,             // Length
                0xFF, "PATHPATHPATH", )
            Interrupt (ResourceConsumer, Edge, ActiveLow, Shared, 0xFF, "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*", )
            {
                0x00000001,
                0x00000002,
                0x00000003,
                0x00000004,
                0x00000005,
                0x00000006,
                0x00000007,
                0x00000008,
                0x00000009,
                0x0000000A,
                0x0000000B,
                0x0000000C,
                0x0000000D,
                0x0000000E,
                0x0000000F,
                0x00000010,
                0x00000011,
                0x00000012,
                0x00000013,
                0x00000014,
                0x00000015,
                0x00000016,
                0x00000017,
                0x00000018,
                0x00000019,
                0x0000001A,
                0x0000001B,
                0x0000001C,
                0x0000001D,
                0x0000001E,
                0x0000001F,
                0x00000020,
                0x00000021,
                0x00000022,
                0x00000023,
                0x00000024,
                0x00000025,
                0x00000026,
                0x00000027,
                0x00000028,
                0x00000029,
                0x0000002A,
                0x0000002B,
                0x0000002C,
                0x0000002D,
                0x0000002E,
                0x0000002F,
                0x00000030,
                0x00000031,
                0x00000032,
                0x00000033,
                0x00000034,
                0x00000035,
                0x00000036,
                0x00000037,
                0x00000038,
                0x00000039,
                0x0000003A,
                0x0000003B,
                0x0000003C,
                0x0000003D,
                0x0000003E,
                0x0000003F,
                0x00000040,
                0x00000041,
                0x00000042,
                0x00000043,
                0x00000044,
                0x00000045,
                0x00000046,
                0x00000047,
                0x00000048,
                0x00000049,
                0x0000004A,
                0x0000004B,
                0x0000004C,
                0x0000004D,
                0x0000004E,
                0x0000004F,
                0x00000050,
                0x00000051,
                0x00000052,
                0x00000053,
                0x00000054,
                0x00000055,
                0x00000056,
                0x00000057,
                0x00000058,
                0x00000059,
                0x0000005A,
                0x0000005B,
                0x0000005C,
                0x0000005D,
                0x0000005E,
                0x0000005F,
                0x00000060,
                0x00000061,
                0x00000062,
                0x00000063,
                0x00000064,
                0x00000065,
                0x00000066,
                0x00000067,
                0x00000068,
                0x00000069,
                0x0000006A,
                0x0000006B,
                0x0000006C,
                0x0000006D,
                0x0000006E,
                0x0000006F,
                0x00000070,
                0x00000071,
                0x00000072,
                0x00000073,
                0x00000074,
                0x00000075,
                0x00000076,
                0x00000077,
                0x00000078,
                0x00000079,
                0x0000007A,
                0x0000007B,
                0x0000007C,
                0x0000007D,
                0x0000007E,
                0x0000007F,
                0x00000080,
                0x00000081,
                0x00000082,
                0x00000083,
                0x00000084,
                0x00000085,
                0x00000086,
                0x00000087,
                0x00000088,
                0x00000089,
                0x0000008A,
                0x0000008B,
                0x0000008C,
                0x0000008D,
                0x0000008E,
                0x0000008F,
                0x00000090,
                0x00000091,
                0x00000092,
                0x00000093,
                0x00000094,
                0x00000095,
                0x00000096,
                0x00000097,
                0x00000098,
                0x00000099,
                0x0000009A,
                0x0000009B,
                0x0000009C,
                0x0000009D,
                0x0000009E,
                0x0000009F,
                0x000000A0,
                0x000000A1,
                0x000000A2,
                0x000000A3,
                0x000000A4,
                0x000000A5,
                0x000000A6,
                0x000000A7,
                0x000000A8,
                0x000000A9,
                0x000000AA,
                0x000000AB,
                0x000000AC,
                0x000000AD,
                0x000000AE,
                0x000000AF,
                0x000000B0,
                0x000000B1,
                0x000000B2,
                0x000000B3,
                0x000000B4,
                0x000000B5,
                0x000000B6,
                0x000000B7,
                0x000000B8,
                0x000000B9,
                0x000000BA,
                0x000000BB,
                0x000000BC,
                0x000000BD,
                0x000000BE,
                0x000000BF,
                0x000000C0,
                0x000000C1,
                0x000000C2,
                0x000000C3,
                0x000000C4,
                0x000000C5,
                0x000000C6,
                0x000000C7,
                0x000000C8,
                0x000000C9,
                0x000000CA,
                0x000000CB,
                0x000000CC,
                0x000000CD,
                0x000000CE,
                0x000000CF,
                0x000000D0,
                0x000000D1,
                0x000000D2,
                0x000000D3,
                0x000000D4,
                0x000000D5,
                0x000000D6,
                0x000000D7,
                0x000000D8,
                0x000000D9,
                0x000000DA,
                0x000000DB,
                0x000000DC,
                0x000000DD,
                0x000000DE,
                0x000000DF,
                0x000000E0,
                0x000000E1,
                0x000000E2,
                0x000000E3,
                0x000000E4,
                0x000000E5,
                0x000000E6,
                0x000000E7,
                0x000000E8,
                0x000000E9,
                0x000000EA,
                0x000000EB,
                0x000000EC,
                0x000000ED,
                0x000000EE,
                0x000000EF,
                0x000000F0,
                0x000000F1,
                0x000000F2,
                0x000000F3,
                0x000000F4,
                0x000000F5,
                0x000000F6,
                0x000000F7,
                0x000000F8,
                0x000000F9,
                0x000000FA,
                0x000000FB,
                0x000000FC,
                0x000000FD,
                0x000000FE,
                0x000000FF,
            }
            Register (FFixedHW,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                ,)
            ExtendedIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0xD0D1D2D3D4D5D6D7, // Granularity
                0xD8D9DADBDCDDDEDF, // Range Minimum
                0xE0E1E2E3E4E5E6E7, // Range Maximum
                0xE8E9EAEBECEDEEEF, // Translation Offset
                0xF0F1F2F3F4F5F6F7, // Length
                0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                , TypeTranslation, SparseTranslation)
            ExtendedMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                0xD0D1D2D3D4D5D6D7, // Granularity
                0xD8D9DADBDCDDDEDF, // Range Minimum
                0xE0E1E2E3E4E5E6E7, // Range Maximum
                0xE8E9EAEBECEDEEEF, // Translation Offset
                0xF0F1F2F3F4F5F6F7, // Length
                0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                , AddressRangeACPI, TypeTranslation)
            ExtendedSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                0xD0D1D2D3D4D5D6D7, // Granularity
                0xD8D9DADBDCDDDEDF, // Range Minimum
                0xE0E1E2E3E4E5E6E7, // Range Maximum
                0xE8E9EAEBECEDEEEF, // Translation Offset
                0xF0F1F2F3F4F5F6F7, // Length
                0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                )
            DWordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                0xFF, "PATHPATHPATH", )
            QWordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                0xFF, "PATHPATHPATH", )
            WordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                0xF6F7,             // Granularity
                0xF8F9,             // Range Minimum
                0xFAFB,             // Range Maximum
                0xFCFD,             // Translation Offset
                0xFEFF,             // Length
                0xFF, "PATHPATHPATH", )
        },

        ResourceTemplate ()
        {
            StartDependentFnNoPri ()
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
            }
            StartDependentFnNoPri ()
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
            }
            StartDependentFn (0x00, 0x00)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
            }
            StartDependentFn (0x00, 0x01)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
            }
            StartDependentFn (0x00, 0x02)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
            }
            StartDependentFn (0x01, 0x00)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
            }
            StartDependentFn (0x01, 0x01)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
                Memory32 (ReadWrite,
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Alignment
                    0xFCFDFEFF,         // Length
                    )
            }
            StartDependentFn (0x01, 0x01)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
                Memory32 (ReadWrite,
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Alignment
                    0xFCFDFEFF,         // Length
                    )
                Memory32Fixed (ReadOnly,
                    0xF0F1F2F3,         // Address Base
                    0xF4F5F6F7,         // Address Length
                    )
                VendorLong  ()      // Length = 0x15
                {
                    /* 0000 */  0x9F, 0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6,  // ........
                    /* 0008 */  0xF7, 0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE,  // ........
                    /* 0010 */  0xFF, 0x00, 0x01, 0x02, 0x03                     // .....
                }
                QWordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                    0xD8D9DADBDCDDDEDF, // Granularity
                    0xE0E1E2E3E4E5E6E7, // Range Minimum
                    0xE8E9EAEBECEDEEEF, // Range Maximum
                    0xF0F1F2F3F4F5F6F7, // Translation Offset
                    0xF8F9FAFBFCFDFEFF, // Length
                    0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
                DWordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                    0xECEDEEEF,         // Granularity
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Translation Offset
                    0xFCFDFEFF,         // Length
                    0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
                WordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                    0xF6F7,             // Granularity
                    0xF8F9,             // Range Minimum
                    0xFAFB,             // Range Maximum
                    0xFCFD,             // Translation Offset
                    0xFEFF,             // Length
                    0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
                QWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                    0xD8D9DADBDCDDDEDF, // Granularity
                    0xE0E1E2E3E4E5E6E7, // Range Minimum
                    0xE8E9EAEBECEDEEEF, // Range Maximum
                    0xF0F1F2F3F4F5F6F7, // Translation Offset
                    0xF8F9FAFBFCFDFEFF, // Length
                    0xFF, "PATHPATHPATH", , AddressRangeACPI, TypeTranslation)
                DWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                    0xECEDEEEF,         // Granularity
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Translation Offset
                    0xFCFDFEFF,         // Length
                    0xFF, "PATHPATHPATH", , AddressRangeACPI, TypeTranslation)
                WordBusNumber (ResourceConsumer, MinFixed, MaxFixed, SubDecode,
                    0xF6F7,             // Granularity
                    0xF8F9,             // Range Minimum
                    0xFAFB,             // Range Maximum
                    0xFCFD,             // Translation Offset
                    0xFEFF,             // Length
                    0xFF, "PATHPATHPATH", )
                Interrupt (ResourceConsumer, Edge, ActiveLow, Shared, 0xFF, "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*", )
                {
                    0x00000001,
                    0x00000002,
                    0x00000003,
                    0x00000004,
                    0x00000005,
                    0x00000006,
                    0x00000007,
                    0x00000008,
                    0x00000009,
                    0x0000000A,
                    0x0000000B,
                    0x0000000C,
                    0x0000000D,
                    0x0000000E,
                    0x0000000F,
                    0x00000010,
                    0x00000011,
                    0x00000012,
                    0x00000013,
                    0x00000014,
                    0x00000015,
                    0x00000016,
                    0x00000017,
                    0x00000018,
                    0x00000019,
                    0x0000001A,
                    0x0000001B,
                    0x0000001C,
                    0x0000001D,
                    0x0000001E,
                    0x0000001F,
                    0x00000020,
                    0x00000021,
                    0x00000022,
                    0x00000023,
                    0x00000024,
                    0x00000025,
                    0x00000026,
                    0x00000027,
                    0x00000028,
                    0x00000029,
                    0x0000002A,
                    0x0000002B,
                    0x0000002C,
                    0x0000002D,
                    0x0000002E,
                    0x0000002F,
                    0x00000030,
                    0x00000031,
                    0x00000032,
                    0x00000033,
                    0x00000034,
                    0x00000035,
                    0x00000036,
                    0x00000037,
                    0x00000038,
                    0x00000039,
                    0x0000003A,
                    0x0000003B,
                    0x0000003C,
                    0x0000003D,
                    0x0000003E,
                    0x0000003F,
                    0x00000040,
                    0x00000041,
                    0x00000042,
                    0x00000043,
                    0x00000044,
                    0x00000045,
                    0x00000046,
                    0x00000047,
                    0x00000048,
                    0x00000049,
                    0x0000004A,
                    0x0000004B,
                    0x0000004C,
                    0x0000004D,
                    0x0000004E,
                    0x0000004F,
                    0x00000050,
                    0x00000051,
                    0x00000052,
                    0x00000053,
                    0x00000054,
                    0x00000055,
                    0x00000056,
                    0x00000057,
                    0x00000058,
                    0x00000059,
                    0x0000005A,
                    0x0000005B,
                    0x0000005C,
                    0x0000005D,
                    0x0000005E,
                    0x0000005F,
                    0x00000060,
                    0x00000061,
                    0x00000062,
                    0x00000063,
                    0x00000064,
                    0x00000065,
                    0x00000066,
                    0x00000067,
                    0x00000068,
                    0x00000069,
                    0x0000006A,
                    0x0000006B,
                    0x0000006C,
                    0x0000006D,
                    0x0000006E,
                    0x0000006F,
                    0x00000070,
                    0x00000071,
                    0x00000072,
                    0x00000073,
                    0x00000074,
                    0x00000075,
                    0x00000076,
                    0x00000077,
                    0x00000078,
                    0x00000079,
                    0x0000007A,
                    0x0000007B,
                    0x0000007C,
                    0x0000007D,
                    0x0000007E,
                    0x0000007F,
                    0x00000080,
                    0x00000081,
                    0x00000082,
                    0x00000083,
                    0x00000084,
                    0x00000085,
                    0x00000086,
                    0x00000087,
                    0x00000088,
                    0x00000089,
                    0x0000008A,
                    0x0000008B,
                    0x0000008C,
                    0x0000008D,
                    0x0000008E,
                    0x0000008F,
                    0x00000090,
                    0x00000091,
                    0x00000092,
                    0x00000093,
                    0x00000094,
                    0x00000095,
                    0x00000096,
                    0x00000097,
                    0x00000098,
                    0x00000099,
                    0x0000009A,
                    0x0000009B,
                    0x0000009C,
                    0x0000009D,
                    0x0000009E,
                    0x0000009F,
                    0x000000A0,
                    0x000000A1,
                    0x000000A2,
                    0x000000A3,
                    0x000000A4,
                    0x000000A5,
                    0x000000A6,
                    0x000000A7,
                    0x000000A8,
                    0x000000A9,
                    0x000000AA,
                    0x000000AB,
                    0x000000AC,
                    0x000000AD,
                    0x000000AE,
                    0x000000AF,
                    0x000000B0,
                    0x000000B1,
                    0x000000B2,
                    0x000000B3,
                    0x000000B4,
                    0x000000B5,
                    0x000000B6,
                    0x000000B7,
                    0x000000B8,
                    0x000000B9,
                    0x000000BA,
                    0x000000BB,
                    0x000000BC,
                    0x000000BD,
                    0x000000BE,
                    0x000000BF,
                    0x000000C0,
                    0x000000C1,
                    0x000000C2,
                    0x000000C3,
                    0x000000C4,
                    0x000000C5,
                    0x000000C6,
                    0x000000C7,
                    0x000000C8,
                    0x000000C9,
                    0x000000CA,
                    0x000000CB,
                    0x000000CC,
                    0x000000CD,
                    0x000000CE,
                    0x000000CF,
                    0x000000D0,
                    0x000000D1,
                    0x000000D2,
                    0x000000D3,
                    0x000000D4,
                    0x000000D5,
                    0x000000D6,
                    0x000000D7,
                    0x000000D8,
                    0x000000D9,
                    0x000000DA,
                    0x000000DB,
                    0x000000DC,
                    0x000000DD,
                    0x000000DE,
                    0x000000DF,
                    0x000000E0,
                    0x000000E1,
                    0x000000E2,
                    0x000000E3,
                    0x000000E4,
                    0x000000E5,
                    0x000000E6,
                    0x000000E7,
                    0x000000E8,
                    0x000000E9,
                    0x000000EA,
                    0x000000EB,
                    0x000000EC,
                    0x000000ED,
                    0x000000EE,
                    0x000000EF,
                    0x000000F0,
                    0x000000F1,
                    0x000000F2,
                    0x000000F3,
                    0x000000F4,
                    0x000000F5,
                    0x000000F6,
                    0x000000F7,
                    0x000000F8,
                    0x000000F9,
                    0x000000FA,
                    0x000000FB,
                    0x000000FC,
                    0x000000FD,
                    0x000000FE,
                    0x000000FF,
                }
                Register (FFixedHW,
                    0xF0,               // Bit Width
                    0xF1,               // Bit Offset
                    0xF2F3F4F5F6F7F8F9, // Address
                    ,)
                ExtendedIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                    0xD0D1D2D3D4D5D6D7, // Granularity
                    0xD8D9DADBDCDDDEDF, // Range Minimum
                    0xE0E1E2E3E4E5E6E7, // Range Maximum
                    0xE8E9EAEBECEDEEEF, // Translation Offset
                    0xF0F1F2F3F4F5F6F7, // Length
                    0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                    , TypeTranslation, SparseTranslation)
                ExtendedMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                    0xD0D1D2D3D4D5D6D7, // Granularity
                    0xD8D9DADBDCDDDEDF, // Range Minimum
                    0xE0E1E2E3E4E5E6E7, // Range Maximum
                    0xE8E9EAEBECEDEEEF, // Translation Offset
                    0xF0F1F2F3F4F5F6F7, // Length
                    0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                    , AddressRangeACPI, TypeTranslation)
                ExtendedSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                    0xD0D1D2D3D4D5D6D7, // Granularity
                    0xD8D9DADBDCDDDEDF, // Range Minimum
                    0xE0E1E2E3E4E5E6E7, // Range Maximum
                    0xE8E9EAEBECEDEEEF, // Translation Offset
                    0xF0F1F2F3F4F5F6F7, // Length
                    0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                    )
                DWordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                    0xECEDEEEF,         // Granularity
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Translation Offset
                    0xFCFDFEFF,         // Length
                    0xFF, "PATHPATHPATH", )
                QWordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                    0xD8D9DADBDCDDDEDF, // Granularity
                    0xE0E1E2E3E4E5E6E7, // Range Minimum
                    0xE8E9EAEBECEDEEEF, // Range Maximum
                    0xF0F1F2F3F4F5F6F7, // Translation Offset
                    0xF8F9FAFBFCFDFEFF, // Length
                    0xFF, "PATHPATHPATH", )
                WordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                    0xF6F7,             // Granularity
                    0xF8F9,             // Range Minimum
                    0xFAFB,             // Range Maximum
                    0xFCFD,             // Translation Offset
                    0xFEFF,             // Length
                    0xFF, "PATHPATHPATH", )
            }
            StartDependentFn (0x01, 0x02)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
                Memory32 (ReadWrite,
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Alignment
                    0xFCFDFEFF,         // Length
                    )
                Memory32Fixed (ReadOnly,
                    0xF0F1F2F3,         // Address Base
                    0xF4F5F6F7,         // Address Length
                    )
            }
            StartDependentFn (0x02, 0x00)
            {
            }
            StartDependentFn (0x02, 0x01)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
                Memory32 (ReadWrite,
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Alignment
                    0xFCFDFEFF,         // Length
                    )
                Memory32Fixed (ReadOnly,
                    0xF0F1F2F3,         // Address Base
                    0xF4F5F6F7,         // Address Length
                    )
                VendorLong  ()      // Length = 0x15
                {
                    /* 0000 */  0x9F, 0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6,  // ........
                    /* 0008 */  0xF7, 0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE,  // ........
                    /* 0010 */  0xFF, 0x00, 0x01, 0x02, 0x03                     // .....
                }
            }
            StartDependentFn (0x02, 0x02)
            {
            }
            EndDependentFn ()
            StartDependentFnNoPri ()
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
            }
            StartDependentFnNoPri ()
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
            }
            StartDependentFn (0x00, 0x00)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
            }
            StartDependentFn (0x00, 0x01)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
            }
            StartDependentFn (0x00, 0x02)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
            }
            StartDependentFn (0x01, 0x00)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
            }
            StartDependentFn (0x01, 0x01)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
                Memory32 (ReadWrite,
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Alignment
                    0xFCFDFEFF,         // Length
                    )
            }
            StartDependentFn (0x01, 0x01)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
                Memory32 (ReadWrite,
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Alignment
                    0xFCFDFEFF,         // Length
                    )
                Memory32Fixed (ReadOnly,
                    0xF0F1F2F3,         // Address Base
                    0xF4F5F6F7,         // Address Length
                    )
                VendorLong  ()      // Length = 0x15
                {
                    /* 0000 */  0x9F, 0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6,  // ........
                    /* 0008 */  0xF7, 0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE,  // ........
                    /* 0010 */  0xFF, 0x00, 0x01, 0x02, 0x03                     // .....
                }
                QWordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                    0xD8D9DADBDCDDDEDF, // Granularity
                    0xE0E1E2E3E4E5E6E7, // Range Minimum
                    0xE8E9EAEBECEDEEEF, // Range Maximum
                    0xF0F1F2F3F4F5F6F7, // Translation Offset
                    0xF8F9FAFBFCFDFEFF, // Length
                    0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
                DWordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                    0xECEDEEEF,         // Granularity
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Translation Offset
                    0xFCFDFEFF,         // Length
                    0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
                WordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                    0xF6F7,             // Granularity
                    0xF8F9,             // Range Minimum
                    0xFAFB,             // Range Maximum
                    0xFCFD,             // Translation Offset
                    0xFEFF,             // Length
                    0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
                QWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                    0xD8D9DADBDCDDDEDF, // Granularity
                    0xE0E1E2E3E4E5E6E7, // Range Minimum
                    0xE8E9EAEBECEDEEEF, // Range Maximum
                    0xF0F1F2F3F4F5F6F7, // Translation Offset
                    0xF8F9FAFBFCFDFEFF, // Length
                    0xFF, "PATHPATHPATH", , AddressRangeACPI, TypeTranslation)
                DWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                    0xECEDEEEF,         // Granularity
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Translation Offset
                    0xFCFDFEFF,         // Length
                    0xFF, "PATHPATHPATH", , AddressRangeACPI, TypeTranslation)
                WordBusNumber (ResourceConsumer, MinFixed, MaxFixed, SubDecode,
                    0xF6F7,             // Granularity
                    0xF8F9,             // Range Minimum
                    0xFAFB,             // Range Maximum
                    0xFCFD,             // Translation Offset
                    0xFEFF,             // Length
                    0xFF, "PATHPATHPATH", )
                Interrupt (ResourceConsumer, Edge, ActiveLow, Shared, 0xFF, "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*", )
                {
                    0x00000001,
                    0x00000002,
                    0x00000003,
                    0x00000004,
                    0x00000005,
                    0x00000006,
                    0x00000007,
                    0x00000008,
                    0x00000009,
                    0x0000000A,
                    0x0000000B,
                    0x0000000C,
                    0x0000000D,
                    0x0000000E,
                    0x0000000F,
                    0x00000010,
                    0x00000011,
                    0x00000012,
                    0x00000013,
                    0x00000014,
                    0x00000015,
                    0x00000016,
                    0x00000017,
                    0x00000018,
                    0x00000019,
                    0x0000001A,
                    0x0000001B,
                    0x0000001C,
                    0x0000001D,
                    0x0000001E,
                    0x0000001F,
                    0x00000020,
                    0x00000021,
                    0x00000022,
                    0x00000023,
                    0x00000024,
                    0x00000025,
                    0x00000026,
                    0x00000027,
                    0x00000028,
                    0x00000029,
                    0x0000002A,
                    0x0000002B,
                    0x0000002C,
                    0x0000002D,
                    0x0000002E,
                    0x0000002F,
                    0x00000030,
                    0x00000031,
                    0x00000032,
                    0x00000033,
                    0x00000034,
                    0x00000035,
                    0x00000036,
                    0x00000037,
                    0x00000038,
                    0x00000039,
                    0x0000003A,
                    0x0000003B,
                    0x0000003C,
                    0x0000003D,
                    0x0000003E,
                    0x0000003F,
                    0x00000040,
                    0x00000041,
                    0x00000042,
                    0x00000043,
                    0x00000044,
                    0x00000045,
                    0x00000046,
                    0x00000047,
                    0x00000048,
                    0x00000049,
                    0x0000004A,
                    0x0000004B,
                    0x0000004C,
                    0x0000004D,
                    0x0000004E,
                    0x0000004F,
                    0x00000050,
                    0x00000051,
                    0x00000052,
                    0x00000053,
                    0x00000054,
                    0x00000055,
                    0x00000056,
                    0x00000057,
                    0x00000058,
                    0x00000059,
                    0x0000005A,
                    0x0000005B,
                    0x0000005C,
                    0x0000005D,
                    0x0000005E,
                    0x0000005F,
                    0x00000060,
                    0x00000061,
                    0x00000062,
                    0x00000063,
                    0x00000064,
                    0x00000065,
                    0x00000066,
                    0x00000067,
                    0x00000068,
                    0x00000069,
                    0x0000006A,
                    0x0000006B,
                    0x0000006C,
                    0x0000006D,
                    0x0000006E,
                    0x0000006F,
                    0x00000070,
                    0x00000071,
                    0x00000072,
                    0x00000073,
                    0x00000074,
                    0x00000075,
                    0x00000076,
                    0x00000077,
                    0x00000078,
                    0x00000079,
                    0x0000007A,
                    0x0000007B,
                    0x0000007C,
                    0x0000007D,
                    0x0000007E,
                    0x0000007F,
                    0x00000080,
                    0x00000081,
                    0x00000082,
                    0x00000083,
                    0x00000084,
                    0x00000085,
                    0x00000086,
                    0x00000087,
                    0x00000088,
                    0x00000089,
                    0x0000008A,
                    0x0000008B,
                    0x0000008C,
                    0x0000008D,
                    0x0000008E,
                    0x0000008F,
                    0x00000090,
                    0x00000091,
                    0x00000092,
                    0x00000093,
                    0x00000094,
                    0x00000095,
                    0x00000096,
                    0x00000097,
                    0x00000098,
                    0x00000099,
                    0x0000009A,
                    0x0000009B,
                    0x0000009C,
                    0x0000009D,
                    0x0000009E,
                    0x0000009F,
                    0x000000A0,
                    0x000000A1,
                    0x000000A2,
                    0x000000A3,
                    0x000000A4,
                    0x000000A5,
                    0x000000A6,
                    0x000000A7,
                    0x000000A8,
                    0x000000A9,
                    0x000000AA,
                    0x000000AB,
                    0x000000AC,
                    0x000000AD,
                    0x000000AE,
                    0x000000AF,
                    0x000000B0,
                    0x000000B1,
                    0x000000B2,
                    0x000000B3,
                    0x000000B4,
                    0x000000B5,
                    0x000000B6,
                    0x000000B7,
                    0x000000B8,
                    0x000000B9,
                    0x000000BA,
                    0x000000BB,
                    0x000000BC,
                    0x000000BD,
                    0x000000BE,
                    0x000000BF,
                    0x000000C0,
                    0x000000C1,
                    0x000000C2,
                    0x000000C3,
                    0x000000C4,
                    0x000000C5,
                    0x000000C6,
                    0x000000C7,
                    0x000000C8,
                    0x000000C9,
                    0x000000CA,
                    0x000000CB,
                    0x000000CC,
                    0x000000CD,
                    0x000000CE,
                    0x000000CF,
                    0x000000D0,
                    0x000000D1,
                    0x000000D2,
                    0x000000D3,
                    0x000000D4,
                    0x000000D5,
                    0x000000D6,
                    0x000000D7,
                    0x000000D8,
                    0x000000D9,
                    0x000000DA,
                    0x000000DB,
                    0x000000DC,
                    0x000000DD,
                    0x000000DE,
                    0x000000DF,
                    0x000000E0,
                    0x000000E1,
                    0x000000E2,
                    0x000000E3,
                    0x000000E4,
                    0x000000E5,
                    0x000000E6,
                    0x000000E7,
                    0x000000E8,
                    0x000000E9,
                    0x000000EA,
                    0x000000EB,
                    0x000000EC,
                    0x000000ED,
                    0x000000EE,
                    0x000000EF,
                    0x000000F0,
                    0x000000F1,
                    0x000000F2,
                    0x000000F3,
                    0x000000F4,
                    0x000000F5,
                    0x000000F6,
                    0x000000F7,
                    0x000000F8,
                    0x000000F9,
                    0x000000FA,
                    0x000000FB,
                    0x000000FC,
                    0x000000FD,
                    0x000000FE,
                    0x000000FF,
                }
                Register (FFixedHW,
                    0xF0,               // Bit Width
                    0xF1,               // Bit Offset
                    0xF2F3F4F5F6F7F8F9, // Address
                    ,)
                ExtendedIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                    0xD0D1D2D3D4D5D6D7, // Granularity
                    0xD8D9DADBDCDDDEDF, // Range Minimum
                    0xE0E1E2E3E4E5E6E7, // Range Maximum
                    0xE8E9EAEBECEDEEEF, // Translation Offset
                    0xF0F1F2F3F4F5F6F7, // Length
                    0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                    , TypeTranslation, SparseTranslation)
                ExtendedMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                    0xD0D1D2D3D4D5D6D7, // Granularity
                    0xD8D9DADBDCDDDEDF, // Range Minimum
                    0xE0E1E2E3E4E5E6E7, // Range Maximum
                    0xE8E9EAEBECEDEEEF, // Translation Offset
                    0xF0F1F2F3F4F5F6F7, // Length
                    0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                    , AddressRangeACPI, TypeTranslation)
                ExtendedSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                    0xD0D1D2D3D4D5D6D7, // Granularity
                    0xD8D9DADBDCDDDEDF, // Range Minimum
                    0xE0E1E2E3E4E5E6E7, // Range Maximum
                    0xE8E9EAEBECEDEEEF, // Translation Offset
                    0xF0F1F2F3F4F5F6F7, // Length
                    0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                    )
                DWordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                    0xECEDEEEF,         // Granularity
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Translation Offset
                    0xFCFDFEFF,         // Length
                    0xFF, "PATHPATHPATH", )
                QWordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                    0xD8D9DADBDCDDDEDF, // Granularity
                    0xE0E1E2E3E4E5E6E7, // Range Minimum
                    0xE8E9EAEBECEDEEEF, // Range Maximum
                    0xF0F1F2F3F4F5F6F7, // Translation Offset
                    0xF8F9FAFBFCFDFEFF, // Length
                    0xFF, "PATHPATHPATH", )
                WordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                    0xF6F7,             // Granularity
                    0xF8F9,             // Range Minimum
                    0xFAFB,             // Range Maximum
                    0xFCFD,             // Translation Offset
                    0xFEFF,             // Length
                    0xFF, "PATHPATHPATH", )
            }
            StartDependentFn (0x01, 0x02)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
                Memory32 (ReadWrite,
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Alignment
                    0xFCFDFEFF,         // Length
                    )
                Memory32Fixed (ReadOnly,
                    0xF0F1F2F3,         // Address Base
                    0xF4F5F6F7,         // Address Length
                    )
            }
            StartDependentFn (0x02, 0x00)
            {
            }
            StartDependentFn (0x02, 0x01)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
                Memory32 (ReadWrite,
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Alignment
                    0xFCFDFEFF,         // Length
                    )
                Memory32Fixed (ReadOnly,
                    0xF0F1F2F3,         // Address Base
                    0xF4F5F6F7,         // Address Length
                    )
                VendorLong  ()      // Length = 0x15
                {
                    /* 0000 */  0x9F, 0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6,  // ........
                    /* 0008 */  0xF7, 0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE,  // ........
                    /* 0010 */  0xFF, 0x00, 0x01, 0x02, 0x03                     // .....
                }
            }
            StartDependentFn (0x02, 0x02)
            {
            }
            EndDependentFn ()
        }
    })
    Method (RT1A, 0, Serialized)
    {
        /* Emit test header, set the filename */

        THDR (__METHOD__, "Resource To Buffer Conversion Macro", "resourcetemplate.asl")
        /* Main test case for packages above */

        M330 (__METHOD__, 0x03, "p438", P438, P439)
    }

    Method (RT1C, 0, Serialized)
    {
        /* Emit test header, set the filename */

        THDR (__METHOD__, "Resource Conversion Macros complex test", "resourcetemplate.asl")
        Name (RT00, ResourceTemplate ()
        {
            IRQ (Level, ActiveHigh, Exclusive, )
                {0}
            IRQNoFlags ()
                {1}
            DMA (Compatibility, NotBusMaster, Transfer16, )
                {2}
            IO (Decode16,
                0xF0F1,             // Range Minimum
                0xF2F3,             // Range Maximum
                0xF4,               // Alignment
                0xF5,               // Length
                )
            FixedIO (
                0x03F1,             // Address
                0xF2,               // Length
                )
            VendorShort ()      // Length = 0x07
            {
                 0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
            }
            Memory24 (ReadWrite,
                0xF0F1,             // Range Minimum
                0xF2F3,             // Range Maximum
                0xF4F5,             // Alignment
                0xF6F7,             // Length
                )
            Memory32 (ReadWrite,
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Alignment
                0xFCFDFEFF,         // Length
                )
            Memory32Fixed (ReadOnly,
                0xF0F1F2F3,         // Address Base
                0xF4F5F6F7,         // Address Length
                )
            VendorLong  ()      // Length = 0x15
            {
                /* 0000 */  0x9F, 0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6,  // ........
                /* 0008 */  0xF7, 0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE,  // ........
                /* 0010 */  0xFF, 0x00, 0x01, 0x02, 0x03                     // .....
            }
            QWordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
            DWordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
            WordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0xF6F7,             // Granularity
                0xF8F9,             // Range Minimum
                0xFAFB,             // Range Maximum
                0xFCFD,             // Translation Offset
                0xFEFF,             // Length
                0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
            QWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                0xFF, "PATHPATHPATH", , AddressRangeACPI, TypeTranslation)
            DWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                0xFF, "PATHPATHPATH", , AddressRangeACPI, TypeTranslation)
            WordBusNumber (ResourceConsumer, MinFixed, MaxFixed, SubDecode,
                0xF6F7,             // Granularity
                0xF8F9,             // Range Minimum
                0xFAFB,             // Range Maximum
                0xFCFD,             // Translation Offset
                0xFEFF,             // Length
                0xFF, "PATHPATHPATH", )
            Interrupt (ResourceConsumer, Edge, ActiveLow, Shared, 0xFF, "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*", )
            {
                0x00000001,
                0x00000002,
                0x00000003,
                0x00000004,
                0x00000005,
                0x00000006,
                0x00000007,
                0x00000008,
                0x00000009,
                0x0000000A,
                0x0000000B,
                0x0000000C,
                0x0000000D,
                0x0000000E,
                0x0000000F,
                0x00000010,
                0x00000011,
                0x00000012,
                0x00000013,
                0x00000014,
                0x00000015,
                0x00000016,
                0x00000017,
                0x00000018,
                0x00000019,
                0x0000001A,
                0x0000001B,
                0x0000001C,
                0x0000001D,
                0x0000001E,
                0x0000001F,
                0x00000020,
                0x00000021,
                0x00000022,
                0x00000023,
                0x00000024,
                0x00000025,
                0x00000026,
                0x00000027,
                0x00000028,
                0x00000029,
                0x0000002A,
                0x0000002B,
                0x0000002C,
                0x0000002D,
                0x0000002E,
                0x0000002F,
                0x00000030,
                0x00000031,
                0x00000032,
                0x00000033,
                0x00000034,
                0x00000035,
                0x00000036,
                0x00000037,
                0x00000038,
                0x00000039,
                0x0000003A,
                0x0000003B,
                0x0000003C,
                0x0000003D,
                0x0000003E,
                0x0000003F,
                0x00000040,
                0x00000041,
                0x00000042,
                0x00000043,
                0x00000044,
                0x00000045,
                0x00000046,
                0x00000047,
                0x00000048,
                0x00000049,
                0x0000004A,
                0x0000004B,
                0x0000004C,
                0x0000004D,
                0x0000004E,
                0x0000004F,
                0x00000050,
                0x00000051,
                0x00000052,
                0x00000053,
                0x00000054,
                0x00000055,
                0x00000056,
                0x00000057,
                0x00000058,
                0x00000059,
                0x0000005A,
                0x0000005B,
                0x0000005C,
                0x0000005D,
                0x0000005E,
                0x0000005F,
                0x00000060,
                0x00000061,
                0x00000062,
                0x00000063,
                0x00000064,
                0x00000065,
                0x00000066,
                0x00000067,
                0x00000068,
                0x00000069,
                0x0000006A,
                0x0000006B,
                0x0000006C,
                0x0000006D,
                0x0000006E,
                0x0000006F,
                0x00000070,
                0x00000071,
                0x00000072,
                0x00000073,
                0x00000074,
                0x00000075,
                0x00000076,
                0x00000077,
                0x00000078,
                0x00000079,
                0x0000007A,
                0x0000007B,
                0x0000007C,
                0x0000007D,
                0x0000007E,
                0x0000007F,
                0x00000080,
                0x00000081,
                0x00000082,
                0x00000083,
                0x00000084,
                0x00000085,
                0x00000086,
                0x00000087,
                0x00000088,
                0x00000089,
                0x0000008A,
                0x0000008B,
                0x0000008C,
                0x0000008D,
                0x0000008E,
                0x0000008F,
                0x00000090,
                0x00000091,
                0x00000092,
                0x00000093,
                0x00000094,
                0x00000095,
                0x00000096,
                0x00000097,
                0x00000098,
                0x00000099,
                0x0000009A,
                0x0000009B,
                0x0000009C,
                0x0000009D,
                0x0000009E,
                0x0000009F,
                0x000000A0,
                0x000000A1,
                0x000000A2,
                0x000000A3,
                0x000000A4,
                0x000000A5,
                0x000000A6,
                0x000000A7,
                0x000000A8,
                0x000000A9,
                0x000000AA,
                0x000000AB,
                0x000000AC,
                0x000000AD,
                0x000000AE,
                0x000000AF,
                0x000000B0,
                0x000000B1,
                0x000000B2,
                0x000000B3,
                0x000000B4,
                0x000000B5,
                0x000000B6,
                0x000000B7,
                0x000000B8,
                0x000000B9,
                0x000000BA,
                0x000000BB,
                0x000000BC,
                0x000000BD,
                0x000000BE,
                0x000000BF,
                0x000000C0,
                0x000000C1,
                0x000000C2,
                0x000000C3,
                0x000000C4,
                0x000000C5,
                0x000000C6,
                0x000000C7,
                0x000000C8,
                0x000000C9,
                0x000000CA,
                0x000000CB,
                0x000000CC,
                0x000000CD,
                0x000000CE,
                0x000000CF,
                0x000000D0,
                0x000000D1,
                0x000000D2,
                0x000000D3,
                0x000000D4,
                0x000000D5,
                0x000000D6,
                0x000000D7,
                0x000000D8,
                0x000000D9,
                0x000000DA,
                0x000000DB,
                0x000000DC,
                0x000000DD,
                0x000000DE,
                0x000000DF,
                0x000000E0,
                0x000000E1,
                0x000000E2,
                0x000000E3,
                0x000000E4,
                0x000000E5,
                0x000000E6,
                0x000000E7,
                0x000000E8,
                0x000000E9,
                0x000000EA,
                0x000000EB,
                0x000000EC,
                0x000000ED,
                0x000000EE,
                0x000000EF,
                0x000000F0,
                0x000000F1,
                0x000000F2,
                0x000000F3,
                0x000000F4,
                0x000000F5,
                0x000000F6,
                0x000000F7,
                0x000000F8,
                0x000000F9,
                0x000000FA,
                0x000000FB,
                0x000000FC,
                0x000000FD,
                0x000000FE,
                0x000000FF,
            }
            Register (FFixedHW,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                ,)
            ExtendedIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0xD0D1D2D3D4D5D6D7, // Granularity
                0xD8D9DADBDCDDDEDF, // Range Minimum
                0xE0E1E2E3E4E5E6E7, // Range Maximum
                0xE8E9EAEBECEDEEEF, // Translation Offset
                0xF0F1F2F3F4F5F6F7, // Length
                0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                , TypeTranslation, SparseTranslation)
            ExtendedMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                0xD0D1D2D3D4D5D6D7, // Granularity
                0xD8D9DADBDCDDDEDF, // Range Minimum
                0xE0E1E2E3E4E5E6E7, // Range Maximum
                0xE8E9EAEBECEDEEEF, // Translation Offset
                0xF0F1F2F3F4F5F6F7, // Length
                0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                , AddressRangeACPI, TypeTranslation)
            ExtendedSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                0xD0D1D2D3D4D5D6D7, // Granularity
                0xD8D9DADBDCDDDEDF, // Range Minimum
                0xE0E1E2E3E4E5E6E7, // Range Maximum
                0xE8E9EAEBECEDEEEF, // Translation Offset
                0xF0F1F2F3F4F5F6F7, // Length
                0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                )
            DWordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                0xFF, "PATHPATHPATH", )
            QWordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                0xFF, "PATHPATHPATH", )
            WordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                0xF6F7,             // Granularity
                0xF8F9,             // Range Minimum
                0xFAFB,             // Range Maximum
                0xFCFD,             // Translation Offset
                0xFEFF,             // Length
                0xFF, "PATHPATHPATH", )
            IRQ (Level, ActiveHigh, Exclusive, )
                {0}
            IRQNoFlags ()
                {1}
            DMA (Compatibility, NotBusMaster, Transfer16, )
                {2}
            IO (Decode16,
                0xF0F1,             // Range Minimum
                0xF2F3,             // Range Maximum
                0xF4,               // Alignment
                0xF5,               // Length
                )
            FixedIO (
                0x03F1,             // Address
                0xF2,               // Length
                )
            VendorShort ()      // Length = 0x07
            {
                 0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
            }
            Memory24 (ReadWrite,
                0xF0F1,             // Range Minimum
                0xF2F3,             // Range Maximum
                0xF4F5,             // Alignment
                0xF6F7,             // Length
                )
            Memory32 (ReadWrite,
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Alignment
                0xFCFDFEFF,         // Length
                )
            Memory32Fixed (ReadOnly,
                0xF0F1F2F3,         // Address Base
                0xF4F5F6F7,         // Address Length
                )
            VendorLong  ()      // Length = 0x15
            {
                /* 0000 */  0x9F, 0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6,  // ........
                /* 0008 */  0xF7, 0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE,  // ........
                /* 0010 */  0xFF, 0x00, 0x01, 0x02, 0x03                     // .....
            }
            QWordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
            DWordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
            WordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0xF6F7,             // Granularity
                0xF8F9,             // Range Minimum
                0xFAFB,             // Range Maximum
                0xFCFD,             // Translation Offset
                0xFEFF,             // Length
                0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
            QWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                0xFF, "PATHPATHPATH", , AddressRangeACPI, TypeTranslation)
            DWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                0xFF, "PATHPATHPATH", , AddressRangeACPI, TypeTranslation)
            WordBusNumber (ResourceConsumer, MinFixed, MaxFixed, SubDecode,
                0xF6F7,             // Granularity
                0xF8F9,             // Range Minimum
                0xFAFB,             // Range Maximum
                0xFCFD,             // Translation Offset
                0xFEFF,             // Length
                0xFF, "PATHPATHPATH", )
            Interrupt (ResourceConsumer, Edge, ActiveLow, Shared, 0xFF, "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*", )
            {
                0x00000001,
                0x00000002,
                0x00000003,
                0x00000004,
                0x00000005,
                0x00000006,
                0x00000007,
                0x00000008,
                0x00000009,
                0x0000000A,
                0x0000000B,
                0x0000000C,
                0x0000000D,
                0x0000000E,
                0x0000000F,
                0x00000010,
                0x00000011,
                0x00000012,
                0x00000013,
                0x00000014,
                0x00000015,
                0x00000016,
                0x00000017,
                0x00000018,
                0x00000019,
                0x0000001A,
                0x0000001B,
                0x0000001C,
                0x0000001D,
                0x0000001E,
                0x0000001F,
                0x00000020,
                0x00000021,
                0x00000022,
                0x00000023,
                0x00000024,
                0x00000025,
                0x00000026,
                0x00000027,
                0x00000028,
                0x00000029,
                0x0000002A,
                0x0000002B,
                0x0000002C,
                0x0000002D,
                0x0000002E,
                0x0000002F,
                0x00000030,
                0x00000031,
                0x00000032,
                0x00000033,
                0x00000034,
                0x00000035,
                0x00000036,
                0x00000037,
                0x00000038,
                0x00000039,
                0x0000003A,
                0x0000003B,
                0x0000003C,
                0x0000003D,
                0x0000003E,
                0x0000003F,
                0x00000040,
                0x00000041,
                0x00000042,
                0x00000043,
                0x00000044,
                0x00000045,
                0x00000046,
                0x00000047,
                0x00000048,
                0x00000049,
                0x0000004A,
                0x0000004B,
                0x0000004C,
                0x0000004D,
                0x0000004E,
                0x0000004F,
                0x00000050,
                0x00000051,
                0x00000052,
                0x00000053,
                0x00000054,
                0x00000055,
                0x00000056,
                0x00000057,
                0x00000058,
                0x00000059,
                0x0000005A,
                0x0000005B,
                0x0000005C,
                0x0000005D,
                0x0000005E,
                0x0000005F,
                0x00000060,
                0x00000061,
                0x00000062,
                0x00000063,
                0x00000064,
                0x00000065,
                0x00000066,
                0x00000067,
                0x00000068,
                0x00000069,
                0x0000006A,
                0x0000006B,
                0x0000006C,
                0x0000006D,
                0x0000006E,
                0x0000006F,
                0x00000070,
                0x00000071,
                0x00000072,
                0x00000073,
                0x00000074,
                0x00000075,
                0x00000076,
                0x00000077,
                0x00000078,
                0x00000079,
                0x0000007A,
                0x0000007B,
                0x0000007C,
                0x0000007D,
                0x0000007E,
                0x0000007F,
                0x00000080,
                0x00000081,
                0x00000082,
                0x00000083,
                0x00000084,
                0x00000085,
                0x00000086,
                0x00000087,
                0x00000088,
                0x00000089,
                0x0000008A,
                0x0000008B,
                0x0000008C,
                0x0000008D,
                0x0000008E,
                0x0000008F,
                0x00000090,
                0x00000091,
                0x00000092,
                0x00000093,
                0x00000094,
                0x00000095,
                0x00000096,
                0x00000097,
                0x00000098,
                0x00000099,
                0x0000009A,
                0x0000009B,
                0x0000009C,
                0x0000009D,
                0x0000009E,
                0x0000009F,
                0x000000A0,
                0x000000A1,
                0x000000A2,
                0x000000A3,
                0x000000A4,
                0x000000A5,
                0x000000A6,
                0x000000A7,
                0x000000A8,
                0x000000A9,
                0x000000AA,
                0x000000AB,
                0x000000AC,
                0x000000AD,
                0x000000AE,
                0x000000AF,
                0x000000B0,
                0x000000B1,
                0x000000B2,
                0x000000B3,
                0x000000B4,
                0x000000B5,
                0x000000B6,
                0x000000B7,
                0x000000B8,
                0x000000B9,
                0x000000BA,
                0x000000BB,
                0x000000BC,
                0x000000BD,
                0x000000BE,
                0x000000BF,
                0x000000C0,
                0x000000C1,
                0x000000C2,
                0x000000C3,
                0x000000C4,
                0x000000C5,
                0x000000C6,
                0x000000C7,
                0x000000C8,
                0x000000C9,
                0x000000CA,
                0x000000CB,
                0x000000CC,
                0x000000CD,
                0x000000CE,
                0x000000CF,
                0x000000D0,
                0x000000D1,
                0x000000D2,
                0x000000D3,
                0x000000D4,
                0x000000D5,
                0x000000D6,
                0x000000D7,
                0x000000D8,
                0x000000D9,
                0x000000DA,
                0x000000DB,
                0x000000DC,
                0x000000DD,
                0x000000DE,
                0x000000DF,
                0x000000E0,
                0x000000E1,
                0x000000E2,
                0x000000E3,
                0x000000E4,
                0x000000E5,
                0x000000E6,
                0x000000E7,
                0x000000E8,
                0x000000E9,
                0x000000EA,
                0x000000EB,
                0x000000EC,
                0x000000ED,
                0x000000EE,
                0x000000EF,
                0x000000F0,
                0x000000F1,
                0x000000F2,
                0x000000F3,
                0x000000F4,
                0x000000F5,
                0x000000F6,
                0x000000F7,
                0x000000F8,
                0x000000F9,
                0x000000FA,
                0x000000FB,
                0x000000FC,
                0x000000FD,
                0x000000FE,
                0x000000FF,
            }
            Register (FFixedHW,
                0xF0,               // Bit Width
                0xF1,               // Bit Offset
                0xF2F3F4F5F6F7F8F9, // Address
                ,)
            ExtendedIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0xD0D1D2D3D4D5D6D7, // Granularity
                0xD8D9DADBDCDDDEDF, // Range Minimum
                0xE0E1E2E3E4E5E6E7, // Range Maximum
                0xE8E9EAEBECEDEEEF, // Translation Offset
                0xF0F1F2F3F4F5F6F7, // Length
                0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                , TypeTranslation, SparseTranslation)
            ExtendedMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                0xD0D1D2D3D4D5D6D7, // Granularity
                0xD8D9DADBDCDDDEDF, // Range Minimum
                0xE0E1E2E3E4E5E6E7, // Range Maximum
                0xE8E9EAEBECEDEEEF, // Translation Offset
                0xF0F1F2F3F4F5F6F7, // Length
                0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                , AddressRangeACPI, TypeTranslation)
            ExtendedSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                0xD0D1D2D3D4D5D6D7, // Granularity
                0xD8D9DADBDCDDDEDF, // Range Minimum
                0xE0E1E2E3E4E5E6E7, // Range Maximum
                0xE8E9EAEBECEDEEEF, // Translation Offset
                0xF0F1F2F3F4F5F6F7, // Length
                0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                )
            DWordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                0xFF, "PATHPATHPATH", )
            QWordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                0xD8D9DADBDCDDDEDF, // Granularity
                0xE0E1E2E3E4E5E6E7, // Range Minimum
                0xE8E9EAEBECEDEEEF, // Range Maximum
                0xF0F1F2F3F4F5F6F7, // Translation Offset
                0xF8F9FAFBFCFDFEFF, // Length
                0xFF, "PATHPATHPATH", )
            WordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                0xF6F7,             // Granularity
                0xF8F9,             // Range Minimum
                0xFAFB,             // Range Maximum
                0xFCFD,             // Translation Offset
                0xFEFF,             // Length
                0xFF, "PATHPATHPATH", )
        })
        Name (RT01, ResourceTemplate ()
        {
            StartDependentFnNoPri ()
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
            }
            StartDependentFnNoPri ()
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
            }
            StartDependentFn (0x00, 0x00)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
            }
            StartDependentFn (0x00, 0x01)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
            }
            StartDependentFn (0x00, 0x02)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
            }
            StartDependentFn (0x01, 0x00)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
            }
            StartDependentFn (0x01, 0x01)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
                Memory32 (ReadWrite,
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Alignment
                    0xFCFDFEFF,         // Length
                    )
            }
            StartDependentFn (0x01, 0x01)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
                Memory32 (ReadWrite,
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Alignment
                    0xFCFDFEFF,         // Length
                    )
                Memory32Fixed (ReadOnly,
                    0xF0F1F2F3,         // Address Base
                    0xF4F5F6F7,         // Address Length
                    )
                VendorLong  ()      // Length = 0x15
                {
                    /* 0000 */  0x9F, 0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6,  // ........
                    /* 0008 */  0xF7, 0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE,  // ........
                    /* 0010 */  0xFF, 0x00, 0x01, 0x02, 0x03                     // .....
                }
                QWordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                    0xD8D9DADBDCDDDEDF, // Granularity
                    0xE0E1E2E3E4E5E6E7, // Range Minimum
                    0xE8E9EAEBECEDEEEF, // Range Maximum
                    0xF0F1F2F3F4F5F6F7, // Translation Offset
                    0xF8F9FAFBFCFDFEFF, // Length
                    0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
                DWordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                    0xECEDEEEF,         // Granularity
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Translation Offset
                    0xFCFDFEFF,         // Length
                    0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
                WordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                    0xF6F7,             // Granularity
                    0xF8F9,             // Range Minimum
                    0xFAFB,             // Range Maximum
                    0xFCFD,             // Translation Offset
                    0xFEFF,             // Length
                    0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
                QWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                    0xD8D9DADBDCDDDEDF, // Granularity
                    0xE0E1E2E3E4E5E6E7, // Range Minimum
                    0xE8E9EAEBECEDEEEF, // Range Maximum
                    0xF0F1F2F3F4F5F6F7, // Translation Offset
                    0xF8F9FAFBFCFDFEFF, // Length
                    0xFF, "PATHPATHPATH", , AddressRangeACPI, TypeTranslation)
                DWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                    0xECEDEEEF,         // Granularity
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Translation Offset
                    0xFCFDFEFF,         // Length
                    0xFF, "PATHPATHPATH", , AddressRangeACPI, TypeTranslation)
                WordBusNumber (ResourceConsumer, MinFixed, MaxFixed, SubDecode,
                    0xF6F7,             // Granularity
                    0xF8F9,             // Range Minimum
                    0xFAFB,             // Range Maximum
                    0xFCFD,             // Translation Offset
                    0xFEFF,             // Length
                    0xFF, "PATHPATHPATH", )
                Interrupt (ResourceConsumer, Edge, ActiveLow, Shared, 0xFF, "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*", )
                {
                    0x00000001,
                    0x00000002,
                    0x00000003,
                    0x00000004,
                    0x00000005,
                    0x00000006,
                    0x00000007,
                    0x00000008,
                    0x00000009,
                    0x0000000A,
                    0x0000000B,
                    0x0000000C,
                    0x0000000D,
                    0x0000000E,
                    0x0000000F,
                    0x00000010,
                    0x00000011,
                    0x00000012,
                    0x00000013,
                    0x00000014,
                    0x00000015,
                    0x00000016,
                    0x00000017,
                    0x00000018,
                    0x00000019,
                    0x0000001A,
                    0x0000001B,
                    0x0000001C,
                    0x0000001D,
                    0x0000001E,
                    0x0000001F,
                    0x00000020,
                    0x00000021,
                    0x00000022,
                    0x00000023,
                    0x00000024,
                    0x00000025,
                    0x00000026,
                    0x00000027,
                    0x00000028,
                    0x00000029,
                    0x0000002A,
                    0x0000002B,
                    0x0000002C,
                    0x0000002D,
                    0x0000002E,
                    0x0000002F,
                    0x00000030,
                    0x00000031,
                    0x00000032,
                    0x00000033,
                    0x00000034,
                    0x00000035,
                    0x00000036,
                    0x00000037,
                    0x00000038,
                    0x00000039,
                    0x0000003A,
                    0x0000003B,
                    0x0000003C,
                    0x0000003D,
                    0x0000003E,
                    0x0000003F,
                    0x00000040,
                    0x00000041,
                    0x00000042,
                    0x00000043,
                    0x00000044,
                    0x00000045,
                    0x00000046,
                    0x00000047,
                    0x00000048,
                    0x00000049,
                    0x0000004A,
                    0x0000004B,
                    0x0000004C,
                    0x0000004D,
                    0x0000004E,
                    0x0000004F,
                    0x00000050,
                    0x00000051,
                    0x00000052,
                    0x00000053,
                    0x00000054,
                    0x00000055,
                    0x00000056,
                    0x00000057,
                    0x00000058,
                    0x00000059,
                    0x0000005A,
                    0x0000005B,
                    0x0000005C,
                    0x0000005D,
                    0x0000005E,
                    0x0000005F,
                    0x00000060,
                    0x00000061,
                    0x00000062,
                    0x00000063,
                    0x00000064,
                    0x00000065,
                    0x00000066,
                    0x00000067,
                    0x00000068,
                    0x00000069,
                    0x0000006A,
                    0x0000006B,
                    0x0000006C,
                    0x0000006D,
                    0x0000006E,
                    0x0000006F,
                    0x00000070,
                    0x00000071,
                    0x00000072,
                    0x00000073,
                    0x00000074,
                    0x00000075,
                    0x00000076,
                    0x00000077,
                    0x00000078,
                    0x00000079,
                    0x0000007A,
                    0x0000007B,
                    0x0000007C,
                    0x0000007D,
                    0x0000007E,
                    0x0000007F,
                    0x00000080,
                    0x00000081,
                    0x00000082,
                    0x00000083,
                    0x00000084,
                    0x00000085,
                    0x00000086,
                    0x00000087,
                    0x00000088,
                    0x00000089,
                    0x0000008A,
                    0x0000008B,
                    0x0000008C,
                    0x0000008D,
                    0x0000008E,
                    0x0000008F,
                    0x00000090,
                    0x00000091,
                    0x00000092,
                    0x00000093,
                    0x00000094,
                    0x00000095,
                    0x00000096,
                    0x00000097,
                    0x00000098,
                    0x00000099,
                    0x0000009A,
                    0x0000009B,
                    0x0000009C,
                    0x0000009D,
                    0x0000009E,
                    0x0000009F,
                    0x000000A0,
                    0x000000A1,
                    0x000000A2,
                    0x000000A3,
                    0x000000A4,
                    0x000000A5,
                    0x000000A6,
                    0x000000A7,
                    0x000000A8,
                    0x000000A9,
                    0x000000AA,
                    0x000000AB,
                    0x000000AC,
                    0x000000AD,
                    0x000000AE,
                    0x000000AF,
                    0x000000B0,
                    0x000000B1,
                    0x000000B2,
                    0x000000B3,
                    0x000000B4,
                    0x000000B5,
                    0x000000B6,
                    0x000000B7,
                    0x000000B8,
                    0x000000B9,
                    0x000000BA,
                    0x000000BB,
                    0x000000BC,
                    0x000000BD,
                    0x000000BE,
                    0x000000BF,
                    0x000000C0,
                    0x000000C1,
                    0x000000C2,
                    0x000000C3,
                    0x000000C4,
                    0x000000C5,
                    0x000000C6,
                    0x000000C7,
                    0x000000C8,
                    0x000000C9,
                    0x000000CA,
                    0x000000CB,
                    0x000000CC,
                    0x000000CD,
                    0x000000CE,
                    0x000000CF,
                    0x000000D0,
                    0x000000D1,
                    0x000000D2,
                    0x000000D3,
                    0x000000D4,
                    0x000000D5,
                    0x000000D6,
                    0x000000D7,
                    0x000000D8,
                    0x000000D9,
                    0x000000DA,
                    0x000000DB,
                    0x000000DC,
                    0x000000DD,
                    0x000000DE,
                    0x000000DF,
                    0x000000E0,
                    0x000000E1,
                    0x000000E2,
                    0x000000E3,
                    0x000000E4,
                    0x000000E5,
                    0x000000E6,
                    0x000000E7,
                    0x000000E8,
                    0x000000E9,
                    0x000000EA,
                    0x000000EB,
                    0x000000EC,
                    0x000000ED,
                    0x000000EE,
                    0x000000EF,
                    0x000000F0,
                    0x000000F1,
                    0x000000F2,
                    0x000000F3,
                    0x000000F4,
                    0x000000F5,
                    0x000000F6,
                    0x000000F7,
                    0x000000F8,
                    0x000000F9,
                    0x000000FA,
                    0x000000FB,
                    0x000000FC,
                    0x000000FD,
                    0x000000FE,
                    0x000000FF,
                }
                Register (FFixedHW,
                    0xF0,               // Bit Width
                    0xF1,               // Bit Offset
                    0xF2F3F4F5F6F7F8F9, // Address
                    ,)
                ExtendedIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                    0xD0D1D2D3D4D5D6D7, // Granularity
                    0xD8D9DADBDCDDDEDF, // Range Minimum
                    0xE0E1E2E3E4E5E6E7, // Range Maximum
                    0xE8E9EAEBECEDEEEF, // Translation Offset
                    0xF0F1F2F3F4F5F6F7, // Length
                    0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                    , TypeTranslation, SparseTranslation)
                ExtendedMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                    0xD0D1D2D3D4D5D6D7, // Granularity
                    0xD8D9DADBDCDDDEDF, // Range Minimum
                    0xE0E1E2E3E4E5E6E7, // Range Maximum
                    0xE8E9EAEBECEDEEEF, // Translation Offset
                    0xF0F1F2F3F4F5F6F7, // Length
                    0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                    , AddressRangeACPI, TypeTranslation)
                ExtendedSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                    0xD0D1D2D3D4D5D6D7, // Granularity
                    0xD8D9DADBDCDDDEDF, // Range Minimum
                    0xE0E1E2E3E4E5E6E7, // Range Maximum
                    0xE8E9EAEBECEDEEEF, // Translation Offset
                    0xF0F1F2F3F4F5F6F7, // Length
                    0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                    )
                DWordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                    0xECEDEEEF,         // Granularity
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Translation Offset
                    0xFCFDFEFF,         // Length
                    0xFF, "PATHPATHPATH", )
                QWordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                    0xD8D9DADBDCDDDEDF, // Granularity
                    0xE0E1E2E3E4E5E6E7, // Range Minimum
                    0xE8E9EAEBECEDEEEF, // Range Maximum
                    0xF0F1F2F3F4F5F6F7, // Translation Offset
                    0xF8F9FAFBFCFDFEFF, // Length
                    0xFF, "PATHPATHPATH", )
                WordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                    0xF6F7,             // Granularity
                    0xF8F9,             // Range Minimum
                    0xFAFB,             // Range Maximum
                    0xFCFD,             // Translation Offset
                    0xFEFF,             // Length
                    0xFF, "PATHPATHPATH", )
            }
            StartDependentFn (0x01, 0x02)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
                Memory32 (ReadWrite,
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Alignment
                    0xFCFDFEFF,         // Length
                    )
                Memory32Fixed (ReadOnly,
                    0xF0F1F2F3,         // Address Base
                    0xF4F5F6F7,         // Address Length
                    )
            }
            StartDependentFn (0x02, 0x00)
            {
            }
            StartDependentFn (0x02, 0x01)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
                Memory32 (ReadWrite,
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Alignment
                    0xFCFDFEFF,         // Length
                    )
                Memory32Fixed (ReadOnly,
                    0xF0F1F2F3,         // Address Base
                    0xF4F5F6F7,         // Address Length
                    )
                VendorLong  ()      // Length = 0x15
                {
                    /* 0000 */  0x9F, 0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6,  // ........
                    /* 0008 */  0xF7, 0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE,  // ........
                    /* 0010 */  0xFF, 0x00, 0x01, 0x02, 0x03                     // .....
                }
            }
            StartDependentFn (0x02, 0x02)
            {
            }
            EndDependentFn ()
            StartDependentFnNoPri ()
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
            }
            StartDependentFnNoPri ()
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
            }
            StartDependentFn (0x00, 0x00)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
            }
            StartDependentFn (0x00, 0x01)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
            }
            StartDependentFn (0x00, 0x02)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
            }
            StartDependentFn (0x01, 0x00)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
            }
            StartDependentFn (0x01, 0x01)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
                Memory32 (ReadWrite,
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Alignment
                    0xFCFDFEFF,         // Length
                    )
            }
            StartDependentFn (0x01, 0x01)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
                Memory32 (ReadWrite,
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Alignment
                    0xFCFDFEFF,         // Length
                    )
                Memory32Fixed (ReadOnly,
                    0xF0F1F2F3,         // Address Base
                    0xF4F5F6F7,         // Address Length
                    )
                VendorLong  ()      // Length = 0x15
                {
                    /* 0000 */  0x9F, 0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6,  // ........
                    /* 0008 */  0xF7, 0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE,  // ........
                    /* 0010 */  0xFF, 0x00, 0x01, 0x02, 0x03                     // .....
                }
                QWordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                    0xD8D9DADBDCDDDEDF, // Granularity
                    0xE0E1E2E3E4E5E6E7, // Range Minimum
                    0xE8E9EAEBECEDEEEF, // Range Maximum
                    0xF0F1F2F3F4F5F6F7, // Translation Offset
                    0xF8F9FAFBFCFDFEFF, // Length
                    0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
                DWordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                    0xECEDEEEF,         // Granularity
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Translation Offset
                    0xFCFDFEFF,         // Length
                    0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
                WordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                    0xF6F7,             // Granularity
                    0xF8F9,             // Range Minimum
                    0xFAFB,             // Range Maximum
                    0xFCFD,             // Translation Offset
                    0xFEFF,             // Length
                    0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
                QWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                    0xD8D9DADBDCDDDEDF, // Granularity
                    0xE0E1E2E3E4E5E6E7, // Range Minimum
                    0xE8E9EAEBECEDEEEF, // Range Maximum
                    0xF0F1F2F3F4F5F6F7, // Translation Offset
                    0xF8F9FAFBFCFDFEFF, // Length
                    0xFF, "PATHPATHPATH", , AddressRangeACPI, TypeTranslation)
                DWordMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                    0xECEDEEEF,         // Granularity
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Translation Offset
                    0xFCFDFEFF,         // Length
                    0xFF, "PATHPATHPATH", , AddressRangeACPI, TypeTranslation)
                WordBusNumber (ResourceConsumer, MinFixed, MaxFixed, SubDecode,
                    0xF6F7,             // Granularity
                    0xF8F9,             // Range Minimum
                    0xFAFB,             // Range Maximum
                    0xFCFD,             // Translation Offset
                    0xFEFF,             // Length
                    0xFF, "PATHPATHPATH", )
                Interrupt (ResourceConsumer, Edge, ActiveLow, Shared, 0xFF, "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*", )
                {
                    0x00000001,
                    0x00000002,
                    0x00000003,
                    0x00000004,
                    0x00000005,
                    0x00000006,
                    0x00000007,
                    0x00000008,
                    0x00000009,
                    0x0000000A,
                    0x0000000B,
                    0x0000000C,
                    0x0000000D,
                    0x0000000E,
                    0x0000000F,
                    0x00000010,
                    0x00000011,
                    0x00000012,
                    0x00000013,
                    0x00000014,
                    0x00000015,
                    0x00000016,
                    0x00000017,
                    0x00000018,
                    0x00000019,
                    0x0000001A,
                    0x0000001B,
                    0x0000001C,
                    0x0000001D,
                    0x0000001E,
                    0x0000001F,
                    0x00000020,
                    0x00000021,
                    0x00000022,
                    0x00000023,
                    0x00000024,
                    0x00000025,
                    0x00000026,
                    0x00000027,
                    0x00000028,
                    0x00000029,
                    0x0000002A,
                    0x0000002B,
                    0x0000002C,
                    0x0000002D,
                    0x0000002E,
                    0x0000002F,
                    0x00000030,
                    0x00000031,
                    0x00000032,
                    0x00000033,
                    0x00000034,
                    0x00000035,
                    0x00000036,
                    0x00000037,
                    0x00000038,
                    0x00000039,
                    0x0000003A,
                    0x0000003B,
                    0x0000003C,
                    0x0000003D,
                    0x0000003E,
                    0x0000003F,
                    0x00000040,
                    0x00000041,
                    0x00000042,
                    0x00000043,
                    0x00000044,
                    0x00000045,
                    0x00000046,
                    0x00000047,
                    0x00000048,
                    0x00000049,
                    0x0000004A,
                    0x0000004B,
                    0x0000004C,
                    0x0000004D,
                    0x0000004E,
                    0x0000004F,
                    0x00000050,
                    0x00000051,
                    0x00000052,
                    0x00000053,
                    0x00000054,
                    0x00000055,
                    0x00000056,
                    0x00000057,
                    0x00000058,
                    0x00000059,
                    0x0000005A,
                    0x0000005B,
                    0x0000005C,
                    0x0000005D,
                    0x0000005E,
                    0x0000005F,
                    0x00000060,
                    0x00000061,
                    0x00000062,
                    0x00000063,
                    0x00000064,
                    0x00000065,
                    0x00000066,
                    0x00000067,
                    0x00000068,
                    0x00000069,
                    0x0000006A,
                    0x0000006B,
                    0x0000006C,
                    0x0000006D,
                    0x0000006E,
                    0x0000006F,
                    0x00000070,
                    0x00000071,
                    0x00000072,
                    0x00000073,
                    0x00000074,
                    0x00000075,
                    0x00000076,
                    0x00000077,
                    0x00000078,
                    0x00000079,
                    0x0000007A,
                    0x0000007B,
                    0x0000007C,
                    0x0000007D,
                    0x0000007E,
                    0x0000007F,
                    0x00000080,
                    0x00000081,
                    0x00000082,
                    0x00000083,
                    0x00000084,
                    0x00000085,
                    0x00000086,
                    0x00000087,
                    0x00000088,
                    0x00000089,
                    0x0000008A,
                    0x0000008B,
                    0x0000008C,
                    0x0000008D,
                    0x0000008E,
                    0x0000008F,
                    0x00000090,
                    0x00000091,
                    0x00000092,
                    0x00000093,
                    0x00000094,
                    0x00000095,
                    0x00000096,
                    0x00000097,
                    0x00000098,
                    0x00000099,
                    0x0000009A,
                    0x0000009B,
                    0x0000009C,
                    0x0000009D,
                    0x0000009E,
                    0x0000009F,
                    0x000000A0,
                    0x000000A1,
                    0x000000A2,
                    0x000000A3,
                    0x000000A4,
                    0x000000A5,
                    0x000000A6,
                    0x000000A7,
                    0x000000A8,
                    0x000000A9,
                    0x000000AA,
                    0x000000AB,
                    0x000000AC,
                    0x000000AD,
                    0x000000AE,
                    0x000000AF,
                    0x000000B0,
                    0x000000B1,
                    0x000000B2,
                    0x000000B3,
                    0x000000B4,
                    0x000000B5,
                    0x000000B6,
                    0x000000B7,
                    0x000000B8,
                    0x000000B9,
                    0x000000BA,
                    0x000000BB,
                    0x000000BC,
                    0x000000BD,
                    0x000000BE,
                    0x000000BF,
                    0x000000C0,
                    0x000000C1,
                    0x000000C2,
                    0x000000C3,
                    0x000000C4,
                    0x000000C5,
                    0x000000C6,
                    0x000000C7,
                    0x000000C8,
                    0x000000C9,
                    0x000000CA,
                    0x000000CB,
                    0x000000CC,
                    0x000000CD,
                    0x000000CE,
                    0x000000CF,
                    0x000000D0,
                    0x000000D1,
                    0x000000D2,
                    0x000000D3,
                    0x000000D4,
                    0x000000D5,
                    0x000000D6,
                    0x000000D7,
                    0x000000D8,
                    0x000000D9,
                    0x000000DA,
                    0x000000DB,
                    0x000000DC,
                    0x000000DD,
                    0x000000DE,
                    0x000000DF,
                    0x000000E0,
                    0x000000E1,
                    0x000000E2,
                    0x000000E3,
                    0x000000E4,
                    0x000000E5,
                    0x000000E6,
                    0x000000E7,
                    0x000000E8,
                    0x000000E9,
                    0x000000EA,
                    0x000000EB,
                    0x000000EC,
                    0x000000ED,
                    0x000000EE,
                    0x000000EF,
                    0x000000F0,
                    0x000000F1,
                    0x000000F2,
                    0x000000F3,
                    0x000000F4,
                    0x000000F5,
                    0x000000F6,
                    0x000000F7,
                    0x000000F8,
                    0x000000F9,
                    0x000000FA,
                    0x000000FB,
                    0x000000FC,
                    0x000000FD,
                    0x000000FE,
                    0x000000FF,
                }
                Register (FFixedHW,
                    0xF0,               // Bit Width
                    0xF1,               // Bit Offset
                    0xF2F3F4F5F6F7F8F9, // Address
                    ,)
                ExtendedIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                    0xD0D1D2D3D4D5D6D7, // Granularity
                    0xD8D9DADBDCDDDEDF, // Range Minimum
                    0xE0E1E2E3E4E5E6E7, // Range Maximum
                    0xE8E9EAEBECEDEEEF, // Translation Offset
                    0xF0F1F2F3F4F5F6F7, // Length
                    0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                    , TypeTranslation, SparseTranslation)
                ExtendedMemory (ResourceConsumer, SubDecode, MinFixed, MaxFixed, NonCacheable, ReadOnly,
                    0xD0D1D2D3D4D5D6D7, // Granularity
                    0xD8D9DADBDCDDDEDF, // Range Minimum
                    0xE0E1E2E3E4E5E6E7, // Range Maximum
                    0xE8E9EAEBECEDEEEF, // Translation Offset
                    0xF0F1F2F3F4F5F6F7, // Length
                    0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                    , AddressRangeACPI, TypeTranslation)
                ExtendedSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                    0xD0D1D2D3D4D5D6D7, // Granularity
                    0xD8D9DADBDCDDDEDF, // Range Minimum
                    0xE0E1E2E3E4E5E6E7, // Range Maximum
                    0xE8E9EAEBECEDEEEF, // Translation Offset
                    0xF0F1F2F3F4F5F6F7, // Length
                    0xF8F9FAFBFCFDFEFF, // Type-Specific Attributes
                    )
                DWordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                    0xECEDEEEF,         // Granularity
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Translation Offset
                    0xFCFDFEFF,         // Length
                    0xFF, "PATHPATHPATH", )
                QWordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                    0xD8D9DADBDCDDDEDF, // Granularity
                    0xE0E1E2E3E4E5E6E7, // Range Minimum
                    0xE8E9EAEBECEDEEEF, // Range Maximum
                    0xF0F1F2F3F4F5F6F7, // Translation Offset
                    0xF8F9FAFBFCFDFEFF, // Length
                    0xFF, "PATHPATHPATH", )
                WordSpace (0xC0, ResourceConsumer, SubDecode, MinFixed, MaxFixed, 0x5A,
                    0xF6F7,             // Granularity
                    0xF8F9,             // Range Minimum
                    0xFAFB,             // Range Maximum
                    0xFCFD,             // Translation Offset
                    0xFEFF,             // Length
                    0xFF, "PATHPATHPATH", )
            }
            StartDependentFn (0x01, 0x02)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
                Memory32 (ReadWrite,
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Alignment
                    0xFCFDFEFF,         // Length
                    )
                Memory32Fixed (ReadOnly,
                    0xF0F1F2F3,         // Address Base
                    0xF4F5F6F7,         // Address Length
                    )
            }
            StartDependentFn (0x02, 0x00)
            {
            }
            StartDependentFn (0x02, 0x01)
            {
                IRQ (Level, ActiveHigh, Exclusive, )
                    {0}
                IRQNoFlags ()
                    {1}
                DMA (Compatibility, NotBusMaster, Transfer16, )
                    {2}
                IO (Decode16,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4,               // Alignment
                    0xF5,               // Length
                    )
                FixedIO (
                    0x03F1,             // Address
                    0xF2,               // Length
                    )
                VendorShort ()      // Length = 0x07
                {
                     0x00, 0xA2, 0xB3, 0x76, 0xD5, 0xE6, 0xF7         // ...v...
                }
                Memory24 (ReadWrite,
                    0xF0F1,             // Range Minimum
                    0xF2F3,             // Range Maximum
                    0xF4F5,             // Alignment
                    0xF6F7,             // Length
                    )
                Memory32 (ReadWrite,
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Alignment
                    0xFCFDFEFF,         // Length
                    )
                Memory32Fixed (ReadOnly,
                    0xF0F1F2F3,         // Address Base
                    0xF4F5F6F7,         // Address Length
                    )
                VendorLong  ()      // Length = 0x15
                {
                    /* 0000 */  0x9F, 0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6,  // ........
                    /* 0008 */  0xF7, 0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE,  // ........
                    /* 0010 */  0xFF, 0x00, 0x01, 0x02, 0x03                     // .....
                }
            }
            StartDependentFn (0x02, 0x02)
            {
            }
            EndDependentFn ()
        })
        M330 (__METHOD__, 0x02, "p445", P445, P446)
        /* Checkings relating to RT00 */

        M331 (__METHOD__, 0x01, 0x18, 0x18, 0x3B68, 0x3B68, "_HE")
        M331 (__METHOD__, 0x02, 0x1B, 0x1B, 0x3B6B, 0x3B6B, "_LL")
        M331 (__METHOD__, 0x03, 0x1C, 0x1C, 0x3B6C, 0x3B6C, "_SHR")
        M331 (__METHOD__, 0x04, 0x4D, 0x4D, 0x3B9D, 0x3B9D, "_TYP")
        M331 (__METHOD__, 0x05, 0x4A, 0x4A, 0x3B9A, 0x3B9A, "_BM")
        M331 (__METHOD__, 0x06, 0x48, 0x48, 0x3B98, 0x3B98, "_SIZ")
        M331 (__METHOD__, 0x07, 0x58, 0x58, 0x3BA8, 0x3BA8, "_DEC")
        M331 (__METHOD__, 0x08, 0x60, 0x60, 0x3BB0, 0x3BB0, "_MIN")
        M331 (__METHOD__, 0x09, 0x70, 0x70, 0x3BC0, 0x3BC0, "_MAX")
        M331 (__METHOD__, 0x0A, 0x80, 0x80, 0x3BD0, 0x3BD0, "_ALN")
        M331 (__METHOD__, 0x0B, 0x88, 0x88, 0x3BD8, 0x3BD8, "_LEN")
        M331 (__METHOD__, 0x0C, 0x98, 0x98, 0x3BE8, 0x3BE8, "_BAS")
        M331 (__METHOD__, 0x0D, 0xA8, 0xA8, 0x3BF8, 0x3BF8, "_LEN")
        M331 (__METHOD__, 0x0E, 0x0108, 0x0108, 0x3C58, 0x3C58, "_RW")
        M331 (__METHOD__, 0x0F, 0x0110, 0x0110, 0x3C60, 0x3C60, "_MIN")
        M331 (__METHOD__, 0x10, 0x0120, 0x0120, 0x3C70, 0x3C70, "_MAX")
        M331 (__METHOD__, 0x11, 0x0130, 0x0130, 0x3C80, 0x3C80, "_ALN")
        M331 (__METHOD__, 0x12, 0x0140, 0x0140, 0x3C90, 0x3C90, "_LEN")
        M331 (__METHOD__, 0x13, 0x0168, 0x0168, 0x3CB8, 0x3CB8, "_RW")
        M331 (__METHOD__, 0x14, 0x0170, 0x0170, 0x3CC0, 0x3CC0, "_MIN")
        M331 (__METHOD__, 0x15, 0x0190, 0x0190, 0x3CE0, 0x3CE0, "_MAX")
        M331 (__METHOD__, 0x16, 0x01B0, 0x01B0, 0x3D00, 0x3D00, "_ALN")
        M331 (__METHOD__, 0x17, 0x01D0, 0x01D0, 0x3D20, 0x3D20, "_LEN")
        M331 (__METHOD__, 0x18, 0x0208, 0x0208, 0x3D58, 0x3D58, "_RW")
        M331 (__METHOD__, 0x19, 0x0210, 0x0210, 0x3D60, 0x3D60, "_BAS")
        M331 (__METHOD__, 0x1A, 0x0230, 0x0230, 0x3D80, 0x3D80, "_LEN")
        M331 (__METHOD__, 0x1B, 0x0331, 0x0331, 0x3E81, 0x3E81, "_DEC")
        M331 (__METHOD__, 0x1C, 0x0332, 0x0332, 0x3E82, 0x3E82, "_MIF")
        M331 (__METHOD__, 0x1D, 0x0333, 0x0333, 0x3E83, 0x3E83, "_MAF")
        M331 (__METHOD__, 0x1E, 0x0338, 0x0338, 0x3E88, 0x3E88, "_RNG")
        M331 (__METHOD__, 0x1F, 0x033C, 0x033C, 0x3E8C, 0x3E8C, "_TTP")
        M331 (__METHOD__, 0x20, 0x033D, 0x033D, 0x3E8D, 0x3E8D, "_TRS")
        M331 (__METHOD__, 0x21, 0x0340, 0x0340, 0x3E90, 0x3E90, "_GRA")
        M331 (__METHOD__, 0x22, 0x0380, 0x0380, 0x3ED0, 0x3ED0, "_MIN")
        M331 (__METHOD__, 0x23, 0x03C0, 0x03C0, 0x3F10, 0x3F10, "_MAX")
        M331 (__METHOD__, 0x24, 0x0400, 0x0400, 0x3F50, 0x3F50, "_TRA")
        M331 (__METHOD__, 0x25, 0x0440, 0x0440, 0x3F90, 0x3F90, "_LEN")
        M331 (__METHOD__, 0x26, 0x0511, 0x0511, 0x4061, 0x4061, "_DEC")
        M331 (__METHOD__, 0x27, 0x0512, 0x0512, 0x4062, 0x4062, "_MIF")
        M331 (__METHOD__, 0x28, 0x0513, 0x0513, 0x4063, 0x4063, "_MAF")
        M331 (__METHOD__, 0x29, 0x0518, 0x0518, 0x4068, 0x4068, "_RNG")
        M331 (__METHOD__, 0x2A, 0x051C, 0x051C, 0x406C, 0x406C, "_TTP")
        M331 (__METHOD__, 0x2B, 0x051D, 0x051D, 0x406D, 0x406D, "_TRS")
        M331 (__METHOD__, 0x2C, 0x0520, 0x0520, 0x4070, 0x4070, "_GRA")
        M331 (__METHOD__, 0x2D, 0x0540, 0x0540, 0x4090, 0x4090, "_MIN")
        M331 (__METHOD__, 0x2E, 0x0560, 0x0560, 0x40B0, 0x40B0, "_MAX")
        M331 (__METHOD__, 0x2F, 0x0580, 0x0580, 0x40D0, 0x40D0, "_TRA")
        M331 (__METHOD__, 0x30, 0x05A0, 0x05A0, 0x40F0, 0x40F0, "_LEN")
        M331 (__METHOD__, 0x31, 0x0651, 0x0651, 0x41A1, 0x41A1, "_DEC")
        M331 (__METHOD__, 0x32, 0x0652, 0x0652, 0x41A2, 0x41A2, "_MIF")
        M331 (__METHOD__, 0x33, 0x0653, 0x0653, 0x41A3, 0x41A3, "_MAF")
        M331 (__METHOD__, 0x34, 0x0658, 0x0658, 0x41A8, 0x41A8, "_RNG")
        M331 (__METHOD__, 0x35, 0x065C, 0x065C, 0x41AC, 0x41AC, "_TTP")
        M331 (__METHOD__, 0x36, 0x065D, 0x065D, 0x41AD, 0x41AD, "_TRS")
        M331 (__METHOD__, 0x37, 0x0660, 0x0660, 0x41B0, 0x41B0, "_GRA")
        M331 (__METHOD__, 0x38, 0x0670, 0x0670, 0x41C0, 0x41C0, "_MIN")
        M331 (__METHOD__, 0x39, 0x0680, 0x0680, 0x41D0, 0x41D0, "_MAX")
        M331 (__METHOD__, 0x3A, 0x0690, 0x0690, 0x41E0, 0x41E0, "_TRA")
        M331 (__METHOD__, 0x3B, 0x06A0, 0x06A0, 0x41F0, 0x41F0, "_LEN")
        M331 (__METHOD__, 0x3C, 0x0741, 0x0741, 0x4291, 0x4291, "_DEC")
        M331 (__METHOD__, 0x3D, 0x0742, 0x0742, 0x4292, 0x4292, "_MIF")
        M331 (__METHOD__, 0x3E, 0x0743, 0x0743, 0x4293, 0x4293, "_MAF")
        M331 (__METHOD__, 0x3F, 0x0748, 0x0748, 0x4298, 0x4298, "_RW")
        M331 (__METHOD__, 0x40, 0x0749, 0x0749, 0x4299, 0x4299, "_MEM")
        M331 (__METHOD__, 0x41, 0x074B, 0x074B, 0x429B, 0x429B, "_MTP")
        M331 (__METHOD__, 0x42, 0x074D, 0x074D, 0x429D, 0x429D, "_TTP")
        M331 (__METHOD__, 0x43, 0x0750, 0x0750, 0x42A0, 0x42A0, "_GRA")
        M331 (__METHOD__, 0x44, 0x0790, 0x0790, 0x42E0, 0x42E0, "_MIN")
        M331 (__METHOD__, 0x45, 0x07D0, 0x07D0, 0x4320, 0x4320, "_MAX")
        M331 (__METHOD__, 0x46, 0x0810, 0x0810, 0x4360, 0x4360, "_TRA")
        M331 (__METHOD__, 0x47, 0x0850, 0x0850, 0x43A0, 0x43A0, "_LEN")
        M331 (__METHOD__, 0x48, 0x0921, 0x0921, 0x4471, 0x4471, "_DEC")
        M331 (__METHOD__, 0x49, 0x0922, 0x0922, 0x4472, 0x4472, "_MIF")
        M331 (__METHOD__, 0x4A, 0x0923, 0x0923, 0x4473, 0x4473, "_MAF")
        M331 (__METHOD__, 0x4B, 0x0928, 0x0928, 0x4478, 0x4478, "_RW")
        M331 (__METHOD__, 0x4C, 0x0929, 0x0929, 0x4479, 0x4479, "_MEM")
        M331 (__METHOD__, 0x4D, 0x092B, 0x092B, 0x447B, 0x447B, "_MTP")
        M331 (__METHOD__, 0x4E, 0x092D, 0x092D, 0x447D, 0x447D, "_TTP")
        M331 (__METHOD__, 0x4F, 0x0930, 0x0930, 0x4480, 0x4480, "_GRA")
        M331 (__METHOD__, 0x50, 0x0950, 0x0950, 0x44A0, 0x44A0, "_MIN")
        M331 (__METHOD__, 0x51, 0x0970, 0x0970, 0x44C0, 0x44C0, "_MAX")
        M331 (__METHOD__, 0x52, 0x0990, 0x0990, 0x44E0, 0x44E0, "_TRA")
        M331 (__METHOD__, 0x53, 0x09B0, 0x09B0, 0x4500, 0x4500, "_LEN")
        M331 (__METHOD__, 0x54, 0x0A61, 0x0A61, 0x45B1, 0x45B1, "_DEC")
        M331 (__METHOD__, 0x55, 0x0A62, 0x0A62, 0x45B2, 0x45B2, "_MIF")
        M331 (__METHOD__, 0x56, 0x0A63, 0x0A63, 0x45B3, 0x45B3, "_MAF")
        M331 (__METHOD__, 0x57, 0x0A70, 0x0A70, 0x45C0, 0x45C0, "_GRA")
        M331 (__METHOD__, 0x58, 0x0A80, 0x0A80, 0x45D0, 0x45D0, "_MIN")
        M331 (__METHOD__, 0x59, 0x0A90, 0x0A90, 0x45E0, 0x45E0, "_MAX")
        M331 (__METHOD__, 0x5A, 0x0AA0, 0x0AA0, 0x45F0, 0x45F0, "_TRA")
        M331 (__METHOD__, 0x5B, 0x0AB0, 0x0AB0, 0x4600, 0x4600, "_LEN")
        M331 (__METHOD__, 0x5C, 0x0B49, 0x0B49, 0x4699, 0x4699, "_HE")
        M331 (__METHOD__, 0x5D, 0x0B4A, 0x0B4A, 0x469A, 0x469A, "_LL")
        M331 (__METHOD__, 0x5E, 0x0B4B, 0x0B4B, 0x469B, 0x469B, "_SHR")
        M331 (__METHOD__, 0x5F, 0x0B58, 0x0B58, 0x46A8, 0x46A8, "_INT")
        M331 (__METHOD__, 0x60, 0x3221, 0x3221, 0x6D71, 0x6D71, "_DEC")
        M331 (__METHOD__, 0x61, 0x3222, 0x3222, 0x6D72, 0x6D72, "_MIF")
        M331 (__METHOD__, 0x62, 0x3223, 0x3223, 0x6D73, 0x6D73, "_MAF")
        M331 (__METHOD__, 0x63, 0x3228, 0x3228, 0x6D78, 0x6D78, "_RNG")
        M331 (__METHOD__, 0x64, 0x322C, 0x322C, 0x6D7C, 0x6D7C, "_TTP")
        M331 (__METHOD__, 0x65, 0x322D, 0x322D, 0x6D7D, 0x6D7D, "_TRS")
        M331 (__METHOD__, 0x66, 0x3240, 0x3240, 0x6D90, 0x6D90, "_GRA")
        M331 (__METHOD__, 0x67, 0x3280, 0x3280, 0x6DD0, 0x6DD0, "_MIN")
        M331 (__METHOD__, 0x68, 0x32C0, 0x32C0, 0x6E10, 0x6E10, "_MAX")
        M331 (__METHOD__, 0x69, 0x3300, 0x3300, 0x6E50, 0x6E50, "_TRA")
        M331 (__METHOD__, 0x6A, 0x3340, 0x3340, 0x6E90, 0x6E90, "_LEN")
        M331 (__METHOD__, 0x6B, 0x3380, 0x3380, 0x6ED0, 0x6ED0, "_ATT")
        M331 (__METHOD__, 0x6C, 0x33E1, 0x33E1, 0x6F31, 0x6F31, "_DEC")
        M331 (__METHOD__, 0x6D, 0x33E2, 0x33E2, 0x6F32, 0x6F32, "_MIF")
        M331 (__METHOD__, 0x6E, 0x33E3, 0x33E3, 0x6F33, 0x6F33, "_MAF")
        M331 (__METHOD__, 0x6F, 0x33E8, 0x33E8, 0x6F38, 0x6F38, "_RW")
        M331 (__METHOD__, 0x70, 0x33E9, 0x33E9, 0x6F39, 0x6F39, "_MEM")
        M331 (__METHOD__, 0x71, 0x33EB, 0x33EB, 0x6F3B, 0x6F3B, "_MTP")
        M331 (__METHOD__, 0x72, 0x33ED, 0x33ED, 0x6F3D, 0x6F3D, "_TTP")
        M331 (__METHOD__, 0x73, 0x3400, 0x3400, 0x6F50, 0x6F50, "_GRA")
        M331 (__METHOD__, 0x74, 0x3440, 0x3440, 0x6F90, 0x6F90, "_MIN")
        M331 (__METHOD__, 0x75, 0x3480, 0x3480, 0x6FD0, 0x6FD0, "_MAX")
        M331 (__METHOD__, 0x76, 0x34C0, 0x34C0, 0x7010, 0x7010, "_TRA")
        M331 (__METHOD__, 0x77, 0x3500, 0x3500, 0x7050, 0x7050, "_LEN")
        M331 (__METHOD__, 0x78, 0x3540, 0x3540, 0x7090, 0x7090, "_ATT")
        M331 (__METHOD__, 0x79, 0x35A1, 0x35A1, 0x70F1, 0x70F1, "_DEC")
        M331 (__METHOD__, 0x7A, 0x35A2, 0x35A2, 0x70F2, 0x70F2, "_MIF")
        M331 (__METHOD__, 0x7B, 0x35A3, 0x35A3, 0x70F3, 0x70F3, "_MAF")
        M331 (__METHOD__, 0x7C, 0x35C0, 0x35C0, 0x7110, 0x7110, "_GRA")
        M331 (__METHOD__, 0x7D, 0x3600, 0x3600, 0x7150, 0x7150, "_MIN")
        M331 (__METHOD__, 0x7E, 0x3640, 0x3640, 0x7190, 0x7190, "_MAX")
        M331 (__METHOD__, 0x7F, 0x3680, 0x3680, 0x71D0, 0x71D0, "_TRA")
        M331 (__METHOD__, 0x80, 0x36C0, 0x36C0, 0x7210, 0x7210, "_LEN")
        M331 (__METHOD__, 0x81, 0x3700, 0x3700, 0x7250, 0x7250, "_ATT")
        M331 (__METHOD__, 0x82, 0x3761, 0x3761, 0x72B1, 0x72B1, "_DEC")
        M331 (__METHOD__, 0x83, 0x3762, 0x3762, 0x72B2, 0x72B2, "_MIF")
        M331 (__METHOD__, 0x84, 0x3763, 0x3763, 0x72B3, 0x72B3, "_MAF")
        M331 (__METHOD__, 0x85, 0x3770, 0x3770, 0x72C0, 0x72C0, "_GRA")
        M331 (__METHOD__, 0x86, 0x3790, 0x3790, 0x72E0, 0x72E0, "_MIN")
        M331 (__METHOD__, 0x87, 0x37B0, 0x37B0, 0x7300, 0x7300, "_MAX")
        M331 (__METHOD__, 0x88, 0x37D0, 0x37D0, 0x7320, 0x7320, "_TRA")
        M331 (__METHOD__, 0x89, 0x37F0, 0x37F0, 0x7340, 0x7340, "_LEN")
        M331 (__METHOD__, 0x8A, 0x38A1, 0x38A1, 0x73F1, 0x73F1, "_DEC")
        M331 (__METHOD__, 0x8B, 0x38A2, 0x38A2, 0x73F2, 0x73F2, "_MIF")
        M331 (__METHOD__, 0x8C, 0x38A3, 0x38A3, 0x73F3, 0x73F3, "_MAF")
        M331 (__METHOD__, 0x8D, 0x38B0, 0x38B0, 0x7400, 0x7400, "_GRA")
        M331 (__METHOD__, 0x8E, 0x38F0, 0x38F0, 0x7440, 0x7440, "_MIN")
        M331 (__METHOD__, 0x8F, 0x3930, 0x3930, 0x7480, 0x7480, "_MAX")
        M331 (__METHOD__, 0x90, 0x3970, 0x3970, 0x74C0, 0x74C0, "_TRA")
        M331 (__METHOD__, 0x91, 0x39B0, 0x39B0, 0x7500, 0x7500, "_LEN")
        M331 (__METHOD__, 0x92, 0x3A81, 0x3A81, 0x75D1, 0x75D1, "_DEC")
        M331 (__METHOD__, 0x93, 0x3A82, 0x3A82, 0x75D2, 0x75D2, "_MIF")
        M331 (__METHOD__, 0x94, 0x3A83, 0x3A83, 0x75D3, 0x75D3, "_MAF")
        M331 (__METHOD__, 0x95, 0x3A90, 0x3A90, 0x75E0, 0x75E0, "_GRA")
        M331 (__METHOD__, 0x96, 0x3AA0, 0x3AA0, 0x75F0, 0x75F0, "_MIN")
        M331 (__METHOD__, 0x97, 0x3AB0, 0x3AB0, 0x7600, 0x7600, "_MAX")
        M331 (__METHOD__, 0x98, 0x3AC0, 0x3AC0, 0x7610, 0x7610, "_TRA")
        M331 (__METHOD__, 0x99, 0x3AD0, 0x3AD0, 0x7620, 0x7620, "_LEN")
        /* Checkings relating to RT01 */

        M331 (__METHOD__, 0x9A, 0x20, 0x20, 0x4780, 0x4780, "_HE")
        M331 (__METHOD__, 0x9B, 0x23, 0x23, 0x4783, 0x4783, "_LL")
        M331 (__METHOD__, 0x9C, 0x24, 0x24, 0x4784, 0x4784, "_SHR")
        M331 (__METHOD__, 0x9D, 0x60, 0x60, 0x47C0, 0x47C0, "_HE")
        M331 (__METHOD__, 0x9E, 0x63, 0x63, 0x47C3, 0x47C3, "_LL")
        M331 (__METHOD__, 0x9F, 0x64, 0x64, 0x47C4, 0x47C4, "_SHR")
        M331 (__METHOD__, 0xA0, 0x95, 0x95, 0x47F5, 0x47F5, "_TYP")
        M331 (__METHOD__, 0xA1, 0x92, 0x92, 0x47F2, 0x47F2, "_BM")
        M331 (__METHOD__, 0xA2, 0x90, 0x90, 0x47F0, 0x47F0, "_SIZ")
        M331 (__METHOD__, 0xA3, 0xC0, 0xC0, 0x4820, 0x4820, "_HE")
        M331 (__METHOD__, 0xA4, 0xC3, 0xC3, 0x4823, 0x4823, "_LL")
        M331 (__METHOD__, 0xA5, 0xC4, 0xC4, 0x4824, 0x4824, "_SHR")
        M331 (__METHOD__, 0xA6, 0xF5, 0xF5, 0x4855, 0x4855, "_TYP")
        M331 (__METHOD__, 0xA7, 0xF2, 0xF2, 0x4852, 0x4852, "_BM")
        M331 (__METHOD__, 0xA8, 0xF0, 0xF0, 0x4850, 0x4850, "_SIZ")
        M331 (__METHOD__, 0xA9, 0x0100, 0x0100, 0x4860, 0x4860, "_DEC")
        M331 (__METHOD__, 0xAA, 0x0108, 0x0108, 0x4868, 0x4868, "_MIN")
        M331 (__METHOD__, 0xAB, 0x0118, 0x0118, 0x4878, 0x4878, "_MAX")
        M331 (__METHOD__, 0xAC, 0x0128, 0x0128, 0x4888, 0x4888, "_ALN")
        M331 (__METHOD__, 0xAD, 0x0130, 0x0130, 0x4890, 0x4890, "_LEN")
        M331 (__METHOD__, 0xAE, 0x0160, 0x0160, 0x48C0, 0x48C0, "_HE")
        M331 (__METHOD__, 0xAF, 0x0163, 0x0163, 0x48C3, 0x48C3, "_LL")
        M331 (__METHOD__, 0xB0, 0x0164, 0x0164, 0x48C4, 0x48C4, "_SHR")
        M331 (__METHOD__, 0xB1, 0x0195, 0x0195, 0x48F5, 0x48F5, "_TYP")
        M331 (__METHOD__, 0xB2, 0x0192, 0x0192, 0x48F2, 0x48F2, "_BM")
        M331 (__METHOD__, 0xB3, 0x0190, 0x0190, 0x48F0, 0x48F0, "_SIZ")
        M331 (__METHOD__, 0xB4, 0x01A0, 0x01A0, 0x4900, 0x4900, "_DEC")
        M331 (__METHOD__, 0xB5, 0x01A8, 0x01A8, 0x4908, 0x4908, "_MIN")
        M331 (__METHOD__, 0xB6, 0x01B8, 0x01B8, 0x4918, 0x4918, "_MAX")
        M331 (__METHOD__, 0xB7, 0x01C8, 0x01C8, 0x4928, 0x4928, "_ALN")
        M331 (__METHOD__, 0xB8, 0x01D0, 0x01D0, 0x4930, 0x4930, "_LEN")
        M331 (__METHOD__, 0xB9, 0x01E0, 0x01E0, 0x4940, 0x4940, "_BAS")
        M331 (__METHOD__, 0xBA, 0x01F0, 0x01F0, 0x4950, 0x4950, "_LEN")
        M331 (__METHOD__, 0xBB, 0x0220, 0x0220, 0x4980, 0x4980, "_HE")
        M331 (__METHOD__, 0xBC, 0x0223, 0x0223, 0x4983, 0x4983, "_LL")
        M331 (__METHOD__, 0xBD, 0x0224, 0x0224, 0x4984, 0x4984, "_SHR")
        M331 (__METHOD__, 0xBE, 0x0255, 0x0255, 0x49B5, 0x49B5, "_TYP")
        M331 (__METHOD__, 0xBF, 0x0252, 0x0252, 0x49B2, 0x49B2, "_BM")
        M331 (__METHOD__, 0xC0, 0x0250, 0x0250, 0x49B0, 0x49B0, "_SIZ")
        M331 (__METHOD__, 0xC1, 0x0260, 0x0260, 0x49C0, 0x49C0, "_DEC")
        M331 (__METHOD__, 0xC2, 0x0268, 0x0268, 0x49C8, 0x49C8, "_MIN")
        M331 (__METHOD__, 0xC3, 0x0278, 0x0278, 0x49D8, 0x49D8, "_MAX")
        M331 (__METHOD__, 0xC4, 0x0288, 0x0288, 0x49E8, 0x49E8, "_ALN")
        M331 (__METHOD__, 0xC5, 0x0290, 0x0290, 0x49F0, 0x49F0, "_LEN")
        M331 (__METHOD__, 0xC6, 0x02A0, 0x02A0, 0x4A00, 0x4A00, "_BAS")
        M331 (__METHOD__, 0xC7, 0x02B0, 0x02B0, 0x4A10, 0x4A10, "_LEN")
        M331 (__METHOD__, 0xC8, 0x0320, 0x0320, 0x4A80, 0x4A80, "_HE")
        M331 (__METHOD__, 0xC9, 0x0323, 0x0323, 0x4A83, 0x4A83, "_LL")
        M331 (__METHOD__, 0xCA, 0x0324, 0x0324, 0x4A84, 0x4A84, "_SHR")
        M331 (__METHOD__, 0xCB, 0x0355, 0x0355, 0x4AB5, 0x4AB5, "_TYP")
        M331 (__METHOD__, 0xCC, 0x0352, 0x0352, 0x4AB2, 0x4AB2, "_BM")
        M331 (__METHOD__, 0xCD, 0x0350, 0x0350, 0x4AB0, 0x4AB0, "_SIZ")
        M331 (__METHOD__, 0xCE, 0x0360, 0x0360, 0x4AC0, 0x4AC0, "_DEC")
        M331 (__METHOD__, 0xCF, 0x0368, 0x0368, 0x4AC8, 0x4AC8, "_MIN")
        M331 (__METHOD__, 0xD0, 0x0378, 0x0378, 0x4AD8, 0x4AD8, "_MAX")
        M331 (__METHOD__, 0xD1, 0x0388, 0x0388, 0x4AE8, 0x4AE8, "_ALN")
        M331 (__METHOD__, 0xD2, 0x0390, 0x0390, 0x4AF0, 0x4AF0, "_LEN")
        M331 (__METHOD__, 0xD3, 0x03A0, 0x03A0, 0x4B00, 0x4B00, "_BAS")
        M331 (__METHOD__, 0xD4, 0x03B0, 0x03B0, 0x4B10, 0x4B10, "_LEN")
        M331 (__METHOD__, 0xD5, 0x0410, 0x0410, 0x4B70, 0x4B70, "_RW")
        M331 (__METHOD__, 0xD6, 0x0418, 0x0418, 0x4B78, 0x4B78, "_MIN")
        M331 (__METHOD__, 0xD7, 0x0428, 0x0428, 0x4B88, 0x4B88, "_MAX")
        M331 (__METHOD__, 0xD8, 0x0438, 0x0438, 0x4B98, 0x4B98, "_ALN")
        M331 (__METHOD__, 0xD9, 0x0448, 0x0448, 0x4BA8, 0x4BA8, "_LEN")
        M331 (__METHOD__, 0xDA, 0x0480, 0x0480, 0x4BE0, 0x4BE0, "_HE")
        M331 (__METHOD__, 0xDB, 0x0483, 0x0483, 0x4BE3, 0x4BE3, "_LL")
        M331 (__METHOD__, 0xDC, 0x0484, 0x0484, 0x4BE4, 0x4BE4, "_SHR")
        M331 (__METHOD__, 0xDD, 0x04B5, 0x04B5, 0x4C15, 0x4C15, "_TYP")
        M331 (__METHOD__, 0xDE, 0x04B2, 0x04B2, 0x4C12, 0x4C12, "_BM")
        M331 (__METHOD__, 0xDF, 0x04B0, 0x04B0, 0x4C10, 0x4C10, "_SIZ")
        M331 (__METHOD__, 0xE0, 0x04C0, 0x04C0, 0x4C20, 0x4C20, "_DEC")
        M331 (__METHOD__, 0xE1, 0x04C8, 0x04C8, 0x4C28, 0x4C28, "_MIN")
        M331 (__METHOD__, 0xE2, 0x04D8, 0x04D8, 0x4C38, 0x4C38, "_MAX")
        M331 (__METHOD__, 0xE3, 0x04E8, 0x04E8, 0x4C48, 0x4C48, "_ALN")
        M331 (__METHOD__, 0xE4, 0x04F0, 0x04F0, 0x4C50, 0x4C50, "_LEN")
        M331 (__METHOD__, 0xE5, 0x0500, 0x0500, 0x4C60, 0x4C60, "_BAS")
        M331 (__METHOD__, 0xE6, 0x0510, 0x0510, 0x4C70, 0x4C70, "_LEN")
        M331 (__METHOD__, 0xE7, 0x0570, 0x0570, 0x4CD0, 0x4CD0, "_RW")
        M331 (__METHOD__, 0xE8, 0x0578, 0x0578, 0x4CD8, 0x4CD8, "_MIN")
        M331 (__METHOD__, 0xE9, 0x0588, 0x0588, 0x4CE8, 0x4CE8, "_MAX")
        M331 (__METHOD__, 0xEA, 0x0598, 0x0598, 0x4CF8, 0x4CF8, "_ALN")
        M331 (__METHOD__, 0xEB, 0x05A8, 0x05A8, 0x4D08, 0x4D08, "_LEN")
        M331 (__METHOD__, 0xEC, 0x05D0, 0x05D0, 0x4D30, 0x4D30, "_RW")
        M331 (__METHOD__, 0xED, 0x05D8, 0x05D8, 0x4D38, 0x4D38, "_MIN")
        M331 (__METHOD__, 0xEE, 0x05F8, 0x05F8, 0x4D58, 0x4D58, "_MAX")
        M331 (__METHOD__, 0xEF, 0x0618, 0x0618, 0x4D78, 0x4D78, "_ALN")
        M331 (__METHOD__, 0xF0, 0x0638, 0x0638, 0x4D98, 0x4D98, "_LEN")
        /* Checkings below are not exhaustive */

        M331 (__METHOD__, 0xF1, 0x0870, 0x0870, 0x4FD0, 0x4FD0, "_RW")
        M331 (__METHOD__, 0xF2, 0x0878, 0x0878, 0x4FD8, 0x4FD8, "_BAS")
        M331 (__METHOD__, 0xF3, 0x0898, 0x0898, 0x4FF8, 0x4FF8, "_LEN")
        M331 (__METHOD__, 0xF4, 0x43D0, 0x43D0, 0x8B30, 0x8B30, "_RW")
        M331 (__METHOD__, 0xF5, 0x43D8, 0x43D8, 0x8B38, 0x8B38, "_BAS")
        M331 (__METHOD__, 0xF6, 0x43F8, 0x43F8, 0x8B58, 0x8B58, "_LEN")
        M331 (__METHOD__, 0xF7, 0x4640, 0x4640, 0x8DA0, 0x8DA0, "_RW")
        M331 (__METHOD__, 0xF8, 0x4648, 0x4648, 0x8DA8, 0x8DA8, "_BAS")
        M331 (__METHOD__, 0xF9, 0x4668, 0x4668, 0x8DC8, 0x8DC8, "_LEN")
    }
