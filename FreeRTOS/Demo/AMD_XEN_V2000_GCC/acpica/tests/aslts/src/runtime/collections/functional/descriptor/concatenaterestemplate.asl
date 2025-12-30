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
     * Concatenate two resource templates
     */
    Name (Z007, 0x07)
    Name (P440, Package (0x03)
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
                0xF0F1,             // Address
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
                0xF0F1,             // Address
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
                    0xF0F1,             // Address
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
                    0xF0F1,             // Address
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
                    0xF0F1,             // Address
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
                    0xF0F1,             // Address
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
                    0xF0F1,             // Address
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
                    0xF0F1,             // Address
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
                    0xF0F1,             // Address
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
                    0xF0F1,             // Address
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
                    0xF0F1,             // Address
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
                    0xF0F1,             // Address
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
                    0xF0F1,             // Address
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
                    0xF0F1,             // Address
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
                    0xF0F1,             // Address
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
                    0xF0F1,             // Address
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
    /* Particular cases */

    Name (P441, Package (0x01)
    {
        ResourceTemplate ()
        {
            DMA (Compatibility, BusMaster, Transfer8_16, )
                {4}
        }
        /* Buffer () {0x00, 0x00, 0x00, 0x79, 0x00}, */
    /* Buffer () {0x2a, 0x10, 0x05, 0x79}, */
    /* Empty buffer */
    })
    Name (P442, Package (0x02)
    {
        ResourceTemplate ()
        {
            IRQNoFlags ()
                {1}
        },

        ResourceTemplate ()
        {
            IRQNoFlags ()
                {1}
        }
        /*
     * ResourceTemplate () {
     *	IRQNoFlags () {1}
     * },
     *
     * ResourceTemplate () {
     *	IRQNoFlags () {1}
     * },
     */
    })
    Name (P443, Package (0x02)
    {
        ResourceTemplate ()
        {
            DMA (Compatibility, BusMaster, Transfer8_16, )
                {4}
            IRQNoFlags ()
                {1}
        },

        /* Buffer () {0x00, 0x00, 0x00, 0x22, 0x02, 0x00, 0x79, 0}, */
        /* Buffer () {0x2a, 0x10, 0x05, 0x22, 0x02, 0x00, 0x79, 0}, */
        ResourceTemplate ()
        {
            IRQNoFlags ()
                {1}
        }
    })
    Name (P444, Package (0x02)
    {
        ResourceTemplate ()
        {
            IRQNoFlags ()
                {1}
            DMA (Compatibility, BusMaster, Transfer8_16, )
                {4}
        },

        /* Buffer () {0x22, 0x02, 0x00, 0x00, 0x00, 0x00, 0x79, 0}, */
        /* Buffer () {0x22, 0x02, 0x00, 0x2a, 0x10, 0x05, 0x79, 0}, */
        ResourceTemplate ()
        {
            IRQNoFlags ()
                {1}
        }
    })
    Method (RT1B, 0, Serialized)
    {
        /* Emit test header, set the filename */

        THDR (__METHOD__, "Concatenate two resource templates", "concatenaterestemplate.asl")
        /* Calculate the checksum for the target first */
        /*	m334(p440, 3) */
        /*	m332(ts, 3, "p440", p438, p438, p440) */
        /* Particular cases */
        /*	Store(0, Local0) */
        /*	Store(Buffer(Local0){}, Local1) */
        /*	Store(Local1, Index(p441, 1)) */
        M332 (__METHOD__, 0x01, "p443", P441, P442, P443)
        M332 (__METHOD__, 0x01, "p444", P442, P441, P444)
        CH03 (__METHOD__, Z007, __LINE__, 0x00, 0x00)
    }
