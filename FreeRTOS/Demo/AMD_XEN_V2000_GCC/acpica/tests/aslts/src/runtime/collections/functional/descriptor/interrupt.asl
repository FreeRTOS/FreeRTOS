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
     * Interrupt() Interrupt Resource Descriptor Macro
     */
    Name (Z017, 0x11)
    Name (P434, Package (0x17)
    {
        ResourceTemplate ()
        {
            Interrupt (ResourceProducer, Level, ActiveHigh, Exclusive, ,, )
            {
                0xFCFDFEFF,
            }
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceProducer, Level, ActiveHigh, Shared, ,, )
            {
                0xF8F9FAFB,
                0xFCFDFEFF,
            }
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceProducer, Level, ActiveLow, Exclusive, ,, )
            {
                0xF4F5F6F7,
                0xF8F9FAFB,
                0xFCFDFEFF,
            }
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceProducer, Level, ActiveLow, Shared, ,, )
            {
                0xF0F1F2F3,
                0xF4F5F6F7,
                0xF8F9FAFB,
                0xFCFDFEFF,
            }
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceProducer, Edge, ActiveHigh, Exclusive, ,, )
            {
                0xECEDEEEF,
                0xF0F1F2F3,
                0xF4F5F6F7,
                0xF8F9FAFB,
                0xFCFDFEFF,
            }
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceProducer, Edge, ActiveHigh, Shared, ,, )
            {
                0xE8E9EAEB,
                0xECEDEEEF,
                0xF0F1F2F3,
                0xF4F5F6F7,
                0xF8F9FAFB,
                0xFCFDFEFF,
            }
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceProducer, Edge, ActiveLow, Exclusive, ,, )
            {
                0xE4E5E6E7,
                0xE8E9EAEB,
                0xECEDEEEF,
                0xF0F1F2F3,
                0xF4F5F6F7,
                0xF8F9FAFB,
                0xFCFDFEFF,
            }
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceProducer, Edge, ActiveLow, Shared, ,, )
            {
                0xE0E1E2E3,
                0xE4E5E6E7,
                0xE8E9EAEB,
                0xECEDEEEF,
                0xF0F1F2F3,
                0xF4F5F6F7,
                0xF8F9FAFB,
                0xFCFDFEFF,
            }
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceConsumer, Level, ActiveHigh, Exclusive, ,, )
            {
                0xDCDDDEDF,
                0xE0E1E2E3,
                0xE4E5E6E7,
                0xE8E9EAEB,
                0xECEDEEEF,
                0xF0F1F2F3,
                0xF4F5F6F7,
                0xF8F9FAFB,
                0xFCFDFEFF,
            }
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceConsumer, Level, ActiveHigh, Shared, ,, )
            {
                0xD8D9DADB,
                0xDCDDDEDF,
                0xE0E1E2E3,
                0xE4E5E6E7,
                0xE8E9EAEB,
                0xECEDEEEF,
                0xF0F1F2F3,
                0xF4F5F6F7,
                0xF8F9FAFB,
                0xFCFDFEFF,
            }
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceConsumer, Level, ActiveLow, Exclusive, ,, )
            {
                0xD4D5D6D7,
                0xD8D9DADB,
                0xDCDDDEDF,
                0xE0E1E2E3,
                0xE4E5E6E7,
                0xE8E9EAEB,
                0xECEDEEEF,
                0xF0F1F2F3,
                0xF4F5F6F7,
                0xF8F9FAFB,
                0xFCFDFEFF,
            }
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceConsumer, Level, ActiveLow, Shared, ,, )
            {
                0xD0D1D2D3,
                0xD4D5D6D7,
                0xD8D9DADB,
                0xDCDDDEDF,
                0xE0E1E2E3,
                0xE4E5E6E7,
                0xE8E9EAEB,
                0xECEDEEEF,
                0xF0F1F2F3,
                0xF4F5F6F7,
                0xF8F9FAFB,
                0xFCFDFEFF,
            }
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceConsumer, Edge, ActiveHigh, Exclusive, ,, )
            {
                0xCCCDCECF,
                0xD0D1D2D3,
                0xD4D5D6D7,
                0xD8D9DADB,
                0xDCDDDEDF,
                0xE0E1E2E3,
                0xE4E5E6E7,
                0xE8E9EAEB,
                0xECEDEEEF,
                0xF0F1F2F3,
                0xF4F5F6F7,
                0xF8F9FAFB,
                0xFCFDFEFF,
            }
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceConsumer, Edge, ActiveHigh, Shared, ,, )
            {
                0xC8C9CACB,
                0xCCCDCECF,
                0xD0D1D2D3,
                0xD4D5D6D7,
                0xD8D9DADB,
                0xDCDDDEDF,
                0xE0E1E2E3,
                0xE4E5E6E7,
                0xE8E9EAEB,
                0xECEDEEEF,
                0xF0F1F2F3,
                0xF4F5F6F7,
                0xF8F9FAFB,
                0xFCFDFEFF,
            }
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceConsumer, Edge, ActiveLow, Exclusive, ,, )
            {
                0xC4C5C6C7,
                0xC8C9CACB,
                0xCCCDCECF,
                0xD0D1D2D3,
                0xD4D5D6D7,
                0xD8D9DADB,
                0xDCDDDEDF,
                0xE0E1E2E3,
                0xE4E5E6E7,
                0xE8E9EAEB,
                0xECEDEEEF,
                0xF0F1F2F3,
                0xF4F5F6F7,
                0xF8F9FAFB,
                0xFCFDFEFF,
            }
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceConsumer, Edge, ActiveLow, Shared, ,, )
            {
                0xC0C1C2C3,
                0xC4C5C6C7,
                0xC8C9CACB,
                0xCCCDCECF,
                0xD0D1D2D3,
                0xD4D5D6D7,
                0xD8D9DADB,
                0xDCDDDEDF,
                0xE0E1E2E3,
                0xE4E5E6E7,
                0xE8E9EAEB,
                0xECEDEEEF,
                0xF0F1F2F3,
                0xF4F5F6F7,
                0xF8F9FAFB,
                0xFCFDFEFF,
            }
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceConsumer, Edge, ActiveLow, Shared, ,, )
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
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceConsumer, Edge, ActiveLow, Shared, 0x01, "", )
            {
                0xFCFDFEFF,
            }
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceConsumer, Edge, ActiveLow, Shared, 0x0F, "P", )
            {
                0xFCFDFEFF,
            }
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceConsumer, Edge, ActiveLow, Shared, 0xF0, "PATH", )
            {
                0xFCFDFEFF,
            }
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceConsumer, Edge, ActiveLow, Shared, 0xFF, "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*", )
            {
                0xFCFDFEFF,
            }
        },

        ResourceTemplate ()
        {
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
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceConsumer, Edge, ActiveLow, Shared, 0x0F,, )
            {
                0xFCFDFEFF,
            }
        }
    })
    /*
     ACPI Specification, Revision 3.0, September 2, 2004
     6.4.3.6   Extended Interrupt Descriptor
     Extended Interrupt Descriptor layout:
     Byte 0	Extended Interrupt Descriptor	Value=10001001B (0x89) (Type = 1, Large item name = 0x9)
     Byte 1	Length, bits[7:0]	Variable: Value = 6 (minimum)
     Byte 2	Length, bits[15:8]	Variable: Value = 0 (minimum)
     Byte 3	Interrupt Vector Flags	Interrupt Vector Information.
     Bit[7:4]	Reserved (must be 0)
     Bit[3]		Interrupt is shareable, _SHR
     Bit[2] 		Interrupt Polarity, _LL
     0	Active-High: This interrupt is sampled
     when the signal is high, or true.
     1	Active-Low: This interrupt is sampled
     when the signal is low, or false.
     Bit[1] 		Interrupt Mode, _HE
     0	Level-Triggered: Interrupt is triggered in response
     to the signal being in either a high or low state.
     1	Edge-Triggered: This interrupt is
     triggered in response to a change in signal
     state, either high to low or low to high.
     Bit[0] 		Consumer/Producer:
     1-This device consumes this resource
     0-This device produces and consumes this resource
     Byte 4	Interrupt table length	Indicates the number of interrupt numbers that follow.
     When this descriptor is returned from _CRS, or when OSPM
     passes this descriptor to _SRS, this field must be set to 1.
     Byte 4n+5	Interrupt Number, _INT bits [7:0]	Interrupt number
     Byte 4n+6	Interrupt Number, _INT bits [15:8]
     Byte 4n+7	Interrupt Number, _INT bits [23:16]
     Byte 4n+8	Interrupt Number, _INT bits [31:24]
     Additional interrupt numbers
     Byte x	Resource Source Index	(Optional) Only present if Resource Source (below) is present.
     This field gives an index to the specific resource descriptor
     that this device consumes from in the current resource template
     for the device object pointed to in Resource Source.
     String	Resource Source	(Optional)  If present, the device that uses this descriptor consumes its
     resources from the resources produces by the named device object.
     If not present, the device consumes its resources out of a global
     pool. If not present, the device consumes this resource from its
     hierarchical parent.
     */
    Name (P435, Package (0x17)
    {
        /* Byte 3 (Interrupt Vector Flags) of Extended Interrupt Descriptor */

        ResourceTemplate ()
        {
            Interrupt (ResourceProducer, Level, ActiveHigh, Exclusive, ,, )
            {
                0xFCFDFEFF,
            }
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceProducer, Level, ActiveHigh, Shared, ,, )
            {
                0xF8F9FAFB,
                0xFCFDFEFF,
            }
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceProducer, Level, ActiveLow, Exclusive, ,, )
            {
                0xF4F5F6F7,
                0xF8F9FAFB,
                0xFCFDFEFF,
            }
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceProducer, Level, ActiveLow, Shared, ,, )
            {
                0xF0F1F2F3,
                0xF4F5F6F7,
                0xF8F9FAFB,
                0xFCFDFEFF,
            }
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceProducer, Edge, ActiveHigh, Exclusive, ,, )
            {
                0xECEDEEEF,
                0xF0F1F2F3,
                0xF4F5F6F7,
                0xF8F9FAFB,
                0xFCFDFEFF,
            }
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceProducer, Edge, ActiveHigh, Shared, ,, )
            {
                0xE8E9EAEB,
                0xECEDEEEF,
                0xF0F1F2F3,
                0xF4F5F6F7,
                0xF8F9FAFB,
                0xFCFDFEFF,
            }
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceProducer, Edge, ActiveLow, Exclusive, ,, )
            {
                0xE4E5E6E7,
                0xE8E9EAEB,
                0xECEDEEEF,
                0xF0F1F2F3,
                0xF4F5F6F7,
                0xF8F9FAFB,
                0xFCFDFEFF,
            }
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceProducer, Edge, ActiveLow, Shared, ,, )
            {
                0xE0E1E2E3,
                0xE4E5E6E7,
                0xE8E9EAEB,
                0xECEDEEEF,
                0xF0F1F2F3,
                0xF4F5F6F7,
                0xF8F9FAFB,
                0xFCFDFEFF,
            }
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceConsumer, Level, ActiveHigh, Exclusive, ,, )
            {
                0xDCDDDEDF,
                0xE0E1E2E3,
                0xE4E5E6E7,
                0xE8E9EAEB,
                0xECEDEEEF,
                0xF0F1F2F3,
                0xF4F5F6F7,
                0xF8F9FAFB,
                0xFCFDFEFF,
            }
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceConsumer, Level, ActiveHigh, Shared, ,, )
            {
                0xD8D9DADB,
                0xDCDDDEDF,
                0xE0E1E2E3,
                0xE4E5E6E7,
                0xE8E9EAEB,
                0xECEDEEEF,
                0xF0F1F2F3,
                0xF4F5F6F7,
                0xF8F9FAFB,
                0xFCFDFEFF,
            }
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceConsumer, Level, ActiveLow, Exclusive, ,, )
            {
                0xD4D5D6D7,
                0xD8D9DADB,
                0xDCDDDEDF,
                0xE0E1E2E3,
                0xE4E5E6E7,
                0xE8E9EAEB,
                0xECEDEEEF,
                0xF0F1F2F3,
                0xF4F5F6F7,
                0xF8F9FAFB,
                0xFCFDFEFF,
            }
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceConsumer, Level, ActiveLow, Shared, ,, )
            {
                0xD0D1D2D3,
                0xD4D5D6D7,
                0xD8D9DADB,
                0xDCDDDEDF,
                0xE0E1E2E3,
                0xE4E5E6E7,
                0xE8E9EAEB,
                0xECEDEEEF,
                0xF0F1F2F3,
                0xF4F5F6F7,
                0xF8F9FAFB,
                0xFCFDFEFF,
            }
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceConsumer, Edge, ActiveHigh, Exclusive, ,, )
            {
                0xCCCDCECF,
                0xD0D1D2D3,
                0xD4D5D6D7,
                0xD8D9DADB,
                0xDCDDDEDF,
                0xE0E1E2E3,
                0xE4E5E6E7,
                0xE8E9EAEB,
                0xECEDEEEF,
                0xF0F1F2F3,
                0xF4F5F6F7,
                0xF8F9FAFB,
                0xFCFDFEFF,
            }
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceConsumer, Edge, ActiveHigh, Shared, ,, )
            {
                0xC8C9CACB,
                0xCCCDCECF,
                0xD0D1D2D3,
                0xD4D5D6D7,
                0xD8D9DADB,
                0xDCDDDEDF,
                0xE0E1E2E3,
                0xE4E5E6E7,
                0xE8E9EAEB,
                0xECEDEEEF,
                0xF0F1F2F3,
                0xF4F5F6F7,
                0xF8F9FAFB,
                0xFCFDFEFF,
            }
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceConsumer, Edge, ActiveLow, Exclusive, ,, )
            {
                0xC4C5C6C7,
                0xC8C9CACB,
                0xCCCDCECF,
                0xD0D1D2D3,
                0xD4D5D6D7,
                0xD8D9DADB,
                0xDCDDDEDF,
                0xE0E1E2E3,
                0xE4E5E6E7,
                0xE8E9EAEB,
                0xECEDEEEF,
                0xF0F1F2F3,
                0xF4F5F6F7,
                0xF8F9FAFB,
                0xFCFDFEFF,
            }
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceConsumer, Edge, ActiveLow, Shared, ,, )
            {
                0xC0C1C2C3,
                0xC4C5C6C7,
                0xC8C9CACB,
                0xCCCDCECF,
                0xD0D1D2D3,
                0xD4D5D6D7,
                0xD8D9DADB,
                0xDCDDDEDF,
                0xE0E1E2E3,
                0xE4E5E6E7,
                0xE8E9EAEB,
                0xECEDEEEF,
                0xF0F1F2F3,
                0xF4F5F6F7,
                0xF8F9FAFB,
                0xFCFDFEFF,
            }
        },

        /* At the moment returning */
        /* Buffer () {0x89, 0x06, 0x00, 0x0f, 0x01, 0x00, 0x00, 0x00, 0x00, 0x79, 0x00}, */
        ResourceTemplate ()
        {
            Interrupt (ResourceConsumer, Edge, ActiveLow, Shared, ,, )
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
        },

        /* Resource Source */

        ResourceTemplate ()
        {
            Interrupt (ResourceConsumer, Edge, ActiveLow, Shared, 0x01, "", )
            {
                0xFCFDFEFF,
            }
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceConsumer, Edge, ActiveLow, Shared, 0x0F, "P", )
            {
                0xFCFDFEFF,
            }
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceConsumer, Edge, ActiveLow, Shared, 0xF0, "PATH", )
            {
                0xFCFDFEFF,
            }
        },

        ResourceTemplate ()
        {
            Interrupt (ResourceConsumer, Edge, ActiveLow, Shared, 0xFF, "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*", )
            {
                0xFCFDFEFF,
            }
        },

        /* Particular cases */

        ResourceTemplate ()
        {
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
        },

        /* 20051021, relaxation for omitted ResourceSource (bug-fix 70 rejection) */

        ResourceTemplate ()
        {
            Interrupt (ResourceConsumer, Edge, ActiveLow, Shared, 0x0F,, )
            {
                0xFCFDFEFF,
            }
        }
    })
    Method (RT18, 0, Serialized)
    {
        /* Emit test header, set the filename */

        THDR (__METHOD__, "Interrupt Resource Descriptor Macro", "interrupt.asl")
        /* Main test case for packages above */

        M330 (__METHOD__, 0x17, "p434", P434, P435)
        /* Check resource descriptor tag offsets */

        Local0 = ResourceTemplate ()
            {
                Interrupt (ResourceProducer, Edge, ActiveLow, Shared, ,, )
                {
                    0xFCFDFEFF,
                }
                Interrupt (ResourceProducer, Edge, ActiveLow, Shared, ,, )
                {
                    0xFCFDFEFF,
                }
            }
        M331 (__METHOD__, 0x01, 0x19, 0x19, 0x61, 0x61, "_HE")
        M331 (__METHOD__, 0x02, 0x1A, 0x1A, 0x62, 0x62, "_LL")
        M331 (__METHOD__, 0x03, 0x1B, 0x1B, 0x63, 0x63, "_SHR")
        M331 (__METHOD__, 0x04, 0x28, 0x28, 0x70, 0x70, "_INT")
        CH03 (__METHOD__, Z017, __LINE__, 0x00, 0x00)
    }
