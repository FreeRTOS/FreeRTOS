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
     * DWord IO Resource Descriptor Macro
     */
    Name (P418, Package (0x25)
    {
        ResourceTemplate ()
        {
            DWordIO (ResourceProducer, MinNotFixed, MaxNotFixed, PosDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceProducer, MinNotFixed, MaxNotFixed, SubDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceProducer, MinNotFixed, MaxFixed, PosDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceProducer, MinNotFixed, MaxFixed, SubDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceProducer, MinFixed, MaxNotFixed, PosDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceProducer, MinFixed, MaxNotFixed, SubDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceProducer, MinFixed, MaxFixed, PosDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceProducer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, SubDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxFixed, PosDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxFixed, SubDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinFixed, MaxNotFixed, PosDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinFixed, MaxNotFixed, SubDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinFixed, MaxFixed, PosDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, NonISAOnlyRanges,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, NonISAOnlyRanges,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, SparseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, NonISAOnlyRanges,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeTranslation, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, NonISAOnlyRanges,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeTranslation, SparseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, ISAOnlyRanges,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, ISAOnlyRanges,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, SparseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, ISAOnlyRanges,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeTranslation, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, ISAOnlyRanges,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeTranslation, SparseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, SparseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeTranslation, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeTranslation, SparseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                0x01, "", , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                0x0F, "P", , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                0xF0, "PATH", , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                0xFF, "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*", , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0x00000000,         // Granularity
                0x00000000,         // Range Minimum
                0x00000000,         // Range Maximum
                0x00000000,         // Translation Offset
                0x00000000,         // Length
                0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                0x0F,, , TypeStatic, DenseTranslation)
        }
    })
    /*
     ACPI Specification, Revision 3.0, September 2, 2004
     6.4.3.5.2   DWord Address Space Descriptor
     I/O DWord Address Space Descriptor layout:
     Byte 0 (Tag Bits): Value=10000111B (0x87) (Type = 1, Large item name = 0x7)
     Byte 1 (Length, bits[7:0]): Variable: Value = 23 (minimum)
     Byte 2 (Length, bits[15:8]): Variable: Value = 0 (minimum)
     Byte 3 (Resource Type):
     1		I/O range
     Byte 4 (General Flags):
     Bits[7:4] 	Reserved (must be 0)
     Bit[3] 		Min Address Fixed, _MAF:
     1	The specified maximum address is fixed
     0	The specified maximum address is not fixed
     and can be changed
     Bit[2] 		Max Address Fixed,_MIF:
     1	The specified minimum address is fixed
     0	The specified minimum address is not fixed
     and can be changed
     Bit[1] 		Decode Type, _DEC:
     1	This bridge subtractively decodes this address
     (top level bridges only)
     0	This bridge positively decodes this address
     Bit[0] 		Consumer/Producer:
     1-This device consumes this resource
     0-This device produces and consumes this resource
     Byte 5 (Type Specific Flags):
     Flags that are specific to each resource type. The meaning of the flags
     in this field depends on the value of the Resource Type field (see above)
     Bits[7:6]	Reserved (must be 0)
     Bit[5]		Sparse Translation, _TRS. This bit is only meaningful if Bit[4] is set.
     1	SparseTranslation: The primary-side memory address of any specific
     I/O port within the secondary-side range can be found using
     the following function.
     address = (((port & 0xFFFc) << 10) || (port & 0xFFF)) + _TRA
     In the address used to access the I/O port, bits[11:2] must be identical
     to bits[21:12], this gives four bytes of I/O ports on each 4 KB page.
     0	DenseTranslation: The primary-side memory address of any specific I/O port
     within the secondary-side range can be found using the following function.
     address = port + _TRA
     Bit[4]		I/O to Memory Translation, _TTP
     1	TypeTranslation: This resource, which is I/O on the secondary side of
     the bridge, is memory on the primary side of the bridge.
     0	TypeStatic: This resource, which is I/O on the secondary side of
     the bridge, is also I/O on the primary side of the bridge.
     Bit[3:2]	Reserved (must be 0)
     Bit[1:0]	_RNG
     3	Memory window covers the entire range
     2	ISARangesOnly. This flag is for bridges on systems with multiple bridges.
     Setting this bit means the memory window specified in this descriptor is
     limited to the ISA I/O addresses that fall within the specified window.
     The ISA I/O ranges are: n000-n0FF, n400-n4FF, n800-n8FF, nC00-nCFF. This
     bit can only be set for bridges entirely configured through ACPI namespace.
     1	NonISARangesOnly. This flag is for bridges on systems with multiple bridges.
     Setting this bit means the memory window specified in this descriptor is
     limited to the non-ISA I/O addresses that fall within the specified window.
     The non-ISA I/O ranges are: n100-n3FF, n500-n7FF, n900-nBFF, nD00-nFFF.
     This bit can only be set for bridges entirely configured through ACPI namespace.
     0	Reserved
     Byte 6 (Address space granularity, _GRA bits[7:0]):
     A set bit in this mask means that this bit is decoded. All bits less
     significant than the most significant set bit must be set. (in other
     words, the value of the full Address Space Granularity field (all 32
     bits) must be a number (2**n-1).
     Byte 7 (Address space granularity, _GRA bits[15:8])
     Byte 8 (Address space granularity, _GRA bits[23:16])
     Byte 9 (Address space granularity, _GRA bits[31:24])
     Byte 10 (Address range minimum, _MIN bits [7:0]):
     For bridges that translate addresses, this is the address space
     on the secondary side of the bridge
     Byte 11 (Address range minimum, _MIN bits[15:8])
     Byte 12 (Address range minimum, _MIN bits[23:16])
     Byte 13 (Address range minimum, _MIN bits[31:24])
     Byte 14 (Address range maximum, _MAX bits [7:0]): See comment for _MIN
     Byte 15 (Address range maximum, _MAX bits[15:8])
     Byte 16 (Address range maximum, _MAX bits[23:16])
     Byte 17 (Address range maximum, _MAX bits[31:24])
     Byte 18 (Address Translation offset, _TRA bits [7:0]):
     For bridges that translate addresses across the bridge, this is the
     offset that must be added to the address on the secondary side to obtain
     the address on the primary side. Non-bridge devices must list 0 for all
     Address Translation offset bits
     Byte 19 (Address Translation offset, _TRA bits[15:8])
     Byte 20 (Address Translation offset, _TRA bits[23:16])
     Byte 21 (Address Translation offset, _TRA bits[31:24])
     Byte 22 (Address Length, _LEN bits [7:0])
     Byte 23 (Address Length, _LEN bits[15:8])
     Byte 24 (Address Length, _LEN bits[23:16])
     Byte 25 (Address Length, _LEN bits[31:24])
     Byte 26 (Resource Source Index):
     (Optional) Only present if Resource Source (below) is present. This
     field gives an index to the specific resource descriptor that this
     device consumes from in the current resource template for the device
     object pointed to in Resource Source
     String (Resource Source):
     (Optional) If present, the device that uses this descriptor consumes
     its resources from the resources produced by the named device object.
     If not present, the device consumes its resources out of a global pool.
     If not present, the device consumes this resource from its hierarchical
     parent.
     */
    Name (P419, Package (0x25)
    {
        /* Byte 4 (General Flags) of DWord Address Space Descriptor */

        ResourceTemplate ()
        {
            DWordIO (ResourceProducer, MinNotFixed, MaxNotFixed, PosDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceProducer, MinNotFixed, MaxNotFixed, SubDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceProducer, MinNotFixed, MaxFixed, PosDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceProducer, MinNotFixed, MaxFixed, SubDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceProducer, MinFixed, MaxNotFixed, PosDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceProducer, MinFixed, MaxNotFixed, SubDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceProducer, MinFixed, MaxFixed, PosDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceProducer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, SubDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxFixed, PosDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxFixed, SubDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinFixed, MaxNotFixed, PosDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinFixed, MaxNotFixed, SubDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinFixed, MaxFixed, PosDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        /* Byte 5 (Type Specific Flags) of DWord Address Space Descriptor */

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, NonISAOnlyRanges,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, NonISAOnlyRanges,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, SparseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, NonISAOnlyRanges,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeTranslation, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, NonISAOnlyRanges,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeTranslation, SparseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, ISAOnlyRanges,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, ISAOnlyRanges,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, SparseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, ISAOnlyRanges,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeTranslation, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, ISAOnlyRanges,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeTranslation, SparseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, SparseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeTranslation, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeTranslation, SparseTranslation)
        },

        /* Particular cases */

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                ,, , TypeStatic, DenseTranslation)
        },

        /* Resource Source */

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                0x01, "", , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                0x0F, "P", , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                0xF0, "PATH", , TypeStatic, DenseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                0xFF, "!\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ !\"#$%&\'()*", , TypeStatic, DenseTranslation)
        },

        /* Particular cases */

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
        },

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinFixed, MaxFixed, SubDecode, EntireRange,
                0x00000000,         // Granularity
                0x00000000,         // Range Minimum
                0x00000000,         // Range Maximum
                0x00000000,         // Translation Offset
                0x00000000,         // Length
                0xFF, "PATHPATHPATH", , TypeTranslation, SparseTranslation)
        },

        /* 20051021, relaxation for omitted ResourceSource (bug-fix 70 rejection) */

        ResourceTemplate ()
        {
            DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, EntireRange,
                0xECEDEEEF,         // Granularity
                0xF0F1F2F3,         // Range Minimum
                0xF4F5F6F7,         // Range Maximum
                0xF8F9FAFB,         // Translation Offset
                0xFCFDFEFF,         // Length
                0x0F,, , TypeStatic, DenseTranslation)
        }
    })
    Method (RT0D, 0, Serialized)
    {
        /* Emit test header, set the filename */

        THDR (__METHOD__, "DWordIo Resource Descriptor Macro", "dwordio.asl")
        /* Main test case for packages above */

        M330 (__METHOD__, 0x25, "p418", P418, P419)
        /* Check resource descriptor tag offsets */

        Local0 = ResourceTemplate ()
            {
                DWordIO (ResourceProducer, MinNotFixed, MaxNotFixed, PosDecode, EntireRange,
                    0xECEDEEEF,         // Granularity
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Translation Offset
                    0xFCFDFEFF,         // Length
                    ,, , TypeStatic, DenseTranslation)
                DWordIO (ResourceConsumer, MinNotFixed, MaxNotFixed, PosDecode, EntireRange,
                    0xECEDEEEF,         // Granularity
                    0xF0F1F2F3,         // Range Minimum
                    0xF4F5F6F7,         // Range Maximum
                    0xF8F9FAFB,         // Translation Offset
                    0xFCFDFEFF,         // Length
                    ,, , TypeStatic, DenseTranslation)
            }
        M331 (__METHOD__, 0x01, 0x21, 0x21, 0xF1, 0xF1, "_DEC")
        M331 (__METHOD__, 0x02, 0x22, 0x22, 0xF2, 0xF2, "_MIF")
        M331 (__METHOD__, 0x03, 0x23, 0x23, 0xF3, 0xF3, "_MAF")
        M331 (__METHOD__, 0x04, 0x28, 0x28, 0xF8, 0xF8, "_RNG")
        M331 (__METHOD__, 0x05, 0x2C, 0x2C, 0xFC, 0xFC, "_TTP")
        M331 (__METHOD__, 0x06, 0x2D, 0x2D, 0xFD, 0xFD, "_TRS")
        M331 (__METHOD__, 0x07, 0x30, 0x30, 0x0100, 0x0100, "_GRA")
        M331 (__METHOD__, 0x08, 0x50, 0x50, 0x0120, 0x0120, "_MIN")
        M331 (__METHOD__, 0x09, 0x70, 0x70, 0x0140, 0x0140, "_MAX")
        M331 (__METHOD__, 0x0A, 0x90, 0x90, 0x0160, 0x0160, "_TRA")
        M331 (__METHOD__, 0x0B, 0xB0, 0xB0, 0x0180, 0x0180, "_LEN")
    }
