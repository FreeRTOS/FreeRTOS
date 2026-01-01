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
     * Common use Data
     */
    Name (ID00, 0xE0385BCD)
    Name (ID01, 0x00) /* Flag of error, used by demo-162 */
    Name (ID02, 0x00) /* Flag of presence of demo-162 test */
    Name (ID09, 0x00)
    Name (ID0A, 0x00)
    Name (ID0B, 0x89ABCDEF)
    Name (SD00, "String")
    Name (BD00, Buffer (0x20)
    {
         0x01, 0x02, 0x03, 0x04                           // ....
    })
    Name (BD02, Buffer (0x14)
    {
        /* 0000 */  0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,  // ........
        /* 0008 */  0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F,  // ........
        /* 0010 */  0x20, 0x21, 0x22, 0x23                           //  !"#
    })
    CreateField (BD00, 0x00, 0x08, BF30)
    CreateField (BD00, 0x08, 0x41, BF31)
    Name (PD00, Package (0x01)
    {
        Buffer (0x04)
        {
             0x01, 0x02, 0x03, 0x04                           // ....
        }
    })
    Device (DD00)
    {
        Name (I900, 0xABCD0017)
    }

    Device (DD01)
    {
        Name (I900, 0xABCD0017)
    }

    Device (DD02)
    {
        Name (I900, 0xABCD0017)
    }

    Device (DD03)
    {
        Name (I900, 0xABCD0017)
    }

    Device (DD04)
    {
        Name (I900, 0xABCD0017)
    }

    Device (DD05)
    {
        Name (I900, 0xABCD0017)
    }

    Device (DD06)
    {
        Name (I900, 0xABCD0017)
    }

    Device (DD07)
    {
        Name (I900, 0xABCD0017)
    }

    OperationRegion (RD00, SystemMemory, 0x0100, 0x0100)
    Field (RD00, ByteAcc, NoLock, Preserve)
    {
        FD00,   8,
        FD01,   65
    }

    /*
     * Global CreateField declarations for bug 161
     */
    /* Comment/uncomment it */
    Name (ID03, 0x08)
    Name (ID04, 0x40)
    Name (ID05, 0x50)
    Name (ID06, 0x08)
    Name (ID07, 0x50)
    Name (ID08, 0x08)
    Name (BD03, Buffer (0x14)
    {
        /* 0000 */  0x10, 0x5D, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,  // .]......
        /* 0008 */  0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F,  // ........
        /* 0010 */  0x20, 0x21, 0x22, 0x23                           //  !"#
    })
    /* Caused stack overflow */

    CreateField (BD03, 0x20, ID03, BF32)
    /* CreateField(bd03, 32, 8, bf32) */

    CreateField (BD03, 0x28, (ID03 + 0x08), BF33)
    /* Caused stack overflow */

    CreateField (BD03, ID04, 0x08, BF34)
    /* CreateField(bd03, 64, 8, bf34) */

    CreateField (BD03, (ID04 + 0x08), 0x08, BF35)
    /* Caused stack overflow */

    CreateField (BD03, ID05, ID06, BF36)
    /* CreateField(bd03, 80, 8, bf36) */

    CreateField (BD03, (ID07 + 0x08), (ID08 + 0x08), BF37)
    /* ==================== Additional: */

    CreateBitField (BD03, 0x08, BF40)
    CreateByteField (BD03, 0x01, BF41)
    CreateWordField (BD03, 0x01, BF42)
    CreateDWordField (BD03, 0x01, BF43)
    CreateQWordField (BD03, 0x01, BF44)
    CreateField (BD03, 0x08, 0x08, BF45)
    Name (ID21, 0x01)
    Name (ID22, 0x08)
    CreateBitField (BD03, ID22, BF46)
    CreateByteField (BD03, ID21, BF47)
    CreateWordField (BD03, ID21, BF48)
    CreateDWordField (BD03, ID21, BF49)
    CreateQWordField (BD03, ID21, BF4A)
    CreateField (BD03, 0x08, ID22, BF4B)
    CreateField (BD03, ID22, 0x08, BF4C)
    CreateField (BD03, ID22, ID22, BF4D)
    /* ==================== bug 161. */
    /* 161 */
    Mutex (MXD0, 0x00)
    Event (ED00)
    OperationRegion (RD01, SystemMemory, 0x0100, 0x0100)
    OperationRegion (RD02, SystemMemory, 0x0100, 0x0100)
    Name (PD01, Package (0x01)
    {
        0x89ABCDEF
    })
    Name (DD08, 0x12)
    Name (SD01, "123456789")
    Name (BD04, Buffer (0x09)
    {
        /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
        /* 0008 */  0x09                                             // .
    })
    Name (ID0C, 0x12)
    Name (SD02, "123456789")
    Name (BD05, Buffer (0x09)
    {
        /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,  // ........
        /* 0008 */  0x09                                             // .
    })
    Name (PD02, Package (0x09)
    {
        0x01,
        0x02,
        0x03,
        0x04,
        0x05,
        0x06,
        0x07,
        0x08,
        0x09
    })
    OperationRegion (RD03, SystemMemory, 0x0100, 0x0100)
    Field (RD03, ByteAcc, NoLock, Preserve)
    {
        FD02,   8
    }

    Device (DD09)
    {
    }

    Event (ED01)
    Method (ME53, 0, NotSerialized)
    {
        Return (0x12)
    }

    Mutex (MXD1, 0x00)
    PowerResource (PWD0, 0x01, 0x0000)
    {
        Method (M001, 0, NotSerialized)
        {
            Return (0x00)
        }
    }

    Processor (PRD0, 0x00, 0xFFFFFFFF, 0x00){}
    ThermalZone (TZD0)
    {
    }

    CreateField (BD05, 0x00, 0x08, BFD0)
    Name (ID0D, 0x00)
    Name (ID0E, 0x00)
    Method (ME69, 0, NotSerialized)
    {
        Return (0x12345678)
    }

    Name (PD03, Package (0x01)
    {
        ME69
    })
    Name (ID0F, 0x00)
    Name (ID10, 0x1234)
    Name (PD04, Package (0x01)
    {
        0x10
    })
    Name (PD05, Package (0x01)
    {
        0x20
    })
    Name (PD06, Package (0x01)
    {
        0x30
    })
    Name (PD07, Package (0x01)
    {
        0x40
    })
    Name (PD08, Package (0x01)
    {
        0x50
    })
    Name (PD09, Package (0x01)
    {
        0x60
    })
    Name (ID11, 0xFE7CB391D650A284)
    Name (BD06, Buffer (0x09)
    {
        /* 0000 */  0x01, 0x02, 0x03, 0x04, 0x59, 0x06, 0x07, 0x08,  // ....Y...
        /* 0008 */  0x09                                             // .
    })
    CreateField (BD06, 0x28, 0x08, BFD1)
    OperationRegion (RD04, SystemMemory, 0x0100, 0x0100)
    Field (RD04, ByteAcc, NoLock, Preserve)
    {
        FD03,   8
    }

    Name (PD0A, Package (0x01)
    {
        ID11
    })
    Name (PD0B, Package (0x01)
    {
        BFD1
    })
    Name (PD0C, Package (0x01)
    {
        FD03
    })
    Name (SD03, "0123456789a")
    Name (BD07, Buffer (0x2001){})
    Name (SD04, "qwer0000")
    Name (BD08, Buffer (0x04)
    {
         0x01, 0x77, 0x03, 0x04                           // .w..
    })
    Name (PD0D, Package (0x03)
    {
        0x05,
        0x77,
        0x07
    })
    Name (ID12, 0x77)
    Name (PD0E, Package (0x01)
    {
        0x77
    })
    Name (ID13, 0x00)
    Name (SD05, "q_er0000")
    Name (BD09, Buffer (0x04)
    {
         0x01, 0x00, 0x03, 0x04                           // ....
    })
    Name (PD0F, Package (0x03)
    {
        0x05,
        0x00,
        0x07
    })
    Name (ID14, 0x11)
    Name (ID15, 0x22)
    Name (ID16, 0x33)
    Name (ID17, 0x44)
    Name (ID18, 0x55)
    Name (ID19, 0x66)
    Name (ID1A, 0x77)
    Name (ID1B, 0xFEDCBA9876543210)
    Name (ID1C, 0xFEDCBA9876543211)
    Name (ID1D, 0xFEDCBA9876543210)
    Device (DD0B)
    {
        Name (S000, "DEV0")
    }

    Event (ED02)
    OperationRegion (RD05, SystemMemory, 0x0100, 0x0100)
    Name (BD0A, Buffer (0x09)
    {
         0x10, 0x11, 0x12, 0x13                           // ....
    })
    CreateField (BD0A, 0x00, 0x08, BFD2)
    Name (RTD0, ResourceTemplate ()
    {
        IRQNoFlags ()
            {1}
        DMA (Compatibility, NotBusMaster, Transfer16, )
            {2}
    })
    Name (BD0B, ResourceTemplate ()
    {
        IRQNoFlags ()
            {1}
        DMA (Compatibility, NotBusMaster, Transfer16, )
            {2}
        IRQNoFlags ()
            {1}
        DMA (Compatibility, NotBusMaster, Transfer16, )
            {2}
    })
    Device (DD0C)
    {
    }

    Processor (PRD1, 0x00, 0xFFFFFFFF, 0x00){}
    OperationRegion (RD06, SystemMemory, 0x0100, 0x0100)
    PowerResource (PWD1, 0x01, 0x0000)
    {
        Method (MMMM, 0, NotSerialized)
        {
            Return (0x00)
        }
    }

    ThermalZone (TZD1)
    {
    }

    Event (ED03)
    Mutex (MXD2, 0x00)
    Event (ED04)
    Name (ID1E, 0x19283746)
    Name (PD10, Package (0x01)
    {
        "Package"
    })
    Name (RTD1, ResourceTemplate ()
    {
        QWordSpace (0xC0, ResourceProducer, PosDecode, MinNotFixed, MaxNotFixed, 0x0A,
            0xD8D9DADBDCDDDEDF, // Granularity
            0xE0E1E2E3E4E5E6E7, // Range Minimum
            0xE8E9EAEBECEDEEEF, // Range Maximum
            0xF0F1F2F3F4F5F6F7, // Translation Offset
            0xF8F9FAFBFCFDFEFF, // Length
            ,, )
    })
    Name (BD0C, ResourceTemplate ()
    {
        QWordSpace (0xC0, ResourceProducer, PosDecode, MinNotFixed, MaxNotFixed, 0x0A,
            0xD8D9DADBDCDDDEDF, // Granularity
            0xE0E1E2E3E4E5E6E7, // Range Minimum
            0xE8E9EAEBECEDEEEF, // Range Maximum
            0xF0F1F2F3F4F5F6F7, // Translation Offset
            0xF8F9FAFBFCFDFEFF, // Length
            ,, )
    })
    Device (DD0D)
    {
    }

    Processor (PRD2, 0x00, 0xFFFFFFFF, 0x00){}
    OperationRegion (RD07, SystemMemory, 0x0100, 0x0100)
    PowerResource (PWD2, 0x01, 0x0000)
    {
        Method (MMMM, 0, NotSerialized)
        {
            Return (0x00)
        }
    }

    ThermalZone (TZD2)
    {
    }

    Event (ED05)
    Mutex (MXD3, 0x00)
    Name (ID1F, 0x31)
    Name (ID20, 0x07)
    OperationRegion (RD08, SystemMemory, 0x00, ID1F++)
    Name (BD0D, Buffer (0x08)
    {
         0x80, 0x99, 0xFF, 0x83, 0x84, 0x85, 0x86, 0x87   // ........
    })
    CreateField (BD0D, 0x08, ID20++, BFD3)
    Name (PD11, Package (0x02)
    {
        0x01
    })
    Name (BD0E, Buffer (0x04)
    {
         0x01, 0x77, 0x03, 0x04                           // .w..
    })
    /* Base of Buffer Field */

    Name (BD0F, Buffer (0x09){})
    /* Benchmark buffer */

    Name (BD10, Buffer (0x09){})
    /* It is used in b198 Name(id24, 0) */
    /* Name(id25, 0) */
    /* Don't use this name bd13! */
    /* Name(bd13, Buffer(9){}) */
    Name (ID29, 0x00)
    Name (ID2A, 0x00)
    Name (ID2B, 0x00)
