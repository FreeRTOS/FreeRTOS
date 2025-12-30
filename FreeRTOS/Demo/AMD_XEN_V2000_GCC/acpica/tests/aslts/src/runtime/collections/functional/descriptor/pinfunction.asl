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
     * PinFunction Resource Descriptor Macro
     */
    Name (P45C, Package (0x09)
    {
        ResourceTemplate ()
        {
            PinFunction (Exclusive, PullDefault, 0x1000, "\\_SB.GPO1", 0x00,
                ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
                {   // Pin list
                    0x0001,
                    0x0002,
                    0x0003
                }
        },

        ResourceTemplate ()
        {
            PinFunction (Exclusive, PullDown, 0x2000, "\\_SB.GPO1", 0x00,
                ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
                {   // Pin list
                    0x0001,
                    0x0002,
                    0x0003
                }
        },

        ResourceTemplate ()
        {
            PinFunction (Exclusive, PullUp, 0x3000, "\\_SB.GPO1", 0x00,
                ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
                {   // Pin list
                    0x0001,
                    0x0002,
                    0x0003
                }
        },

        ResourceTemplate ()
        {
            PinFunction (Exclusive, PullNone, 0x4000, "\\_SB.GPO1", 0x00,
                ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
                {   // Pin list
                    0x0001,
                    0x0002,
                    0x0003
                }
        },

        ResourceTemplate ()
        {
            PinFunction (Shared, PullDefault, 0x1000, "\\_SB.GPO1", 0x00,
                ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
                {   // Pin list
                    0x0001,
                    0x0002,
                    0x0003
                }
        },

        ResourceTemplate ()
        {
            PinFunction (Shared, PullDown, 0x2000, "\\_SB.GPO1", 0x00,
                ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
                {   // Pin list
                    0x0001,
                    0x0002,
                    0x0003
                }
        },

        ResourceTemplate ()
        {
            PinFunction (Shared, PullUp, 0x3000, "\\_SB.GPO1", 0x00,
                ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
                {   // Pin list
                    0x0001,
                    0x0002,
                    0x0003
                }
        },

        ResourceTemplate ()
        {
            PinFunction (Shared, PullNone, 0x4000, "\\_SB.GPO1", 0x00,
                ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
                {   // Pin list
                    0x0001,
                    0x0002,
                    0x0003
                }
        },

        ResourceTemplate ()
        {
            PinFunction (Exclusive, PullNone, 0xABCD, "\\_SB.GPO1", 0x00,
                ResourceConsumer, ,)
                {   // Pin list
                    0x0011
                }
        }
    })
    Name (P45D, Package (0x09)
    {
        ResourceTemplate ()
        {
            PinFunction (Exclusive, PullDefault, 0x1000, "\\_SB.GPO1", 0x00,
                ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
                {   // Pin list
                    0x0001,
                    0x0002,
                    0x0003
                }
        },

        ResourceTemplate ()
        {
            PinFunction (Exclusive, PullDown, 0x2000, "\\_SB.GPO1", 0x00,
                ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
                {   // Pin list
                    0x0001,
                    0x0002,
                    0x0003
                }
        },

        ResourceTemplate ()
        {
            PinFunction (Exclusive, PullUp, 0x3000, "\\_SB.GPO1", 0x00,
                ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
                {   // Pin list
                    0x0001,
                    0x0002,
                    0x0003
                }
        },

        ResourceTemplate ()
        {
            PinFunction (Exclusive, PullNone, 0x4000, "\\_SB.GPO1", 0x00,
                ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
                {   // Pin list
                    0x0001,
                    0x0002,
                    0x0003
                }
        },

        ResourceTemplate ()
        {
            PinFunction (Shared, PullDefault, 0x1000, "\\_SB.GPO1", 0x00,
                ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
                {   // Pin list
                    0x0001,
                    0x0002,
                    0x0003
                }
        },

        ResourceTemplate ()
        {
            PinFunction (Shared, PullDown, 0x2000, "\\_SB.GPO1", 0x00,
                ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
                {   // Pin list
                    0x0001,
                    0x0002,
                    0x0003
                }
        },

        ResourceTemplate ()
        {
            PinFunction (Shared, PullUp, 0x3000, "\\_SB.GPO1", 0x00,
                ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
                {   // Pin list
                    0x0001,
                    0x0002,
                    0x0003
                }
        },

        ResourceTemplate ()
        {
            PinFunction (Shared, PullNone, 0x4000, "\\_SB.GPO1", 0x00,
                ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0x0A, 0x0B, 0x0C, 0x0D
                })
                {   // Pin list
                    0x0001,
                    0x0002,
                    0x0003
                }
        },

        ResourceTemplate ()
        {
            PinFunction (Exclusive, PullNone, 0xABCD, "\\_SB.GPO1", 0x00,
                ResourceConsumer, ,)
                {   // Pin list
                    0x0011
                }
        }
    })
    Method (RT26, 0, Serialized)
    {
        /* Emit test header, set the filename */

        THDR (__METHOD__, "PinFunction Resource Descriptor Macro", "pinfunction.asl")
        /* The main test packages must have the same number of entries */

        If ((SizeOf (P45C) != SizeOf (P45D)))
        {
            ERR (__METHOD__, 0xB3, __LINE__, 0x00, 0x00, 0x00, "Incorrect package length")
            Return (Zero)
        }

        /* Main test case for packages above */

        M330 (__METHOD__, SizeOf (P45C), "P45C", P45C, P45D)
                    /* Check resource descriptor tag offsets */

Local0 = ResourceTemplate ()
            {
                PinFunction (Exclusive, PullDefault, 0x1234, "\\_SB.GPO1", 0x00,
                    ResourceConsumer, ,
                    RawDataBuffer (0x04)  // Vendor Data
                    {
                        0x0A, 0x0B, 0x0C, 0x0D
                    })
                    {   // Pin list
                        0x0001,
                        0x0002,
                        0x0003
                    }
                PinFunction (Exclusive, PullDefault, 0x1234, "\\_SB.GPO1", 0x00,
                    ResourceConsumer, ,
                    RawDataBuffer (0x04)  // Vendor Data
                    {
                        0x0A, 0x0B, 0x0C, 0x0D
                    })
                    {   // Pin list
                        0x0001,
                        0x0002,
                        0x0003
                    }
            }
        M331 (__METHOD__, 0x01, 0x20, 0x20, 0x0150, 0x0150, "_SHR")
        M331 (__METHOD__, 0x02, 0x30, 0x30, 0x0160, 0x0160, "_PPI")
        M331 (__METHOD__, 0x03, 0x38, 0x38, 0x0168, 0x0168, "_FUN")
        M331 (__METHOD__, 0x04, 0x0110, 0x0110, 0x0240, 0x0240, "_VEN")
    }
