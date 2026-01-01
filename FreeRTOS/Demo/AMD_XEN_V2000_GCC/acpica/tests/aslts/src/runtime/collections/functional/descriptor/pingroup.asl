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
     * PinGroup Resource Descriptor Macro
     */
    Name (P460, Package (0x08)
    {
        ResourceTemplate ()
        {
            PinGroup ("group1", ResourceProducer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0xAA, 0xBB, 0xCC
                })
                {   // Pin list
                    0x0001,
                    0x0002,
                    0x0003,
                    0x0004
                }
        },

        ResourceTemplate ()
        {
            PinGroup ("group2", ResourceProducer, ,)
                {   // Pin list
                    0x0001,
                    0x0002,
                    0x0003,
                    0x0004
                }
        },

        ResourceTemplate ()
        {
            PinGroup ("group3", ResourceProducer, ,)
                {   // Pin list
                    0x0001,
                    0x0002,
                    0x0003,
                    0x0004
                }
        },

        ResourceTemplate ()
        {
            PinGroup ("group4", ResourceProducer, ,)
                {   // Pin list
                    0x0001,
                    0x0002,
                    0x0003,
                    0x0004
                }
        },

        ResourceTemplate ()
        {
            PinGroup ("group5", ResourceProducer, ,)
                {   // Pin list
                    0x0001,
                    0x0002,
                    0x0003,
                    0x0004
                }
        },

        ResourceTemplate ()
        {
            PinGroup ("group6", ResourceProducer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0xAA, 0xBB, 0xCC
                })
                {   // Pin list
                    0x0001,
                    0x0002,
                    0x0003,
                    0x0004
                }
        },

        ResourceTemplate ()
        {
            PinGroup ("AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA", ResourceProducer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0xAA, 0xBB, 0xCC
                })
                {   // Pin list
                    0x0001,
                    0x0002,
                    0x0003,
                    0x0004
                }
        },

        ResourceTemplate ()
        {
            PinGroup ("a", ResourceProducer, ,)
                {   // Pin list
                    0x0001,
                    0x0002,
                    0x0003,
                    0x0004
                }
        }
    })
    Name (P461, Package (0x08)
    {
        ResourceTemplate ()
        {
            PinGroup ("group1", ResourceProducer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0xAA, 0xBB, 0xCC
                })
                {   // Pin list
                    0x0001,
                    0x0002,
                    0x0003,
                    0x0004
                }
        },

        ResourceTemplate ()
        {
            PinGroup ("group2", ResourceProducer, ,)
                {   // Pin list
                    0x0001,
                    0x0002,
                    0x0003,
                    0x0004
                }
        },

        ResourceTemplate ()
        {
            PinGroup ("group3", ResourceProducer, ,)
                {   // Pin list
                    0x0001,
                    0x0002,
                    0x0003,
                    0x0004
                }
        },

        ResourceTemplate ()
        {
            PinGroup ("group4", ResourceProducer, ,)
                {   // Pin list
                    0x0001,
                    0x0002,
                    0x0003,
                    0x0004
                }
        },

        ResourceTemplate ()
        {
            PinGroup ("group5", ResourceProducer, ,)
                {   // Pin list
                    0x0001,
                    0x0002,
                    0x0003,
                    0x0004
                }
        },

        ResourceTemplate ()
        {
            PinGroup ("group6", ResourceProducer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0xAA, 0xBB, 0xCC
                })
                {   // Pin list
                    0x0001,
                    0x0002,
                    0x0003,
                    0x0004
                }
        },

        ResourceTemplate ()
        {
            PinGroup ("AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA", ResourceProducer, ,
                RawDataBuffer (0x03)  // Vendor Data
                {
                    0xAA, 0xBB, 0xCC
                })
                {   // Pin list
                    0x0001,
                    0x0002,
                    0x0003,
                    0x0004
                }
        },

        ResourceTemplate ()
        {
            PinGroup ("a", ResourceProducer, ,)
                {   // Pin list
                    0x0001,
                    0x0002,
                    0x0003,
                    0x0004
                }
        }
    })
    Method (RT28, 0, Serialized)
    {
        /* Emit test header, set the filename */

        THDR (__METHOD__, "PinGroup Resource Descriptor Macro", "pingroup.asl")
        /* The main test packages must have the same number of entries */

        If ((SizeOf (P460) != SizeOf (P461)))
        {
            ERR (__METHOD__, 0xB3, __LINE__, 0x00, 0x00, 0x00, "Incorrect package length")
            Return (Zero)
        }

        /* Main test case for packages above */

        M330 (__METHOD__, SizeOf (P460), "P460", P460, P461)
                    /* Check resource descriptor tag offsets */

Local0 = ResourceTemplate ()
            {
                PinGroup ("group0", ResourceProducer, ,
                    RawDataBuffer (0x03)  // Vendor Data
                    {
                        0xAA, 0xBB, 0xCC
                    })
                    {   // Pin list
                        0x0001,
                        0x0002,
                        0x0003,
                        0x0004
                    }
                PinGroup ("group1", ResourceProducer, ,
                    RawDataBuffer (0x03)  // Vendor Data
                    {
                        0xAA, 0xBB, 0xCC
                    })
                    {   // Pin list
                        0x0001,
                        0x0002,
                        0x0003,
                        0x0004
                    }
            }
        M331 (__METHOD__, 0x01, 0xE8, 0xE8, 0x01E8, 0x01E8, "_VEN")
        M331 (__METHOD__, 0x01, 0x70, 0x70, 0x0170, 0x0170, "_PIN")
    }
