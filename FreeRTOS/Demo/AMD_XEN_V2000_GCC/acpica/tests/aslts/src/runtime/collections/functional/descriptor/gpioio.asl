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
     * GpioIO Resource Descriptor Macro
     */
    Device (GPIO)
    {
    }

    Name (P454, Package (0xC4)
    {
        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullUp, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullUp, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullUp, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDown, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDown, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDown, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullNone, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullNone, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullNone, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDefault, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDefault, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDefault, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullUp, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullUp, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullUp, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDown, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDown, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDown, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullNone, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullNone, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullNone, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDefault, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDefault, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDefault, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullUp, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullUp, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullUp, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDown, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDown, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDown, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullNone, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullNone, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullNone, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDefault, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDefault, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDefault, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullUp, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullUp, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullUp, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDown, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDown, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDown, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullNone, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullNone, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullNone, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDefault, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDefault, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDefault, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullUp, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullUp, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullUp, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDown, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDown, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDown, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullNone, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullNone, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullNone, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDefault, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDefault, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDefault, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullUp, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullUp, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullUp, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDown, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDown, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDown, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullNone, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullNone, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullNone, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDefault, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDefault, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDefault, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullUp, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullUp, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullUp, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDown, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDown, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDown, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullNone, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullNone, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullNone, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDefault, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDefault, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDefault, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullUp, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullUp, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullUp, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDown, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDown, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDown, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullNone, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullNone, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullNone, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDefault, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDefault, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDefault, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullUp, 0x0DEB, 0xABCD, IoRestrictionNoneAndPreserve,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionNoneAndPreserve,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullUp, 0x0DEB, 0xABCD, IoRestrictionNoneAndPreserve,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullUp, 0x0000, 0x0000, IoRestrictionNone,
                "\\GPIO", 0x00, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        }
    })
    Name (P455, Package (0xC4)
    {
        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullUp, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullUp, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullUp, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDown, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDown, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDown, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullNone, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullNone, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullNone, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDefault, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDefault, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDefault, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullUp, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullUp, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullUp, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDown, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDown, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDown, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullNone, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullNone, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullNone, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDefault, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDefault, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDefault, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullUp, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullUp, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullUp, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDown, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDown, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDown, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullNone, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullNone, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullNone, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDefault, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDefault, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDefault, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullUp, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullUp, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullUp, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDown, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDown, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDown, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullNone, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullNone, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullNone, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDefault, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDefault, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDefault, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullUp, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullUp, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullUp, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDown, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDown, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDown, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullNone, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullNone, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullNone, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDefault, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDefault, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDefault, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullUp, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullUp, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullUp, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDown, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDown, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDown, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullNone, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullNone, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullNone, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDefault, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDefault, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDefault, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullUp, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullUp, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullUp, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDown, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDown, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDown, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullNone, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullNone, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullNone, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDefault, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDefault, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullDefault, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullUp, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullUp, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullUp, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDown, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDown, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDown, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullNone, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullNone, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullNone, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDefault, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDefault, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullDefault, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (ExclusiveAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullUp, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDown, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullNone, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionNone,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionInputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                "\\GPIO", 0xEE, ResourceProducer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullUp, 0x0DEB, 0xABCD, IoRestrictionNoneAndPreserve,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                RawDataBuffer (0x04)  // Vendor Data
                {
                    0xC1, 0xC2, 0xC3, 0xC4
                })
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        },

        ResourceTemplate ()
        {
            GpioIo (SharedAndWake, PullDefault, 0x0DEB, 0xABCD, IoRestrictionNoneAndPreserve,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Shared, PullUp, 0x0DEB, 0xABCD, IoRestrictionNoneAndPreserve,
                "\\GPIO", 0xEE, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1
                }
        },

        ResourceTemplate ()
        {
            GpioIo (Exclusive, PullUp, 0x0000, 0x0000, IoRestrictionNone,
                "\\GPIO", 0x00, ResourceConsumer, ,
                )
                {   // Pin list
                    0x11E1,
                    0x22E2,
                    0x33E3
                }
        }
    })
    Method (RT22, 0, Serialized)
    {
        /* Emit test header, set the filename */

        THDR (__METHOD__, "GpioIO Resource Descriptor Macro", "gpioio.asl")
        /* The main test packages must have the same number of entries */

        If ((SizeOf (P454) != SizeOf (P455)))
        {
            ERR (__METHOD__, 0xB3, __LINE__, 0x00, 0x00, 0x00, "Incorrect package length")
            Return (Zero)
        }

        /* Main test case for packages above */

        M330 (__METHOD__, SizeOf (P454), "p454", P454, P455)
        /* Check resource descriptor tag offsets */

        Local0 = ResourceTemplate ()
            {
                GpioIo (Exclusive, PullUp, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                    "\\GPIO", 0xEE, ResourceConsumer, ,
                    RawDataBuffer (0x04)  // Vendor Data
                    {
                        0xC1, 0xC2, 0xC3, 0xC4
                    })
                    {   // Pin list
                        0x11E1,
                        0x22E2,
                        0x33E3
                    }
                GpioIo (Exclusive, PullUp, 0x0DEB, 0xABCD, IoRestrictionOutputOnly,
                    "\\GPIO", 0xEE, ResourceConsumer, ,
                    RawDataBuffer (0x04)  // Vendor Data
                    {
                        0xC1, 0xC2, 0xC3, 0xC4
                    })
                    {   // Pin list
                        0x11E1,
                        0x22E2,
                        0x33E3
                    }
            }
        M331 (__METHOD__, 0x01, 0x3B, 0x3B, 0x0173, 0x0173, "_SHR")
        M331 (__METHOD__, 0x02, 0x48, 0x48, 0x0180, 0x0180, "_PPI")
        M331 (__METHOD__, 0x03, 0x60, 0x60, 0x0198, 0x0198, "_DBT")
        M331 (__METHOD__, 0x04, 0x50, 0x50, 0x0188, 0x0188, "_DRS")
        M331 (__METHOD__, 0x05, 0x38, 0x38, 0x0170, 0x0170, "_IOR")
        M331 (__METHOD__, 0x06, 0xB8, 0xB8, 0x01F0, 0x01F0, "_PIN")
        M331 (__METHOD__, 0x07, 0x0118, 0x0118, 0x0250, 0x0250, "_VEN")
    }
