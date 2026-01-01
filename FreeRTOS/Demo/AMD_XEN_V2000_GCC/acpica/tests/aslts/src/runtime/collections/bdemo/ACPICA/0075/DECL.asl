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
     * Bug 0075:
     *
     * SUMMARY: Each scope of DefinitionBlock should be supplied with its set of _T_x objects
     *
     * Compiler should return an error...
     */
    Method (ME0C, 1, Serialized)
    {
        Local0 = 0x0100
        Switch (ToInteger (Arg0))
        {
            Case (0x01)
            {
                Local0 = 0x01
            }

        }

        Switch (ToInteger (Arg0))
        {
            Case (0x02)
            {
                Local0 = 0x02
            }

        }

        Switch (ToInteger (Arg0))
        {
            Case (0x03)
            {
                Local0 = 0x03
            }

        }

        Switch (ToInteger (Arg0))
        {
            Case (0x04)
            {
                Local0 = 0x04
            }

        }

        Switch (ToInteger (Arg0))
        {
            Case (0x05)
            {
                Local0 = 0x05
            }

        }

        Switch (ToInteger (Arg0))
        {
            Case (0x06)
            {
                Local0 = 0x06
            }

        }

        Switch (ToInteger (Arg0))
        {
            Case (0x07)
            {
                Local0 = 0x07
            }

        }

        Switch (ToInteger (Arg0))
        {
            Case (0x08)
            {
                Local0 = 0x08
            }

        }

        Switch (ToInteger (Arg0))
        {
            Case (0x09)
            {
                Local0 = 0x09
            }

        }

        Switch (ToInteger (Arg0))
        {
            Case (0x0A)
            {
                Local0 = 0x0A
            }

        }

        Switch (ToInteger (Arg0))
        {
            Case (0x0B)
            {
                Local0 = 0x0B
            }

        }

        Switch (ToInteger (Arg0))
        {
            Case (0x0C)
            {
                Local0 = 0x0C
            }

        }

        Switch (ToInteger (Arg0))
        {
            Case (0x0D)
            {
                Local0 = 0x0D
            }

        }

        Switch (ToInteger (Arg0))
        {
            Case (0x0E)
            {
                Local0 = 0x0E
            }

        }

        Switch (ToInteger (Arg0))
        {
            Case (0x0F)
            {
                Local0 = 0x0F
            }

        }

        Switch (ToInteger (Arg0))
        {
            Case (0x10)
            {
                Local0 = 0x10
            }

        }

        Switch (ToInteger (Arg0))
        {
            Case (0x11)
            {
                Local0 = 0x11
            }

        }

        Switch (ToInteger (Arg0))
        {
            Case (0x12)
            {
                Local0 = 0x12
            }

        }

        Switch (ToInteger (Arg0))
        {
            Case (0x13)
            {
                Local0 = 0x13
            }

        }

        Switch (ToInteger (Arg0))
        {
            Case (0x14)
            {
                Local0 = 0x14
            }

        }

        Switch (ToInteger (Arg0))
        {
            Case (0x15)
            {
                Local0 = 0x15
            }

        }

        Switch (ToInteger (Arg0))
        {
            Case (0x16)
            {
                Local0 = 0x16
            }

        }

        Switch (ToInteger (Arg0))
        {
            Case (0x17)
            {
                Local0 = 0x17
            }

        }

        Switch (ToInteger (Arg0))
        {
            Case (0x18)
            {
                Local0 = 0x18
            }

        }

        Switch (ToInteger (Arg0))
        {
            Case (0x19)
            {
                Local0 = 0x19
            }

        }

        Switch (ToInteger (Arg0))
        {
            Case (0x1A)
            {
                Local0 = 0x1A
            }

        }

        Switch (ToInteger (Arg0))
        {
            Case (0x1B)
            {
                Local0 = 0x1B
            }

        }

        Return (Local0)
    }

    Method (ME0D, 0, NotSerialized)
    {
        Local7 = 0x01
        While ((Local7 <= 0x1B))
        {
            Local0 = ME0C (Local7)
            If ((Local0 != Local7))
            {
                Debug = "Error:"
                Debug = Local7
            }

            Local7++
        }

        Return (0x00)
    }

    /* ////////////////////// */

    Method (ME0E, 1, Serialized)
    {
        Local0 = 0x0100
        Switch (ToInteger (Arg0))
        {
            Case (0x01)
            {
                Local0 = 0x01
            }

        }

        Return (Local0)
    }

    Method (ME0F, 1, Serialized)
    {
        Local0 = 0x0100
        Switch (ToInteger (Arg0))
        {
            Case (0x02)
            {
                Local0 = 0x02
            }

        }

        Return (Local0)
    }

    Method (ME10, 1, Serialized)
    {
        Local0 = 0x0100
        Switch (ToInteger (Arg0))
        {
            Case (0x03)
            {
                Local0 = 0x03
            }

        }

        Return (Local0)
    }

    Method (ME11, 1, Serialized)
    {
        Local0 = 0x0100
        Switch (ToInteger (Arg0))
        {
            Case (0x04)
            {
                Local0 = 0x04
            }

        }

        Return (Local0)
    }

    Method (ME12, 1, Serialized)
    {
        Local0 = 0x0100
        Switch (ToInteger (Arg0))
        {
            Case (0x05)
            {
                Local0 = 0x05
            }

        }

        Return (Local0)
    }

    Method (ME13, 1, Serialized)
    {
        Local0 = 0x0100
        Switch (ToInteger (Arg0))
        {
            Case (0x06)
            {
                Local0 = 0x06
            }

        }

        Return (Local0)
    }

    Method (ME14, 1, Serialized)
    {
        Local0 = 0x0100
        Switch (ToInteger (Arg0))
        {
            Case (0x07)
            {
                Local0 = 0x07
            }

        }

        Return (Local0)
    }

    Method (ME15, 1, Serialized)
    {
        Local0 = 0x0100
        Switch (ToInteger (Arg0))
        {
            Case (0x08)
            {
                Local0 = 0x08
            }

        }

        Return (Local0)
    }

    Method (ME16, 1, Serialized)
    {
        Local0 = 0x0100
        Switch (ToInteger (Arg0))
        {
            Case (0x09)
            {
                Local0 = 0x09
            }

        }

        Return (Local0)
    }

    Method (ME17, 1, Serialized)
    {
        Local0 = 0x0100
        Switch (ToInteger (Arg0))
        {
            Case (0x0A)
            {
                Local0 = 0x0A
            }

        }

        Return (Local0)
    }

    Method (ME18, 1, Serialized)
    {
        Local0 = 0x0100
        Switch (ToInteger (Arg0))
        {
            Case (0x0B)
            {
                Local0 = 0x0B
            }

        }

        Return (Local0)
    }

    Method (ME19, 1, Serialized)
    {
        Local0 = 0x0100
        Switch (ToInteger (Arg0))
        {
            Case (0x0C)
            {
                Local0 = 0x0C
            }

        }

        Return (Local0)
    }

    Method (ME1A, 1, Serialized)
    {
        Local0 = 0x0100
        Switch (ToInteger (Arg0))
        {
            Case (0x0D)
            {
                Local0 = 0x0D
            }

        }

        Return (Local0)
    }

    Method (ME1B, 1, Serialized)
    {
        Local0 = 0x0100
        Switch (ToInteger (Arg0))
        {
            Case (0x0E)
            {
                Local0 = 0x0E
            }

        }

        Return (Local0)
    }

    Method (ME1C, 1, Serialized)
    {
        Local0 = 0x0100
        Switch (ToInteger (Arg0))
        {
            Case (0x0F)
            {
                Local0 = 0x0F
            }

        }

        Return (Local0)
    }

    Method (ME1D, 1, Serialized)
    {
        Local0 = 0x0100
        Switch (ToInteger (Arg0))
        {
            Case (0x10)
            {
                Local0 = 0x10
            }

        }

        Return (Local0)
    }

    Method (ME1E, 1, Serialized)
    {
        Local0 = 0x0100
        Switch (ToInteger (Arg0))
        {
            Case (0x11)
            {
                Local0 = 0x11
            }

        }

        Return (Local0)
    }

    Method (ME1F, 1, Serialized)
    {
        Local0 = 0x0100
        Switch (ToInteger (Arg0))
        {
            Case (0x12)
            {
                Local0 = 0x12
            }

        }

        Return (Local0)
    }

    Method (ME20, 1, Serialized)
    {
        Local0 = 0x0100
        Switch (ToInteger (Arg0))
        {
            Case (0x13)
            {
                Local0 = 0x13
            }

        }

        Return (Local0)
    }

    Method (ME21, 1, Serialized)
    {
        Local0 = 0x0100
        Switch (ToInteger (Arg0))
        {
            Case (0x14)
            {
                Local0 = 0x14
            }

        }

        Return (Local0)
    }

    Method (ME22, 1, Serialized)
    {
        Local0 = 0x0100
        Switch (ToInteger (Arg0))
        {
            Case (0x15)
            {
                Local0 = 0x15
            }

        }

        Return (Local0)
    }

    Method (ME23, 1, Serialized)
    {
        Local0 = 0x0100
        Switch (ToInteger (Arg0))
        {
            Case (0x16)
            {
                Local0 = 0x16
            }

        }

        Return (Local0)
    }

    Method (ME24, 1, Serialized)
    {
        Local0 = 0x0100
        Switch (ToInteger (Arg0))
        {
            Case (0x17)
            {
                Local0 = 0x17
            }

        }

        Return (Local0)
    }

    Method (ME25, 1, Serialized)
    {
        Local0 = 0x0100
        Switch (ToInteger (Arg0))
        {
            Case (0x18)
            {
                Local0 = 0x18
            }

        }

        Return (Local0)
    }

    Method (ME26, 1, Serialized)
    {
        Local0 = 0x0100
        Switch (ToInteger (Arg0))
        {
            Case (0x19)
            {
                Local0 = 0x19
            }

        }

        Return (Local0)
    }

    Method (ME27, 1, Serialized)
    {
        Local0 = 0x0100
        Switch (ToInteger (Arg0))
        {
            Case (0x1A)
            {
                Local0 = 0x1A
            }

        }

        Return (Local0)
    }

    Method (ME28, 1, Serialized)
    {
        Local0 = 0x0100
        Switch (ToInteger (Arg0))
        {
            Case (0x1B)
            {
                Local0 = 0x1B
            }

        }

        Return (Local0)
    }
