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
     * Start/End Dependent Function Resource Descriptor Macro
     */
    Name (P406, Package (0x0E)
    {
        ResourceTemplate ()
        {
            StartDependentFnNoPri ()
            {
            }
            EndDependentFn ()
        },

        ResourceTemplate ()
        {
            StartDependentFn (0x00, 0x00)
            {
            }
            EndDependentFn ()
        },

        ResourceTemplate ()
        {
            StartDependentFn (0x00, 0x01)
            {
            }
            EndDependentFn ()
        },

        ResourceTemplate ()
        {
            StartDependentFn (0x00, 0x02)
            {
            }
            EndDependentFn ()
        },

        ResourceTemplate ()
        {
            StartDependentFn (0x01, 0x00)
            {
            }
            EndDependentFn ()
        },

        ResourceTemplate ()
        {
            StartDependentFn (0x01, 0x01)
            {
            }
            EndDependentFn ()
        },

        ResourceTemplate ()
        {
            StartDependentFn (0x01, 0x02)
            {
            }
            EndDependentFn ()
        },

        ResourceTemplate ()
        {
            StartDependentFn (0x02, 0x00)
            {
            }
            EndDependentFn ()
        },

        ResourceTemplate ()
        {
            StartDependentFn (0x02, 0x01)
            {
            }
            EndDependentFn ()
        },

        ResourceTemplate ()
        {
            StartDependentFn (0x02, 0x02)
            {
            }
            EndDependentFn ()
        },

        ResourceTemplate ()
        {
            StartDependentFnNoPri ()
            {
            }
            StartDependentFnNoPri ()
            {
            }
            StartDependentFnNoPri ()
            {
            }
            EndDependentFn ()
        },

        ResourceTemplate ()
        {
            StartDependentFn (0x01, 0x01)
            {
            }
            StartDependentFn (0x01, 0x01)
            {
            }
            StartDependentFn (0x01, 0x01)
            {
            }
            EndDependentFn ()
        },

        ResourceTemplate ()
        {
            StartDependentFn (0x00, 0x00)
            {
            }
            StartDependentFn (0x00, 0x01)
            {
            }
            StartDependentFn (0x00, 0x02)
            {
            }
            StartDependentFn (0x01, 0x00)
            {
            }
            StartDependentFn (0x01, 0x01)
            {
            }
            StartDependentFn (0x01, 0x02)
            {
            }
            StartDependentFn (0x02, 0x00)
            {
            }
            StartDependentFn (0x02, 0x01)
            {
            }
            StartDependentFn (0x02, 0x02)
            {
            }
            EndDependentFn ()
        },

        ResourceTemplate ()
        {
            StartDependentFn (0x00, 0x00)
            {
            }
            EndDependentFn ()
            StartDependentFn (0x00, 0x01)
            {
            }
            StartDependentFn (0x00, 0x02)
            {
            }
            EndDependentFn ()
            StartDependentFn (0x01, 0x00)
            {
            }
            StartDependentFn (0x01, 0x01)
            {
            }
            StartDependentFn (0x01, 0x02)
            {
            }
            EndDependentFn ()
            StartDependentFn (0x02, 0x00)
            {
            }
            EndDependentFn ()
            StartDependentFn (0x02, 0x01)
            {
            }
            EndDependentFn ()
            StartDependentFn (0x02, 0x02)
            {
            }
            EndDependentFn ()
        }
    })
    /*
     ACPI Specification, Revision 3.0, September 2, 2004
     6.4.2.3   Start Dependent Functions Descriptor
     Start Dependent Functions Descriptor layout (length = 1):
     Byte 0 (Tag Bits): Value = 00110001B (0x31)(Type = 0, small item name = 0x6, length = 1)
     Byte 1 (Priority byte ):
     Bits[3:2]	Performance/robustness. Acceptable values are:
     0	Good configuration: Highest Priority and preferred configuration
     1	Acceptable configuration: Lower Priority but acceptable configuration
     2	Sub-optimal configuration: Functional configuration but not optimal
     3	Reserved
     Bits[1:0]	Compatibility priority. Acceptable values are:
     0	Good configuration: Highest Priority and preferred configuration
     1	Acceptable configuration: Lower Priority but acceptable configuration
     2	Sub-optimal configuration: Functional configuration but not optimal
     3	Reserved
     Start Dependent Functions Descriptor layout (length = 0):
     Byte 0 (Tag Bits): Value = 00110000B (0x30)(Type = 0, small item name = 0x6, length = 0)
     6.4.2.4   End Dependent Functions Descriptor
     End Dependent Functions Descriptor layout:
     Byte 0 (Tag Bits): Value = 00111000B (0x38)(Type = 0, small item name = 0x7 length =0)
     */
    Name (P407, Package (0x0E)
    {
        ResourceTemplate ()
        {
            StartDependentFnNoPri ()
            {
            }
            EndDependentFn ()
        },

        ResourceTemplate ()
        {
            StartDependentFn (0x00, 0x00)
            {
            }
            EndDependentFn ()
        },

        ResourceTemplate ()
        {
            StartDependentFn (0x00, 0x01)
            {
            }
            EndDependentFn ()
        },

        ResourceTemplate ()
        {
            StartDependentFn (0x00, 0x02)
            {
            }
            EndDependentFn ()
        },

        ResourceTemplate ()
        {
            StartDependentFn (0x01, 0x00)
            {
            }
            EndDependentFn ()
        },

        ResourceTemplate ()
        {
            StartDependentFn (0x01, 0x01)
            {
            }
            EndDependentFn ()
        },

        ResourceTemplate ()
        {
            StartDependentFn (0x01, 0x02)
            {
            }
            EndDependentFn ()
        },

        ResourceTemplate ()
        {
            StartDependentFn (0x02, 0x00)
            {
            }
            EndDependentFn ()
        },

        ResourceTemplate ()
        {
            StartDependentFn (0x02, 0x01)
            {
            }
            EndDependentFn ()
        },

        ResourceTemplate ()
        {
            StartDependentFn (0x02, 0x02)
            {
            }
            EndDependentFn ()
        },

        ResourceTemplate ()
        {
            StartDependentFnNoPri ()
            {
            }
            StartDependentFnNoPri ()
            {
            }
            StartDependentFnNoPri ()
            {
            }
            EndDependentFn ()
        },

        ResourceTemplate ()
        {
            StartDependentFn (0x01, 0x01)
            {
            }
            StartDependentFn (0x01, 0x01)
            {
            }
            StartDependentFn (0x01, 0x01)
            {
            }
            EndDependentFn ()
        },

        ResourceTemplate ()
        {
            StartDependentFn (0x00, 0x00)
            {
            }
            StartDependentFn (0x00, 0x01)
            {
            }
            StartDependentFn (0x00, 0x02)
            {
            }
            StartDependentFn (0x01, 0x00)
            {
            }
            StartDependentFn (0x01, 0x01)
            {
            }
            StartDependentFn (0x01, 0x02)
            {
            }
            StartDependentFn (0x02, 0x00)
            {
            }
            StartDependentFn (0x02, 0x01)
            {
            }
            StartDependentFn (0x02, 0x02)
            {
            }
            EndDependentFn ()
        },

        ResourceTemplate ()
        {
            StartDependentFn (0x00, 0x00)
            {
            }
            EndDependentFn ()
            StartDependentFn (0x00, 0x01)
            {
            }
            StartDependentFn (0x00, 0x02)
            {
            }
            EndDependentFn ()
            StartDependentFn (0x01, 0x00)
            {
            }
            StartDependentFn (0x01, 0x01)
            {
            }
            StartDependentFn (0x01, 0x02)
            {
            }
            EndDependentFn ()
            StartDependentFn (0x02, 0x00)
            {
            }
            EndDependentFn ()
            StartDependentFn (0x02, 0x01)
            {
            }
            EndDependentFn ()
            StartDependentFn (0x02, 0x02)
            {
            }
            EndDependentFn ()
        }
    })
    Method (RT04, 0, Serialized)
    {
        /* Emit test header, set the filename */

        THDR (__METHOD__, "Start/End DependentFunction Resource Descriptor Macro", "dependentfn.asl")
        /* Main test case for packages above */

        M330 (__METHOD__, 0x0E, "p406", P406, P407)
    }
