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
     * Bug 0060:
     *
     * SUMMARY: "Outstanding allocations" on processing the Type Conversion
     *
     * Methods show "outstanding allocations" errors produced
     * by ACPICA during processing the Type Conversion. When the
     * "Dynamic object deletion" test will be implemented the
     * memory consumption problems like these will be encountered
     * by it.
     */
    /* No outstanding allocations */
    Method (MDFA, 0, Serialized)
    {
        OperationRegion (R001, SystemMemory, 0x10, 0x10)
        Field (R001, ByteAcc, NoLock, Preserve)
        {
            F001,   32,
            F002,   32
        }

        F001 = 0x01
        F002 = 0x02
        Store ((F001 + F002), Local0)
    }

    /* Outstanding: 0x1 allocations after execution */

    Method (MDFB, 0, Serialized)
    {
        OperationRegion (R001, SystemMemory, 0x10, 0x10)
        Field (R001, ByteAcc, NoLock, Preserve)
        {
            F001,   32,
            F002,   72
        }

        F001 = 0x01
        F002 = 0x02
        Store ((F001 + F002), Local0)
    }

    /* No outstanding allocations */

    Method (MDFC, 0, NotSerialized)
    {
        Store ((0x01 + 0x02), Local0)
    }

    /* Outstanding: 0x1 allocations after execution */

    Method (MDFD, 0, NotSerialized)
    {
        Store ((0x01 + "2"), Local0)
    }

    /* Outstanding: 0x1 allocations after execution */

    Method (MDFE, 0, NotSerialized)
    {
        Store (("1" + 0x02), Local0)
    }

    /* Outstanding: 0x2 allocations after execution */

    Method (MDFF, 0, NotSerialized)
    {
        Store (("1" + "2"), Local0)
    }

    /* Outstanding: 0x1 allocations after execution */

    Method (ME00, 0, Serialized)
    {
        Name (B000, Buffer (0x01)
        {
             0x91                                             // .
        })
        Store ((B000 + 0x02), Local0)
    }

    Method (ME01, 0, NotSerialized)
    {
        MDFA ()
        MDFB ()
        MDFC ()
        MDFD ()
        MDFE ()
        MDFF ()
        ME00 ()
    }
