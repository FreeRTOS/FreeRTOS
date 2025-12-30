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
     * Bug 208 (local-bugzilla-343):
     *
     * SUMMARY: Store-to-Debug operation falls into infinite loop for ring of Index references
     *
     * Note: add verifications while sorting out and fixing the bug (CH03/CH04/..)
     */
    Method (M818, 0, NotSerialized)
    {
        Method (M000, 0, Serialized)
        {
            Name (P000, Package (0x04)
            {
                0x10,
                0x11,
                0x12,
                0x13
            })
            Store (P000 [0x00], P000 [0x01])
            Store (P000 [0x01], P000 [0x02])
            Store (P000 [0x02], P000 [0x00])
            Store (P000 [0x00], Local0)
            Debug = Local0
                /* RING_OF_REFS_EXCEPTION? */
        }

        Method (M001, 0, Serialized)
        {
            Name (P000, Package (0x04)
            {
                0x10,
                0x11,
                0x12,
                0x13
            })
            Name (P001, Package (0x04)
            {
                0x20,
                0x21,
                0x22,
                0x23
            })
            Store (P000 [0x00], P001 [0x01])
            Store (P001 [0x00], P000 [0x01])
            Store (P000 [0x00], Local0)
            Debug = Local0
                /* RING_OF_REFS_EXCEPTION? */
        }

        Method (M002, 0, Serialized)
        {
            Name (P000, Package (0x04)
            {
                0x10,
                0x11,
                0x12,
                0x13
            })
            Store (P000 [0x00], P000 [0x01])
            Store (P000 [0x03], Local0)
            Debug = Local0
                /* RING_OF_REFS_EXCEPTION? */
        }

        M000 ()
        M001 ()
        M002 ()
    }
