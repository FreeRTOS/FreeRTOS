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
     * Methods of common use.
     */
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
     * RefCounts of named objects are incremented
     * and then decremented just after completions
     * of operations applied to them - it is true
     * for the following operations:
     *
     * - object used in AML operations except Index one
     * - object passed as parameter to Method
     *
     * The following AML operations increment the RefCounts
     * of objects which are decremented only while deleting
     * the objects where the results of these operations are
     * saved:
     *
     * - Index AML operation
     * - RefOf AML operation
     */
    Method (M806, 0, Serialized)
    {
        Name (P000, Package (0x40){})
        Name (P001, Package (0x40){})
        Name (S000, "01234567890-qwertyuiop[]")
        Name (B000, Buffer (0x07)
        {
             0x10, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17         // .......
        })
        Name (I000, 0xABCD0000)
        Name (I001, 0xABCD0001)
        Name (I002, 0xABCD0002)
        Name (I003, 0xABCD0003)
        Name (I004, 0xABCD0004)
        Name (I005, 0xABCD0005)
        Name (I006, 0xABCD0006)
        Name (I007, 0xABCD0007)
        Method (M000, 0, NotSerialized)
        {
            Store (S000 [0x00], P001 [0x04])
            Store (S000 [0x00], P001 [0x04])
        }

        Method (M001, 0, NotSerialized)
        {
            Store (B000 [0x00], P001 [0x07])
            Store (B000 [0x00], P001 [0x07])
        }

        M000 ()
        M001 ()
    }

    Method (M807, 0, Serialized)
    {
        Name (P000, Package (0x40){})
        Name (P001, Package (0x40){})
        Name (S000, "01234567890-qwertyuiop[]")
        Name (B000, Buffer (0x07)
        {
             0x10, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17         // .......
        })
        Name (I000, 0xABCD0000)
        Name (I001, 0xABCD0001)
        Name (I002, 0xABCD0002)
        Name (I003, 0xABCD0003)
        Name (I004, 0xABCD0004)
        Name (I005, 0xABCD0005)
        Name (I006, 0xABCD0006)
        Name (I007, 0xABCD0007)
        Method (MM00, 2, NotSerialized)
        {
            Method (M000, 0, NotSerialized)
            {
                Store (P000 [0x00], P001 [0x00])
                Store (P000 [0x01], P001 [0x01])
                Store (P000 [0x02], P001 [0x02])
                Store (P000 [0x03], P001 [0x03])
                Store (S000 [0x00], P001 [0x04])
                Store (S000 [0x01], P001 [0x05])
                Store (S000 [0x02], P001 [0x06])
                Store (B000 [0x00], P001 [0x07])
                Store (B000 [0x01], P001 [0x08])
                Store (B000 [0x02], P001 [0x09])
            }

            Method (M001, 0, NotSerialized)
            {
                Store (P000 [0x00], P001 [0x00])
                Store (P000 [0x01], P001 [0x01])
                Store (P000 [0x02], P001 [0x02])
                Store (P000 [0x03], P001 [0x03])
                Store (P001 [0x00], P000 [0x00])
                Store (P001 [0x01], P000 [0x01])
                Store (P001 [0x02], P000 [0x02])
                Store (P001 [0x03], P000 [0x03])
                Store (S000 [0x00], P001 [0x04])
                Store (S000 [0x01], P001 [0x05])
                Store (S000 [0x02], P001 [0x06])
                Store (B000 [0x00], P001 [0x07])
                Store (B000 [0x01], P001 [0x08])
                Store (B000 [0x02], P001 [0x09])
            }

            Method (M002, 0, NotSerialized)
            {
                Store (P000 [0x00], Local0)
                Store (P000 [0x01], Local1)
                Store (P000 [0x02], Local2)
                Store (P000 [0x03], Local3)
            }

            Method (M003, 4, NotSerialized)
            {
                Store (P000 [0x00], Arg0)
                Store (P000 [0x01], Arg1)
                Store (P000 [0x02], Arg2)
                Store (P000 [0x03], Arg3)
            }

            Method (M004, 4, NotSerialized)
            {
                Store (P000 [0x00], P001 [0x00])
                Store (P000 [0x01], P001 [0x01])
                Store (P000 [0x02], P001 [0x02])
                Store (P000 [0x03], P001 [0x03])
                Store (P001 [0x00], P000 [0x00])
                Store (P001 [0x01], P000 [0x01])
                Store (P001 [0x02], P000 [0x02])
                Store (P001 [0x03], P000 [0x03])
                Store (S000 [0x00], P001 [0x04])
                Store (S000 [0x01], P001 [0x05])
                Store (S000 [0x02], P001 [0x06])
                Store (B000 [0x00], P001 [0x07])
                Store (B000 [0x01], P001 [0x08])
                Store (B000 [0x02], P001 [0x09])
                Store (P000 [0x00], Local0)
                Store (P000 [0x01], Local1)
                Store (P000 [0x02], Local2)
                Store (P000 [0x03], Local3)
                Store (P000 [0x00], Arg0)
                Store (P000 [0x01], Arg1)
                Store (P000 [0x02], Arg2)
                Store (P000 [0x03], Arg3)
            }

            Method (M005, 6, NotSerialized)
            {
                Store (Arg0 [0x00], Arg1 [0x00])
                Store (Arg0 [0x01], Arg1 [0x01])
                Store (Arg0 [0x02], Arg1 [0x02])
                Store (Arg0 [0x03], Arg1 [0x03])
                Store (Arg1 [0x00], Arg0 [0x00])
                Store (Arg1 [0x01], Arg0 [0x01])
                Store (Arg1 [0x02], Arg0 [0x02])
                Store (Arg1 [0x03], Arg0 [0x03])
                Store (S000 [0x00], P001 [0x04])
                Store (S000 [0x01], P001 [0x05])
                Store (S000 [0x02], P001 [0x06])
                Store (B000 [0x00], P001 [0x07])
                Store (B000 [0x01], P001 [0x08])
                Store (B000 [0x02], P001 [0x09])
                Store (Arg0 [0x00], Local0)
                Store (Arg0 [0x01], Local1)
                Store (Arg0 [0x02], Local2)
                Store (Arg0 [0x03], Local3)
                Store (Arg0 [0x00], Arg2)
                Store (Arg0 [0x01], Arg3)
                Store (Arg0 [0x02], Arg4)
                Store (Arg0 [0x03], Arg5)
            }

            M000 ()
            M001 ()
            M002 ()
            M003 (0x00, 0x00, 0x00, 0x00)
            M004 (0x00, 0x00, 0x00, 0x00)
            M005 (P000, P001, 0x00, 0x00, 0x00, 0x00)
            M005 (Arg0, Arg1, 0x00, 0x00, 0x00, 0x00)
        }

        Method (MM01, 2, NotSerialized)
        {
            M000 ()
            M001 ()
            M002 ()
            M003 (0x00, 0x00, 0x00, 0x00)
            M004 (0x00, 0x00, 0x00, 0x00)
            M005 (P000, P001, 0x00, 0x00, 0x00, 0x00)
            M005 (Arg0, Arg1, 0x00, 0x00, 0x00, 0x00)
        }

        Method (M000, 0, NotSerialized)
        {
            Store (P000 [0x00], P001 [0x00])
            Store (P000 [0x01], P001 [0x01])
            Store (P000 [0x02], P001 [0x02])
            Store (P000 [0x03], P001 [0x03])
        }

        Method (M001, 0, NotSerialized)
        {
            Store (P000 [0x00], P001 [0x00])
            Store (P000 [0x01], P001 [0x01])
            Store (P000 [0x02], P001 [0x02])
            Store (P000 [0x03], P001 [0x03])
            Store (P001 [0x00], P000 [0x00])
            Store (P001 [0x01], P000 [0x01])
            Store (P001 [0x02], P000 [0x02])
            Store (P001 [0x03], P000 [0x03])
        }

        Method (M002, 0, NotSerialized)
        {
            Store (P000 [0x00], Local0)
            Store (P000 [0x01], Local1)
            Store (P000 [0x02], Local2)
            Store (P000 [0x03], Local3)
        }

        Method (M003, 4, NotSerialized)
        {
            Store (P000 [0x00], Arg0)
            Store (P000 [0x01], Arg1)
            Store (P000 [0x02], Arg2)
            Store (P000 [0x03], Arg3)
        }

        Method (M004, 4, NotSerialized)
        {
            Store (P000 [0x00], P001 [0x00])
            Store (P000 [0x01], P001 [0x01])
            Store (P000 [0x02], P001 [0x02])
            Store (P000 [0x03], P001 [0x03])
            Store (P001 [0x00], P000 [0x00])
            Store (P001 [0x01], P000 [0x01])
            Store (P001 [0x02], P000 [0x02])
            Store (P001 [0x03], P000 [0x03])
            Store (S000 [0x00], P001 [0x04])
            Store (S000 [0x01], P001 [0x05])
            Store (S000 [0x02], P001 [0x06])
            Store (B000 [0x00], P001 [0x07])
            Store (B000 [0x01], P001 [0x08])
            Store (B000 [0x02], P001 [0x09])
            Store (P000 [0x00], Local0)
            Store (P000 [0x01], Local1)
            Store (P000 [0x02], Local2)
            Store (P000 [0x03], Local3)
            Store (P000 [0x00], Arg0)
            Store (P000 [0x01], Arg1)
            Store (P000 [0x02], Arg2)
            Store (P000 [0x03], Arg3)
        }

        Method (M005, 6, NotSerialized)
        {
            Store (Arg0 [0x00], Arg1 [0x00])
            Store (Arg0 [0x01], Arg1 [0x01])
            Store (Arg0 [0x02], Arg1 [0x02])
            Store (Arg0 [0x03], Arg1 [0x03])
            Store (Arg1 [0x00], Arg0 [0x00])
            Store (Arg1 [0x01], Arg0 [0x01])
            Store (Arg1 [0x02], Arg0 [0x02])
            Store (Arg1 [0x03], Arg0 [0x03])
            Store (S000 [0x00], P001 [0x04])
            Store (S000 [0x01], P001 [0x05])
            Store (S000 [0x02], P001 [0x06])
            Store (B000 [0x00], P001 [0x07])
            Store (B000 [0x01], P001 [0x08])
            Store (B000 [0x02], P001 [0x09])
            Store (Arg0 [0x00], Local0)
            Store (Arg0 [0x01], Local1)
            Store (Arg0 [0x02], Local2)
            Store (Arg0 [0x03], Local3)
            Store (Arg0 [0x00], Arg2)
            Store (Arg0 [0x01], Arg3)
            Store (Arg0 [0x02], Arg4)
            Store (Arg0 [0x03], Arg5)
        }

        Method (M006, 0, Serialized)
        {
            Name (P000, Package (0x08){})
            Name (P001, Package (0x08){})
            P001 [0x00] = RefOf (P000)
            P000 [0x00] = RefOf (P001)
            P000 [0x01] = RefOf (P000)
            P001 [0x01] = RefOf (P001)
            /* Repeat the same */

            P001 [0x00] = RefOf (P000)
            P000 [0x00] = RefOf (P001)
            P000 [0x01] = RefOf (P000)
            P001 [0x01] = RefOf (P001)
        }

        M000 ()
        M001 ()
        M002 ()
        M003 (0x00, 0x00, 0x00, 0x00)
        M004 (0x00, 0x00, 0x00, 0x00)
        M005 (P000, P001, 0x00, 0x00, 0x00, 0x00)
        MM00 (P000, P001)
        MM01 (P000, P001)
        M006 ()
    }

    Method (M80F, 0, Serialized)
    {
        Name (IG00, 0xABCD0001)
        Name (IR00, 0xABCD0002)
        Method (M000, 0, Serialized)
        {
            Name (I000, 0xABCD0003)
            CopyObject (RefOf (I000), IR00) /* \M80F.IR00 */
        }

        Method (M001, 1, Serialized)
        {
            Name (III0, 0xABCD0004)
            Name (III1, 0xABCD0005)
            Name (III2, 0xABCD0006)
            Name (III3, 0xABCD0007)
            Name (III4, 0xABCD0008)
            Name (III5, 0xABCD0009)
            Name (III6, 0xABCD000A)
            Name (III7, 0xABCD000B)
            CopyObject (DerefOf (IR00), Local0)
            If ((Local0 != Arg0))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Local0, Arg0)
            }
        }

        M000 ()
        M001 (0xABCD0003)
    }

    Method (M810, 0, Serialized)
    {
        Name (P000, Package (0x04)
        {
            0x00,
            0x01,
            0x02,
            0x03
        })
        Method (M000, 0, NotSerialized)
        {
            Local0 = 0xABCD0009
            P000 [0x02] = RefOf (Local0)
        }

        M000 ()
    }

    Method (M811, 0, Serialized)
    {
        Name (P000, Package (0x04)
        {
            0x00,
            0x01,
            0x02,
            0x03
        })
        Method (M000, 0, NotSerialized)
        {
            P000 [0x02] = RefOf (Local0)
        }

        M000 ()
    }

    Method (M805, 0, NotSerialized)
    {
        SRMT ("m806")
        M806 ()
        SRMT ("m807")
        If (Y135)
        {
            M807 ()
        }
        Else
        {
            BLCK ()
        }

        SRMT ("m80f")
        M80F ()
        SRMT ("m810")
        M810 ()
        SRMT ("m811")
        M811 ()
    }
