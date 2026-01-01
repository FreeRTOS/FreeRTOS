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
     * Bug 264:
     *
     * SUMMARY: Crash on re-writing named element of Package
     */
    /*
     * To be done:
     *
     * 1) Do then the bdemo-test for different type element of Package
     *    (not only Integer i000 as now).
     *
     * 2) See below: what should be there the result of Store operations?
     *
     * 3) After (2) do the relevant tests - writing/rewriting to such type elements of packages.
     */
    Method (M025, 0, NotSerialized)
    {
        Method (M000, 0, Serialized)
        {
            Name (I000, 0xABCD0000)
            Name (P000, Package (0x01)
            {
                I000
            })
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            DerefOf (P000 [0x00]) = 0xABCD0001
            /*
             Specify then what should be there the result of Store operation above?
             Store(DerefOf(Index(p000, 0)), Local0)
             if (LNotEqual(Local0, 0xabcd0000)) {
             err("", zFFF, __LINE__, 0, 0, Local0, 0xabcd0000)
             }
             */
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        }

        Method (M001, 0, Serialized)
        {
            Name (I000, 0xABCD0000)
            Name (P000, Package (0x01)
            {
                I000
            })
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            DerefOf (Local0 = P000 [0x00]) = 0xABCD0001
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        }

        Method (M002, 0, Serialized)
        {
            Name (I000, 0xABCD0000)
            Name (P000, Package (0x01)
            {
                I000
            })
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local0 = P000 [0x00]
            DerefOf (Local0) = 0xABCD0001
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        }

        Method (M003, 0, Serialized)
        {
            Name (I000, 0xABCD0000)
            Name (P000, Package (0x01)
            {
                I000
            })
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Store (P000 [0x00], Local0)
            DerefOf (Local0) = 0xABCD0001
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        }

        Method (M004, 0, Serialized)
        {
            Name (I000, 0xABCD0000)
            Name (P000, Package (0x01)
            {
                I000
            })
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local1 = Local0 = P000 [0x00]
            DerefOf (Local0) = 0xABCD0001
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        }

        Method (M005, 0, Serialized)
        {
            Name (I000, 0xABCD0000)
            Name (P000, Package (0x01)
            {
                I000
            })
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
            Local1 = Local0 = P000 [0x00]
            DerefOf (Local1) = 0xABCD0001
            CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        }

        Method (M006, 0, NotSerialized)
        {
            M000 ()
            M001 ()
            M002 ()
            M003 ()
            M004 ()
            M005 ()
        }

        M006 ()
    }
