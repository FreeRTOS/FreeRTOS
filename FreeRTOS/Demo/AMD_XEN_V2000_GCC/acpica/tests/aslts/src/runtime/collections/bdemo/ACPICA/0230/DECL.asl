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
     * Bug 230:
     *
     * SUMMARY: ReturnType argument of Method declaration is not supported
     */
    Method (M127, 0, Serialized)
    {
        /* Data to be passed to Method */

        Name (I000, 0xFE7CB391D65A0000)
        Name (S000, "12340002")
        Name (B000, Buffer (0x04)
        {
             0x01, 0x02, 0x03, 0x04                           // ....
        })
        Name (B001, Buffer (0x05)
        {
             0xB0, 0xB1, 0xB2, 0xB3, 0xB4                     // .....
        })
        Name (P000, Package (0x04)
        {
            0x01,
            0x02,
            0x03,
            0x04
        })
        Event (E000)
        Mutex (MX00, 0x00)
        Device (D000)
        {
            Name (I000, 0xABCD0017)
        }

        ThermalZone (TZ00)
        {
        }

        Processor (PR00, 0x00, 0xFFFFFFFF, 0x00){}
        OperationRegion (R900, SystemMemory, 0x0100, 0x0100)
        OperationRegion (R9Z0, SystemMemory, 0x0100, 0x0100)
        PowerResource (PW90, 0x01, 0x0000)
        {
            Method (MMMM, 0, NotSerialized)
            {
                Return (0x00)
            }
        }

        CreateField (B001, 0x00, 0x08, BF90)
        Field (R9Z0, ByteAcc, NoLock, Preserve)
        {
            F900,   8,
            F901,   8,
            F902,   8,
            F903,   8
        }

        BankField (R9Z0, F901, 0x00, ByteAcc, NoLock, Preserve)
        {
            BN90,   4
        }

        IndexField (F902, F903, ByteAcc, NoLock, Preserve)
        {
            IF90,   8,
            IF91,   8
        }

        Method (MMM0, 0, NotSerialized)
        {
            Return ("mmm0")
        }

        /* Method */

        Method (M000, 0, NotSerialized)
        {
            Return (I000) /* \M127.I000 */
        }

        Method (M001, 0, NotSerialized)
        {
            Return (S000) /* \M127.S000 */
        }

        Method (M002, 0, NotSerialized)
        {
            Return (B000) /* \M127.B000 */
        }

        Method (M003, 0, NotSerialized)
        {
            Return (P000) /* \M127.P000 */
        }

        Method (M004, 0, NotSerialized)
        {
            Return (E000) /* \M127.E000 */
        }

        Method (M005, 0, NotSerialized)
        {
            Return (MX00) /* \M127.MX00 */
        }

        Method (M006, 0, NotSerialized)
        {
            Return (D000) /* \M127.D000 */
        }

        Method (M007, 0, NotSerialized)
        {
            Return (TZ00) /* \M127.TZ00 */
        }

        Method (M008, 0, NotSerialized)
        {
            Return (PR00) /* \M127.PR00 */
        }

        Method (M009, 0, NotSerialized)
        {
            Return (R900) /* \M127.R900 */
        }

        Method (M00A, 0, NotSerialized)
        {
            Return (PW90) /* \M127.PW90 */
        }

        Method (M00B, 0, NotSerialized)
        {
            Return (BF90) /* \M127.BF90 */
        }

        Method (M00C, 0, NotSerialized)
        {
            Return (F900) /* \M127.F900 */
        }

        Method (M00D, 0, NotSerialized)
        {
            Return (BN90) /* \M127.BN90 */
        }

        Method (M00E, 0, NotSerialized)
        {
            Return (IF90) /* \M127.IF90 */
        }

        Method (M00F, 0, NotSerialized)
        {
            Return (MMM0 ())
        }

        Method (M010, 0, NotSerialized)
        {
            Return (0xFE7CB391D65A0000)
        }

        Method (M011, 0, NotSerialized)
        {
            Return ("12340002")
        }

        Method (M012, 0, NotSerialized)
        {
            Return (Buffer (0x04)
            {
                 0x01, 0x02, 0x03, 0x04                           // ....
            })
        }

        Method (M013, 0, NotSerialized)
        {
            Return (Package (0x04)
            {
                0x01,
                0x02,
                0x03,
                0x04
            })
        }

        Method (M100, 0, NotSerialized)
        {
            Debug = "Start of test"
            M000 ()
            M001 ()
            M002 ()
            M003 ()
            M004 ()
            M005 ()
            M006 ()
            M007 ()
            M008 ()
            M009 ()
            M00A ()
            M00B ()
            M00C ()
            M00D ()
            M00E ()
            M00F ()
            M010 ()
            M011 ()
            M012 ()
            M013 ()
            Debug = "Finish of test"
        }

        CH03 (__METHOD__, 0x00, __LINE__, 0x00, 0x00)
        M100 ()
        /* Expect either ASL compiler error or any AML interpreter exception */

        CH04 (__METHOD__, 0x00, 0xFF, 0x00, __LINE__, 0x00, 0x00)
    }
