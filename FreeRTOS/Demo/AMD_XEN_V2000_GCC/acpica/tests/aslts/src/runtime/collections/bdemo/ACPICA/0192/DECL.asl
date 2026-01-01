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
     * Bug 192:
     *
     * SUMMARY: Incorrect value of Bank register after storing to its banked field
     */
    Method (MFA4, 0, Serialized)
    {
        /* CHK0 (CheckValue, BenchMarkValue, CheckNum) */

        Method (CHK0, 3, NotSerialized)
        {
            If ((Arg0 != Arg1))
            {
                ERR (__METHOD__, ZFFF, __LINE__, 0x00, 0x00, Arg0, Arg1)
            }
        }

        /* 8-bit Bank field */

        Method (M010, 0, Serialized)
        {
            OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
            Field (R000, ByteAcc, NoLock, Preserve)
            {
                BNK0,   8
            }

            BankField (R000, BNK0, 0x00, ByteAcc, NoLock, Preserve)
            {
                Offset (0x10),
                BF00,   8
            }

            BankField (R000, BNK0, 0x01, ByteAcc, NoLock, Preserve)
            {
                Offset (0x11),
                BF01,   8
            }

            BankField (R000, BNK0, 0xFF, ByteAcc, NoLock, Preserve)
            {
                Offset (0x12),
                BFFF,   8
            }

            /* Deal with 0-th bank layout: */

            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x00)
            BF00 = 0x87
            CHK0 (BNK0, 0x00, 0x01)
            CHK0 (BF00, 0x87, 0x02)
            /* Deal with 1-th bank layout: */

            BNK0 = 0x01
            CHK0 (BNK0, 0x01, 0x03)
            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x04)
            BF01 = 0x96
            CHK0 (BNK0, 0x01, 0x05)
            CHK0 (BF01, 0x96, 0x06)
            /* Deal with 0xFF-th bank layout: */

            BNK0 = 0xFF
            CHK0 (BNK0, 0xFF, 0x07)
            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x08)
            BFFF = 0xC3
            CHK0 (BNK0, 0xFF, 0x09)
            CHK0 (BFFF, 0xC3, 0x0A)
        }

        /* 16-bit Bank field */

        Method (M011, 0, Serialized)
        {
            OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
            Field (R000, WordAcc, NoLock, Preserve)
            {
                BNK0,   16
            }

            BankField (R000, BNK0, 0x00, ByteAcc, NoLock, Preserve)
            {
                Offset (0x10),
                BF00,   8
            }

            BankField (R000, BNK0, 0x01, ByteAcc, NoLock, Preserve)
            {
                Offset (0x11),
                BF01,   8
            }

            BankField (R000, BNK0, 0xFFFF, ByteAcc, NoLock, Preserve)
            {
                Offset (0x12),
                BFFF,   8
            }

            /* Deal with 0-th bank layout: */

            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x0B)
            BF00 = 0x87
            CHK0 (BNK0, 0x00, 0x0C)
            CHK0 (BF00, 0x87, 0x0D)
            /* Deal with 1-th bank layout: */

            BNK0 = 0x01
            CHK0 (BNK0, 0x01, 0x0E)
            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x0F)
            BF01 = 0x96
            CHK0 (BNK0, 0x01, 0x10)
            CHK0 (BF01, 0x96, 0x11)
            /* Deal with 0xFFFF-th bank layout: */

            BNK0 = 0xFFFF
            CHK0 (BNK0, 0xFFFF, 0x12)
            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x13)
            BFFF = 0xC3
            CHK0 (BNK0, 0xFFFF, 0x14)
            CHK0 (BFFF, 0xC3, 0x15)
        }

        /* 32-bit Bank field */

        Method (M012, 0, Serialized)
        {
            OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
            Field (R000, DWordAcc, NoLock, Preserve)
            {
                BNK0,   32
            }

            BankField (R000, BNK0, 0x00, ByteAcc, NoLock, Preserve)
            {
                Offset (0x10),
                BF00,   8
            }

            BankField (R000, BNK0, 0x01, ByteAcc, NoLock, Preserve)
            {
                Offset (0x11),
                BF01,   8
            }

            BankField (R000, BNK0, 0xFFFFFFFF, ByteAcc, NoLock, Preserve)
            {
                Offset (0x12),
                BFFF,   8
            }

            /* Deal with 0-th bank layout: */

            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x16)
            BF00 = 0x87
            CHK0 (BNK0, 0x00, 0x17)
            CHK0 (BF00, 0x87, 0x18)
            /* Deal with 1-th bank layout: */

            BNK0 = 0x01
            CHK0 (BNK0, 0x01, 0x19)
            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x1A)
            BF01 = 0x96
            CHK0 (BNK0, 0x01, 0x1B)
            CHK0 (BF01, 0x96, 0x1C)
            /* Deal with 0xFFFFFFFF-th bank layout: */

            BNK0 = 0xFFFFFFFF
            CHK0 (BNK0, 0xFFFFFFFF, 0x1D)
            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x1E)
            BFFF = 0xC3
            CHK0 (BNK0, 0xFFFFFFFF, 0x1F)
            CHK0 (BFFF, 0xC3, 0x20)
        }

        /* 33-bit Bank field and QWordAcc */

        Method (M013, 0, Serialized)
        {
            OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
            Field (R000, QWordAcc, NoLock, Preserve)
            {
                BNK0,   33
            }

            BankField (R000, BNK0, 0x00000001FFFFFFFF, ByteAcc, NoLock, Preserve)
            {
                Offset (0x12),
                BFFF,   8
            }

            /* Deal with 0x1FFFFFFFF-th bank layout: */

            BNK0 = 0x00000001FFFFFFFF
            CHK0 (BNK0, 0x00000001FFFFFFFF, 0x21)
            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x22)
            BFFF = 0xC3
            CHK0 (BNK0, 0x00000001FFFFFFFF, 0x23)
            CHK0 (BFFF, 0xC3, 0x24)
        }

        /* BankValues set up with Integer Constants */

        Method (M001, 0, NotSerialized)
        {
            /* 8-bit Bank field */

            M010 ()
            /* 16-bit Bank field */

            M011 ()
            /* 32-bit Bank field */

            M012 ()
            /* 33-bit Bank field and QWordAcc */

            If (Y215)
            {
                M013 ()
            }
        }

        /* BankValues set up with Named Integers */

        Name (I000, 0x00)
        Name (I001, 0x01)
        Name (I002, 0xFF)
        Name (I003, 0xFFFF)
        Name (I004, 0xFFFFFFFF)
        Name (I005, 0x00000001FFFFFFFF)
        /* 8-bit Bank field */

        Method (M020, 0, Serialized)
        {
            OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
            Field (R000, ByteAcc, NoLock, Preserve)
            {
                BNK0,   8
            }

            BankField (R000, BNK0, I000, ByteAcc, NoLock, Preserve)
            {
                Offset (0x10),
                BF00,   8
            }

            BankField (R000, BNK0, I001, ByteAcc, NoLock, Preserve)
            {
                Offset (0x11),
                BF01,   8
            }

            BankField (R000, BNK0, I002, ByteAcc, NoLock, Preserve)
            {
                Offset (0x12),
                BFFF,   8
            }

            /* Deal with 0-th bank layout: */

            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x25)
            BF00 = 0x87
            CHK0 (BNK0, 0x00, 0x01)
            CHK0 (BF00, 0x87, 0x26)
            /* Deal with 1-th bank layout: */

            BNK0 = 0x01
            CHK0 (BNK0, 0x01, 0x27)
            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x28)
            BF01 = 0x96
            CHK0 (BNK0, 0x01, 0x29)
            CHK0 (BF01, 0x96, 0x2A)
            /* Deal with 0xFF-th bank layout: */

            BNK0 = 0xFF
            CHK0 (BNK0, 0xFF, 0x2B)
            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x2C)
            BFFF = 0xC3
            CHK0 (BNK0, 0xFF, 0x2D)
            CHK0 (BFFF, 0xC3, 0x2E)
        }

        /* 16-bit Bank field */

        Method (M021, 0, Serialized)
        {
            OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
            Field (R000, WordAcc, NoLock, Preserve)
            {
                BNK0,   16
            }

            BankField (R000, BNK0, I000, ByteAcc, NoLock, Preserve)
            {
                Offset (0x10),
                BF00,   8
            }

            BankField (R000, BNK0, I001, ByteAcc, NoLock, Preserve)
            {
                Offset (0x11),
                BF01,   8
            }

            BankField (R000, BNK0, I003, ByteAcc, NoLock, Preserve)
            {
                Offset (0x12),
                BFFF,   8
            }

            /* Deal with 0-th bank layout: */

            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x2F)
            BF00 = 0x87
            CHK0 (BNK0, 0x00, 0x30)
            CHK0 (BF00, 0x87, 0x31)
            /* Deal with 1-th bank layout: */

            BNK0 = 0x01
            CHK0 (BNK0, 0x01, 0x32)
            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x33)
            BF01 = 0x96
            CHK0 (BNK0, 0x01, 0x34)
            CHK0 (BF01, 0x96, 0x35)
            /* Deal with 0xFFFF-th bank layout: */

            BNK0 = 0xFFFF
            CHK0 (BNK0, 0xFFFF, 0x36)
            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x13)
            BFFF = 0xC3
            CHK0 (BNK0, 0xFFFF, 0x37)
            CHK0 (BFFF, 0xC3, 0x38)
        }

        /* 32-bit Bank field */

        Method (M022, 0, Serialized)
        {
            OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
            Field (R000, DWordAcc, NoLock, Preserve)
            {
                BNK0,   32
            }

            BankField (R000, BNK0, I000, ByteAcc, NoLock, Preserve)
            {
                Offset (0x10),
                BF00,   8
            }

            BankField (R000, BNK0, I001, ByteAcc, NoLock, Preserve)
            {
                Offset (0x11),
                BF01,   8
            }

            BankField (R000, BNK0, I004, ByteAcc, NoLock, Preserve)
            {
                Offset (0x12),
                BFFF,   8
            }

            /* Deal with 0-th bank layout: */

            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x39)
            BF00 = 0x87
            CHK0 (BNK0, 0x00, 0x3A)
            CHK0 (BF00, 0x87, 0x3B)
            /* Deal with 1-th bank layout: */

            BNK0 = 0x01
            CHK0 (BNK0, 0x01, 0x3C)
            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x3E)
            BF01 = 0x96
            CHK0 (BNK0, 0x01, 0x3F)
            CHK0 (BF01, 0x96, 0x40)
            /* Deal with 0xFFFFFFFF-th bank layout: */

            BNK0 = 0xFFFFFFFF
            CHK0 (BNK0, 0xFFFFFFFF, 0x41)
            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x42)
            BFFF = 0xC3
            CHK0 (BNK0, 0xFFFFFFFF, 0x43)
            CHK0 (BFFF, 0xC3, 0x44)
        }

        /* 33-bit Bank field and QWordAcc */

        Method (M023, 0, Serialized)
        {
            OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
            Field (R000, QWordAcc, NoLock, Preserve)
            {
                BNK0,   33
            }

            BankField (R000, BNK0, I005, ByteAcc, NoLock, Preserve)
            {
                Offset (0x12),
                BFFF,   8
            }

            /* Deal with 0x1FFFFFFFF-th bank layout: */

            BNK0 = 0x00000001FFFFFFFF
            CHK0 (BNK0, 0x00000001FFFFFFFF, 0x45)
            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x4E)
            BFFF = 0xC3
            CHK0 (BNK0, 0x00000001FFFFFFFF, 0x46)
            CHK0 (BFFF, 0xC3, 0x47)
        }

        /* BankValues set up with Named Integers */

        Method (M002, 0, NotSerialized)
        {
            /* 8-bit Bank field */

            M020 ()
            /* 16-bit Bank field */

            M021 ()
            /* 32-bit Bank field */

            M022 ()
            /* 33-bit Bank field and QWordAcc */

            If (Y215)
            {
                M023 ()
            }
        }

        /* BankValues set up with LocalX */
        /* 8-bit Bank field */
        Method (M030, 0, Serialized)
        {
            Local0 = 0x00
            Local1 = 0x01
            Local2 = 0xFF
            OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
            Field (R000, ByteAcc, NoLock, Preserve)
            {
                BNK0,   8
            }

            BankField (R000, BNK0, Local0, ByteAcc, NoLock, Preserve)
            {
                Offset (0x10),
                BF00,   8
            }

            BankField (R000, BNK0, Local1, ByteAcc, NoLock, Preserve)
            {
                Offset (0x11),
                BF01,   8
            }

            BankField (R000, BNK0, Local2, ByteAcc, NoLock, Preserve)
            {
                Offset (0x12),
                BFFF,   8
            }

            /* Deal with 0-th bank layout: */

            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x48)
            BF00 = 0x87
            CHK0 (BNK0, 0x00, 0x49)
            CHK0 (BF00, 0x87, 0x4A)
            /* Deal with 1-th bank layout: */

            BNK0 = 0x01
            CHK0 (BNK0, 0x01, 0x4B)
            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x4C)
            BF01 = 0x96
            CHK0 (BNK0, 0x01, 0x4E)
            CHK0 (BF01, 0x96, 0x4F)
            /* Deal with 0xFF-th bank layout: */

            BNK0 = 0xFF
            CHK0 (BNK0, 0xFF, 0x50)
            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x08)
            BFFF = 0xC3
            CHK0 (BNK0, 0xFF, 0x51)
            CHK0 (BFFF, 0xC3, 0x52)
        }

        /* 16-bit Bank field */

        Method (M031, 0, Serialized)
        {
            Local0 = 0x00
            Local1 = 0x01
            Local3 = 0xFFFF
            OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
            Field (R000, WordAcc, NoLock, Preserve)
            {
                BNK0,   16
            }

            BankField (R000, BNK0, Local0, ByteAcc, NoLock, Preserve)
            {
                Offset (0x10),
                BF00,   8
            }

            BankField (R000, BNK0, Local1, ByteAcc, NoLock, Preserve)
            {
                Offset (0x11),
                BF01,   8
            }

            BankField (R000, BNK0, Local3, ByteAcc, NoLock, Preserve)
            {
                Offset (0x12),
                BFFF,   8
            }

            /* Deal with 0-th bank layout: */

            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x53)
            BF00 = 0x87
            CHK0 (BNK0, 0x00, 0x54)
            CHK0 (BF00, 0x87, 0x55)
            /* Deal with 1-th bank layout: */

            BNK0 = 0x01
            CHK0 (BNK0, 0x01, 0x56)
            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x57)
            BF01 = 0x96
            CHK0 (BNK0, 0x01, 0x58)
            CHK0 (BF01, 0x96, 0x59)
            /* Deal with 0xFFFF-th bank layout: */

            BNK0 = 0xFFFF
            CHK0 (BNK0, 0xFFFF, 0x5A)
            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x5B)
            BFFF = 0xC3
            CHK0 (BNK0, 0xFFFF, 0x5C)
            CHK0 (BFFF, 0xC3, 0x5D)
        }

        /* 32-bit Bank field */

        Method (M032, 0, Serialized)
        {
            Local0 = 0x00
            Local1 = 0x01
            Local4 = 0xFFFFFFFF
            OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
            Field (R000, DWordAcc, NoLock, Preserve)
            {
                BNK0,   32
            }

            BankField (R000, BNK0, Local0, ByteAcc, NoLock, Preserve)
            {
                Offset (0x10),
                BF00,   8
            }

            BankField (R000, BNK0, Local1, ByteAcc, NoLock, Preserve)
            {
                Offset (0x11),
                BF01,   8
            }

            BankField (R000, BNK0, Local4, ByteAcc, NoLock, Preserve)
            {
                Offset (0x12),
                BFFF,   8
            }

            /* Deal with 0-th bank layout: */

            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x5E)
            BF00 = 0x87
            CHK0 (BNK0, 0x00, 0x5F)
            CHK0 (BF00, 0x87, 0x60)
            /* Deal with 1-th bank layout: */

            BNK0 = 0x01
            CHK0 (BNK0, 0x01, 0x61)
            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x62)
            BF01 = 0x96
            CHK0 (BNK0, 0x01, 0x63)
            CHK0 (BF01, 0x96, 0x64)
            /* Deal with 0xFFFFFFFF-th bank layout: */

            BNK0 = 0xFFFFFFFF
            CHK0 (BNK0, 0xFFFFFFFF, 0x65)
            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x66)
            BFFF = 0xC3
            CHK0 (BNK0, 0xFFFFFFFF, 0x67)
            CHK0 (BFFF, 0xC3, 0x68)
        }

        /* 33-bit Bank field and QWordAcc */

        Method (M033, 0, Serialized)
        {
            Local5 = 0x00000001FFFFFFFF
            OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
            Field (R000, QWordAcc, NoLock, Preserve)
            {
                BNK0,   33
            }

            BankField (R000, BNK0, Local5, ByteAcc, NoLock, Preserve)
            {
                Offset (0x12),
                BFFF,   8
            }

            /* Deal with 0x1FFFFFFFF-th bank layout: */

            BNK0 = 0x00000001FFFFFFFF
            CHK0 (BNK0, 0x00000001FFFFFFFF, 0x69)
            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x6A)
            BFFF = 0xC3
            CHK0 (BNK0, 0x00000001FFFFFFFF, 0x6B)
            CHK0 (BFFF, 0xC3, 0x6C)
        }

        /* BankValues set up with LocalX */

        Method (M003, 0, NotSerialized)
        {
            /* 8-bit Bank field */

            M030 ()
            /* 16-bit Bank field */

            M031 ()
            /* 32-bit Bank field */

            M032 ()
            /* 33-bit Bank field and QWordAcc */

            If (Y215)
            {
                M033 ()
            }
        }

        /* BankValues set up with ArgX */
        /* 8-bit Bank field */
        Method (M040, 3, Serialized)
        {
            OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
            Field (R000, ByteAcc, NoLock, Preserve)
            {
                BNK0,   8
            }

            BankField (R000, BNK0, Arg0, ByteAcc, NoLock, Preserve)
            {
                Offset (0x10),
                BF00,   8
            }

            BankField (R000, BNK0, Arg1, ByteAcc, NoLock, Preserve)
            {
                Offset (0x11),
                BF01,   8
            }

            BankField (R000, BNK0, Arg2, ByteAcc, NoLock, Preserve)
            {
                Offset (0x12),
                BFFF,   8
            }

            /* Deal with 0-th bank layout: */

            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x6E)
            BF00 = 0x87
            CHK0 (BNK0, 0x00, 0x6F)
            CHK0 (BF00, 0x87, 0x70)
            /* Deal with 1-th bank layout: */

            BNK0 = 0x01
            CHK0 (BNK0, 0x01, 0x71)
            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x72)
            BF01 = 0x96
            CHK0 (BNK0, 0x01, 0x73)
            CHK0 (BF01, 0x96, 0x74)
            /* Deal with 0xFF-th bank layout: */

            BNK0 = 0xFF
            CHK0 (BNK0, 0xFF, 0x75)
            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x76)
            BFFF = 0xC3
            CHK0 (BNK0, 0xFF, 0x77)
            CHK0 (BFFF, 0xC3, 0x78)
        }

        /* 16-bit Bank field */

        Method (M041, 3, Serialized)
        {
            OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
            Field (R000, WordAcc, NoLock, Preserve)
            {
                BNK0,   16
            }

            BankField (R000, BNK0, Arg0, ByteAcc, NoLock, Preserve)
            {
                Offset (0x10),
                BF00,   8
            }

            BankField (R000, BNK0, Arg1, ByteAcc, NoLock, Preserve)
            {
                Offset (0x11),
                BF01,   8
            }

            BankField (R000, BNK0, Arg2, ByteAcc, NoLock, Preserve)
            {
                Offset (0x12),
                BFFF,   8
            }

            /* Deal with 0-th bank layout: */

            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x79)
            BF00 = 0x87
            CHK0 (BNK0, 0x00, 0x7A)
            CHK0 (BF00, 0x87, 0x7B)
            /* Deal with 1-th bank layout: */

            BNK0 = 0x01
            CHK0 (BNK0, 0x01, 0x7C)
            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x7E)
            BF01 = 0x96
            CHK0 (BNK0, 0x01, 0x7F)
            CHK0 (BF01, 0x96, 0x80)
            /* Deal with 0xFFFF-th bank layout: */

            BNK0 = 0xFFFF
            CHK0 (BNK0, 0xFFFF, 0x81)
            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x82)
            BFFF = 0xC3
            CHK0 (BNK0, 0xFFFF, 0x83)
            CHK0 (BFFF, 0xC3, 0x84)
        }

        /* 32-bit Bank field */

        Method (M042, 3, Serialized)
        {
            OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
            Field (R000, DWordAcc, NoLock, Preserve)
            {
                BNK0,   32
            }

            BankField (R000, BNK0, Arg0, ByteAcc, NoLock, Preserve)
            {
                Offset (0x10),
                BF00,   8
            }

            BankField (R000, BNK0, Arg1, ByteAcc, NoLock, Preserve)
            {
                Offset (0x11),
                BF01,   8
            }

            BankField (R000, BNK0, Arg2, ByteAcc, NoLock, Preserve)
            {
                Offset (0x12),
                BFFF,   8
            }

            /* Deal with 0-th bank layout: */

            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x85)
            BF00 = 0x87
            CHK0 (BNK0, 0x00, 0x86)
            CHK0 (BF00, 0x87, 0x87)
            /* Deal with 1-th bank layout: */

            BNK0 = 0x01
            CHK0 (BNK0, 0x01, 0x88)
            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x89)
            BF01 = 0x96
            CHK0 (BNK0, 0x01, 0x8A)
            CHK0 (BF01, 0x96, 0x8B)
            /* Deal with 0xFFFFFFFF-th bank layout: */

            BNK0 = 0xFFFFFFFF
            CHK0 (BNK0, 0xFFFFFFFF, 0x8C)
            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x8D)
            BFFF = 0xC3
            CHK0 (BNK0, 0xFFFFFFFF, 0x8E)
            CHK0 (BFFF, 0xC3, 0x8F)
        }

        /* 33-bit Bank field and QWordAcc */

        Method (M043, 1, Serialized)
        {
            OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
            Field (R000, QWordAcc, NoLock, Preserve)
            {
                BNK0,   33
            }

            BankField (R000, BNK0, Arg0, ByteAcc, NoLock, Preserve)
            {
                Offset (0x12),
                BFFF,   8
            }

            /* Deal with 0x1FFFFFFFF-th bank layout: */

            BNK0 = 0x00000001FFFFFFFF
            CHK0 (BNK0, 0x00000001FFFFFFFF, 0x90)
            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x91)
            BFFF = 0xC3
            CHK0 (BNK0, 0x00000001FFFFFFFF, 0x92)
            CHK0 (BFFF, 0xC3, 0x93)
        }

        /* BankValues set up with ArgX */

        Method (M004, 0, NotSerialized)
        {
            /* 8-bit Bank field */

            M040 (0x00, 0x01, 0xFF)
            /* 16-bit Bank field */

            M041 (0x00, 0x01, 0xFFFF)
            /* 32-bit Bank field */

            M042 (0x00, 0x01, 0xFFFFFFFF)
            /* 33-bit Bank field and QWordAcc */

            If (Y215)
            {
                M043 (0x00000001FFFFFFFF)
            }
        }

        /* BankValues set up with Expressions */
        /* 8-bit Bank field */
        Method (M050, 3, Serialized)
        {
            Local0 = 0x00
            Local1 = 0x01
            OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
            Field (R000, ByteAcc, NoLock, Preserve)
            {
                BNK0,   8
            }

            BankField (R000, BNK0, (Arg0 + Local0), ByteAcc, NoLock, Preserve)
            {
                Offset (0x10),
                BF00,   8
            }

            BankField (R000, BNK0, (Arg1 + 0x01), ByteAcc, NoLock, Preserve)
            {
                Offset (0x11),
                BF01,   8
            }

            BankField (R000, BNK0, (Arg2 + Local1), ByteAcc, NoLock, Preserve)
            {
                Offset (0x12),
                BFFF,   8
            }

            /* Deal with 0-th bank layout: */

            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x94)
            BF00 = 0x87
            CHK0 (BNK0, 0x00, 0x95)
            CHK0 (BF00, 0x87, 0x96)
            /* Deal with 1-th bank layout: */

            BNK0 = 0x01
            CHK0 (BNK0, 0x01, 0x97)
            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x98)
            BF01 = 0x96
            CHK0 (BNK0, 0x01, 0x99)
            CHK0 (BF01, 0x96, 0x9A)
            /* Deal with 0xFF-th bank layout: */

            BNK0 = 0xFF
            CHK0 (BNK0, 0xFF, 0x9B)
            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x9C)
            BFFF = 0xC3
            CHK0 (BNK0, 0xFF, 0x9D)
            CHK0 (BFFF, 0xC3, 0x9E)
        }

        /* 16-bit Bank field */

        Method (M051, 3, Serialized)
        {
            Local0 = 0x00
            Local1 = 0x01
            OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
            Field (R000, WordAcc, NoLock, Preserve)
            {
                BNK0,   16
            }

            BankField (R000, BNK0, (Arg0 + Local0), ByteAcc, NoLock, Preserve)
            {
                Offset (0x10),
                BF00,   8
            }

            BankField (R000, BNK0, (Arg1 + Local1), ByteAcc, NoLock, Preserve)
            {
                Offset (0x11),
                BF01,   8
            }

            BankField (R000, BNK0, (Arg2 + 0x01), ByteAcc, NoLock, Preserve)
            {
                Offset (0x12),
                BFFF,   8
            }

            /* Deal with 0-th bank layout: */

            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0x9F)
            BF00 = 0x87
            CHK0 (BNK0, 0x00, 0xA0)
            CHK0 (BF00, 0x87, 0xA1)
            /* Deal with 1-th bank layout: */

            BNK0 = 0x01
            CHK0 (BNK0, 0x01, 0xA2)
            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0xA3)
            BF01 = 0x96
            CHK0 (BNK0, 0x01, 0xA4)
            CHK0 (BF01, 0x96, 0xA5)
            /* Deal with 0xFFFF-th bank layout: */

            BNK0 = 0xFFFF
            CHK0 (BNK0, 0xFFFF, 0xA6)
            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0xA7)
            BFFF = 0xC3
            CHK0 (BNK0, 0xFFFF, 0xA8)
            CHK0 (BFFF, 0xC3, 0xA9)
        }

        /* 32-bit Bank field */

        Method (M052, 3, Serialized)
        {
            Local0 = 0x00
            Local1 = 0x01
            OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
            Field (R000, DWordAcc, NoLock, Preserve)
            {
                BNK0,   32
            }

            BankField (R000, BNK0, (Arg0 + Local0), ByteAcc, NoLock, Preserve)
            {
                Offset (0x10),
                BF00,   8
            }

            BankField (R000, BNK0, (Arg1 + Local1), ByteAcc, NoLock, Preserve)
            {
                Offset (0x11),
                BF01,   8
            }

            BankField (R000, BNK0, (Arg2 + 0x01), ByteAcc, NoLock, Preserve)
            {
                Offset (0x12),
                BFFF,   8
            }

            /* Deal with 0-th bank layout: */

            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0xAA)
            BF00 = 0x87
            CHK0 (BNK0, 0x00, 0xAB)
            CHK0 (BF00, 0x87, 0xAC)
            /* Deal with 1-th bank layout: */

            BNK0 = 0x01
            CHK0 (BNK0, 0x01, 0xAD)
            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0xAE)
            BF01 = 0x96
            CHK0 (BNK0, 0x01, 0xAF)
            CHK0 (BF01, 0x96, 0xB0)
            /* Deal with 0xFFFFFFFF-th bank layout: */

            BNK0 = 0xFFFFFFFF
            CHK0 (BNK0, 0xFFFFFFFF, 0xB1)
            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0xB2)
            BFFF = 0xC3
            CHK0 (BNK0, 0xFFFFFFFF, 0xB3)
            CHK0 (BFFF, 0xC3, 0xB4)
        }

        /* 33-bit Bank field and QWordAcc */

        Method (M053, 1, Serialized)
        {
            OperationRegion (R000, SystemMemory, 0x0100, 0x0100)
            Field (R000, QWordAcc, NoLock, Preserve)
            {
                BNK0,   33
            }

            BankField (R000, BNK0, (Arg0 + 0x01), ByteAcc, NoLock, Preserve)
            {
                Offset (0x12),
                BFFF,   8
            }

            /* Deal with 0x1FFFFFFFF-th bank layout: */

            BNK0 = 0x00000001FFFFFFFF
            CHK0 (BNK0, 0x00000001FFFFFFFF, 0xB5)
            BNK0 = 0x00
            CHK0 (BNK0, 0x00, 0xB6)
            BFFF = 0xC3
            CHK0 (BNK0, 0x00000001FFFFFFFF, 0xB7)
            CHK0 (BFFF, 0xC3, 0xB8)
        }

        /* BankValues set up with Expressions */

        Method (M005, 0, NotSerialized)
        {
            /* 8-bit Bank field */

            M050 (0x00, 0x00, 0xFE)
            /* 16-bit Bank field */

            M051 (0x00, 0x00, 0xFFFE)
            /* 32-bit Bank field */

            M052 (0x00, 0x00, 0xFFFFFFFE)
            /* 33-bit Bank field and QWordAcc */

            If (Y215)
            {
                M053 (0x00000001FFFFFFFE)
            }
        }

        Debug = "BankValues set up with Integer Constants"
        M001 ()
        Debug = "BankValues set up with Named Integers"
        M002 ()
        Debug = "BankValues set up with LocalX"
        M003 ()
        Debug = "BankValues set up with ArgX"
        M004 ()
        Debug = "BankValues set up with Expressions"
        M005 ()
    }
