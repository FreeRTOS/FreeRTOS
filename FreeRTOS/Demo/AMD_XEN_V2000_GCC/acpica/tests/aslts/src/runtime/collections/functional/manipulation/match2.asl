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
     * Data type conversion and manipulation
     *
     * Find Object Match
     */
    /*
     This is the initial point of designing the test of
     functionality of Match operator not covered by match1.asl
     (match1.asl - Match operator with Integer only).
     */
    /*
     Prepare one Method (m330,m332...) with all the
     p000,p001... mix differently the contents, so
     traveling will be different...
     */
    /*
     * Digital map of operations:
     *
     *                     MTR MEQ MLE MLT MGE MGT
     *                       0   1   2   3   4   5
     *                    ------------------------
     * always TRUE ) MTR 0| 00  01  02  03  04  05
     *          == ) MEQ 1| 10  11  12  13  14  15
     *          <= ) MLE 2| 20  21  22  23  24  25
     *          <  ) MLT 3| 30  31  32  33  34  35
     *          >= ) MGE 4| 40  41  42  43  44  45
     *          >  ) MGT 5| 50  51  52  53  54  55
     *                    ------------------------
     */
    Name (Z075, 0x4B)
    /*
     // The same as m0df and m0e0 but all the values
     // of Cases are in one Package
     Method(m330, 1)
     {
     Name(i000, 0x12)
     Name(s000, "12")
     Name(b000, Buffer() {0x12})
     Name(p000, Package() {0x12})
     OperationRegion(r000, SystemMemory, 0x100, 0x100)
     Field(r000, ByteAcc, NoLock, Preserve) { f000, 8 }
     Device(d000) {}
     Event(e000)
     Method(m000) { return (0x12) }
     Mutex(mx00, 0)
     PowerResource(pwr0, 1, 0) {Method(m001){return (0)}}
     Processor(prc0, 0, 0xFFFFFFFF, 0) {}
     ThermalZone(tz00) {}
     CreateField(b000, 0, 8, bf00)
     Name(p001, Package(32) {
     i000, s000, b000, p000, f000, d000, e000, m000,
     mx00, r000, pwr0, prc0, tz00, bf00,
     })
     //	Store(0x12, Index(p001, 31))
     Store(Match(p000, MEQ, arg0, MEQ, arg0, 0), Local0)
     return (Local0)
     }
     Method(m331, 1)
     {
     Store(m330(0x12), Local0)
     if (LNotEqual(Local0, Ones)) {
     err(arg0, z075, __LINE__, 0, 0, Local0, Ones)
     }
     }
     */
    /*
     // The same as m0df and m0e0 but all the values
     // of Cases are in one Package
     Method(m330, 1)
     {
     Name(p000, Package() {
     // Buffer
     Buffer(1){10},
     Buffer(2){11,12},
     Buffer() {13,14,15},
     Buffer(2){16,17,18},
     Buffer(3){19,20},
     Buffer(3){21,22,23},
     Buffer(4){24,25,26,27},
     Buffer(5){28,29,30,31,32},
     Buffer(8){33,34,35,36,37,38,39,40},
     Buffer(){0x12,0x34,0x56,0x78,0x9a,0xbc,0xde,0xf0},
     Buffer(9){41,42,43,44,45,46,47,48,49},
     Buffer(67){0x7d},
     Buffer() {
     0x00,0x00,0x02,0x03,0x04,0x05,0x06,0x07,
     0x08,0x09,0x0a,0x0b,0x0c,0x0d,0x0e,0x0f,
     0x00,0x11,0x12,0x13,0x14,0x15,0x16,0x17,
     0x18,0x19,0x1a,0x1b,0x1c,0x1d,0x1e,0x1f,
     0x10,0x21,0x22,0x23,0x24,0x25,0x26,0x27,
     0x28,0x29,0x2a,0x2b,0x2c,0x2d,0x2e,0x2f,
     0x20,0x31,0x32,0x33,0x34,0x35,0x36,0x37,
     0x38,0x39,0x3a,0x3b,0x3c,0x3d,0x3e,0x3f,
     0x30,0x41,0x42},
     Buffer(67) {
     0x00,0x00,0x02,0x03,0x04,0x05,0x06,0x07,
     0x08,0x09,0x0a,0x0b,0x0c,0x0d,0x0e,0x0f,
     0x00,0x11,0x12,0x13,0x14,0x15,0x16,0x17,
     0x18,0x19,0x1a,0x1b,0x1c,0x1d,0x1e,0x1f,
     0x10,0x21,0x22,0x23,0x24,0x25,0x26,0x27,
     0x28,0x29,0x2a,0x2b,0x2c,0x2d,0x2e,0x2f,
     0x20,0x31,0x32,0x33,0x34,0x35,0x36,0x37,
     0x38,0x39,0x3a,0x3b,0x3c,0x3d,0x3e,0x3f,
     0x30,0x41,0x42},
     Buffer(4){0,0,0,0},
     Buffer(8){0,0,0,0,0,0,0,0},
     Buffer(4){0xff,0xff,0xff,0xff},
     Buffer(9){0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff},
     Buffer(8){0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff},
     Buffer(5){0xff,0xff,0xff,0xff,0xff},
     Buffer(1){0xff},
     Buffer(1){},
     Buffer(5){},
     Buffer(9){},
     Buffer(9){0xab, 0xcd, 0xef},
     // String
     "0321",
     "321",
     "ba9876",
     "c179b3fe",
     "fe7cb391d650a284",
     "ffffffff",
     "ffffffffffffffff",
     "ffffffffff",
     "ff",
     "987654321",
     "0xfe7cb3",
     // Integer
     0321,
     9876543210,
     0xc179b3fe,
     0xfe7cb391d650a284,
     0,
     0xffffffff,
     0xffffffffffffffff,
     0xff,
     0xabcdef
     })
     Store(Match(p000, MEQ, arg0, MEQ, arg0, 0), Local0)
     return (Local0)
     }
     Method(m331, 1)
     {
     // Integer
     Store(m330(0321), Local0)
     if (LNotEqual(Local0, 36)) {
     err(arg0, z075, __LINE__, Local0, 36)
     }
     Store(m330(0xd1), Local0)
     if (LNotEqual(Local0, 36)) {
     err(arg0, z075, __LINE__, Local0, 36)
     }
     Store(m330(9876543210), Local0)
     if (F64) {
     if (LNotEqual(Local0, 37)) {
     err(arg0, z075, __LINE__, Local0, 37)
     }
     } else {
     if (LNotEqual(Local0, 45)) {
     err(arg0, z075, __LINE__, Local0, 45)
     }
     }
     Store(m330(0xc179b3fe), Local0)
     if (LNotEqual(Local0, 28)) {
     err(arg0, z075, __LINE__, Local0, 28)
     }
     Store(m330(0xfe7cb391d650a284), Local0)
     if (LNotEqual(Local0, 29)) {
     err(arg0, z075, __LINE__, Local0, 29)
     }
     Store(m330(0), Local0)
     if (LNotEqual(Local0, 14)) {
     err(arg0, z075, __LINE__, Local0, 14)
     }
     Store(m330(0xffffffff), Local0)
     if (LNotEqual(Local0, 16)) {
     err(arg0, z075, __LINE__, Local0, 16)
     }
     Store(m330(0xffffffffffffffff), Local0)
     if (F64) {
     if (LNotEqual(Local0, 17)) {
     err(arg0, z075, __LINE__, Local0, 17)
     }
     } else {
     if (LNotEqual(Local0, 16)) {
     err(arg0, z075, __LINE__, Local0, 16)
     }
     }
     Store(m330(0xff), Local0)
     if (LNotEqual(Local0, 20)) {
     err(arg0, z075, __LINE__, Local0, 20)
     }
     Store(m330(0xabcdef), Local0)
     if (LNotEqual(Local0, 44)) {
     err(arg0, z075, __LINE__, Local0, 44)
     }
     }
     // The same as m0e3 and m0e4 but all the values
     // of Cases are in one Package
     Method(m332, 1)
     {
     Name(p000, Package() {
     // Integer
     0321,
     9876543210,
     0xc179b3fe,
     0xfe7cb391d650a284,
     0,
     0xffffffff,
     0xffffffffffffffff,
     0xff,
     0xabcdef,
     // Buffer
     Buffer(1){10},
     Buffer(2){11,12},
     Buffer() {13,14,15},
     Buffer(2){16,17,18},
     Buffer(3){19,20},
     Buffer(3){21,22,23},
     Buffer(4){24,25,26,27},
     Buffer(5){28,29,30,31,32},
     Buffer(8){33,34,35,36,37,38,39,40},
     Buffer(){0x12,0x34,0x56,0x78,0x9a,0xbc,0xde,0xf0},
     Buffer(9){41,42,43,44,45,46,47,48,49},
     Buffer(67){0x7d},
     Buffer() {
     0x00,0x00,0x02,0x03,0x04,0x05,0x06,0x07,
     0x08,0x09,0x0a,0x0b,0x0c,0x0d,0x0e,0x0f,
     0x00,0x11,0x12,0x13,0x14,0x15,0x16,0x17,
     0x18,0x19,0x1a,0x1b,0x1c,0x1d,0x1e,0x1f,
     0x10,0x21,0x22,0x23,0x24,0x25,0x26,0x27,
     0x28,0x29,0x2a,0x2b,0x2c,0x2d,0x2e,0x2f,
     0x20,0x31,0x32,0x33,0x34,0x35,0x36,0x37,
     0x38,0x39,0x3a,0x3b,0x3c,0x3d,0x3e,0x3f,
     0x30,0x41,0x42},
     Buffer(67) {
     0x00,0x00,0x02,0x03,0x04,0x05,0x06,0x07,
     0x08,0x09,0x0a,0x0b,0x0c,0x0d,0x0e,0x0f,
     0x00,0x11,0x12,0x13,0x14,0x15,0x16,0x17,
     0x18,0x19,0x1a,0x1b,0x1c,0x1d,0x1e,0x1f,
     0x10,0x21,0x22,0x23,0x24,0x25,0x26,0x27,
     0x28,0x29,0x2a,0x2b,0x2c,0x2d,0x2e,0x2f,
     0x20,0x31,0x32,0x33,0x34,0x35,0x36,0x37,
     0x38,0x39,0x3a,0x3b,0x3c,0x3d,0x3e,0x3f,
     0x30,0x41,0x42},
     Buffer(4){0,0,0,0},
     Buffer(8){0,0,0,0,0,0,0,0},
     Buffer(4){0xff,0xff,0xff,0xff},
     Buffer(9){0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff},
     Buffer(8){0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff},
     Buffer(5){0xff,0xff,0xff,0xff,0xff},
     Buffer(1){0xff},
     Buffer(1){},
     Buffer(5){},
     Buffer(9){},
     Buffer(9){0xab, 0xcd, 0xef},
     // String
     "0321",
     "321",
     "ba9876",
     "c179b3fe",
     "fe7cb391d650a284",
     "ffffffff",
     "ffffffffffffffffff",
     "ffffffffffffffff",
     "ffffffffff",
     "ff",
     "fe7cb391d650a2841",
     "987654321",
     "0xfe7cb3",
     "1234q",
     "qwertyuiopasdfghjklzxcvbnm1234567890QWERTYUIOPASDFGHJKLZXCVBNMqwertyuiopasdfghjklzxcvbnm1234567890QWERTYUIOPASDFGHJKLZXCVBNMqwertyuiopasdfghjklzxcvbnm1234567890QWERTYUIOPASDFGHJKLZXCVBNMqwertyuiopasdf",
     "",
     " ",
     "`1234567890-=qwertyuiop[]\\asdfghjkl;'zxcvbnm,./~!@#$%^&*()_+QWERTYUIOP{}|ASDFGHJKL:\"ZXCVBNM<>?",
     "abcdef",
     "ABCDEF",
     })
     Store(Match(p000, MEQ, arg0, MEQ, arg0, 0), Local0)
     return (Local0)
     }
     Method(m333, 1)
     {
     // String
     if (0) {
     Store(m332("0321"), Local0)
     if (LNotEqual(Local0, 34)) {
     err(arg0, z075, __LINE__, Local0, 34)
     }
     Store(m332("321"), Local0)
     if (LNotEqual(Local0, 34)) {
     err(arg0, z075, __LINE__, Local0, 34)
     }
     Store(m332("ba9876"), Local0)
     if (LNotEqual(Local0, 36)) {
     err(arg0, z075, __LINE__, Local0, 36)
     }
     Store(m332("c179b3fe"), Local0)
     if (LNotEqual(Local0, 2)) {
     err(arg0, z075, __LINE__, Local0, 2)
     }
     Store(m332("fe7cb391d650a284"), Local0)
     if (LNotEqual(Local0, 3)) {
     err(arg0, z075, __LINE__, Local0, 3)
     }
     Store(m332("ffffffff"), Local0)
     if (LNotEqual(Local0, 5)) {
     err(arg0, z075, __LINE__, Local0, 5)
     }
     }
     Store(m332("ffffffffffffffffff"), Local0)
     if (LNotEqual(Local0, 40)) {
     err(arg0, z075, __LINE__, Local0, 40)
     }
     if (0) {
     Store(m332("ffffffffffffffff"), Local0)
     if (LNotEqual(Local0, 41)) {
     err(arg0, z075, __LINE__, Local0, 41)
     }
     Store(m332("ffffffffff"), Local0)
     if (LNotEqual(Local0, 42)) {
     err(arg0, z075, __LINE__, Local0, 42)
     }
     Store(m332("ff"), Local0)
     if (LNotEqual(Local0, 43)) {
     err(arg0, z075, __LINE__, Local0, 43)
     }
     Store(m332("fe7cb391d650a2841"), Local0)
     if (LNotEqual(Local0, 44)) {
     err(arg0, z075, __LINE__, Local0, 44)
     }
     Store(m332("987654321"), Local0)
     if (LNotEqual(Local0, 45)) {
     err(arg0, z075, __LINE__, Local0, 45)
     }
     Store(m332("0xfe7cb3"), Local0)
     if (LNotEqual(Local0, 46)) {
     err(arg0, z075, __LINE__, Local0, 46)
     }
     Store(m332("1234q"), Local0)
     if (LNotEqual(Local0, 47)) {
     err(arg0, z075, __LINE__, Local0, 47)
     }
     Store(m332(BIG0), Local0)
     if (LNotEqual(Local0, 48)) {
     err(arg0, z075, __LINE__, Local0, 48)
     }
     Store(m332(""), Local0)
     if (LNotEqual(Local0, 49)) {
     err(arg0, z075, __LINE__, Local0, 49)
     }
     Store(m332(" "), Local0)
     if (LNotEqual(Local0, 50)) {
     err(arg0, z075, __LINE__, Local0, 50)
     }
     Store(m332(ALL0), Local0)
     if (LNotEqual(Local0, 51)) {
     err(arg0, z075, __LINE__, Local0, 51)
     }
     Store(m332("abcdef"), Local0)
     if (LNotEqual(Local0, 52)) {
     err(arg0, z075, __LINE__, Local0, 52)
     }
     Store(m332("ABCDEF"), Local0)
     if (LNotEqual(Local0, 53)) {
     err(arg0, z075, __LINE__, Local0, 53)
     }
     }
     }
     */
    /* Run-method */
    Method (MAT1, 0, Serialized)
    {
        Debug = "TEST: MAT1, Find Object Match"
        /*	m331(ts) */
    /*	m333(ts) */
    }
