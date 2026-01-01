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
 * Auxiliary tests used during investigating of the problem.
 * Without verification.
 *
 * 0x1 Outstanding allocations because of
 * AcpiExec doesn't run the unload of the table have been processed.
 * All they are caused by call to SRMT Method.
 *
 * Outstanding: 0x1 allocations after execution.
 */
Method(mfe6)
{
	Method(m000,, Serialized)
	{
		Name(p000, Package(16) {0x40,0x41,0x42,0x43,0x45,0x46,0x47,0x48,0x49,0x4a})

		if (1) {
			Store(Index(p000, 0), Index(p000, 8))
			Store(Index(p000, 1), Index(p000, 9))
			Store(Index(p000, 2), Index(p000, 10))
			Store(Index(p000, 3), Index(p000, 11))
			Store(Index(p000, 4), Index(p000, 12))
			Store(Index(p000, 5), Index(p000, 13))
			Store(Index(p000, 6), Index(p000, 14))
			Store(Index(p000, 7), Index(p000, 15))
		}
		if (1) {
			Store(Index(p000, 0), Index(p000, 8))
			Store(Index(p000, 0), Index(p000, 9))
			Store(Index(p000, 0), Index(p000, 10))
			Store(Index(p000, 0), Index(p000, 11))
			Store(Index(p000, 0), Index(p000, 12))
			Store(Index(p000, 0), Index(p000, 13))
			Store(Index(p000, 0), Index(p000, 14))
			Store(Index(p000, 0), Index(p000, 15))
		}
		if (1) {
			Store(Index(p000, 0), Index(p000, 8))
			Store(Index(p000, 1), Index(p000, 8))
			Store(Index(p000, 2), Index(p000, 8))
			Store(Index(p000, 3), Index(p000, 8))
			Store(Index(p000, 4), Index(p000, 8))
			Store(Index(p000, 5), Index(p000, 8))
			Store(Index(p000, 6), Index(p000, 8))
			Store(Index(p000, 7), Index(p000, 8))
		}
		if (1) {
			Store(Index(p000, 0), Index(p000, 8))
			Store(Index(p000, 0), Index(p000, 8))
			Store(Index(p000, 0), Index(p000, 8))
			Store(Index(p000, 0), Index(p000, 8))
			Store(Index(p000, 0), Index(p000, 8))
			Store(Index(p000, 0), Index(p000, 8))
			Store(Index(p000, 0), Index(p000, 8))
			Store(Index(p000, 0), Index(p000, 8))
		}
	}

	Method(m001,, Serialized)
	{
		Name(p000, Package() {0x54,0x55,0x56,0x57})
		// Name(p001, Package() {1,2,3,4})

		Store("----------------------------- 0, p000:", Debug)

		Store(p000, Debug)

		Store("----------------------------- 1, Local0 == Store(Index(p000, 0), Local0)", Debug)

		Store(Index(p000, 0), Local0)

		Store(Local0, Debug)

		Store("----------------------------- 2, p000:", Debug)

		Store(p000, Debug)

		Store("----------------------------- 3, p000 == Store(Local0, Index(p000, 1)):", Debug)

		Store(Local0, Index(p000, 1))

		Store(p000, Debug)

		Store("----------------------------- End.", Debug)
	}

	Method(m002,, Serialized)
	{
		Name(p000, Package() {0x68,0x69,0x6a,0x6b})

		Store("-----------------------------", Debug)

		Store(Index(p000, 1), Local0)

		Store("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!", Debug)

		Store(Local0, Debug)

		Store("=============================", Debug)
	}

	Method(m003,, Serialized)
	{
		Name(p000, Package() {0x70,0x71,0x72,0x73,0x74,0x75,0x76,0x77})
		Name(p001, Package() {0x80,0x81,0x82,0x83,0x84,0x85,0x86,0x87})
		Name(p002, Package(8) {0x90})
		Name(p003, Package() {0xa0,0xa1,0xa2,0xa3})
		Name(p004, Package() {0xb0,0xb1,0xb2,0xb3})

		Store("----------------------------- 0, p000:", Debug)

		Store(p000, Debug)

		Store("----------------------------- 1, IRef to 1-th element of p000 (into Local0):", Debug)

		Index(p000, 1, Local0)

		Store(Local0, Debug)

		Store("----------------------------- 2, p000:", Debug)

		Store(p000, Debug)

		Store("----------------------------- 3, IRef to 2-th element of p000 (into Local1):", Debug)

		Index(p000, 2, Local1)

		Store(Local1, Debug)

		Store("----------------------------- 4, p000:", Debug)

		Store(p000, Debug)

		Store("----------------------------- 5, IRef to 3-th element of p000 (again into Local1):", Debug)

		Index(p000, 3, Local1)

		Store(Local1, Debug)

		Store("----------------------------- 6, p000:", Debug)

		Store(p000, Debug)

		Store("----------------------------- 7, IRef to 4-th element of p000 (into Local2):", Debug)

		Index(p000, 4, Local2)

		Store(Local2, Debug)

		Store("----------------------------- 8, p000:", Debug)

		Store(p000, Debug)

		Store("----------------------------- 9, IRef to 4-th element of p000 (into Local3):", Debug)

		Index(p000, 4, Local3)

		Store(Local3, Debug)

		Store("----------------------------- 10, p000:", Debug)

		Store(p000, Debug)

		Store("----------------------------- 11, IRef to 1-th element of p001 (into Local4):", Debug)

		Index(p001, 1, Local4)

		Store(Local4, Debug)

		Store("----------------------------- 12, p001:", Debug)

		Store(p001, Debug)

		Store("----------------------------- 13, p000:", Debug)

		Store(p000, Debug)

		Store("----------------------------- 14, IRef to 1-th element of p001 (Local4) into 5-th element of p000:", Debug)

		Store(Local4, Index(p000, 5))

		Store("----------------------------- 15, p000:", Debug)

		Store(p000, Debug)

		Store("----------------------------- 16, p001:", Debug)

		Store(p001, Debug)

		//////////////////////////////

		Store("----------------------------- 17, IRef to 2-th element of p001 (into Local5):", Debug)

		Index(p001, 2, Local5)

		Store(Local5, Debug)

		Store("----------------------------- 18, p001:", Debug)

		Store(p001, Debug)

		Store("----------------------------- 19, p000:", Debug)

		Store(p000, Debug)

		Store("----------------------------- 20, IRef to 2-th element of p001 (Local5) into 6-th element of p000:", Debug)

		Store(Local5, Index(p000, 6))


		Store("----------------------------- 21, p001:", Debug)

		Store(p001, Debug)

		//////////////////////////////

		Store("----------------------------- 22, p000:", Debug)

		Store(p000, Debug)

		Store("----------------------------- 23, p000:", Debug)

		Store(0, Local0)

		Store(p000, Debug)

		Store("----------------------------- 24, Local2 == IRef to 4-th element of p000:", Debug)

		Store(Local2, Debug)

		//////////////////////////////

		Store("----------------------------- 25, p002:", Debug)

		Store(p002, Debug)

		Store("----------------------------- 26, p002:", Debug)

		Store(0x93, Index(p002, 3))

		Store(p002, Debug)

		Store("----------------------------- 27, p002:", Debug)

		Store(p003, Index(p002, 4))

		Store(p002, Debug)

		Store("----------------------------- 28, p002:", Debug)

		Store(p004, Index(p002, 6))

		Store(p002, Debug)

		Store("----------------------------- 29, p002:", Debug)

		Store(p003, Index(p002, 7))

		Store(p002, Debug)

		Store("----------------------------- 30, p003:", Debug)

		Store(p003, Debug)

		Store("----------------------------- End.", Debug)
	}

	Method(m004,, Serialized)
	{
		Name(p000, Package() {0x54,0x55,0x56,0x57})

		Store("----------------------------- 0", Debug)

		Store(Index(p000, 0), Local0)

		Store("----------------------------- 1", Debug)

		Store(Local0, Index(p000, 1))

		Store("----------------------------- 2", Debug)

		Store(p000, Debug)

		Store("----------------------------- End.", Debug)

		Store(0, Local0)
	}

	Method(m005,, Serialized)
	{
		Name(p000, Package() {0x54,0x55,0x56,0x57})
		Name(p001, Package() {0x64,0x65,0x66,0x67})

		Store(Index(p000, 0), Local0)
		Store(Local0, Index(p001, 1))

		Store(p000, Debug)
		Store(Local0, Debug)
	}

	Method(m006,, Serialized)
	{
		Name(p000, Package() {0x54,0x55})
		Name(p001, Package() {0x54,0x55,0x56,0x57})

		Store(Index(p000, 0), Index(p001, 1))
		Store(Index(p000, 0), Index(p000, 1))
		Store(0x29, Index(p000, 1))
		Store(p000, Debug)
	}

	Method(m007,, Serialized)
	{
		Name(p000, Package(16) {0x50,0x51,0x52,0x53,0x54,0x55,0x56,0x57})
		Name(p001, Package() {0x54,0x55,0x56,0x57})

		Store(Index(p000, 0), Index(p000, 4))
		Store(Index(p000, 0), Index(p000, 4))
		Store(Index(p000, 1), Index(p000, 4))
		Store(Index(p000, 2), Index(p000, 5))
		Store(Index(p000, 3), Index(p000, 6))
		Store(Index(p000, 4), Index(p000, 7))

		Store(Index(p001, 0), Index(p000, 4))
		Store(Index(p001, 0), Index(p000, 8))
		Store(Index(p001, 0), Index(p000, 8))
		Store(Index(p001, 0), Index(p000, 9))

		Store(p000, Debug)
	}

	Method(m008,, Serialized)
	{
		Name(i000, 0xabcd0001)
		Name(p000, Package() {0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,
						0x08,0x09,0x0a,0x0b,0x0c,0x0d,0x0e,0x0f})
		Name(p001, Package() {0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17,
						0x18,0x19,0x1a,0x1b,0x1c,0x1d,0x1e,0x1f})

		Store(RefOf(i000), Index(p000, 0))

		Store(Index(p000,  0), Index(p001, 0))
		Store(Index(p001,  0), Index(p000, 1))
	}

	Method(m009,, Serialized)
	{
		Name(p000, Package() {0xa0,0xa1,0xa2,0xa3,0xa4})
		Name(p001, Package() {0xb0,0xb1,0xb2,0xb3,0xb4,0xb5,0xb6,0xb7})

		Store(Index(p000,  1), Index(p001, 2))
		Store(Index(p001,  3), Index(p000, 4))

		Store(Index(p000,  0), Index(p001, 4))
	}

	Method(m00a,, Serialized)
	{
//		Name(p000, Package() {0xa0,0xa1,0xa2,0xa3,0xa4,0xa5,0xa6,0xa7})
//		Name(p001, Package() {0xb0,0xb1,0xb2,0xb3,0xb4,0xb5,0xb6,0xb7})

		Name(p000, Package() {0xa0,0xa1,0xa2,0xa3,0xa4,0xa5})
		Name(p001, Package() {0xb0,0xb1,0xb2,0xb3,0xb4,0xb5,0xb6,0xb7,0xb8,0xb9,0xba,0xbb})

		Store(0x80, Index(p001, 3))
		Store(0x90, Index(p001, 4))

		Store(Index(p000,  1), Index(p001, 6))
		Store(Index(p000,  2), Index(p001, 7))
		Store(Index(p000,  3), Index(p001, 8))
		Store(Index(p000,  4), Index(p001, 9))
		Store(Index(p000,  5), Index(p001, 10))

		Store(Index(p000,  2), Index(p001, 2))
		Store(Index(p000,  3), Index(p001, 3))
		Store(Index(p000,  4), Index(p001, 4))
		Store(p000, Debug)
		Store(p001, Debug)
	}

	Method(m00b,, Serialized)
	{
		Name(p000, Package() {0xa0,0xa1,0xa2,0xa3,0xa4,0xa5})
		Name(p001, Package() {0xb0,0xb1,0xb2,0xb3,0xb4,0xb5,0xb6,0xb7})

		Store(Index(p000,  0), Index(p001, 0))
		Store(Index(p000,  1), Index(p001, 1))
		Store(Index(p000,  2), Index(p001, 2))
		Store(Index(p000,  3), Index(p001, 3))
		Store(Index(p000,  4), Index(p001, 4))
		Store(Index(p000,  5), Index(p001, 5))

		Store(Index(p000,  1), Index(p001, 2))
		Store(Index(p001,  3), Index(p000, 4))

		Store(p000, Debug)
		Store(p001, Debug)
	}

	Method(m00c,, Serialized)
	{
//		Name(i000, 0xabcd0000)
//		Name(i001, 0xabcd0001)
//		Name(i002, 0xabcd0002)
//		Name(i003, 0xabcd0003)

		Name(p000, Package() {0xa0,0xa1,0xa2})
		Name(p001, Package() {0xb0,0xb1,0xb2,0xb3,0xb4})

		Name(p002, Package(16) {0xc0,0xc1,0xc2})
		Store(Index(p001,  0), Index(p002, 0))
		Store(Index(p001,  0), Index(p002, 1))
		Store(Index(p001,  0), Index(p002, 2))
		Store(Index(p001,  0), Index(p002, 3))
		Store(Index(p001,  0), Index(p002, 4))
		Store(Index(p001,  0), Index(p002, 5))
		Store(Index(p001,  0), Index(p002, 6))
		Store(Index(p001,  0), Index(p002, 7))
		Store(Index(p001,  0), Index(p002, 8))
		Store(Index(p001,  0), Index(p002, 9))
		Store(Index(p001,  0), Index(p002, 10))
		Store(Index(p001,  0), Index(p002, 11))
		Store(Index(p001,  0), Index(p002, 12))

		Store(Index(p000,  1), Index(p001, 3))
		Store(Index(p000,  2), Index(p001, 4))

//		Add(Local0, Local1, Local7)
//		Add(Local2, Local3, Local7)
//		Add(Local4, Local5, Local7)
//		Add(Local6, Local7, Local7)
//		Return (Local7)
	}

	Method(m00d,, Serialized)
	{
		Name(p000, Package() {0xa0,0xa1,0xa2,0xa3,0xa4,0xa5,0xa6,0xa7,0xa8,0xa9,0xaa,0xab})
		Name(p001, Package() {0xb0,0xb1,0xb2,0xb3,0xb4,0xb5,0xb6,0xb7,0xb8,0xb9,0xba,0xbb,0xbc})

		Store(Index(p001,  1), Index(p000, 2))
		Store(Index(p000,  3), Index(p001, 4))

		Store(Index(p000,  5), Index(p000, 6))
		Store(Index(p000,  7), Index(p000, 8))

		Store(Index(p001,  9), Index(p001, 10))

		Store(p000, Debug)
		Store(p001, Debug)
	}

	Method(m00e,, Serialized)
	{
		Name(p000, Package() {0x54,0x55,0x56,0x57})
		Name(p001, Package() {0x64,0x65,0x66,0x67})


		Store(Index(p000, 0), Local0)
		Store(Local0, Index(p001, 1))

		Store(Index(p000, 0), Index(p000, 1))
	}

	Method(m00f,, Serialized)
	{
		Name(p000, Package() {0x54,0x55,0x56,0x57})


		Store(Index(p000, 0), Local0)
		Store(Local0, Index(p000, 1))

		Store(Index(p000, 0), Index(p000, 1))
	}

	Method(m010,, Serialized)
	{
		Name(p000, Package() {0x54,0x55,0x56,0x57})
		Store(Index(p000, 0), Index(p000, 0))
	}

	Method(m011,, Serialized)
	{
		Name(p000, Package() {0xa0,0xa1,0xa2,0xa3,0xa4,0xa5,0xa6,0xa7})
		Name(p001, Package() {0xb0,0xb1,0xb2,0xb3,0xb4,0xb5,0xb6,0xb7})

		Store(Index(p001,  0), Index(p000, 1))
		Store(Index(p000,  2), Index(p000, 3))
		Store(Index(p000,  4), Index(p000, 5))
		Store(Index(p001,  6), Index(p001, 7))
	}

	Method(m012,, Serialized)
	{
		Name(p000, Package() {0xa0,0xa1,0xa2,0xa3,0xa4,0xa5})
		Name(p001, Package() {0xb0,0xb1,0xb2,0xb3,0xb4,0xb5,0xb6,0xb7})

		Store(Index(p000,  0), Index(p001, 0))
		Store(Index(p000,  0), Index(p001, 0))

		Store(Index(p000,  0), Index(p001, 0))
		Store(Index(p000,  0), Index(p001, 0))
		Store(Index(p000,  0), Index(p001, 0))
		Store(Index(p000,  0), Index(p001, 0))
		Store(Index(p000,  0), Index(p001, 0))
		Store(Index(p000,  0), Index(p001, 0))


		Store(Index(p000,  0), Index(p001, 0))
		Store(Index(p000,  1), Index(p001, 1))
		Store(Index(p000,  2), Index(p001, 2))
		Store(Index(p000,  3), Index(p001, 3))
		Store(Index(p000,  4), Index(p001, 4))
		Store(Index(p000,  5), Index(p001, 5))

		Store(Index(p000,  1), Index(p001, 2))
		Store(Index(p001,  3), Index(p000, 4))

		Store(Index(p000,  0), Index(p000, 1))
		Store(Index(p000,  0), Index(p000, 1))
		Store(Index(p000,  0), Index(p000, 1))
		Store(Index(p000,  0), Index(p000, 1))
		Store(Index(p000,  0), Index(p000, 1))
		Store(Index(p000,  0), Index(p000, 1))
		Store(Index(p000,  0), Index(p000, 1))
		Store(Index(p000,  0), Index(p000, 1))

		Store(Index(p000,  0), Index(p000, 0))
		Store(Index(p000,  0), Index(p000, 0))
		Store(Index(p000,  0), Index(p000, 0))
		Store(Index(p000,  0), Index(p000, 0))
		Store(Index(p000,  0), Index(p000, 0))
		Store(Index(p000,  0), Index(p000, 0))
		Store(Index(p000,  0), Index(p000, 0))
		Store(Index(p000,  0), Index(p000, 0))

		Store(p000, Debug)
		Store(p001, Debug)
	}

	Method(m013,, Serialized)
	{
		Name(p000, Package() {0xa0,0xa1})
		Name(p001, Package() {0xb0,0xb1,0xb2,0xb3,0xb4})

		Store(Index(p000,  0), Index(p001, 0))
		Store(Index(p000,  0), Index(p001, 0))
	}

	Method(m014,, Serialized)
	{
		Name(p000, Package() {
			0xa0,0xa1,0xa2,0xa3,0xa4,0xa5,0xa6,0xa7,
			0xa0,0xa1,0xa2,0xa3,0xa4,0xa5,0xa6,0xa7,
			0xa0,0xa1,0xa2,0xa3,0xa4,0xa5,0xa6,0xa7,
			0xa0,0xa1,0xa2,0xa3,0xa4,0xa5,0xa6,0xa7,
			})
		Name(p001, Package() {
			0xb0,0xb1,0xb2,0xb3,0xb4,0xb5,0xb6,0xb7,
			0xb0,0xb1,0xb2,0xb3,0xb4,0xb5,0xb6,0xb7,
			0xb0,0xb1,0xb2,0xb3,0xb4,0xb5,0xb6,0xb7,
			0xb0,0xb1,0xb2,0xb3,0xb4,0xb5,0xb6,0xb7,
			})

		Store(Index(p000,  0), Index(p001, 0))
		Store(Index(p001,  1), Index(p000, 1))
		Store(Index(p000,  2), Index(p001, 2))
		Store(Index(p001,  3), Index(p000, 3))
		Store(Index(p000,  4), Index(p001, 4))
		Store(Index(p001,  5), Index(p000, 5))
		Store(Index(p000,  6), Index(p001, 6))
		Store(Index(p001,  7), Index(p000, 7))


		Store(Index(p000,  0), Index(p001, 0))
		Store(Index(p000,  0), Index(p001, 0))
		Store(Index(p001,  1), Index(p000, 1))
		Store(Index(p001,  1), Index(p000, 1))
		Store(Index(p000,  2), Index(p001, 2))
		Store(Index(p000,  2), Index(p001, 2))
		Store(Index(p001,  3), Index(p000, 3))
		Store(Index(p001,  3), Index(p000, 3))
		Store(Index(p000,  4), Index(p001, 4))
		Store(Index(p000,  4), Index(p001, 4))
		Store(Index(p001,  5), Index(p000, 5))
		Store(Index(p001,  5), Index(p000, 5))
		Store(Index(p000,  6), Index(p001, 6))
		Store(Index(p000,  6), Index(p001, 6))
		Store(Index(p001,  7), Index(p000, 7))
		Store(Index(p001,  7), Index(p000, 7))

		Store(Index(p000,  0), Local0)
		Store(Local0, Index(p001, 0))
		Store(Index(p000,  0), Local0)
		Store(Local0, Index(p001, 0))
	}

	Method(m015,, Serialized)
	{
		Name(p000, Package() {0xa0,0xa1,0xa2})
		Name(p001, Package() {0xb0,0xb1,0xb2,0xb3})

		Store(p000, Index(p001, 0))
		Store(0xabcd0000, Index(p001, 1))
		Store(0xabcd0001, Index(p001, 0))

		Store(0xabcd0001, Local0)
		Store(Local0, Index(p001, 2))
		Store(Local0, Index(p001, 0))
		Store(Local0, Index(p001, 1))
		Store(Local0, Index(p001, 2))

		Store(p001, Debug)
	}

	Method(m016,, Serialized)
	{
		Name(p000, Package() {0xabcd0000})
		Name(p001, Package() {0xabcd0001, 0xabcd0002})

		CopyObject(p001, p000)

		Store(p001, Debug)
	}

	Method(m017,, Serialized)
	{
		Name(p000, Package() {0x20, 0x21})
		Name(p001, Package(18) {0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17})

		Method(m000, 1)
		{
			Store(Index(p000, 0), Index(arg0, 0))
			Store(Index(p000, 1), Index(arg0, 1))

//			+ self Store(Index(p000, 0), Index(arg0, 0)) arg0 - p000
//			Store(Index(arg0, 2), Index(p001, 2))
//			Store(Index(arg0, 3), Index(p001, 3))
//			Store(Index(arg0, 2), Index(arg1, 2))
//			Store(Index(arg0, 3), Index(arg1, 3))
//			Store(Index(arg1, 2), Index(arg0, 2))
//			Store(Index(arg1, 3), Index(arg0, 3))
//			.................
		}
		Method(m001, 1)
		{
			m000(arg0)
		}

		Method(m002, 1)
		{
			m001(arg0)
		}


		m000(p001)

		m000(Package(18) {0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17})

		m000(p000)
		Store(p000, Debug)
		Store(p001, Debug)
	}

	Method(m018,, Serialized)
	{
		Name(p000, Package() {0xa0,0xa1,0xa2,0xa3,0xa4,0xa5})
		Name(p001, Package() {0xb0,0xb1,0xb2,0xb3,0xb4,0xb5})

		Store(Index(p000,  0), Index(p001, 1))
		Store(Index(p001,  2), Index(p000, 3))

		Store(Index(p000,  0), Index(p001, 0))
		Store(Index(p000,  1), Index(p001, 1))
		Store(Index(p000,  2), Index(p001, 2))
		Store(Index(p000,  3), Index(p001, 3))
		Store(Index(p000,  4), Index(p001, 4))
		Store(Index(p000,  5), Index(p001, 5))

		Store(Index(p001,  2), Index(p000, 3))
		Store(Index(p000,  4), Index(p001, 5))
	}

	Method(m019,, Serialized)
	{
		Name(p000, Package() {0xa0,0xa1,0xa2,0xa3,0xa4,0xa5})
		Name(p001, Package() {0xb0,0xb1,0xb2,0xb3,0xb4,0xb5})
		Name(p002, Package() {0xb0,0xb1,0xb2,0xb3,0xb4,0xb5})
		Method(m000)
		{
			Store(Index(p000,  0), Index(p001, 0))
		}

		Store(Index(p000,  0), Index(p002, 0))
		Store(Index(p000,  1), Index(p002, 1))
		Store(Index(p000,  2), Index(p002, 2))
		Store(Index(p000,  3), Index(p002, 3))
		Store(Refof(p000), Index(p002, 4))
		Store(Index(p000,  5), Index(p002, 5))

		m000()

		Store(Index(p000,  0), Index(p001, 0))
	}

	Method(m01a,, Serialized)
	{
		Name(p000, Package() {0xa0,0xa1,0xa2,0xa3,0xa4,0xa5})
		Name(p001, Package() {0xb0,0xb1,0xb2,0xb3,0xb4,0xb5})

		Store(Index(p000,  0), Index(p001, 0))
		Store(Refof(p000), Index(p001, 1))
	}

	Method(m01b,, Serialized)
	{
		Name(p000, Package() {0x20,0x21,0x22,0x23,0x24,0x25})
		Name(p001, Package(18) {0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17})

		Method(m000, 1)
		{
			Store(Index(p000, 0), Index(arg0, 0))

			Store(Index(p000, 0), Index(arg0, 0))
			Store(Index(p000, 0), Index(arg0, 0))

			Store(Index(arg0, 0), Index(p000, 1))
			Store(Index(arg0, 0), Index(p000, 1))
			Store(Index(arg0, 0), Index(p000, 1))

			Store(Index(arg0, 0), Index(p000, 1))
			Store(Index(arg0, 1), Index(p000, 1))
			Store(Index(arg0, 2), Index(p000, 1))

			Store(Index(arg0, 0), Index(p000, 0))
			Store(Index(arg0, 1), Index(p000, 1))
			Store(Index(arg0, 2), Index(p000, 2))
			Store(Index(arg0, 3), Index(p000, 3))
			Store(Index(arg0, 4), Index(p000, 4))
			Store(Index(arg0, 5), Index(p000, 5))


			Store(Index(arg0, 0), Index(p000, 0))
			Store(Index(p000, 0), Index(arg0, 0))
			Store(Index(arg0, 1), Index(p000, 1))
			Store(Index(p000, 0), Index(arg0, 0))
			Store(Index(arg0, 2), Index(p000, 2))
			Store(Index(p000, 0), Index(arg0, 0))
			Store(Index(arg0, 3), Index(p000, 3))
			Store(Index(p000, 0), Index(arg0, 0))
			Store(Index(arg0, 4), Index(p000, 4))
			Store(Index(p000, 0), Index(arg0, 0))
			Store(Index(arg0, 5), Index(p000, 5))
			Store(Index(p000, 0), Index(arg0, 0))
		}
		Method(m001, 1)
		{
			Store("Start m001", Debug)
			m000(arg0)
			Store("Finish m001", Debug)
		}

		Method(m002, 1)
		{
			m001(arg0)
		}

		Method(m003, 1)
		{
			m002(arg0)
		}

		Method(m004, 1)
		{
			Store("Start m004", Debug)
			m003(arg0)
			Store("Finish m004", Debug)
		}

		Store(Index(p000, 0), Index(p001, 0))
		Store(Index(p000, 0), Index(p001, 0))

		m004(p000)
		m000(p001)
		m001(p000)
		m002(p001)
		m003(p000)
		m004(p001)
		m000(p000)
		m001(p001)
		m002(p000)
		m003(p001)
		m004(p000)
	}

	Method(m01c,, Serialized)
	{
		Name(p000, Package() {0x20,0x21,0x22,0x23,0x24,0x25})
		Name(p001, Package(18) {0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17})
		Name(p002, Package(18) {0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17})

		Method(m000, 1)
		{
			Store(Index(arg0, 0), Index(p000, 1))
		}

		m000(p001)
		m000(p000)
		m000(p001)
		m000(p001)
		m000(p000)
		m000(p001)
	}

	Method(m01d,, Serialized)
	{
		Name(p000, Package() {0x20,0x21,0x22,0x23,0x24,0x25})
		Name(p001, Package(18) {0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17})

		Store(Index(p000, 0), Index(p000, 0))
		Store(Index(p000, 0), Index(p001, 0))
		Store(Index(p001, 0), Index(p000, 0))
		Store(Index(p000, 0), Index(p000, 0))
		Store(Index(p000, 0), Index(p001, 0))
		Store(Index(p001, 0), Index(p000, 0))
		Store(Index(p000, 0), Index(p000, 0))
		Store(Index(p000, 0), Index(p001, 0))
		Store(Index(p001, 0), Index(p000, 0))

		Store(Index(p000, 1), Index(p001, 1))
		Store(p000, Index(p001, 1))
	}

	Method(m01e,, Serialized)
	{
		Name(p000, Package() {0x10, 0x11})
		Name(p001, Package() {0x20, 0x21})

		Method(m000, 1)
		{
			Store(Index(p000, 0), Index(arg0, 0))

			Store(Index(arg0, 1), Index(p000, 1))
			Store(Index(arg0, 1), Index(p000, 1))
			Store(Index(arg0, 1), Index(p000, 1))
			Store(Index(arg0, 1), Index(p000, 0))
			Store(Index(arg0, 1), Index(p000, 0))
			Store(Index(arg0, 1), Index(p000, 0))
			Store(Index(arg0, 1), Index(p000, 0))
			Store(Index(arg0, 1), Index(p000, 1))
			Store(Index(arg0, 1), Index(p000, 0))
			Store(Index(arg0, 1), Index(p000, 1))
			Store(Index(arg0, 1), Index(p000, 0))
			Store(Index(arg0, 1), Index(p000, 1))
			Store(Index(p000, 0), Index(arg0, 0))
			Store(Index(p000, 0), Index(arg0, 0))
			Store(Index(p000, 0), Index(arg0, 0))
			Store(Index(p000, 0), Index(arg0, 1))
			Store(Index(p000, 0), Index(arg0, 1))
			Store(Index(p000, 0), Index(arg0, 1))
			Store(Index(p000, 0), Index(arg0, 0))
			Store(Index(p000, 0), Index(arg0, 0))
			Store(Index(p000, 0), Index(arg0, 1))
			Store(Index(p000, 0), Index(arg0, 1))
			Store(Index(p000, 0), Index(arg0, 0))
			Store(Index(p000, 0), Index(arg0, 1))
			Store(Index(p000, 0), Index(arg0, 0))
			Store(Index(p000, 0), Index(arg0, 1))
			Store(Index(p000, 0), Index(arg0, 0))
			Store(Index(p000, 0), Index(arg0, 1))
			Store(Index(arg0, 0), Index(p000, 0))
			Store(Index(arg0, 0), Index(p000, 1))
			Store(Index(arg0, 0), Index(arg0, 0))
			Store(Index(arg0, 0), Index(arg0, 1))
			Store(Index(arg0, 1), Index(p000, 0))
			Store(Index(arg0, 1), Index(p000, 1))
			Store(Index(arg0, 1), Index(arg0, 1))
			Store(Index(arg0, 1), Index(arg0, 1))
			Store(Index(p000, 0), Index(p000, 0))
			Store(Index(p000, 0), Index(p000, 1))
			Store(Index(p000, 0), Index(arg0, 0))
			Store(Index(p000, 0), Index(arg0, 1))
			Store(Index(p000, 1), Index(p000, 0))
			Store(Index(p000, 1), Index(p000, 1))
			Store(Index(p000, 1), Index(arg0, 0))
			Store(Index(p000, 1), Index(arg0, 1))
			Store(Index(arg0, 0), Index(p000, 0))
			Store(Index(arg0, 0), Index(p000, 0))
			Store(Index(arg0, 0), Index(p000, 0))
			Store(Index(arg0, 0), Index(p000, 1))
			Store(Index(arg0, 0), Index(p000, 1))
			Store(Index(arg0, 0), Index(p000, 1))
			Store(Index(arg0, 0), Index(arg0, 0))
			Store(Index(arg0, 0), Index(arg0, 0))
			Store(Index(arg0, 0), Index(arg0, 0))
			Store(Index(arg0, 0), Index(arg0, 1))
			Store(Index(arg0, 0), Index(arg0, 1))
			Store(Index(arg0, 0), Index(arg0, 1))
			Store(Index(arg0, 1), Index(p000, 0))
			Store(Index(arg0, 1), Index(p000, 0))
			Store(Index(arg0, 1), Index(p000, 0))
			Store(Index(arg0, 1), Index(p000, 1))
			Store(Index(arg0, 1), Index(p000, 1))
			Store(Index(arg0, 1), Index(p000, 1))
			Store(Index(arg0, 1), Index(arg0, 1))
			Store(Index(arg0, 1), Index(arg0, 1))
			Store(Index(arg0, 1), Index(arg0, 1))
			Store(Index(arg0, 1), Index(arg0, 1))
			Store(Index(arg0, 1), Index(arg0, 1))
			Store(Index(arg0, 1), Index(arg0, 1))
			Store(Index(p000, 0), Index(p000, 0))
			Store(Index(p000, 0), Index(p000, 0))
			Store(Index(p000, 0), Index(p000, 0))
			Store(Index(p000, 0), Index(p000, 1))
			Store(Index(p000, 0), Index(p000, 1))
			Store(Index(p000, 0), Index(p000, 1))
			Store(Index(p000, 0), Index(arg0, 0))
			Store(Index(p000, 0), Index(arg0, 0))
			Store(Index(p000, 0), Index(arg0, 0))
			Store(Index(p000, 0), Index(arg0, 1))
			Store(Index(p000, 0), Index(arg0, 1))
			Store(Index(p000, 0), Index(arg0, 1))
			Store(Index(p000, 1), Index(p000, 0))
			Store(Index(p000, 1), Index(p000, 0))
			Store(Index(p000, 1), Index(p000, 0))
			Store(Index(p000, 1), Index(p000, 1))
			Store(Index(p000, 1), Index(p000, 1))
			Store(Index(p000, 1), Index(p000, 1))
			Store(Index(p000, 1), Index(arg0, 0))
			Store(Index(p000, 1), Index(arg0, 0))
			Store(Index(p000, 1), Index(arg0, 0))
			Store(Index(p000, 1), Index(arg0, 1))
			Store(Index(p000, 1), Index(arg0, 1))
			Store(Index(p000, 1), Index(arg0, 1))
		}
		Method(m001, 1)
		{
			m000(arg0)
		}

		Method(m002, 1)
		{
			m001(arg0)
		}

		m000(Package(2) {0x10,0x11})
		m000(Package(4) {0x20,0x21,0x22,0x23})

		m000(Package(4) {0x30,0x31,0x32,0x33})
		m000(Package(4) {0x40,0x41,0x42,0x43})
		m000(Package(4) {0x50,0x51,0x52,0x53})
		m000(Package(4) {0x60,0x61,0x62,0x63})
		m000(Package(4) {0x70,0x71,0x72,0x73})
		m000(Package(4) {0x80,0x81,0x82,0x83})
		m000(Package(4) {0x40,0x41,0x42,0x43})
		m000(Package(4) {0x40,0x41,0x42,0x43})
		m000(Package(4) {0x40,0x41,0x42,0x43})
		m000(Package(4) {0x40,0x41,0x42,0x43})
		m000(Package(4) {0x40,0x41,0x42,0x43})
		m000(Package(4) {0x40,0x41,0x42,0x43})

		m000(Package(7) {0x40,0x41,0x42,0x43})
		m000(Package(7) {0x40,0x41,0x42,0x43})
		m000(Package(9) {0x30,0x31,0x32,0x33})
		m000(Package(18) {0x30,0x31,0x32,0x33})
		m001(Package(18) {0x30,0x31,0x32,0x33})
		m001(Package(18) {0x30,0x31,0x32,0x33})
		m001(Package(18) {0x30,0x31,0x32,0x33})
		m001(Package(18) {0x30,0x31,0x32,0x33})
		m001(Package(18) {0x30,0x31,0x32,0x33})
		m002(Package(18) {0x30,0x31,0x32,0x33})
		m002(Package(18) {0x30,0x31,0x32,0x33})
		m002(Package(18) {0x30,0x31,0x32,0x33})
		m002(Package(18) {0x30,0x31,0x32,0x33})
		m002(Package(18) {0x30,0x31,0x32,0x33})


		m000(p000)
		m000(p001)
		m001(p000)
		m001(p001)
		m002(p000)
		m002(p001)
	}

	Method(m01f,, Serialized)
	{
		Name(s900, "qwertyuiop")

		Method(m000, 1)
		{
			Store(RefOf(arg0), Local0)
			Store(DerefOf(Local0), Local7)

			return (Local7)
		}

		Method(m001, 1)
		{
			Store(RefOf(arg0), Local0)
			Store(DerefOf(Local0), Local7)

			Store(m000(Local7), Local0)
		}

		Store(Index(s900, 0), Local0)
		m001(Local0)
		Store(DerefOf(Local0), Local2)

		Store(Index(Package(){0xabcd0000}, 0), Local0)
		m001(Local0)
		Store(DerefOf(Local0), Local2)
	}

	Method(m020)
	{
		Method(m000,, Serialized)
		{
			Name(p953, Package() {0xabcd2018, 0xabcd2019})
			Name(p954, Package() {0xabcd2018, 0xabcd2019})
			CopyObject(p954, p953)
		}
		m000()
	}

	Method(m021)
	{
		Method(m000, 1)
		{
			Store(0xabcd0000, arg0)
		}

		Method(m001,, Serialized)
		{
		Name(pp00, Package() {0xabcd0001})
		Name(p000, Package() {0xabcd0002, 0xabcd0003})
		Name(p001, Package() {0xabcd0004, 0xabcd0005})


			Store(RefOf(p000), Local0)
			m000(Local0)
			CopyObject(p001, p000)

		}

		m001()
	}

	Method(m022,, Serialized)
	{
		Name(i000, 0xabcd0000)
		Name(p000, Package() {0xabcd0001})

		CopyObject(i000, p000)
		Store(i000, p000)
	}

	Method(m023,, Serialized)
	{
		Name(p000, Package() {0xabcd0000})
		Name(p001, Package() {0xabcd0001, 0xabcd0002})

		CopyObject(p000, p001)
		CopyObject(p001, p000)
	}

	Method(m024,, Serialized)
	{
		Name(p000, Package() {0xabcd0000})
		Name(i000, 0xabcd0000)
		CopyObject(p000, i000)

		m006()
		m021()
		m022()
		m023()

		if (1) {
			m000()
			m001()
			m002()
			m003()
			m004()
			m005()
			m006()
			m007()
			m008()
			m009()
			m00a()
			m00b()
			m00c()
			m00d()
			m00e()
			m00f()
			m010()
			m011()
			m012()
			m013()
			m014()
			m015()
			m016()
			m017()
			m018()
			m019()
			m01a()
			m01b()
			m01c()
			m01d()
			m01e()
			m01f()
			m020()
			m021()
			m022()
			m023()
		}
	}

	SRMT("mfe6")
	m024()
}
