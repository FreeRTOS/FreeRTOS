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
 * Mix of IRefs which have different type parents -
 * Packages, Buffers and Strings.
 *
 * Outstanding: 0x7 allocations after execution.
 */

Method(m80a, 4)
{
	Store(DerefOf(DerefOf(Index(arg0, arg1))), Local0)
	if (LNotEqual(Local0, arg2)) {
		err("", zFFF, __LINE__, 0, 0, Local0, arg2)
	}
}

Method(m809, 1)
{
    Method(mm00, 1, Serialized)
    {
	Name(FL00, 0)

	Name(i000, 0)
	Name(i001, 0)
	Name(i002, 0)
	Name(i003, 0)

	Name(rd00, 0)
	Name(wr00, 8)

	Name(p000, Package(64){0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07})
	Name(b000, Buffer(64) {0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17})
	Name(b001, Buffer(64) {0x20,0x21,0x22,0x23,0x24,0x25,0x26,0x27})
	Name(s000, "01234567")
	Name(p001, Package(64){0x40,0x41,0x42,0x43,0x44,0x45,0x46,0x47})
	Name(b002, Buffer(64) {0x50,0x51,0x52,0x53,0x54,0x55,0x56,0x57})
	Name(s001, "`abcdefg")
	Name(p002, Package(64){0x70,0x71,0x72,0x73,0x74,0x75,0x76,0x77})

	Store(arg0, FL00)

	Concatenate("Run with FL00 equal to ", FL00, Debug)

	/* Writing IRefs to the same element of package */

	Store(0, rd00)
	Store(8, wr00)

	Store(Index(p000, rd00), Index(p000, wr00))
	m80a(p000, wr00, 0x00, 0x500)
	Store(Index(b000, rd00), Index(p000, wr00))
	m80a(p000, wr00, 0x10, 0x501)
	Store(Index(b001, rd00), Index(p000, wr00))
	m80a(p000, wr00, 0x20, 0x502)
	Store(Index(s000, rd00), Index(p000, wr00))
	m80a(p000, wr00, 0x30, 0x503)
	Store(Index(p001, rd00), Index(p000, wr00))
	m80a(p000, wr00, 0x40, 0x504)
	Store(Index(b002, rd00), Index(p000, wr00))
	m80a(p000, wr00, 0x50, 0x505)
	Store(Index(s001, rd00), Index(p000, wr00))
	m80a(p000, wr00, 0x60, 0x506)
	Store(Index(p002, rd00), Index(p000, wr00))
	m80a(p000, wr00, 0x70, 0x507)

	Method(m001, 7, Serialized)
	{
		Name(i104, 0)
		Name(i105, 0)
		Name(i106, 0)

		if (LEqual(FL00, 1)) {

			Store(arg0, Local0)
			Store(arg1, Local1)
			Store(arg2, Local2)
			Store(arg3, Local3)
			Store(arg4, Local4)
			Store(arg5, Local5)
			Store(arg6, Local6)

			CopyObject(Local0, i000)
			CopyObject(Local1, i001)
			CopyObject(Local2, i002)
			CopyObject(Local3, i003)
			CopyObject(Local4, i104)
			CopyObject(Local5, i105)
			CopyObject(Local6, i106)

			Store(i000, arg0)
			Store(i001, arg1)
			Store(i002, arg2)
			Store(i003, arg3)
			Store(i104, arg4)
			Store(i105, arg5)
			Store(i106, arg6)
		}

		/* IRefs(1): Write IRefs into 9,10.. */

		Store(1, rd00)
		Store(8, wr00)

		Store(Index(arg0, rd00), Index(arg0, Increment(wr00)))
		Store(Index(arg1, rd00), Index(arg0, Increment(wr00)))
		Store(Index(arg2, rd00), Index(arg0, Increment(wr00)))
		Store(Index(arg3, rd00), Index(arg0, Increment(wr00)))
		Store(Index(arg4, rd00), Index(arg0, Increment(wr00)))
		Store(Index(arg5, rd00), Index(arg0, Increment(wr00)))
		Store(Index(arg6, rd00), Index(arg0, Increment(wr00)))

		Store(2, rd00)
		Store(8, wr00)

		Store(Index(arg2, rd00), Index(arg4, Increment(wr00)))
		Store(Index(arg3, rd00), Index(arg4, Increment(wr00)))
		Store(Index(arg4, rd00), Index(arg4, Increment(wr00)))
		Store(Index(arg5, rd00), Index(arg4, Increment(wr00)))
		Store(Index(arg6, rd00), Index(arg4, Increment(wr00)))

		Store(3, rd00)
		Store(15, wr00)

		Store(Index(arg1, rd00), Index(arg0, Increment(wr00)))
		Store(Index(arg3, rd00), Index(arg0, Increment(wr00)))
		Store(Index(arg4, rd00), Index(arg0, Increment(wr00)))

		/* Writing IRefs to the same (8-th) element of package */

		Store(0, rd00)
		Store(8, wr00)

		Store(Index(arg0, rd00), Index(arg0, wr00))
		m80a(arg0, wr00, 0x00, 0x508)
		Store(Index(arg1, rd00), Index(arg0, wr00))
		m80a(arg0, wr00, 0x10, 0x509)
		Store(Index(arg2, rd00), Index(arg0, wr00))
		m80a(arg0, wr00, 0x20, 0x50a)
		Store(Index(arg3, rd00), Index(arg0, wr00))
		m80a(arg0, wr00, 0x30, 0x50b)
		Store(Index(arg4, rd00), Index(arg0, wr00))
		m80a(arg0, wr00, 0x40, 0x50c)
		Store(Index(arg5, rd00), Index(arg0, wr00))
		m80a(arg0, wr00, 0x50, 0x50d)
		Store(Index(arg6, rd00), Index(arg0, wr00))
		m80a(arg0, wr00, 0x60, 0x50e)

		Store(4, rd00)
		Store(20, wr00)

		Store(Index(arg0, rd00), Index(arg0, wr00))
		m80a(arg0, wr00, 0x04, 0x50f)
		Store(Index(arg0, rd00), Index(arg4, wr00))
		m80a(arg4, wr00, 0x04, 0x510)

		Store(Index(arg1, rd00), Index(arg0, wr00))
		m80a(arg0, wr00, 0x14, 0x511)
		Store(Index(arg1, rd00), Index(arg4, wr00))
		m80a(arg4, wr00, 0x14, 0x512)

		Store(Index(arg2, rd00), Index(arg0, wr00))
		m80a(arg0, wr00, 0x24, 0x513)
		Store(Index(arg2, rd00), Index(arg4, wr00))
		m80a(arg4, wr00, 0x24, 0x514)

		Store(Index(arg3, rd00), Index(arg0, wr00))
		m80a(arg0, wr00, 0x34, 0x515)
		Store(Index(arg3, rd00), Index(arg4, wr00))
		m80a(arg4, wr00, 0x34, 0x516)

		Store(Index(arg4, rd00), Index(arg0, wr00))
		m80a(arg0, wr00, 0x44, 0x517)
		Store(Index(arg4, rd00), Index(arg4, wr00))
		m80a(arg4, wr00, 0x44, 0x518)

		Store(Index(arg5, rd00), Index(arg0, wr00))
		m80a(arg0, wr00, 0x54, 0x519)
		Store(Index(arg5, rd00), Index(arg4, wr00))
		m80a(arg4, wr00, 0x54, 0x51a)

		Store(Index(arg6, rd00), Index(arg0, wr00))
		m80a(arg0, wr00, 0x64, 0x51b)
		Store(Index(arg6, rd00), Index(arg4, wr00))
		m80a(arg4, wr00, 0x64, 0x51c)

		/* Read by IRefs (1) */

		Store(8, wr00)
		m80a(arg0, Increment(wr00), 0x01, 0x51d)
		m80a(arg0, Increment(wr00), 0x11, 0x51e)
		m80a(arg0, Increment(wr00), 0x21, 0x51f)
		m80a(arg0, Increment(wr00), 0x31, 0x520)
		m80a(arg0, Increment(wr00), 0x41, 0x521)
		m80a(arg0, Increment(wr00), 0x51, 0x522)
		m80a(arg0, Increment(wr00), 0x61, 0x523)

		Store(8, wr00)
		m80a(arg4, Increment(wr00), 0x22, 0x524)
		m80a(arg4, Increment(wr00), 0x32, 0x525)
		m80a(arg4, Increment(wr00), 0x42, 0x526)
		m80a(arg4, Increment(wr00), 0x52, 0x527)
		m80a(arg4, Increment(wr00), 0x62, 0x528)

		Store(15, wr00)
		m80a(arg0, Increment(wr00), 0x13, 0x529)
		m80a(arg0, Increment(wr00), 0x33, 0x52a)
		m80a(arg0, Increment(wr00), 0x43, 0x52b)
	}

	m001(p000,b000,b001,s000,p001,b002,s001)

	Method(m002, 7, Serialized)
	{
		Name(i104, 0)
		Name(i105, 0)
		Name(i106, 0)

		Store(0, rd00)
		Store(8, wr00)

		Store(arg0, Local0)
		Store(Index(Local0, rd00), Index(arg0, wr00))
		m80a(arg0, wr00, 0x00, 0x52c)
		Store(arg1, Local0)
		Store(Index(Local0, rd00), Index(arg0, wr00))
		m80a(arg0, wr00, 0x10, 0x52d)
		Store(arg2, Local0)
		Store(Index(Local0, rd00), Index(arg0, wr00))
		m80a(arg0, wr00, 0x20, 0x52e)
		Store(arg3, Local0)
		Store(Index(Local0, rd00), Index(arg0, wr00))
		m80a(arg0, wr00, 0x30, 0x52f)
		Store(arg4, Local0)
		Store(Index(Local0, rd00), Index(arg0, wr00))
		m80a(arg0, wr00, 0x40, 0x530)
		Store(arg5, Local0)
		Store(Index(Local0, rd00), Index(arg0, wr00))
		m80a(arg0, wr00, 0x50, 0x531)
		Store(arg6, Local0)
		Store(Index(Local0, rd00), Index(arg0, wr00))
		m80a(arg0, wr00, 0x60, 0x532)

		m001(arg0,arg1,arg2,arg3,arg4,arg5,arg6)

		Store(arg0, Local0)
		Store(arg1, Local1)
		Store(arg2, Local2)
		Store(arg3, Local3)
		Store(arg4, Local4)
		Store(arg5, Local5)
		Store(arg6, Local6)
		m001(Local0,Local1,Local2,Local3,Local4,Local5,Local6)

		CopyObject(arg0, i000)
		CopyObject(arg1, i001)
		CopyObject(arg2, i002)
		CopyObject(arg3, i003)
		CopyObject(arg4, i104)
		CopyObject(arg5, i105)
		CopyObject(arg6, i106)
		m001(i000,i001,i002,i003,i104,i105,i106)

		Store(arg0, Local0)
		Store(arg1, Local1)
		Store(arg2, Local2)
		Store(arg3, Local3)
		Store(arg4, Local4)
		Store(arg5, Local5)
		Store(arg6, Local6)

		Store(Local0, arg0)
		Store(Local1, arg1)
		Store(Local2, arg2)
		Store(Local3, arg3)
		Store(Local4, arg4)
		Store(Local5, arg5)
		Store(Local6, arg6)
		m001(arg0,arg1,arg2,arg3,arg4,arg5,arg6)

		CopyObject(arg0, i000)
		CopyObject(arg1, i001)
		CopyObject(arg2, i002)
		CopyObject(arg3, i003)
		CopyObject(arg4, i104)
		CopyObject(arg5, i105)
		CopyObject(arg6, i106)

		Store(i000, arg0)
		Store(i001, arg1)
		Store(i002, arg2)
		Store(i003, arg3)
		Store(i104, arg4)
		Store(i105, arg5)
		Store(i106, arg6)
		m001(arg0,arg1,arg2,arg3,arg4,arg5,arg6)
	}

	m002(p000,b000,b001,s000,p001,b002,s001)
    } /* mm00 */

	mm00(arg0)
}

Method(m80b,, Serialized)
{
	Name(rd00, 0)
	Name(wr00, 8)
	Name(wr01, 9)

	Name(p000, Package(64){0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07})
	Name(p001, Package(64){0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17})
	Name(p002, Package(64){0x20,0x21,0x22,0x23,0x24,0x25,0x26,0x27})
	Name(p003, Package(64){0x30,0x31,0x32,0x33,0x34,0x35,0x36,0x37})

	/*
	 * 1 -
	 * write reference to p001[0] into p002[wr00]
	 * save reference to p002[wr00] into Local0
	 */

	Store(0, rd00)
	Store(8, wr00)

	Store(Index(p001, rd00), Index(p002, wr00))
	m80a(p002, wr00, 0x10, 0x533)

	Store(Index(p002, wr00), Local0)

	Store(DerefOf(DerefOf(Local0)), Local1)
	if (LNotEqual(Local1, 0x10)) {
		err("", zFFF, __LINE__, 0, 0, Local1, 0x10)
	}

	/*
	 * 2 -
	 * re-write reference to p001[5] into p002[wr00]
	 * use the old reference to p002[wr00] saved into Local0
	 */

	Store(DerefOf(DerefOf(Local0)), Local1)
	if (LNotEqual(Local1, 0x10)) {
		err("", zFFF, __LINE__, 0, 0, Local1, 0x10)
	}

	Store(5, rd00)
	Store(8, wr00)

	Store(Index(p001, rd00), Index(p002, wr00))
	m80a(p002, wr00, 0x15, 0x535)

	Store(DerefOf(DerefOf(Local0)), Local1)
	if (LNotEqual(Local1, 0x15)) {
		err("", zFFF, __LINE__, 0, 0, Local1, 0x15)
	}

	/*
	 * 1 -
	 * write reference to p001[0] into p001[wr00]
	 * save reference to p001[wr00] into Local0
	 */

	Store(0, rd00)
	Store(8, wr00)

	Store(Index(p001, rd00), Index(p001, wr00))
	m80a(p001, wr00, 0x10, 0x537)

	Store(Index(p001, wr00), Local0)

	Store(DerefOf(DerefOf(Local0)), Local1)
	if (LNotEqual(Local1, 0x10)) {
		err("", zFFF, __LINE__, 0, 0, Local1, 0x10)
	}

	/*
	 * 2 -
	 * re-write reference to p001[5] into p001[wr00]
	 * use the old reference to p001[wr00] saved into Local0
	 */

	Store(DerefOf(DerefOf(Local0)), Local1)
	if (LNotEqual(Local1, 0x10)) {
		err("", zFFF, __LINE__, 0, 0, Local1, 0x10)
	}

	Store(5, rd00)
	Store(8, wr00)

	Store(Index(p001, rd00), Index(p001, wr00))
	m80a(p001, wr00, 0x15, 0x53a)

	Store(DerefOf(DerefOf(Local0)), Local1)
	if (LNotEqual(Local1, 0x15)) {
		err("", zFFF, __LINE__, 0, 0, Local1, 0x15)
	}

	/*
	 * 1 -
	 * write reference to p001[0] into p002[wr00]
	 * save reference to p002[wr00] into p003[wr00]
	 */

	Store(7, rd00)
	Store(8, wr00)

	Store(Index(p001, rd00), Index(p002, wr00))
	m80a(p002, wr00, 0x17, 0x53c)

	Store(Index(p002, wr00), Index(p003, wr00))
	Store(DerefOf(DerefOf(DerefOf(Index(p003, wr00)))), Local1)
	if (LNotEqual(Local1, 0x17)) {
		err("", zFFF, __LINE__, 0, 0, Local1, 0x17)
	}

	/*
	 * 2 -
	 * re-write reference to p001[5] into p002[wr00]
	 * use the old reference to p002[wr00] saved into p003[wr00]
	 */

	Store(DerefOf(DerefOf(DerefOf(Index(p003, wr00)))), Local1)
	if (LNotEqual(Local1, 0x17)) {
		err("", zFFF, __LINE__, 0, 0, Local1, 0x17)
	}

	Store(6, rd00)
	Store(8, wr00)

	Store(Index(p001, rd00), Index(p002, wr00))
	m80a(p002, wr00, 0x16, 0x53f)

	Store(DerefOf(DerefOf(DerefOf(Index(p003, wr00)))), Local1)
	if (LNotEqual(Local1, 0x16)) {
		err("", zFFF, __LINE__, 0, 0, Local1, 0x16)
	}

	/*
	 * 1 -
	 * write reference to p001[0] into p001[wr00]
	 * save reference to p001[wr00] into p003[wr00]
	 */

	Store(7, rd00)
	Store(8, wr00)

	Store(Index(p001, rd00), Index(p001, wr00))
	m80a(p001, wr00, 0x17, 0x541)

	Store(Index(p001, wr00), Index(p003, wr00))
	Store(DerefOf(DerefOf(DerefOf(Index(p003, wr00)))), Local1)
	if (LNotEqual(Local1, 0x17)) {
		err("", zFFF, __LINE__, 0, 0, Local1, 0x17)
	}

	/*
	 * 2 -
	 * re-write reference to p001[5] into p001[wr00]
	 * use the old reference to p001[wr00] saved into p003[wr00]
	 */

	Store(DerefOf(DerefOf(DerefOf(Index(p003, wr00)))), Local1)
	if (LNotEqual(Local1, 0x17)) {
		err("", zFFF, __LINE__, 0, 0, Local1, 0x17)
	}

	Store(6, rd00)
	Store(8, wr00)

	Store(Index(p001, rd00), Index(p001, wr00))
	m80a(p001, wr00, 0x16, 0x544)

	Store(DerefOf(DerefOf(DerefOf(Index(p003, wr00)))), Local1)
	if (LNotEqual(Local1, 0x16)) {
		err("", zFFF, __LINE__, 0, 0, Local1, 0x16)
	}

	/*
	 * 1 -
	 * write reference to p001[0] into p001[wr00]
	 * save reference to p001[wr00] into p001[wr00]
	 */

	Store(7, rd00)
	Store(8, wr00)
	Store(9, wr01)

	Store(Index(p001, rd00), Index(p001, wr00))
	m80a(p001, wr00, 0x17, 0x546)

	Store(Index(p001, wr00), Index(p001, wr01))
	Store(DerefOf(DerefOf(DerefOf(Index(p001, wr01)))), Local1)
	if (LNotEqual(Local1, 0x17)) {
		err("", zFFF, __LINE__, 0, 0, Local1, 0x17)
	}

	/*
	 * 2 -
	 * re-write reference to p001[5] into p001[wr00]
	 * use the old reference to p001[wr00] saved into p001[wr01]
	 */

	Store(DerefOf(DerefOf(DerefOf(Index(p001, wr01)))), Local1)
	if (LNotEqual(Local1, 0x17)) {
		err("", zFFF, __LINE__, 0, 0, Local1, 0x17)
	}

	Store(6, rd00)
	Store(8, wr00)

	Store(Index(p001, rd00), Index(p001, wr00))
	m80a(p001, wr00, 0x16, 0x549)

	Store(DerefOf(DerefOf(DerefOf(Index(p001, wr01)))), Local1)
	if (LNotEqual(Local1, 0x16)) {
		err("", zFFF, __LINE__, 0, 0, Local1, 0x16)
	}
}

Method(m80c,, Serialized)
{
	Name(p000, Package(8) {0x78,1,2})
	Name(p001, Package(8) {0,1,2,3,4,5,6,7})

	Store(Index(p000, 0), Local0)
	Store(Local0, Index(p001, 0))
	Store(Local0, Index(p001, 1))
	Store(Local0, Index(p001, 2))
	Store(Local0, Index(p001, 3))
	Store(Local0, Index(p001, 4))
	Store(Local0, Index(p001, 5))
	Store(Local0, Index(p001, 6))
	Store(Local0, Index(p001, 7))

	Store(Local0, Index(p000, 0))
	Store(Local0, Index(p000, 1))
	Store(Local0, Index(p000, 2))
	Store(Local0, Index(p000, 3))
	Store(Local0, Index(p000, 4))
	Store(Local0, Index(p000, 5))
	Store(Local0, Index(p000, 6))
	Store(Local0, Index(p000, 7))

	Store(Local0, Index(p001, 0))
	Store(Local0, Index(p000, 0))
	Store(Local0, Index(p001, 1))
	Store(Local0, Index(p000, 1))
	Store(Local0, Index(p001, 2))
	Store(Local0, Index(p000, 2))
	Store(Local0, Index(p001, 3))
	Store(Local0, Index(p000, 3))
	Store(Local0, Index(p001, 4))
	Store(Local0, Index(p000, 4))
	Store(Local0, Index(p001, 5))
	Store(Local0, Index(p000, 5))
	Store(Local0, Index(p001, 6))
	Store(Local0, Index(p000, 6))
	Store(Local0, Index(p001, 7))
	Store(Local0, Index(p000, 7))

	Store(p000, Index(p001, 7))
	Store(p000, Index(p000, 7))

	Store(p001, Index(p001, 6))
	Store(p001, Index(p000, 6))
}

Method(m80d,, Serialized)
{
	Name(p000, Package(8) {0x78,1,2})
	Name(p001, Package(8) {0,1,2,3,4,5,6,7})

	Store(Index(p000, 0), Index(p001, 0))
	Store(DerefOf(Index(p001, 0)), Index(p001, 1))
	Store(DerefOf(Index(p001, 0)), Index(p001, 2))
	Store(DerefOf(Index(p001, 0)), Index(p001, 3))
	Store(DerefOf(Index(p001, 0)), Index(p001, 4))
	Store(DerefOf(Index(p001, 0)), Index(p001, 5))
	Store(DerefOf(Index(p001, 0)), Index(p001, 6))
	Store(DerefOf(Index(p001, 0)), Index(p001, 7))

	Store(Index(p001, 0), Index(p000, 0))
	Store(DerefOf(Index(p000, 0)), Index(p000, 1))
	Store(DerefOf(Index(p000, 0)), Index(p000, 2))
	Store(DerefOf(Index(p000, 0)), Index(p000, 3))
	Store(DerefOf(Index(p000, 0)), Index(p000, 4))
	Store(DerefOf(Index(p000, 0)), Index(p000, 5))
	Store(DerefOf(Index(p000, 0)), Index(p000, 6))
	Store(DerefOf(Index(p000, 0)), Index(p000, 7))

	Store(Index(p000, 0), Index(p001, 0))
	Store(DerefOf(Index(p001, 0)), Index(p001, 1))
	Store(DerefOf(Index(p001, 0)), Index(p001, 2))
	Store(DerefOf(Index(p001, 0)), Index(p001, 3))
	Store(DerefOf(Index(p001, 0)), Index(p001, 4))
	Store(DerefOf(Index(p001, 0)), Index(p001, 5))
	Store(DerefOf(Index(p001, 0)), Index(p001, 6))
	Store(DerefOf(Index(p001, 0)), Index(p001, 7))

	Store(Index(p001, 0), Index(p000, 0))
	Store(DerefOf(Index(p000, 0)), Index(p000, 1))
	Store(DerefOf(Index(p000, 0)), Index(p000, 2))
	Store(DerefOf(Index(p000, 0)), Index(p000, 3))
	Store(DerefOf(Index(p000, 0)), Index(p000, 4))
	Store(DerefOf(Index(p000, 0)), Index(p000, 5))
	Store(DerefOf(Index(p000, 0)), Index(p000, 6))
	Store(DerefOf(Index(p000, 0)), Index(p000, 7))

	Store(p000, Index(p001, 7))
	Store(p000, Index(p000, 7))

	Store(p001, Index(p001, 6))
	Store(p001, Index(p000, 6))
}

Method(m80e,, Serialized)
{
	Name(p000, Package(64){0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07})
	Name(b000, Buffer(64) {0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17})

	Method(m000, 2)
	{
		Store(DerefOf(DerefOf(Index(p000, arg1))), Local0)
	}

	Method(m001)
	{
		Method(m002)
		{
			Store(Index(p000, 1), Index(p000, 9))
			Store(Index(b000, 1), Index(p000, 10))

			m000(p000,9)
			m000(p000,10)
		}

		m002()
	}

	Method(m003, 2)
	{
		Store(DerefOf(DerefOf(Index(arg0, arg1))), Local0)
	}

	Method(m004,, Serialized)
	{
		Name(p000, Package(64){0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07})
		Name(b000, Buffer(64) {0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17})

		Method(m005)
		{
			Store(Index(p000, 1), Index(p000, 9))
			Store(Index(b000, 1), Index(p000, 10))

			m003(p000,9)
			m003(p000,10)
		}

		m005()
	}

	Method(m006, 2)
	{
		Store(Index(p000, arg1), Local0)
		Store(DerefOf(Local0), Local1)
		Store(DerefOf(Local1), Local2)
	}

	Method(m007)
	{
		Method(m008)
		{
			Store(Index(p000, 1), Index(p000, 9))
			Store(Index(b000, 1), Index(p000, 10))

			m006(p000,9)
			m006(p000,10)
		}

		m008()
	}

	m001()
	m004()
	m007()
}

Method(m812,, Serialized)
{
	Name(p000, Package(64){0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07})
	Name(b000, Buffer(64) {0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17})

	Method(m000, 2)
	{
		Store(Index(p000, arg1), Local0)
		Store(DerefOf(Local0), Local1)
		Store(DerefOf(Local1), Local2)
	}

	Method(m001)
	{
		Method(m002)
		{
			Store(Index(p000, 1), Index(p000, 9))
			Store(Index(b000, 1), Index(p000, 10))

			m000(p000,9)
			m000(p000,10)
		}

		m002()
	}

	m001()
}

Method(m808)
{
	SRMT("m809-0")
	m809(0)
	SRMT("m809-1")
	m809(1)
	SRMT("m80b")
	m80b()
	SRMT("m80c")
	m80c()
	SRMT("m80d")
	m80d()
	SRMT("m80e")
	m80e()
	SRMT("m812")
	m812()
}
