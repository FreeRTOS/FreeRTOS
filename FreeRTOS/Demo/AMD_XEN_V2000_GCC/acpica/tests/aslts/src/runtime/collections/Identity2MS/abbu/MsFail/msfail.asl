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
 * Accumulate features which don't work on MS
 *
 * This should help to adapt tests to MS
 *
 * Stuff not working under MS:
 *
 *  1) Mod
 *  2) Concatenate
 *  3) CopyObject
 *  4) POUT - is restricted by abbu, apparently, by byte-size(!),
 *     not by the number of elements (!), and ABBU reports Failure in
 *     that case not distinguishable from failures of MS being examined.
 *  5) Return (Add(i000, m001())) -- !! but this works: Return (Add(Local7, m006()))
 *  6) Arg instead of i000 (in m001):
 *     Store(0x07000000, arg1)
 *     Return (Add(arg1, m007()))
 *  7) LNotEqual(bf00, 0x80) : bf00 - Buffer Field
 *
 *  8) (?) Buffer Field by arg -- doesn't work (?) (see xxx)
 *  9) Field passed by arg -- doesn't work (see m30c)
 * 10) Bank Field passed by arg -- doesn't work (see m30d):
 * 11) Index Field passed by arg -- doesn't work (see m30e):
 *
 * 12) write access to element of String by Index/DerefOf
 * 13) Stack overflow on about 10-12 method calls depth,
 *     call methods chain is restricted by ~11
 * 14) Named element of Package is, perhaps, not implemented by MS,
 *     i000 in Package(){i000} is, on MS, the same as Package(){"i000"},
 *     (see ns1.asl for example).
 * 15) Stack (resource) overflow depends very much on other
 *     reasons, not only the depth of method calls.
 *     So, trying to wrap methods of ns0.asl into one parent method
 *     decreases the available number of levels by more than 4 levels.
 * 16) Internal objects of methods on MS consume some internal
 *     resources of ACPI MS interpreter. Pulling some internal objects
 *     of that method helps to prevent breakage of MS interpreter.
 */

Name(z161, 161)

/*
 * Named Integer i000
 */

/*
 * CopyObject
 *
 * fail
 */
Method(mf00,, Serialized)
{
	Name(ts, "mf00")
	Name(i000, 0xabcd0000)
	Name(i001, 0xabcd0001)

	/* Breaks on this command itself */
	CopyObject(i000, i001)

	if (chk0) {
		if (LNotEqual(i001, 0xabcd0000)) {
			err(ts, z161, __LINE__, 0, 0, i001, 0xabcd0000)
		}
	}

	Return(POUT)
}

/*
 * Concatenate
 *
 * success/fail
 */
Method(mf01,, Serialized)
{
	Name(ts, "mf01")
	Name(s000, "qwertyuiop")
	Name(s001, "_sdfghjkl")

	/* Doesn't break on this command itself */
	Concatenate(s000, s001, Local0)

	OUTP(Local0)

	if (chk0) {
		/* This LNotEqual breaks */
		if (LNotEqual(Local0, "qwertyuiop_sdfghjkl")) {
			err(ts, z161, __LINE__, 0, 0, Local0, "qwertyuiop_sdfghjkl")
		}
	}

	Return(POUT)
}

/*
 * LEqual of Strings
 *
 * fail
 */
Method(mf02,, Serialized)
{
	Name(ts, "mf02")
	Name(s000, "qwertyuiop")
	Name(s001, "_sdfghjkl")

	Store(LEqual("qwerty", "sdfghj"), Local3)

	if (chk0) {
		/* This LNotEqual breaks */
		if (LEqual("qwerty", "sdfghj")) {
			err(ts, z161, __LINE__, 0, 0, "qwerty", "sdfghj")
		}
	}

	Return(POUT)
}

/*
 * Return (Add(i000, m001()))
 *
 * success
 */
Method(mf03,, Serialized)
{
	Name(ts, "mf03")
	Name(i000, 0x12340001)

	Method(m000)
	{
		Method(m001)
		{
			Method(m002)
			{
				Return (1)
			}
			Return (Add(i000, m002()))
		}
		Return (Add(i000, m001()))
	}

	m000()

	if (chk1) {
		Store(m000(), Local0)
		if (LNotEqual(Local0, 0x24680003)) {
			err(ts, z161, __LINE__, 0, 0, Local0, 0x24680003)
		}
	}

	Return(POUT)
}

/*
 * Store to uninitialized ArgX (no value passed by that ArgX)
 *
 * Store(0x00001000, arg6)
 * Return (Add(arg6, m007()))
 *
 * fail
 */
Method(mf04,, Serialized)
{
	Name(ts, "mf04")
	Name(i000, 0xabcd0000)

	Method(m000)
	{
		Store(0x00001001, arg6)
		Return (Add(arg6, 5))
	}

	Method(m001)
	{
		// With this line commented works:
		// Store(0x00001001, arg6)

		Store(0x00001001, arg6)

		// Doesn't work:
		// Return (Add(arg6, 5))
		// Return (0)
	}

	m001()

	if (chk0) {
		Store(m000(), Local0)
		if (LNotEqual(Local0, 0x1006)) {
			err(ts, z161, __LINE__, 0, 0, Local0, 0x1006)
		}
		CH03(ts, z161, 0x00b, __LINE__, 0)
	}

	Return(POUT)
}

/*
 * Store to initialized ArgX (ArgX is passed with Constant Integer)
 *
 * Store(0x00001000, arg0)
 * Return (Add(arg0, m007(0xabcd0000)))
 *
 * succeeded
 */
Method(mf05,, Serialized)
{
	Name(ts, "mf05")

	Method(m000, 1)
	{
		Store(0x00001001, arg0)
		Return (Add(arg0, 5))
	}

	m000(0xabcd0000)

	if (chk1) {
		Store(m000(0xabcd0000), Local0)
		if (LNotEqual(Local0, 0x1006)) {
			err(ts, z161, __LINE__, 0, 0, Local0, 0x1006)
		}
	}

	Return(POUT)
}

/*
 * Store to initialized ArgX (ArgX is passed with Named Integer)
 *
 * Store(0x00001000, arg0)
 * Return (Add(arg0, m007(i000)))
 *
 * succeeded
 */
Method(mf06,, Serialized)
{
	Name(ts, "mf06")
	Name(i000, 0xabcd0000)

	Method(m000, 1)
	{
		Store(0x00001001, arg0)
		Return (Add(arg0, 5))
	}

	Store(m000(i000), Local0)

	if (chk1) {
		if (LNotEqual(Local0, 0x1006)) {
			err(ts, z161, __LINE__, 0, 0, Local0, 0x1006)
		}
		if (LNotEqual(i000, 0xabcd0000)) {
			err(ts, z161, __LINE__, 0, 0, i000, 0xabcd0000)
		}
	}

	Return(POUT)
}

/*
 * Store to initialized ArgX (ArgX is passed with Integer by LocalX)
 *
 * Store(0x00001000, arg0)
 * Return (Add(arg0, m007(i000)))
 *
 * succeeded
 */
Method(mf07,, Serialized)
{
	Name(ts, "mf07")

	Method(m000, 1)
	{
		Store(0x00001001, arg0)
		Return (Add(arg0, 5))
	}

	Store(0xabcd0000, Local7)
	Store(m000(Local7), Local0)

	if (chk1) {
		if (LNotEqual(Local0, 0x1006)) {
			err(ts, z161, __LINE__, 0, 0, Local0, 0x1006)
		}
		if (LNotEqual(Local7, 0xabcd0000)) {
			err(ts, z161, __LINE__, 0, 0, Local7, 0xabcd0000)
		}
	}

	Return(POUT)
}

/*
 * LNotEqual(bf00, 0x80)
 *   bf00 -- Buffer Field
 *
 * fail
 */
Method(mf08,, Serialized)
{
	Name(ts, "mf08")
	Name(pr, 1)
	Name(i001, 0)
	Name(b000, Buffer(9) {0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18})
	CreateField(b000, 0, 8, bf00)

	// Doesn't work
	Store(LNotEqual(bf00, 0x80), Local3)

	if (chk0) {

	// Works
	Store(bf00, Local0)

	// Doesn't work (!) too:
	Store(LNotEqual(Local0, 0x80), Local3)

	// Doesn't work (!) too:
	Store(Local0, Local1)
	Store(LNotEqual(Local1, 0x80), Local3)

	// Works
	if (pr) {
		OUTP(Local0)
		OUTP(bf00)
	}

	// Works
	Store(0x80, bf00)

	// Works
	if (pr) {
		// There is ok:
		OUTP(bf00)
	}

	Store(0x80, bf00)

	if (LNotEqual(bf00, Buffer(){0x80})) {
		err(ts, z161, __LINE__, 0, 0, bf00, Buffer(){0x80})
	}

	} /* if(chk0) */

	Return(POUT)
}

/*
 * Write access to element of String by Index operator
 *
 * fail
 */
Method(mf09,, Serialized)
{
	Name(ts, "mf09")
	Name(s000, "qqqqqqqqqqqqqq")

	Store(0x38, Index(s000, 0))

	if (chk0) {
		Store(DerefOf(Index(s000, 0)), Local0)
		if (LNotEqual(Local0, 0x38)) {
			err(ts, z161, __LINE__, 0, 0, Local0, 0x38)
		}
	}

	Return(POUT)
}

/*
 * Field passed by agrX doesn't work
 *
 * success
 */
Method(mf0a,, Serialized)
{
	Name(ts, "mf0a")
	OperationRegion(r000, SystemMemory, 0x100, 0x100)
	Field(r000, ByteAcc, NoLock, Preserve) { f000, 32 }

	Method(m000, 1)
	{
		Method(m001, 1)
		{
			Store(0x00000020, arg0)
			Return (Add(arg0, 5))
		}

		Add(arg0, 1, Local0)

		Store(Local0, arg0)
		Store(Add(arg0, m001(arg0)), Local0)

		Return (Local0)
	}

	Method(m001, 1)
	{
		Method(m001, 1)
		{
			Return (Add(arg0, 5))
		}

		Store(Add(arg0, m001(arg0)), Local0)

		Return (Local0)
	}

	Store(0x12345678, f000)
	Store(m000(f000), Local0)
	if (chk1) {
		if (LNotEqual(Local0, 0x1234569e)) {
			err(ts, z161, __LINE__, 0, 0, Local0, 0x1234569e)
		}
		if (LNotEqual(f000, 0x12345678)) {
			err(ts, z161, __LINE__, 0, 0, f000, 0x12345678)
		}
	}

	Store(0x12345675, f000)
	Store(m001(f000), Local0)
	if (chk1) {
		if (LNotEqual(Local0, 0x2468acef)) {
			err(ts, z161, __LINE__, 0, 0, Local0, 0x2468acef)
		}
		if (LNotEqual(f000, 0x12345675)) {
			err(ts, z161, __LINE__, 0, 0, f000, 0x12345675)
		}
	}

	Return(POUT)
}

/*
 * Bank Field passed by agrX doesn't work
 *
 * succeeded
 */
Method(mf0b,, Serialized)
{
	Name(ts, "mf0b")
	OperationRegion(r000, SystemMemory, 0x100, 0x100)
	Field(r000, ByteAcc, NoLock, Preserve) { f000,32, f001,32 }
	BankField(r000, f001, 0, ByteAcc, NoLock, Preserve) { bnk0, 32 }

	Method(m000, 1)
	{
		Method(m001, 1)
		{
			Store(0x00000020, arg0)
			Return (Add(arg0, 5))
		}

		Add(arg0, 1, Local0)

		Store(Local0, arg0)
		Store(Add(arg0, m001(arg0)), Local0)

		Return (Local0)
	}

	Method(m001, 1)
	{
		Method(m001, 1)
		{
			Return (Add(arg0, 5))
		}

		Store(Add(arg0, m001(arg0)), Local0)

		Return (Local0)
	}

	Store(0x12345678, bnk0)
	Store(m000(bnk0), Local0)
	if (chk1) {
		if (LNotEqual(Local0, 0x1234569e)) {
			err(ts, z161, __LINE__, 0, 0, Local0, 0x1234569e)
		}
		if (LNotEqual(bnk0, 0x12345678)) {
			err(ts, z161, __LINE__, 0, 0, bnk0, 0x12345678)
		}
	}

	Store(0x12345675, bnk0)
	Store(m001(bnk0), Local0)
	if (chk1) {
		if (LNotEqual(Local0, 0x2468acef)) {
			err(ts, z161, __LINE__, 0, 0, Local0, 0x2468acef)
		}
		if (LNotEqual(bnk0, 0x12345675)) {
			err(ts, z161, __LINE__, 0, 0, bnk0, 0x12345675)
		}
	}

	Return(POUT)
}

/*
 * Index Field passed by agrX doesn't work
 *
 * succeeded
 */
Method(mf0c,, Serialized)
{
	Name(ts, "mf0c")
	OperationRegion(r000, SystemMemory, 0x100, 0x100)
	Field(r000, ByteAcc, NoLock, Preserve) { f000,32, f001,32 }
	IndexField(f000, f001, ByteAcc, NoLock, Preserve) { if00, 32 }

	Method(m000, 1)
	{
		Method(m001, 1)
		{
			Store(0x00000020, arg0)
			Return (Add(arg0, 5))
		}

		Add(arg0, 1, Local0)

		Store(Local0, arg0)
		Store(Add(arg0, m001(arg0)), Local0)

		Return (Local0)
	}

	Method(m001, 1)
	{
		Method(m001, 1)
		{
			Return (Add(arg0, 5))
		}

		Store(Add(arg0, m001(arg0)), Local0)

		Return (Local0)
	}

	Store(0x12345678, if00)
	Store(m000(if00), Local0)
	if (chk1) {
		if (LNotEqual(Local0, 0x12121238)) {
			err(ts, z161, __LINE__, 0, 0, Local0, 0x12121238)
		}
		if (LNotEqual(if00, 0x12121212)) {
			err(ts, z161, __LINE__, 0, 0, if00, 0x12121212)
		}
	}

	Store(0x12345675, if00)
	Store(m001(if00), Local0)
	if (chk1) {
		if (LNotEqual(Local0, 0x24242429)) {
			err(ts, z161, __LINE__, 0, 0, Local0, 0x24242429)
		}
		if (LNotEqual(if00, 0x12121212)) {
			err(ts, z161, __LINE__, 0, 0, if00, 0x12121212)
		}
	}

	Return(POUT)
}

/*
 * Buffer Field passed by agrX
 *
 * fail
 */
Method(mf0d,, Serialized)
{
	Name(ts, "mf0d")
	Name(b000, Buffer(16) {})
	CreateField(b000, 5, 32, bf00)

	Method(m000, 1)
	{
		Method(m001, 1)
		{
			Store(0x00000020, arg0)
			Return (Add(arg0, 5))
		}

		Add(arg0, 1, Local0)

		Store(Local0, arg0)
		Store(Add(arg0, m001(arg0)), Local0)

		Return (Local0)
	}

	Store(0x12345678, bf00)
	Store(m000(bf00), Local0)
	if (chk0) {
		if (LNotEqual(Local0, 0x1234569e)) {
			err(ts, z161, __LINE__, 0, 0, Local0, 0x1234569e)
		}
		if (LNotEqual(bf00, Buffer(){0x78, 0x56, 0x34, 0x12})) {
			err(ts, z161, __LINE__, 0, 0, bf00, Buffer(){0x78, 0x56, 0x34, 0x12})
		}
	}

	Return(POUT)
}

/*
 * Buffer Field passed by agrX
 *
 * fail
 */
Method(mf0e,, Serialized)
{
	Name(ts, "mf0e")
	Name(b000, Buffer(16) {})
	CreateField(b000, 5, 32, bf00)

	Method(m001, 1)
	{
		Method(m001, 1)
		{
			Return (Add(arg0, 5))
		}

		Store(Add(arg0, m001(arg0)), Local0)

		Return (Local0)
	}

	Store(0x12345675, bf00)
	Store(m001(bf00), Local0)
	if (chk0) {
		if (LNotEqual(Local0, 0x2468acef)) {
			err(ts, z161, __LINE__, 0, 0, Local0, 0x2468acef)
		}
		if (LNotEqual(bf00, Buffer(){0x75, 0x56, 0x34, 0x12})) {
			err(ts, z161, __LINE__, 0, 0, bf00, Buffer(){0x75, 0x56, 0x34, 0x12})
		}
	}

	Return(POUT)
}

/*
 * Buffer Field passed by agrX
 *
 * fail
 */
Method(mf0f,, Serialized)
{
	Name(ts, "mf0f")
	Name(b000, Buffer(16) {})
	CreateField(b000, 5, 32, bf00)

	Method(m000, 1)
	{
		Method(m001, 1)
		{
			Store(0x00000020, arg0)
			Return (Add(arg0, 5))
		}

		Add(arg0, 1, Local0)

		Store(Local0, arg0)
		Store(Add(arg0, m001(arg0)), Local0)

		Return (Local0)
	}

	Method(m001, 1)
	{
		Method(m001, 1)
		{
			Return (Add(arg0, 5))
		}

		Store(Add(arg0, m001(arg0)), Local0)

		Return (Local0)
	}

	Store(0x12345678, bf00)
	Store(m000(bf00), Local0)
	if (chk0) {
		if (LNotEqual(Local0, 0x1234569e)) {
			err(ts, z161, __LINE__, 0, 0, Local0, 0x1234569e)
		}
		if (LNotEqual(bf00, Buffer(){0x78, 0x56, 0x34, 0x12})) {
			err(ts, z161, __LINE__, 0, 0, bf00, Buffer(){0x78, 0x56, 0x34, 0x12})
		}
	}

	Store(0x12345675, bf00)
	Store(m001(bf00), Local0)
	if (chk0) {
		if (LNotEqual(Local0, 0x2468acef)) {
			err(ts, z161, __LINE__, 0, 0, Local0, 0x2468acef)
		}
		if (LNotEqual(bf00, Buffer(){0x75, 0x56, 0x34, 0x12})) {
			err(ts, z161, __LINE__, 0, 0, bf00, Buffer(){0x75, 0x56, 0x34, 0x12})
		}
	}

	Return(POUT)
}

/*
 * Buffer Field passed by agrX
 *
 * fail
 */
Method(mf10,, Serialized)
{
	Name(ts, "mf10")
	Name(b000, Buffer(16) {})
	CreateField(b000, 0, 32, bf00)

	Method(m000, 1)
	{
		Return (arg0)
	}

	// Ok
	OUTP(b000)

	// This write works correctly:
	Store(0x12345678, bf00)

	// Succeeds:
	Store(m000(bf00), Local0)

	// Breaks:
	// LNotEqual(Local0, 0x12345678)

	// Breaks:
	// Add(Local0, 0)

	// Breaks:
	// Add(bf00, 0)

	// Ok
	OUTP(b000)

		if (LNotEqual(Local0, Buffer(){0x78, 0x56, 0x34, 0x12})) {
			err(ts, z161, __LINE__, 0, 0, Local0, Buffer(){0x78, 0x56, 0x34, 0x12})
		}
		if (LNotEqual(bf00, Buffer(){0x78, 0x56, 0x34, 0x12})) {
			err(ts, z161, __LINE__, 0, 0, bf00, Buffer(){0x78, 0x56, 0x34, 0x12})
		}

	Return(POUT)
}

/*
 * LEqual of Buffers
 *
 * fail
 */
Method(mf11,, Serialized)
{
	Name(ts, "mf11")
	Name(b000, Buffer(4) {0x10, 0x11, 0x12, 0x13})
	Name(b001, Buffer(4) {0x10, 0x11, 0x12, 0x13})

	Store(LEqual(b000, b001), Local3)

	Return(POUT)
}

/*
 * Method calculation stack overflow
 *
 * If remove one level the test succeeds
 *
 * fail
 */
Method(mf12,, Serialized)
{
	Name(ts, "mf12")

	Name(i000, 0)
	Name(i001, 0)
	Name(i002, 0)
	Name(i003, 0)
	Name(i004, 0)
	Name(i005, 0)
	Name(i006, 0)
	Name(i007, 0)
	Name(i008, 0)
	Name(i009, 0)
	Name(i00a, 0)
	Name(i00b, 0)
	Name(i00c, 0)

	Method(m000)
	{
		Method(m001)
		{
			Method(m002)
			{
				Method(m003)
				{
					Method(m004)
					{
						Method(m005)
						{
							Method(m006)
							{
								Method(m007)
								{
									Method(m008)
									{
										Method(m009)
										{
											Method(m00a)
											{
												Method(m00b)
												{
													Method(m00c)
													{
														Store(0xabcd000c, i00c)
													}
													Store(0xabcd000b, i00b)
													m00c()
												}
												Store(0xabcd000a, i00a)
												m00b()
											}
											Store(0xabcd0009, i009)
											m00a()
										}
										Store(0xabcd0008, i008)
										m009()
									}
									Store(0xabcd0007, i007)
									m008()
								}
								Store(0xabcd0006, i006)
								m007()
							}
							Store(0xabcd0005, i005)
							m006()
						}
						Store(0xabcd0004, i004)
						m005()
					}
					Store(0xabcd0003, i003)
					m004()
				}
				Store(0xabcd0002, i002)
				m003()
			}
			Store(0xabcd0001, i001)
			m002()
		}
		Store(0xabcd0000, i000)
		m001()
	}

	/*
	 * If remove one level the test succeeds
	 */
	m000()

	if (LNotEqual(i000, 0xabcd0000)) {
		err(ts, z161, __LINE__, 0, 0, i000, 0xabcd0000)
	}
	if (LNotEqual(i001, 0xabcd0001)) {
		err(ts, z161, __LINE__, 0, 0, i001, 0xabcd0001)
	}
	if (LNotEqual(i002, 0xabcd0002)) {
		err(ts, z161, __LINE__, 0, 0, i002, 0xabcd0002)
	}
	if (LNotEqual(i003, 0xabcd0003)) {
		err(ts, z161, __LINE__, 0, 0, i003, 0xabcd0003)
	}
	if (LNotEqual(i004, 0xabcd0004)) {
		err(ts, z161, __LINE__, 0, 0, i004, 0xabcd0004)
	}
	if (LNotEqual(i005, 0xabcd0005)) {
		err(ts, z161, __LINE__, 0, 0, i005, 0xabcd0005)
	}
	if (LNotEqual(i006, 0xabcd0006)) {
		err(ts, z161, __LINE__, 0, 0, i006, 0xabcd0006)
	}
	if (LNotEqual(i007, 0xabcd0007)) {
		err(ts, z161, __LINE__, 0, 0, i007, 0xabcd0007)
	}
	if (LNotEqual(i008, 0xabcd0008)) {
		err(ts, z161, __LINE__, 0, 0, i008, 0xabcd0008)
	}
	if (LNotEqual(i009, 0xabcd0009)) {
		err(ts, z161, __LINE__, 0, 0, i009, 0xabcd0009)
	}
	if (LNotEqual(i00a, 0xabcd000a)) {
		err(ts, z161, __LINE__, 0, 0, i00a, 0xabcd000a)
	}
	if (LNotEqual(i00b, 0xabcd000b)) {
		err(ts, z161, __LINE__, 0, 0, i00b, 0xabcd000b)
	}
	if (LNotEqual(i00c, 0xabcd000c)) {
		err(ts, z161, __LINE__, 0, 0, i00c, 0xabcd000c)
	}

	Return(POUT)
}

/*
 * Method calculation stack overflow
 *
 * If remove one level the test succeeds
 *
 * fail
 */
Method(mf13,, Serialized)
{
	Name(ts, "mf13")

	Name(i000, 0)
	Name(i001, 0)
	Name(i002, 0)
	Name(i003, 0)
	Name(i004, 0)
	Name(i005, 0)
	Name(i006, 0)
	Name(i007, 0)
	Name(i008, 0)
	Name(i009, 0)
	Name(i00a, 0)
	Name(i00b, 0)
	Name(i00c, 0)
	Name(i00d, 0)
	Name(i00e, 0)
	Name(i00f, 0)
	Name(i010, 0)


	Method(m000)
	{
		Store(0xabcd0000, i000)
	}
	Method(m001)
	{
		Store(0xabcd0001, i001)
		m000()
	}
	Method(m002)
	{
		Store(0xabcd0002, i002)
		m001()
	}
	Method(m003)
	{
		Store(0xabcd0003, i003)
		m002()
	}
	Method(m004)
	{
		Store(0xabcd0004, i004)
		m003()
	}
	Method(m005)
	{
		Store(0xabcd0005, i005)
		m004()
	}
	Method(m006)
	{
		Store(0xabcd0006, i006)
		m005()
	}
	Method(m007)
	{
		Store(0xabcd0007, i007)
		m006()
	}
	Method(m008)
	{
		Store(0xabcd0008, i008)
		m007()
	}
	Method(m009)
	{
		Store(0xabcd0009, i009)
		m008()
	}
	Method(m00a)
	{
		Store(0xabcd000a, i00a)
		m009()
	}
	Method(m00b)
	{
		Store(0xabcd000b, i00b)
		m00a()
	}
	Method(m00c)
	{
		Store(0xabcd000c, i00c)
		m00b()
	}
	Method(m00d)
	{
		Store(0xabcd000d, i00d)
		m00c()
	}
	Method(m00e)
	{
		Store(0xabcd000e, i00e)
		m00d()
	}
	Method(m00f)
	{
		Store(0xabcd000f, i00f)
		m00e()
	}
	Method(m010)
	{
		Store(0xabcd0010, i010)
		m00f()
	}


	/*
	 * If remove one level the test succeeds
	 */
	m010()


	if (LNotEqual(i000, 0xabcd0000)) {
		err(ts, z161, __LINE__, 0, 0, i000, 0xabcd0000)
	}
	if (LNotEqual(i001, 0xabcd0001)) {
		err(ts, z161, __LINE__, 0, 0, i001, 0xabcd0001)
	}
	if (LNotEqual(i002, 0xabcd0002)) {
		err(ts, z161, __LINE__, 0, 0, i002, 0xabcd0002)
	}
	if (LNotEqual(i003, 0xabcd0003)) {
		err(ts, z161, __LINE__, 0, 0, i003, 0xabcd0003)
	}
	if (LNotEqual(i004, 0xabcd0004)) {
		err(ts, z161, __LINE__, 0, 0, i004, 0xabcd0004)
	}
	if (LNotEqual(i005, 0xabcd0005)) {
		err(ts, z161, __LINE__, 0, 0, i005, 0xabcd0005)
	}
	if (LNotEqual(i006, 0xabcd0006)) {
		err(ts, z161, __LINE__, 0, 0, i006, 0xabcd0006)
	}
	if (LNotEqual(i007, 0xabcd0007)) {
		err(ts, z161, __LINE__, 0, 0, i007, 0xabcd0007)
	}
	if (LNotEqual(i008, 0xabcd0008)) {
		err(ts, z161, __LINE__, 0, 0, i008, 0xabcd0008)
	}
	if (LNotEqual(i009, 0xabcd0009)) {
		err(ts, z161, __LINE__, 0, 0, i009, 0xabcd0009)
	}
	if (LNotEqual(i00a, 0xabcd000a)) {
		err(ts, z161, __LINE__, 0, 0, i00a, 0xabcd000a)
	}
	if (LNotEqual(i00b, 0xabcd000b)) {
		err(ts, z161, __LINE__, 0, 0, i00b, 0xabcd000b)
	}
	if (LNotEqual(i00c, 0xabcd000c)) {
		err(ts, z161, __LINE__, 0, 0, i00c, 0xabcd000c)
	}
	if (LNotEqual(i00d, 0xabcd000d)) {
		err(ts, z161, __LINE__, 0, 0, i00d, 0xabcd000d)
	}
	if (LNotEqual(i00e, 0xabcd000e)) {
		err(ts, z161, __LINE__, 0, 0, i00e, 0xabcd000e)
	}
	if (LNotEqual(i00f, 0xabcd000f)) {
		err(ts, z161, __LINE__, 0, 0, i00f, 0xabcd000f)
	}
	if (LNotEqual(i010, 0xabcd0010)) {
		err(ts, z161, __LINE__, 0, 0, i010, 0xabcd0010)
	}

	Return(POUT)
}

/*
 * Check Timer
 *
 * fail
 */
Method(mf14,, Serialized)
{
	Name(ts, "mf14")
	Name(i000, 0)

	Store(Timer, i000)
	OUTP(i000)

	Return(POUT)
}

/*
 * Mod
 *
 * fail
 */
Method(mf15,, Serialized)
{
	Name(ts, "mf15")

	Store(0x1234567d, Local1)
	Store(8, Local2)

	/* This Mod breaks */
	Mod(Local1, Local2, Local0)

	OUTP(Local0)

	if (chk0) {
		if (LNotEqual(Local0, 5)) {
			err(ts, z161, __LINE__, 0, 0, Local0, 5)
		}
	}

	Return(POUT)
}

/*
 * Return (Package)
 *
 * success
 */
Method(mf16,, Serialized)
{
	Name(ts, "mf16")

	Name(p000, Package() {0xabcd0000, 0xabcd0001, 0xabcd0003})

	Method(m000, 1)
	{
		Return (arg0)
	}

	Store(m000(p000), Local0)
	Store(DerefOf(Index(Local0, 1)), Local0)
	if (LNotEqual(Local0, 0xabcd0001)) {
		err(ts, z161, __LINE__, 0, 0, Local0, 0xabcd0001)
	}

	Return(POUT)
}

/*
 * Return (Package)
 *
 * success
 */
Method(mf17,, Serialized)
{
	Name(ts, "mf17")
	Name(p000, Package() {0xabcd0000, 0xabcd0001, 0xabcd0003})

	Method(m000,, Serialized)
	{
		Name(pp00, Package() {0xabcd0000, 0xabcd0001, 0xabcd0003})

		Return (pp00)
	}

	Store(m000(), Local0)
	Store(DerefOf(Index(Local0, 1)), Local0)
	if (LNotEqual(Local0, 0xabcd0001)) {
		err(ts, z161, __LINE__, 0, 0, Local0, 0xabcd0001)
	}

	Return(POUT)
}

/*
 * LEqual (String, String)
 *
 * fail
 */
Method(mf18,, Serialized)
{
	Name(ts, "mf18")
	Name(s000, "qwertyuiop")
	Name(s001, "qwertyuiop")

	Store(LEqual(s000, s001), Local3)

	if (chk0) {
		Store(LEqual(s000, s001), Local0)
		if (LNot(Local0)) {
			err(ts, z161, __LINE__, 0, 0, Local0, Ones)
		}
	}

	Return(POUT)
}

/*
 * LEqual (Buffer, Buffer)
 *
 * fail
 */
Method(mf19,, Serialized)
{
	Name(ts, "mf19")
	Name(b000, Buffer(4) {0x10, 0x11, 0x12, 0x13})
	Name(b001, Buffer(4) {0x10, 0x11, 0x12, 0x13})

	Store(LEqual(b000, b001), Local3)

	if (chk0) {
		Store(LEqual(b000, b001), Local0)
		if (LNot(Local0)) {
			err(ts, z161, __LINE__, 0, 0, Local0, Ones)
		}
	}

	Return(POUT)
}

/*
 * Store (Package, Package)
 *
 * fail
 */
Method(mf1a,, Serialized)
{
	Name(ts, "mf1a")

	Name(p000, Package() {0xabcd0000, 0xabcd0001, 0xabcd0003})
	Name(pp00, Package(3) {})

	Store(p000, pp00)

	if (chk0) {
		Store(DerefOf(Index(pp00, 1)), Local0)
		if (LNotEqual(Local0, 0xabcd0001)) {
			err(ts, z161, __LINE__, 0, 0, Local0, 0xabcd0001)
		}
	}

	Return(POUT)
}

/*
 * Add (String, String)
 *
 * fail
 */
Method(mf1b,, Serialized)
{
	Name(ts, "mf1b")
	Name(s000, "12345678")
	Name(s001, "56789012")

	Store(Add(s000, s001), Local3)

	if (chk0) {
		Store(Add(s000, s001), Local0)
		if (LNotEqual(Local0, 0x68ACE68A)) {
			err(ts, z161, __LINE__, 0, 0, Local0, 0x68ACE68A)
		}
	}

	Return(POUT)
}

/*
 * Add (Buffer, Buffer)
 *
 * fail
 */
Method(mf1c,, Serialized)
{
	Name(ts, "mf1c")
	Name(b000, Buffer(4) {0x10, 0x11, 0x12, 0x13})
	Name(b001, Buffer(4) {0x24, 0x35, 0x46, 0x57})

	Store(Add(b000, b001), Local3)

	if (chk0) {
		Store(Add(b000, b001), Local0)
		if (LNotEqual(Local0, 0x6A584634)) {
			err(ts, z161, __LINE__, 0, 0, Local0, 0x6A584634)
		}
	}

	Return(POUT)
}

/*
 * LEqual (Field, ....)
 *
 * success
 */
Method(mf1d,, Serialized)
{
	Name(ts, "mf1d")
	OperationRegion(r000, SystemMemory, 0x100, 0x100)
	Field(r000, ByteAcc, NoLock, Preserve) {f000,32}

	Store(0xabcd0000, f000)

	Store(LEqual(f000, 0xabcd0000), Local3)

	Store(LEqual(f000, 0xabcd0000), Local0)
	if (LNot(Local0)) {
		err(ts, z161, __LINE__, 0, 0, Local0, Ones)
	}

	Return(POUT)
}

/*
 * LEqual (Field, ....)
 *
 * success
 */
Method(mf1e,, Serialized)
{
	Name(ts, "mf1e")
	OperationRegion(r000, SystemMemory, 0x100, 0x100)
	Field(r000, ByteAcc, NoLock, Preserve) {f000,32}

	Store(0xabcd0000, f000)

	Method(m000, 1)
	{
		Store(LEqual(arg0, 0xabcd0000), Local0)
		Return (Local0)
	}

	m000(f000)

	Store(m000(f000), Local0)
	if (LNot(Local0)) {
		err(ts, z161, __LINE__, 0, 0, Local0, Ones)
	}

	Return(POUT)
}

/*
 * LNotEqual (Field, ....)
 *
 * success
 */
Method(mf1f,, Serialized)
{
	Name(ts, "mf1f")
	OperationRegion(r000, SystemMemory, 0x100, 0x100)
	Field(r000, ByteAcc, NoLock, Preserve) {f000,32}

	Store(0xabcd0000, f000)

	Method(m000, 1)
	{
		if (LNotEqual(arg0, 0xabcd0000)) {
			err(ts, z161, __LINE__, 0, 0, arg0, 0xabcd0000)
		}
	}

	m000(f000)

	Return(POUT)
}

/*
 * Add (Field, .......)
 *
 * success
 */
Method(mf20,, Serialized)
{
	Name(ts, "mf20")
	OperationRegion(r000, SystemMemory, 0x100, 0x100)
	Field(r000, ByteAcc, NoLock, Preserve) {f000,32}

	Store(0xabcd0000, f000)

	Store(Add(f000, 0x12), Local3)

	Store(Add(f000, 0x12), Local0)
	if (LNotEqual(Local0, 0xabcd0012)) {
		err(ts, z161, __LINE__, 0, 0, Local0, 0xabcd0012)
	}

	Return(POUT)
}

/*
 * Add (Field, .......)
 *
 * success
 */
Method(mf21,, Serialized)
{
	Name(ts, "mf21")
	OperationRegion(r000, SystemMemory, 0x100, 0x100)
	Field(r000, ByteAcc, NoLock, Preserve) {f000,32}

	Store(0xabcd0000, f000)

	Method(m000, 1)
	{
		Store(Add(arg0, 0x12), Local0)
		Return (Local0)
	}

	m000(f000)

	Store(m000(f000), Local0)
	if (LNotEqual(Local0, 0xabcd0012)) {
		err(ts, z161, __LINE__, 0, 0, Local0, 0xabcd0012)
	}

	Return(POUT)
}

/*
 * LNotEqual (Index Field, ....)
 *
 * success
 */
Method(mf22,, Serialized)
{
	Name(ts, "mf22")
	OperationRegion(r003, SystemMemory, 0x180, 0x080)
	Field(r003, ByteAcc, NoLock, Preserve) {f004,32, f005,32}
	IndexField(f004, f005, ByteAcc, NoLock, Preserve) {if02,32}

	Store(0xabcd0000, if02)

	Method(m000, 1)
	{
		if (LNotEqual(arg0, 0xabababab)) {
			err(ts, z161, __LINE__, 0, 0, arg0, 0xabababab)
		}
	}

	m000(if02)

	Return(POUT)
}

/*
 * Two the same simultaneously (Index Field, ....)
 *
 * success
 */
Method(mf23,, Serialized)
{
	Name(ts, "mf23")
	OperationRegion(r003, SystemMemory, 0x180, 0x080)
	Field(r003, ByteAcc, NoLock, Preserve) {f004,32, f005,32}
	IndexField(f004, f005, ByteAcc, NoLock, Preserve) {if02,32}

	Store(0xabcd0000, if02)

	Method(m000, 2)
	{
		if (LNotEqual(arg0, 0xabababab)) {
			err(ts, z161, __LINE__, 0, 0, arg0, 0xabababab)
		}
		if (LNotEqual(arg1, 0xabababab)) {
			err(ts, z161, __LINE__, 0, 0, arg1, 0xabababab)
		}
	}

	m000(if02, if02)

	Return(POUT)
}

/*
 * Two the same simultaneously (Index Field, ....)
 *
 * success
 */
Method(mf24,, Serialized)
{
	Name(ts, "mf24")
	OperationRegion(r003, SystemMemory, 0x180, 0x080)
	Field(r003, ByteAcc, NoLock, Preserve) {f004,32, f005,32}
	IndexField(f004, f005, ByteAcc, NoLock, Preserve) {if02,32}

	Store(0xabcd0000, if02)

	Method(m001, 1)
	{
		if (LNotEqual(arg0, 0xabababab)) {
			err(ts, z161, __LINE__, 0, 0, arg0, 0xabababab)
		}
		Return (arg0)
	}
	Method(m002, 2)
	{
		if (LNotEqual(arg0, 0xabababab)) {
			err(ts, z161, __LINE__, 0, 0, arg0, 0xabababab)
		}
		if (LNotEqual(arg1, 0xabababab)) {
			err(ts, z161, __LINE__, 0, 0, arg1, 0xabababab)
		}
		Return (arg1)
	}

	Store(m001(if02), Local0)
	Store(m002(if02, if02), Local0)

	Return(POUT)
}

/*
 * Store (Device, Local)
 *
 * succeed
 */
Method(mf25,, Serialized)
{
/*
// Removed 09/2015. iASL now disallows these stores
	Name(ts, "mf25")
	Device(d000) { Name(id00, 0xabcd0005) }

	Store(d000, Local1)

	Store(ObjectType(Local1), Local0)
	if (LNotEqual(Local0, c00e)) {
		err(ts, z161, __LINE__, 0, 0, Local0, c00e)
	}
*/
	Return(POUT)
}

/*
 * Store (Event, Local)
 *
 * success
 */
Method(mf27,, Serialized)
{
/*
// Removed 09/2015. iASL now disallows these stores
	Name(ts, "mf27")
	Event(e000)

	Store(e000, Local1)

	Store(ObjectType(Local1), Local0)
	if (LNotEqual(Local0, c00f)) {
		err(ts, z161, __LINE__, 0, 0, Local0, c00f)
	}
*/
	Return(POUT)
}

/*
 * Store (Mutex, Local)
 *
 * success
 */
Method(mf28,, Serialized)
{
/*
// Removed 09/2015. iASL now disallows these stores

	Name(ts, "mf28")
	Mutex(mx00, 0)

	Store(mx00, Local1)

	Store(ObjectType(Local1), Local0)
	if (LNotEqual(Local0, c011)) {
		err(ts, z161, __LINE__, 0, 0, Local0, c011)
	}
*/
	Return(POUT)
}

/*
 * Store (Event, Local)
 *
 * success
 */
Method(mf29, 1, Serialized)
{
/*
// Removed 09/2015. iASL now disallows these stores

	Name(ts, "mf29")
	Event(e000)

	Store(e000, arg0)

	Store(ObjectType(arg0), Local0)
	if (LNotEqual(Local0, c00f)) {
		err(ts, z161, __LINE__, 0, 0, Local0, c00f)
	}
*/
	Return(POUT)
}

/*
 * Store (Mutex, Local)
 *
 * success
 */
Method(mf2a, 1, Serialized)
{
/*
// Removed 09/2015. iASL now disallows these stores

	Name(ts, "mf2a")
	Mutex(mx00, 0)

	Store(mx00, arg0)

	Store(ObjectType(arg0), Local0)
	if (LNotEqual(Local0, c011)) {
		err(ts, z161, __LINE__, 0, 0, Local0, c011)
	}
*/
	Return(POUT)
}

/*
 * Store (Device, Local)
 * Store (another type object, into the same Local)
 *
 * fail
 */
Method(mf2b,, Serialized)
{
/*
// Removed 09/2015. iASL now disallows these stores

	Name(ts, "mf2b")
	Device(d000) { Name(id00, 0xabcd0005) }

	Store(d000, Local1)
	Store(0, Local1)

	if (chk0) {
		Store(d000, Local1)
		Store(ObjectType(Local1), Local0)
		if (LNotEqual(Local0, c00e)) {
			err(ts, z161, __LINE__, 0, 0, Local0, c00e)
		}
	}
*/
	Return(POUT)
}

/*
 * Store (Device, Arg)
 * Store (another type object, into the same Arg)
 *
 * fail
 */
Method(mf2c, 1, Serialized)
{
/*
// Removed 09/2015. iASL now disallows these stores

	Name(ts, "mf2c")
	Device(d000) { Name(id00, 0xabcd0005) }

	Store(d000, arg0)
	Store(0, arg0)

	if (chk0) {
		Store(d000, arg0)
		Store(ObjectType(arg0), Local0)
		if (LNotEqual(Local0, c00e)) {
			err(ts, z161, __LINE__, 0, 0, Local0, c00e)
		}
	}
*/
	Return(POUT)
}


Method(msf0)
{
	SRMT("mf00")
	if (chk0) {
		mf00()
	} else {
		BLCK()
	}
	SRMT("mf01")
	mf01()
	SRMT("mf02")
	if (chk0) {
		mf02()
	} else {
		BLCK()
	}
	SRMT("mf03")
	mf03()
	SRMT("mf04")
	if (LAnd(chk0, y275)) {
		mf04()
	} else {
		BLCK()
	}
	SRMT("mf05")
	mf05()
	SRMT("mf06")
	mf06()
	SRMT("mf07")
	mf07()
	SRMT("mf08")
	if (chk0) {
		mf08()
	} else {
		BLCK()
	}
	SRMT("mf09")
	if (chk0) {
		mf09()
	} else {
		BLCK()
	}
	SRMT("mf0a")
	mf0a()
	SRMT("mf0b")
	mf0b()
	SRMT("mf0c")
	mf0c()
	SRMT("mf0d")
	if (chk0) {
		mf0d()
	} else {
		BLCK()
	}
	SRMT("mf0e")
	if (chk0) {
		mf0e()
	} else {
		BLCK()
	}
	SRMT("mf0f")
	if (chk0) {
		mf0f()
	} else {
		BLCK()
	}
	SRMT("mf10")
	if (chk0) {
		mf10()
	} else {
		BLCK()
	}
	SRMT("mf11")
	if (chk0) {
		mf11()
	} else {
		BLCK()
	}
	SRMT("mf12")
	if (chk0) {
		mf12()
	} else {
		BLCK()
	}
	SRMT("mf13")
	if (chk0) {
		mf13()
	} else {
		BLCK()
	}
	SRMT("mf14")
	if (chk0) {
		mf14()
	} else {
		BLCK()
	}
	SRMT("mf15")
	if (chk0) {
		mf15()
	} else {
		BLCK()
	}
	SRMT("mf16")
	mf16()
	SRMT("mf17")
	mf17()
	SRMT("mf18")
	if (chk0) {
		mf18()
	} else {
		BLCK()
	}
	SRMT("mf19")
	if (chk0) {
		mf19()
	} else {
		BLCK()
	}
	SRMT("mf1a")
	if (chk0) {
		mf1a()
	} else {
		BLCK()
	}
	SRMT("mf1b")
	if (chk0) {
		mf1b()
	} else {
		BLCK()
	}
	SRMT("mf1c")
	if (chk0) {
		mf1c()
	} else {
		BLCK()
	}
	SRMT("mf1d")
	mf1d()
	SRMT("mf1e")
	mf1e()
	SRMT("mf1f")
	mf1f()
	SRMT("mf20")
	mf20()
	SRMT("mf21")
	mf21()
	SRMT("mf22")
	mf22()
	SRMT("mf23")
	mf23()
	SRMT("mf24")
	mf24()
	SRMT("mf25")
	if (SLC0) {
		mf25()
	} else {
		BLCK()
	}
	SRMT("mf26")
	if (LAnd(SLC0, chk0)) {
		mf26()
	} else {
		BLCK()
	}
	SRMT("mf27")
	if (SLC0) {
		mf27()
	} else {
		BLCK()
	}
	SRMT("mf28")
	if (SLC0) {
		mf28()
	} else {
		BLCK()
	}
	SRMT("mf29")
	if (SLC0) {
		mf29(0)
	} else {
		BLCK()
	}
	SRMT("mf2a")
	if (SLC0) {
		mf2a(0)
	} else {
		BLCK()
	}
	SRMT("mf2b")
	if (LAnd(SLC0, chk0)) {
		mf2b()
	} else {
		BLCK()
	}
	SRMT("mf2c")
	if (LAnd(SLC0, chk0)) {
		mf2c(0)
	} else {
		BLCK()
	}
}
