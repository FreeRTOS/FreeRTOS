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
 * Tests originated from namespace/ns0
 */

/*
 * Trying to get the chain of calls of methods such that
 * sections of operative stack corresponding to different
 * methods contain the internal object (itself, not a RefOf
 * reference to it) of the same Name Space node.
 *
 * Then force (by Store/CopyObject):
 *   1) changing the value of that internal object
 *   2) replacing the internal object itself by some another one
 *
 * Check that the changing/replacing has no effect on the
 * values evaluated on the lowest stages of calculation.
 *
 * Accessing objects by argX and directly by name too.
 */

Name(z163, 163)

/*
 * Named Integer i000
 */

/*
 * Simple, 3-level
 */
Method(in00, 1, Serialized)
{
	Name(ts, "in00")
	Name(i000, 0x00000001)
	Name(p000, Package() {1,2,3,4})

	Name(i001, 0)

	Store(arg0, i001)

	Method(m001)
	{
		Method(m002)
		{
			Method(m003)
			{
				if (i001) {
					CopyObject(p000, i000)
				}
				Return (0xabcd0000)
			}
			Return (Add(i000, m003()))
		}
		Return (Add(i000, m002()))
	}
	Store(Add(i000, m001()), Local0)
	if (LNotEqual(Local0, 0xabcd0003)) {
		err(ts, z163, __LINE__, 0, 0, Local0, 0xabcd0003)
	}
}

/*
 * 8-level
 * added writing into i000:
 *    Store(0x00040000, i000)
 */
Method(in01, 1, Serialized)
{
	Name(ts, "in01")
	Name(i000, 0x00000001)
	Name(i001, 0)
	Name(p000, Package() {1,2,3,4})

	Store(arg0, i001)

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
									if (i001)
									{
										CopyObject(p000, i000)
									}
									Return (0)
								}
								Store(0x80000000, i000)
								Return (Add(i000, m008()))
							}
							Store(0x07000000, i000)
							Return (Add(i000, m007()))
						}
						Store(0x00600000, i000)
						Return (Add(i000, m006()))
					}
					Store(0x00050000, i000)
					Return (Add(i000, m005()))
				}
				Store(0x00004000, i000)
				Return (Add(i000, m004()))
			}
			Store(0x00000300, i000)
			Return (Add(i000, m003()))
		}
		Store(0x00000020, i000)
		Return (Add(i000, m002()))
	}
	Store(Add(i000, m001()), Local0)

	if (LNotEqual(Local0, 0x87654321)) {
		err(ts, z163, __LINE__, 0, 0, Local0, 0x87654321)
	}

	if (LNotEqual(i000, 0x80000000)) {
		err(ts, z163, __LINE__, 0, 0, i000, 0x80000000)
	}
}

/*
 * Recurcive execution of m001:
 *   Add(i000, m001(), Local0)
 */
Method(in02,, Serialized)
{
	Name(ts, "in02")
	Name(i000, 0x00100000)
	Name(i001, 0)

	Method(m001)
	{
		/*
		 * Because of the stack overflow issues on MS the number
		 * of repetitions was changed from 100 to 11 here.
		 */
		if (LLess(i001, 11)) {
			Increment(i000)
			Increment(i001)
			Add(i000, m001(), Local0)
			Return (Local0)
		}
		Return (0)
	}
	Store(Add(i000, m001()), Local0)

	if (LNotEqual(Local0, 0x00c00042)) {
		err(ts, z163, __LINE__, 0, 0, Local0, 0x00c00042)
	}

	if (LNotEqual(i000, 0x0010000b)) {
		err(ts, z163, __LINE__, 0, 0, i000, 0x0010000b)
	}
}

/*
 * Local instead of i000 (in in01)
 */
Method(in03, 1, Serialized)
{
	Name(ts, "in03")
	Name(i001, 0)
	Name(p000, Package() {1,2,3,4})

	Store(arg0, i001)

	Store(0x00000001, Local7)

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
									if (i001)
									{
										CopyObject(p000, Local7)
									}
									Return (0)
								}
								Store(0x80000000, Local7)
								Return (Add(Local7, m008()))
							}
							Store(0x07000000, Local7)
							Return (Add(Local7, m007()))
						}
						Store(0x00600000, Local7)
						Return (Add(Local7, m006()))
					}
					Store(0x00050000, Local7)
					Return (Add(Local7, m005()))
				}
				Store(0x00004000, Local7)
				Return (Add(Local7, m004()))
			}
			Store(0x00000300, Local7)
			Return (Add(Local7, m003()))
		}
		Store(0x00000020, Local7)
		Return (Add(Local7, m002()))
	}
	Store(Add(Local7, m001()), Local0)

	if (LNotEqual(Local0, 0x87654321)) {
		err(ts, z163, __LINE__, 0, 0, Local0, 0x87654321)
	}

	if (LNotEqual(Local7, 1)) {
		err(ts, z163, __LINE__, 0, 0, Local7, 1)
	}
}

/*
 * Arg instead of i000 (in in01)
 *
 * see ns_0100.asl
 */

/*
 * 8-level
 * added writing into i000:
 *    Store(0x00040000, i000)
 *
 * in01 +:
 *    m00X are passed with i000
 *    argX inside m00X is rewritten
 */
Method(in04,, Serialized)
{
	Name(ts, "in04")
	Name(i000, 0x00000001)
	Name(i001, 0)
	Name(p000, Package() {1,2,3,4})

	Method(m001, 2)
	{
		Method(m002, 2)
		{
			Method(m003, 2)
			{
				Method(m004, 2)
				{
					Method(m005, 2)
					{
						Method(m006, 2)
						{
							Method(m007, 2)
							{
								/*
								 * ====================== >>>>>>>>
								 * Sometimes, after I added a big group of
								 * 'If' operators, this fragment of code causes
								 * break of execution on MS. But, namely --
								 * sometimes! To investigate the reason I
								 * commented part by part of it to find
								 * workable code, then un-commented it
								 * part by part too.
								 * It entire initial code
								 * started working on MS again!
								 */
								/*
								Method(m008, 2)
								{
									if (i001)
									{
										CopyObject(p000, i000)
									}
									Store(0x10000008, arg0)
									Return (0)
								}
								Store(0x80000000, i000)
								Store(0x10000007, arg0)
								Return (Add(i000, m008(i000, arg0)))
								 */
								/*
								 * ====================== <<<<<<<<
								 */

								Store(0x80000000, i000)
								Store(0x10000007, arg0)
								Add(i000, 0, Local0)

								Return (Local0)
							}
							Store(0x07000000, i000)
							Store(0x10000006, arg0)
							Return (Add(i000, m007(i000, arg0)))
						}
						Store(0x00600000, i000)
						Store(0x10000005, arg0)
						Return (Add(i000, m006(i000, arg0)))
					}
					Store(0x00050000, i000)
					Store(0x10000004, arg0)
					Return (Add(i000, m005(i000, arg0)))
				}
				if (LNotEqual(arg0, 0x00000300)) {
					err(ts, z163, __LINE__, 0, 0, arg0, 0x00000300)
				}
				if (LNotEqual(arg1, 0x10000001)) {
					err(ts, z163, __LINE__, 0, 0, arg1, 0x10000001)
				}
				Store(0x00004000, i000)
				Store(0x10000003, arg0)
				Return (Add(i000, m004(i000, arg0)))
			}
			if (LNotEqual(arg0, 0x00000020)) {
				err(ts, z163, __LINE__, 0, 0, arg0, 0x00000020)
			}
			if (LNotEqual(i000, 0x00000020)) {
				err(ts, z163, __LINE__, 0, 0, i000, 0x00000020)
			}
			Store(0x10000002, arg0)
			if (LNotEqual(i000, 0x00000020)) {
				err(ts, z163, __LINE__, 0, 0, i000, 0x00000020)
			}
			if (LNotEqual(arg0, 0x10000002)) {
				err(ts, z163, __LINE__, 0, 0, arg0, 0x10000002)
			}
			Store(0x00000300, i000)
			if (LNotEqual(i000, 0x00000300)) {
				err(ts, z163, __LINE__, 0, 0, i000, 0x00000300)
			}
			if (LNotEqual(arg0, 0x10000002)) {
				err(ts, z163, __LINE__, 0, 0, arg0, 0x10000002)
			}
			if (LNotEqual(arg1, 0x10000001)) {
				err(ts, z163, __LINE__, 0, 0, arg1, 0x10000001)
			}
			Store(0x10000002, arg0)
			Store(0x00000300, i000)
			Return (Add(i000, m003(i000, arg1)))
		}
		if (LNotEqual(arg0, 0x00000001)) {
			err(ts, z163, __LINE__, 0, 0, arg0, 0x00000001)
		}
		if (LNotEqual(i000, 0x00000001)) {
			err(ts, z163, __LINE__, 0, 0, i000, 0x00000001)
		}
		Store(0x10000001, arg0)
		if (LNotEqual(i000, 0x00000001)) {
			err(ts, z163, __LINE__, 0, 0, i000, 0x00000001)
		}
		if (LNotEqual(arg0, 0x10000001)) {
			err(ts, z163, __LINE__, 0, 0, arg0, 0x10000001)
		}
		Store(0x00000020, i000)
		if (LNotEqual(i000, 0x00000020)) {
			err(ts, z163, __LINE__, 0, 0, i000, 0x00000020)
		}
		if (LNotEqual(arg0, 0x10000001)) {
			err(ts, z163, __LINE__, 0, 0, arg0, 0x10000001)
		}
		if (LNotEqual(arg1, 0x10000000)) {
			err(ts, z163, __LINE__, 0, 0, arg1, 0x10000000)
		}
		Store(0x10000001, arg0)
		Store(0x00000020, i000)
		Return (Add(i000, m002(i000, arg0)))
	}
	Store(Add(i000, m001(i000, 0x10000000)), Local0)

	if (LNotEqual(Local0, 0x87654321)) {
		err(ts, z163, __LINE__, 0, 0, Local0, 0x87654321)
	}

	if (LNotEqual(i000, 0x80000000)) {
		err(ts, z163, __LINE__, 0, 0, i000, 0x80000000)
	}
}

/*
 * Note: now the checkings are so that in05 succeeds on MS.
 */
Method(in05,, Serialized)
{
	Name(ts, "in05")

	Name(i000, 0xabcd0000)
	Name(s000, "qwrtyu0003")
	Name(b000, Buffer() {0xb0,0xb1,0xb2,0xb3,0xb4})
	Name(p000, Package() {0xabcd0001, 0xabcd0002, 0xabcd0003})
	Event(e000)
	Mutex(mx00, 0)
	Method(mmm0,, Serialized) {
		Name(im00, 0xabcd0004)
		Name(sm00, "qwertyui")
		// Return ( "qwertyui" )
	}
	Method(mmm1,, Serialized) {
		Name(im00, 0xabcd0004)
		Name(sm00, "qwertyui")
		// Return ( 0xabcd0004 )
		Return ( "qwertyui" )
	}
	Device(d000) { Name(id00, 0xabcd0005) }
	ThermalZone(tz00) { Name(itz0, 0xabcd0006) }
	Processor(pr00, 0, 0xFFFFFFFF, 0) { Name(ipr0, 0xabcd0007) }
	PowerResource(pw00, 1, 0) { Name(ipw0, 0xabcd0008) }
	OperationRegion(r000, SystemMemory, 0x100, 0x100)

	Name(b001, Buffer() {0xa0,0xa1,0xa2,0xa3,0xa4})
	CreateField(b001, 0, 8, bf00)

	OperationRegion(r001, SystemMemory, 0x100, 0x100)
	Field(r001, ByteAcc, NoLock, Preserve) {f000,32, f001,32, f002,32, f003,32}
	BankField(r001, f001, 0, ByteAcc, NoLock, Preserve) {bnk0,32}
	IndexField(f002, f003, ByteAcc, NoLock, Preserve) {if00,32, if01,32}

	Method(m001, 2)
	{
		Store(ObjectType(arg0), Local0)
		if (LNotEqual(Local0, arg1)) {
			err(ts, z163, __LINE__, 0, 0, Local0, arg1)
		}
		Return (5)
	}

	CH03(ts, z163, 0x000, __LINE__, 0)

	Store(Add(DerefOf(Index(p000, 0)), m001(i000, c009)), Local0)
	if (LNotEqual(Local0, 0xabcd0006)) {
		err(ts, z163, __LINE__, 0, 0, Local0, 0xabcd0006)
	}
	Store(Add(DerefOf(Index(p000, 0)), m001(s000, c00a)), Local0)
	if (LNotEqual(Local0, 0xabcd0006)) {
		err(ts, z163, __LINE__, 0, 0, Local0, 0xabcd0006)
	}
	Store(Add(DerefOf(Index(p000, 0)), m001(b000, c00b)), Local0)
	if (LNotEqual(Local0, 0xabcd0006)) {
		err(ts, z163, __LINE__, 0, 0, Local0, 0xabcd0006)
	}
	Store(Add(DerefOf(Index(p000, 0)), m001(p000, c00c)), Local0)
	if (LNotEqual(Local0, 0xabcd0006)) {
		err(ts, z163, __LINE__, 0, 0, Local0, 0xabcd0006)
	}
	Store(Add(DerefOf(Index(p000, 0)), m001(e000, c00f)), Local0)
	if (LNotEqual(Local0, 0xabcd0006)) {
		err(ts, z163, __LINE__, 0, 0, Local0, 0xabcd0006)
	}
	Store(Add(DerefOf(Index(p000, 0)), m001(mx00, c011)), Local0)
	if (LNotEqual(Local0, 0xabcd0006)) {
		err(ts, z163, __LINE__, 0, 0, Local0, 0xabcd0006)
	}
	Store(Add(DerefOf(Index(p000, 0)), m001(mmm0, c008)), Local0)
	if (LNotEqual(Local0, 0xabcd0006)) {
		err(ts, z163, __LINE__, 0, 0, Local0, 0xabcd0006)
	}
	Store(Add(DerefOf(Index(p000, 0)), m001(mmm1, c00a)), Local0)
	if (LNotEqual(Local0, 0xabcd0006)) {
		err(ts, z163, __LINE__, 0, 0, Local0, 0xabcd0006)
	}
	Store(Add(DerefOf(Index(p000, 0)), m001(d000, c00e)), Local0)
	if (LNotEqual(Local0, 0xabcd0006)) {
		err(ts, z163, __LINE__, 0, 0, Local0, 0xabcd0006)
	}
	Store(Add(DerefOf(Index(p000, 0)), m001(tz00, c015)), Local0)
	if (LNotEqual(Local0, 0xabcd0006)) {
		err(ts, z163, __LINE__, 0, 0, Local0, 0xabcd0006)
	}
	Store(Add(DerefOf(Index(p000, 0)), m001(pr00, c014)), Local0)
	if (LNotEqual(Local0, 0xabcd0006)) {
		err(ts, z163, __LINE__, 0, 0, Local0, 0xabcd0006)
	}
	Store(Add(DerefOf(Index(p000, 0)), m001(pw00, c013)), Local0)
	if (LNotEqual(Local0, 0xabcd0006)) {
		err(ts, z163, __LINE__, 0, 0, Local0, 0xabcd0006)
	}
	Store(Add(DerefOf(Index(p000, 0)), m001(r000, c012)), Local0)
	if (LNotEqual(Local0, 0xabcd0006)) {
		err(ts, z163, __LINE__, 0, 0, Local0, 0xabcd0006)
	}
	Store(Add(DerefOf(Index(p000, 0)), m001(bf00, c00b)), Local0)
	if (LNotEqual(Local0, 0xabcd0006)) {
		err(ts, z163, __LINE__, 0, 0, Local0, 0xabcd0006)
	}
	Store(Add(DerefOf(Index(p000, 0)), m001(f000, c009)), Local0)
	if (LNotEqual(Local0, 0xabcd0006)) {
		err(ts, z163, __LINE__, 0, 0, Local0, 0xabcd0006)
	}
	Store(Add(DerefOf(Index(p000, 0)), m001(bnk0, c009)), Local0)
	if (LNotEqual(Local0, 0xabcd0006)) {
		err(ts, z163, __LINE__, 0, 0, Local0, 0xabcd0006)
	}
	Store(Add(DerefOf(Index(p000, 0)), m001(if00, c009)), Local0)
	if (LNotEqual(Local0, 0xabcd0006)) {
		err(ts, z163, __LINE__, 0, 0, Local0, 0xabcd0006)
	}


	Store(ObjectType(f000), Local0)
	if (LNotEqual(Local0, c00d)) {
		err(ts, z163, __LINE__, 0, 0, Local0, c00d)
	}
	Store(ObjectType(if00), Local0)
	if (LNotEqual(Local0, c00d)) {
		err(ts, z163, __LINE__, 0, 0, Local0, c00d)
	}
	Store(ObjectType(bnk0), Local0)
	if (LNotEqual(Local0, c00d)) {
		err(ts, z163, __LINE__, 0, 0, Local0, c00d)
	}
	Store(ObjectType(bf00), Local0)
	if (LNotEqual(Local0, c016)) {
		err(ts, z163, __LINE__, 0, 0, Local0, c016)
	}

	CH03(ts, z163, 0x000, __LINE__, 0)
}

Method(in06,, Serialized)
{
	Name(ts, "in06")
	Name(i000, 0xabcd0000)

	Store(ObjectType(i000), Local0)
	if (LNotEqual(Local0, c009)) {
		err(ts, z163, __LINE__, 0, 0, Local0, c009)
	}
}

Method(ini0)
{
	SRMT("in00-0")
	in00(0)
	SRMT("in01-0")
	in01(0)
	SRMT("in02")
	in02()
	SRMT("in03-0")
	in03(0)
	SRMT("in04")
	in04()
	SRMT("in05")
	if (LAnd(fix1, chk2)) {
		/*
		 * It breaks MS while re-booting,
		 * for ACPICA it causes exception
		 * and breaks path.
		 */
		in05()
	} else {
		BLCK()
	}
	SRMT("in06")
	in06()

	CH03("ini0", z163, 0x000, __LINE__, 0)
}
