/*
 * Access to elements of combined objects (Device)
 */
Name(z167, 167)

/*
 * Named Integer i000
 */

/*
 * Simple, 3-level
 */

Method(dv00)
{
	Name(ts, "dv00")
	Device(d000) {
		Name(i000, 0x00000001)
	}

	Method(m001, 1)
	{
		Method(m002, 1)
		{
			Method(m003, 1)
			{
				Return (0xabcd0000)
			}
			Return (Add(arg0, m003(arg0)))
		}
		Return (Add(arg0, m002(arg0)))
	}
	Store(Add(d000.i000, m001(d000.i000)), Local0)
	if (LNotEqual(Local0, 0xabcd0003)) {
		err(ts, z167, __LINE__, 0, 0, Local0, 0xabcd0003)
	}
}

Method(dvf0)
{
	Name(ts, "dvf0")
	Device(d000) {
		Name(i000, 0x00000001)
	}

	Method(m001)
	{
		Method(m002)
		{
			Method(m003)
			{
				Return (0xabcd0000)
			}
			Return (Add(^^d000.i000, m003()))
		}
		Return (Add(^d000.i000, m002()))
	}

	Store(Add(d000.i000, m001()), Local0)
	if (LNotEqual(Local0, 0xabcd0003)) {
		err(ts, z163, __LINE__, 0, 0, Local0, 0xabcd0003)
	}
}

Method(dvf1)
{
	Name(ts, "dvf1")
	Device(d000) {
		Name(i000, 0x00000001)
	}

	Method(m001)
	{
		Method(m002)
		{
			Method(m003)
			{
				Return (0xabcd0000)
			}
			Return (Add(^^^dvf1.d000.i000, m003()))
		}
		Return (Add(^^dvf1.d000.i000, m002()))
	}

	Store(Add(^dvf1.d000.i000, m001()), Local0)
	if (LNotEqual(Local0, 0xabcd0003)) {
		err(ts, z163, __LINE__, 0, 0, Local0, 0xabcd0003)
	}
}

/*
 * 8-level
 * added writing into i000:
 *    Store(0x00040000, i000)
 */
Method(dv01, 1)
{
	Name(ts, "dv01")
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
		err(ts, z167, __LINE__, 0, 0, Local0, 0x87654321)
	}

	if (LNotEqual(i000, 0x80000000)) {
		err(ts, z167, __LINE__, 0, 0, i000, 0x80000000)
	}
}

/*
 * Recurcive execution of m001:
 *   Add(i000, m001(), Local0)
 */
Method(dv02)
{
	Name(ts, "dv02")
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
		err(ts, z167, __LINE__, 0, 0, Local0, 0x00c00042)
	}

	if (LNotEqual(i000, 0x0010000b)) {
		err(ts, z167, __LINE__, 0, 0, i000, 0x0010000b)
	}
}

/*
 * Local instead of i000 (in in01)
 */
Method(dv03, 1)
{
	Name(ts, "dv03")
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
		err(ts, z167, __LINE__, 0, 0, Local0, 0x87654321)
	}

	if (LNotEqual(Local7, 1)) {
		err(ts, z167, __LINE__, 0, 0, Local7, 1)
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
 * dv01 +:
 *    m00X are passed with i000
 *    argX inside m00X is rewritten
 */
Method(dv04)
{
	Name(ts, "dv04")
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
					err(ts, z167, __LINE__, 0, 0, arg0, 0x00000300)
				}
				if (LNotEqual(arg1, 0x10000001)) {
					err(ts, z167, __LINE__, 0, 0, arg1, 0x10000001)
				}
				Store(0x00004000, i000)
				Store(0x10000003, arg0)
				Return (Add(i000, m004(i000, arg0)))
			}
			if (LNotEqual(arg0, 0x00000020)) {
				err(ts, z167, __LINE__, 0, 0, arg0, 0x00000020)
			}
			if (LNotEqual(i000, 0x00000020)) {
				err(ts, z167, __LINE__, 0, 0, i000, 0x00000020)
			}
			Store(0x10000002, arg0)
			if (LNotEqual(i000, 0x00000020)) {
				err(ts, z167, __LINE__, 0, 0, i000, 0x00000020)
			}
			if (LNotEqual(arg0, 0x10000002)) {
				err(ts, z167, __LINE__, 0, 0, arg0, 0x10000002)
			}
			Store(0x00000300, i000)
			if (LNotEqual(i000, 0x00000300)) {
				err(ts, z167, __LINE__, 0, 0, i000, 0x00000300)
			}
			if (LNotEqual(arg0, 0x10000002)) {
				err(ts, z167, __LINE__, 0, 0, arg0, 0x10000002)
			}
			if (LNotEqual(arg1, 0x10000001)) {
				err(ts, z167, __LINE__, 0, 0, arg1, 0x10000001)
			}
			Store(0x10000002, arg0)
			Store(0x00000300, i000)
			Return (Add(i000, m003(i000, arg1)))
		}
		if (LNotEqual(arg0, 0x00000001)) {
			err(ts, z167, __LINE__, 0, 0, arg0, 0x00000001)
		}
		if (LNotEqual(i000, 0x00000001)) {
			err(ts, z167, __LINE__, 0, 0, i000, 0x00000001)
		}
		Store(0x10000001, arg0)
		if (LNotEqual(i000, 0x00000001)) {
			err(ts, z167, __LINE__, 0, 0, i000, 0x00000001)
		}
		if (LNotEqual(arg0, 0x10000001)) {
			err(ts, z167, __LINE__, 0, 0, arg0, 0x10000001)
		}
		Store(0x00000020, i000)
		if (LNotEqual(i000, 0x00000020)) {
			err(ts, z167, __LINE__, 0, 0, i000, 0x00000020)
		}
		if (LNotEqual(arg0, 0x10000001)) {
			err(ts, z167, __LINE__, 0, 0, arg0, 0x10000001)
		}
		if (LNotEqual(arg1, 0x10000000)) {
			err(ts, z167, __LINE__, 0, 0, arg1, 0x10000000)
		}
		Store(0x10000001, arg0)
		Store(0x00000020, i000)
		Return (Add(i000, m002(i000, arg0)))
	}
	Store(Add(i000, m001(i000, 0x10000000)), Local0)

	if (LNotEqual(Local0, 0x87654321)) {
		err(ts, z167, __LINE__, 0, 0, Local0, 0x87654321)
	}

	if (LNotEqual(i000, 0x80000000)) {
		err(ts, z167, __LINE__, 0, 0, i000, 0x80000000)
	}
}

/*
 * Note: now the checkings are so that dv05 succeeds on MS.
 */
Method(dv05)
{
	Name(ts, "dv05")

	Name(i000, 0xabcd0000)
	Name(s000, "qwrtyu0003")
	Name(b000, Buffer() {0xb0,0xb1,0xb2,0xb3,0xb4})
	Name(p000, Package() {0xabcd0001, 0xabcd0002, 0xabcd0003})
	Event(e000)
	Mutex(mx00, 0)
	Method(mmm0) {
		Name(im00, 0xabcd0004)
		Name(sm00, "qwertyui")
		// Return ( "qwertyui" )
	}
	Method(mmm1) {
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
			err(ts, z167, __LINE__, 0, 0, Local0, arg1)
		}
		Return (5)
	}

	CH03(ts, z167, 0x000, __LINE__, 0)

	Store(Add(DerefOf(Index(p000, 0)), m001(i000, c009)), Local0)
	if (LNotEqual(Local0, 0xabcd0006)) {
		err(ts, z167, __LINE__, 0, 0, Local0, 0xabcd0006)
	}
	Store(Add(DerefOf(Index(p000, 0)), m001(s000, c00a)), Local0)
	if (LNotEqual(Local0, 0xabcd0006)) {
		err(ts, z167, __LINE__, 0, 0, Local0, 0xabcd0006)
	}
	Store(Add(DerefOf(Index(p000, 0)), m001(b000, c00b)), Local0)
	if (LNotEqual(Local0, 0xabcd0006)) {
		err(ts, z167, __LINE__, 0, 0, Local0, 0xabcd0006)
	}
	Store(Add(DerefOf(Index(p000, 0)), m001(p000, c00c)), Local0)
	if (LNotEqual(Local0, 0xabcd0006)) {
		err(ts, z167, __LINE__, 0, 0, Local0, 0xabcd0006)
	}
	Store(Add(DerefOf(Index(p000, 0)), m001(e000, c00f)), Local0)
	if (LNotEqual(Local0, 0xabcd0006)) {
		err(ts, z167, __LINE__, 0, 0, Local0, 0xabcd0006)
	}
	Store(Add(DerefOf(Index(p000, 0)), m001(mx00, c011)), Local0)
	if (LNotEqual(Local0, 0xabcd0006)) {
		err(ts, z167, __LINE__, 0, 0, Local0, 0xabcd0006)
	}
	Store(Add(DerefOf(Index(p000, 0)), m001(mmm0, c008)), Local0)
	if (LNotEqual(Local0, 0xabcd0006)) {
		err(ts, z167, __LINE__, 0, 0, Local0, 0xabcd0006)
	}
	Store(Add(DerefOf(Index(p000, 0)), m001(mmm1, c00a)), Local0)
	if (LNotEqual(Local0, 0xabcd0006)) {
		err(ts, z167, __LINE__, 0, 0, Local0, 0xabcd0006)
	}
	Store(Add(DerefOf(Index(p000, 0)), m001(d000, c00e)), Local0)
	if (LNotEqual(Local0, 0xabcd0006)) {
		err(ts, z167, __LINE__, 0, 0, Local0, 0xabcd0006)
	}
	Store(Add(DerefOf(Index(p000, 0)), m001(tz00, c015)), Local0)
	if (LNotEqual(Local0, 0xabcd0006)) {
		err(ts, z167, __LINE__, 0, 0, Local0, 0xabcd0006)
	}
	Store(Add(DerefOf(Index(p000, 0)), m001(pr00, c014)), Local0)
	if (LNotEqual(Local0, 0xabcd0006)) {
		err(ts, z167, __LINE__, 0, 0, Local0, 0xabcd0006)
	}
	Store(Add(DerefOf(Index(p000, 0)), m001(pw00, c013)), Local0)
	if (LNotEqual(Local0, 0xabcd0006)) {
		err(ts, z167, __LINE__, 0, 0, Local0, 0xabcd0006)
	}
	Store(Add(DerefOf(Index(p000, 0)), m001(r000, c012)), Local0)
	if (LNotEqual(Local0, 0xabcd0006)) {
		err(ts, z167, __LINE__, 0, 0, Local0, 0xabcd0006)
	}
	Store(Add(DerefOf(Index(p000, 0)), m001(bf00, c00b)), Local0)
	if (LNotEqual(Local0, 0xabcd0006)) {
		err(ts, z167, __LINE__, 0, 0, Local0, 0xabcd0006)
	}
	Store(Add(DerefOf(Index(p000, 0)), m001(f000, c009)), Local0)
	if (LNotEqual(Local0, 0xabcd0006)) {
		err(ts, z167, __LINE__, 0, 0, Local0, 0xabcd0006)
	}
	Store(Add(DerefOf(Index(p000, 0)), m001(bnk0, c009)), Local0)
	if (LNotEqual(Local0, 0xabcd0006)) {
		err(ts, z167, __LINE__, 0, 0, Local0, 0xabcd0006)
	}
	Store(Add(DerefOf(Index(p000, 0)), m001(if00, c009)), Local0)
	if (LNotEqual(Local0, 0xabcd0006)) {
		err(ts, z167, __LINE__, 0, 0, Local0, 0xabcd0006)
	}

	CH03(ts, z167, 0x000, __LINE__, 0)
}

Method(dv06)
{
	Name(ts, "dv06")
	Name(i000, 0xabcd0000)

	Store(ObjectType(i000), Local0)
	if (LNotEqual(Local0, c009)) {
		err(ts, z167, __LINE__, 0, 0, Local0, c009)
	}
}

Method(dev0)
{
	SRMT("dv00")
	dv00()

	SRMT("dvf0")
	dvf0()
	SRMT("dvf1")
	dvf1()

	SRMT("dv01-0")
	dv01(0)
	SRMT("dv02")
	dv02()
	SRMT("dv03-0")
	dv03(0)
	SRMT("dv04")
	dv04()
	SRMT("dv05")
	if (LAnd(fix1, chk3)) {
		/*
		 * It breaks MS while re-booting,
		 * for ACPICA it causes exception
		 * and breaks path.
		 */
		dv05()
	} else {
		BLCK()
	}
	SRMT("dv06")
	dv06()
}
