/*
 * Source file ns_0000.asl
 *
 * The tests differ those from ns_0000.asl by that the objects are
 * passed to methods as argument (Arg) but not directly by name.
 */

Name(z165, 165)

/*
 * Named Integer i000
 */

/*
 * Simple, 3-level
 */
Method(in20, 1)
{
	Name(ts, "in20")
	Name(i000, 0x00000001)
	Name(p000, Package() {1,2,3,4})

	Name(i001, 0)

	CH03(ts, z165, 0x000, __LINE__, 0)

	Store(arg0, i001)

	Method(m000, 1)
	{
		Method(m001, 1)
		{
			Method(m002, 1)
			{
				Method(m003, 1)
				{
					if (i001) {
						CopyObject(p000, arg0)
					}
					Return (0xabcd0000)
				}
				Return (Add(arg0, m003(arg0)))
			}
			Return (Add(arg0, m002(arg0)))
		}
		Store(Add(arg0, m001(arg0)), Local0)

		Return (Local0)
	}

	Store(m000(i000), Local0)

	if (LNotEqual(Local0, 0xabcd0003)) {
		err(ts, z165, __LINE__, 0, 0, Local0, 0xabcd0003)
	}
}

/*
 * 8-level
 * added writing into i000:
 *    Store(0x00040000, i000)
 */
Method(in21, 1)
{
	Name(ts, "in21")
	Name(i000, 0x00000001)
	Name(i001, 0)
	Name(p000, Package() {1,2,3,4})

	Store(arg0, i001)

	Method(m001, 1)
	{
		Method(m002, 1)
		{
			Method(m003, 1)
			{
				Method(m004, 1)
				{
					Method(m005, 1)
					{
						Method(m006, 1)
						{
							Method(m007, 1)
							{
								Method(m008, 1)
								{
									if (i001)
									{
										CopyObject(p000, arg0)
									}
									Return (0)
								}
								Store(0x80000000, arg0)
								Return (Add(arg0, m008(arg0)))
							}
							Store(0x07000000, arg0)
							Return (Add(arg0, m007(arg0)))
						}
						Store(0x00600000, arg0)
						Return (Add(arg0, m006(arg0)))
					}
					Store(0x00050000, arg0)
					Return (Add(arg0, m005(arg0)))
				}
				Store(0x00004000, arg0)
				Return (Add(arg0, m004(arg0)))
			}
			Store(0x00000300, arg0)
			Return (Add(arg0, m003(arg0)))
		}
		Store(0x00000020, arg0)
		Return (Add(arg0, m002(arg0)))
	}

	Store(Add(i000, m001(i000)), Local0)

	if (LNotEqual(Local0, 0x87654321)) {
		err(ts, z165, __LINE__, 0, 0, Local0, 0x87654321)
	}

	if (LNotEqual(i000, 0x00000001)) {
		err(ts, z165, __LINE__, 0, 0, i000, 0x00000001)
	}
}

/*
 * Recurcive execution of m001:
 *   Add(i000, m001(), Local0)
 */
Method(in22)
{
	Name(ts, "in22")
	Name(i000, 0x00100000)
	Name(i001, 0)

	Method(m000, 1)
	{
		Method(m001, 1)
		{
			/*
			 * Because of the stack overflow issues on MS the number
			 * of repetitions was changed from 100 to 9 here.
			 */
			if (LLess(i001, 9)) {
				Increment(arg0)
				Increment(i001)
				Add(arg0, m001(arg0), Local0)
				Return (Local0)
			}
			Return (0)
		}
		Store(Add(arg0, m001(arg0)), Local0)
		Return (Local0)
	}

	Store(Add(i000, m000(i000)), Local0)

	if (LNotEqual(Local0, 0x00b0002d)) {
		err(ts, z165, __LINE__, 0, 0, Local0, 0x00b0002d)
	}

	if (LNotEqual(i000, 0x00100000)) {
		err(ts, z165, __LINE__, 0, 0, i000, 0x00100000)
	}
}

/*
 * Arg instead of i000 (in in01)
 */
Method(in23, 2)
{
	Name(ts, "in23")
	Name(i001, 0)
	Name(p000, Package() {1,2,3,4})

	Store(arg0, i001)

	Store(0x00000001, arg1)

	Method(m001, 1)
	{
		Method(m002, 1)
		{
			Method(m003, 1)
			{
				Method(m004, 1)
				{
					Method(m005, 1)
					{
						Method(m006, 1)
						{
							Method(m007, 1)
							{
								Method(m008, 1)
								{
									if (i001)
									{
										CopyObject(p000, arg0)
									}
									Return (0)
								}
								Store(0x80000000, arg0)
								Return (Add(arg0, m008(8)))
							}
							Store(0x07000000, arg0)
							Return (Add(arg0, m007(7)))
						}
						Store(0x00600000, arg0)
						Return (Add(arg0, m006(6)))
					}
					Store(0x00050000, arg0)
					Return (Add(arg0, m005(5)))
				}
				Store(0x00004000, arg0)
				Return (Add(arg0, m004(4)))
			}
			Store(0x00000300, arg0)
			Return (Add(arg0, m003(3)))
		}
		Store(0x00000020, arg0)
		Return (Add(arg0, m002(2)))
	}
	Store(Add(arg1, m001(1)), Local0)

	if (LNotEqual(Local0, 0x87654321)) {
		err(ts, z165, __LINE__, 0, 0, Local0, 0x87654321)
	}

	if (LNotEqual(arg1, 1)) {
		err(ts, z165, __LINE__, 0, 0, arg1, 1)
	}

	CH03(ts, z165, 0x011, __LINE__, 0)
}

Method(ini2)
{
	SRMT("in20-0")
	in20(0)
	SRMT("in21-0")
	in21(0)
	SRMT("in22")
	in22()
	SRMT("in23-0")
	in23(0, 0)
}
