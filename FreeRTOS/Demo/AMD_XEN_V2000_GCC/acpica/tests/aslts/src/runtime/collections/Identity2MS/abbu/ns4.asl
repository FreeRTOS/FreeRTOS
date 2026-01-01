/*
 * Tests originated from namespace/ns4
 */

/*
 * Calls to methods instead of Add
 */

/*
in progress
// !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! z100 ????????????????????????????
// ??????????????????????????????????????????????????
*/
Name(z100, 100)

Method(m401, 1, Serialized)
{
	Name(ts, "m401")
	Name(i000, 0x00000001)
	Name(i001, 0)
	Name(p000, Package() {1,2,3,4})

	CH03(ts, z100, 0x000, __LINE__, 0)

	Store(arg0, i001)

	Method(MAdd, 2)
	{
		Add(arg0, arg1, Local0)
		Return (Local0)
	}

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
								/*
								 * Because of the stack overflow issues on MS
								 * the number of method calls eliminated.
								 */
								Return (0)
							}
							Store(0x07000000, i000)
							Return (MAdd(i000, m007()))
						}
						Store(0x00600000, i000)
						Return (MAdd(i000, m006()))
					}
					Store(0x00050000, i000)
					Return (MAdd(i000, m005()))
				}
				Store(0x00004000, i000)
				Return (MAdd(i000, m004()))
			}
			Store(0x00000300, i000)
			Return (MAdd(i000, m003()))
		}
		Store(0x00000020, i000)
		Return (MAdd(i000, m002()))
	}
	Store(MAdd(i000, m001()), Local0)

	if (LNotEqual(Local0, 0x07654321)) {
		err(ts, z100, __LINE__, 0, 0, Local0, 0x07654321)
	}

	if (LNotEqual(i000, 0x07000000)) {
		err(ts, z100, __LINE__, 0, 0, i000, 0x07000000)
	}

	CH03(ts, z100, 0x003, __LINE__, 0)
}

Method(n004)
{
	SRMT("m401-0")
	m401(0)
}
