in progress

do these tests - enclose in method, pass device to method and check that
really deal with objects of initial device Integer/package/buffer/string/...

/*

same as ns2 (and+ to cover all type Fields elements of Package /buffer/string)
but pass that device/power/tz/... by argument. do for all types of combined
objects: device/power/tz/...


*/
Name(z159, 159)


/*
 * Check access to elements Package/Buffer/String and Buffer Field
 * where the parent is an element of some complex object (Device).
 */

Method(m500)
{
	Name(ts, "m500")
	Device(d000)
	{
		Name(p000, Package() {0xabcd0000, 0xabcd0001, 0xabcd0002})
	}

	Method(m001, 2)
	{
		Store(0x11112222, Index(arg0, 0))
	}

	m001(d000.p000, RefOf(d000.p000))

	Store(DerefOf(Index(d000.p000, 0)), Local0)

	if (LNotEqual(Local0, 0x11112222)) {
		err(ts, z159, __LINE__, 0, 0, Local0, 0x11112222)
	}

	CH03(ts, z159, 0x100, __LINE__, 0)
}

Method(m501)
{
	Name(ts, "m501")
	Device(d000)
	{
		Name(b000, Buffer() {0x10, 0x11, 0x12})
	}
	Method(m001, 2)
	{
		Store(0x67, Index(arg0, 0))
	}

	m001(d000.b000, RefOf(d000.b000))

	Store(DerefOf(Index(d000.b000, 0)), Local0)

	if (LNotEqual(Local0, 0x67)) {
		err(ts, z159, __LINE__, 0, 0, Local0, 0x67)
	}

	CH03(ts, z159, 0x101, __LINE__, 0)
}

Method(m502)
{
	Name(ts, "m502")
	Device(d000)
	{
		Name(s000, "qqqqqqqqqqqqqq")
	}
	Method(m001, 2)
	{
		Store(0x38, Index(arg0, 0))
	}

	m001(d000.s000, RefOf(d000.s000))

	Store(DerefOf(Index(d000.s000, 0)), Local0)

	if (LNotEqual(Local0, 0x38)) {
		err(ts, z159, __LINE__, 0, 0, Local0, 0x38)
	}

	CH03(ts, z159, 0x102, __LINE__, 0)
}

/*
 * Element of Package instead of i000 (in m001)
 */
Method(m503, 1)
{
	Name(ts, "m503")
	Name(i001, 0)
	Name(p000, Package() {1,2,3,4})
	Device(d000)
	{
		Name(pp00, Package() {0x11111111, 0x00000001, 0x22223333})
	}

	CH03(ts, z159, 0x103, __LINE__, 0)

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
										Store(p000, Index(\m503.d000.pp00, 1))
									}
									Return (0)
								}
								Store(0x80000000, Index(\m503.d000.pp00, 1))
								Return (Add(DerefOf(Index(\m503.d000.pp00, 1)), m008()))
							}
							Store(0x07000000, Index(\m503.d000.pp00, 1))
							Return (Add(DerefOf(Index(\m503.d000.pp00, 1)), m007()))
						}
						Store(0x00600000, Index(\m503.d000.pp00, 1))
						Return (Add(DerefOf(Index(\m503.d000.pp00, 1)), m006()))
					}
					Store(0x00050000, Index(\m503.d000.pp00, 1))
					Return (Add(DerefOf(Index(\m503.d000.pp00, 1)), m005()))
				}
				Store(0x00004000, Index(\m503.d000.pp00, 1))
				Return (Add(DerefOf(Index(\m503.d000.pp00, 1)), m004()))
			}
			Store(0x00000300, Index(\m503.d000.pp00, 1))
			Return (Add(DerefOf(Index(\m503.d000.pp00, 1)), m003()))
		}
		Store(0x00000020, Index(^d000.pp00, 1))
		Return (Add(DerefOf(Index(^d000.pp00, 1)), m002()))
	}
	Store(Add(DerefOf(Index(d000.pp00, 1)), m001()), Local0)

	if (LNotEqual(Local0, 0x87654321)) {
		err(ts, z159, __LINE__, 0, 0, Local0, 0x87654321)
	}

	Store(DerefOf(Index(d000.pp00, 1)), Local0)

	if (LNotEqual(Local0, 0x80000000)) {
		err(ts, z159, __LINE__, 0, 0, Local0, 0x80000000)
	}

	CH03(ts, z159, 0x104, __LINE__, 0)
}

/*
 * Element of Package instead of i000 (in m002)
 */
Method(m504)
{
	Name(ts, "m504")
	Name(i001, 0)
	Device(d000)
	{
		Name(pp00, Package() {0x11111111, 0x00100000, 0x22223333})
	}

	Method(m001)
	{
		if (LLess(i001, 100)) {

			Store(DerefOf(Index(^d000.pp00, 1)), Local0)
			Increment(Local0)
			Store(Local0, Index(^d000.pp00, 1))
			Increment(i001)
			Add(DerefOf(Index(^d000.pp00, 1)), m001(), Local0)
			Return (Local0)
		}
		Return (0)
	}
	Store(Add(DerefOf(Index(d000.pp00, 1)), m001()), Local0)

	if (LNotEqual(Local0, 0x065013BA)) {
		err(ts, z159, __LINE__, 0, 0, Local0, 0x065013BA)
	}

	Store(DerefOf(Index(d000.pp00, 1)), Local0)

	if (LNotEqual(Local0, 0x00100064)) {
		err(ts, z159, __LINE__, 0, 0, Local0, 0x00100064)
	}

	CH03(ts, z159, 0x105, __LINE__, 0)
}

/*
 * Buffer Field instead of i000 (in m001)
 */
Method(m505, 1)
{
	Name(ts, "m505")
	Name(i001, 0)
	Name(p000, Package() {1,2,3,4})

	CH03(ts, z159, 0x200, __LINE__, 0)

	Device(d000)
	{
		Name(b000, Buffer(16) {})
		CreateField(b000, 5, 32, bf00)
	}

	CH03(ts, z159, 0x106, __LINE__, 0)

	if (0) {
		CreateField(d000.b000, 5, 32, bf00)
	}

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
										Store(p000, Index(\m505.d000.bf00, 1))
									}
									Return (0)
								}
								Store(0x80000000, Index(\m505.d000.bf00, 1))
								Return (Add(DerefOf(Index(\m505.d000.bf00, 1)), m008()))
							}
							Store(0x07000000, Index(\m505.d000.bf00, 1))
							Return (Add(DerefOf(Index(\m505.d000.bf00, 1)), m007()))
						}
						Store(0x00600000, Index(\m505.d000.bf00, 1))
						Return (Add(DerefOf(Index(\m505.d000.bf00, 1)), m006()))
					}
					Store(0x00050000, Index(\m505.d000.bf00, 1))
					Return (Add(DerefOf(Index(\m505.d000.bf00, 1)), m005()))
				}
				Store(0x00004000, Index(\m505.d000.bf00, 1))
				Return (Add(DerefOf(Index(\m505.d000.bf00, 1)), m004()))
			}
			Store(0x00000300, Index(\m505.d000.bf00, 1))
			Return (Add(DerefOf(Index(\m505.d000.bf00, 1)), m003()))
		}
		Store(0x00000020, Index(^d000.bf00, 1))
		Return (Add(DerefOf(Index(^d000.bf00, 1)), m002()))
	}
	Store(Add(DerefOf(Index(d000.bf00, 1)), m001()), Local0)

	if (LNotEqual(Local0, 0x87654321)) {
		err(ts, z159, __LINE__, 0, 0, Local0, 0x87654321)
	}

	Store(DerefOf(Index(d000.bf00, 1)), Local0)

	if (LNotEqual(Local0, 0x80000000)) {
		err(ts, z159, __LINE__, 0, 0, Local0, 0x80000000)
	}

	CH03(ts, z159, 0x107, __LINE__, 0)
}


Method(n005)
{
if (1) {
	SRMT("m500")
	m500()
	SRMT("m501")
	m501()
	SRMT("m502")
	m502()
	SRMT("m503-0")
	m503(0)
	SRMT("m503-1")
	if (y200) {
		m503(1)
	} else {
		BLCK()
	}
	SRMT("m504")
	m504()
	SRMT("m505-0")
	if (y216) {
		m505(0)
	} else {
		BLCK()
	}
	SRMT("m505-1")
	if (LAnd(y200, y216)) {
		m505(1)
	} else {
		BLCK()
	}
} else {
	SRMT("m505-0")
	m505(0)
}
}
