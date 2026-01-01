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
 * Check recursive calls to methods
 *
 * recursively called methods may have internal NS objects and Switch operations
 */

Name(z177, 177)

/*
 * Simplest example of recursive calls of methods
 * not overburden with the additional checkings.
 *
 * When the method m100 is invoked last time (44-th invocation),
 * we have there the following hierarchy of method calls - 45 method
 * invocations in progress:
 *
 *   m100  ...
 *   m200  ... ...
 *   m300  ... ... ... ...
 *   m400  ... ... ... ... ... ... ... ...
 *
 * The sequence of invocations is this:
 *
 *   m100  0,22,44
 *   m200  1,11,21  23,33,43
 *   m300  2, 6,10  12,16,20  24,28,32  34,38,42
 *   m400  3, 4, 5   7, 8, 9  13,14,15  17,18,19  25,26,27  29,30,31  35,36,37  39,40,41
 */
Method(m0ef,, Serialized)
{
	Name(ts, "m0ef")

	Name(rpt0, 0)

	/*
	 * Total number of calls of the same Recursively Called method (RCM),
	 * the first call is counted there too.
	 */
	Name(n000, 3)

	Name(cnt0, 0) // how many methods are in progress simultaneously
	Name(max0, 0) // maximal number of methods being in progress simultaneously

	/*
	 * Open method execution
	 *
	 * arg0 - ID of method (1,2,3...)
	 * arg1 - the message to be reported
	 */
	Method(m800, 2)
	{
		if (rpt0) {
			Store(arg1, Debug)
		}
		Increment(cnt0)

		if (LGreater(cnt0, max0)) {
			Store(cnt0, max0)
		}
	}

	/*
	 * Close method execution
	 *
	 * arg0 - ID of method (1,2,3...)
	 */
	Method(m801, 1)
	{
		Decrement(cnt0)
	}

	/*
	 * Arguments of methods:
	 * arg0 - 0 - the first call, otherwise - recursive calls
	 */

	Name(c000, 3)

	Method(m100,, Serialized)
	{
		Name(c100, 3)
		Method(m200,, Serialized)
		{
			Name(c200, 3)
			Method(m300,, Serialized)
			{
				Name(c300, 3)
				Method(m400)
				{
					m800(4, "m400")
					Decrement(c300)
					if (LEqual(c300, 0)) {
						m300()
					} else {
						m400()
					}
					m801(4)
				}
				m800(3, "m300")
				Decrement(c200)
				if (LEqual(c200, 0)) {
					m200()
				} else {
					m400()
				}
				m801(3)
			}
			m800(2, "m200")
			Decrement(c100)
			if (LEqual(c100, 0)) {
				m100()
			} else {
				m300()
			}
			m801(2)
		}
		m800(1, "m100")
		Decrement(c000)
		if (LEqual(c000, 0)) {
			// m000()
		} else {
			m200()
		}
		m801(1)
	}

	CH03(ts, z177, 0x000, __LINE__, 0)

	m100()

	Concatenate("Maximal number of methods being in progress simultaneously ", max0, Debug)

	/* Check Maximal number of methods being in progress simultaneously */
	if (LNotEqual(max0, 45)) {
		err(ts, z177, __LINE__, 0, 0, max0, 45)
	}

	/* Overall got out of methods the same number as got into methods */
	if (LNotEqual(cnt0, 0)) {
		err(ts, z177, __LINE__, 0, 0, cnt0, 0)
	}

	CH03(ts, z177, 0x003, __LINE__, 0)
}

/*
 * The same hierarchy of recursive calls like m0ef
 * but more checkings added.
 */
Method(m0fb,, Serialized)
{
	Name(ts, "m0fb")

	Name(rpt0, 0)

	/*
	 * Total number of calls of the same Recursively Called method (RCM),
	 * the first call is counted there too.
	 */
	Name(n000, 3)

	Name(cnt0, 0) // how many methods are in progress simultaneously
	Name(max0, 0) // maximal number of methods being in progress simultaneously
	Name(cnt1, 0) // summary of total indexes

	Name(ix00, 0) // total index of current call
	Name(ind1, 0) // index of call to m100
	Name(ind2, 0) // index of call to m200
	Name(ind3, 0) // index of call to m300
	Name(ind4, 0) // index of call to m400

	Name(n100,  3) // number of calls to m100
	Name(n200,  6) // number of calls to m200
	Name(n300, 12) // number of calls to m300
	Name(n400, 24) // number of calls to m400

	Name(p100, Package(n100) {}) // Package to keep total indexes of call to m100
	Name(p200, Package(n200) {}) // Package to keep total indexes of call to m200
	Name(p300, Package(n300) {}) // Package to keep total indexes of call to m300
	Name(p400, Package(n400) {}) // Package to keep total indexes of call to m400

	// Benchmarks of indexes
	Name(b1b0, Buffer(n100) {0,22,44})
	Name(b2b0, Buffer(n200) {1,11,21,  23,33,43})
	Name(b3b0, Buffer(n300) {2, 6,10,  12,16,20,  24,28,32,  34,38,42})
	Name(b4b0, Buffer(n400) {3, 4, 5,   7, 8, 9,  13,14,15,  17,18,19,
					25,26,27,  29,30,31,  35,36,37,  39,40,41})

	/*
	 * Open method execution
	 *
	 * arg0 - ID of method (1,2,3...)
	 * arg1 - the message to be reported
	 */
	Method(m800, 2)
	{
		if (rpt0) {
			Store(arg1, Debug)
		}
		Increment(cnt0)

		if (LGreater(cnt0, max0)) {
			Store(cnt0, max0)
		}

		Switch (arg0) {
			Case (1) {
				Store(ix00, Index(p100, ind1))
				Increment(ind1)
			}
			Case (2) {
				Store(ix00, Index(p200, ind2))
				Increment(ind2)
			}
			Case (3) {
				Store(ix00, Index(p300, ind3))
				Increment(ind3)
			}
			Case (4) {
				Store(ix00, Index(p400, ind4))
				Increment(ind4)
			}
		}

		Increment(ix00) // total index
	}

	/*
	 * Close method execution
	 *
	 * arg0 - ID of method (1,2,3...)
	 */
	Method(m801, 1)
	{
		Decrement(cnt0)
	}

	/*
	 * arg0 - ID of method (1,2,3...)
	 * arg1 - number of elements to be compared
	 * arg2 - Package
	 * arg3 - Package with the benchmark values
	 */
	Method(m802, 4) {
		Name(lpN0, 0)
		Name(lpC0, 0)

		Store(arg1, lpN0)
		Store(0, lpC0)

		While (lpN0) {

			Store(DeRefOf(Index(arg2, lpC0)), Local0)
			Store(DeRefOf(Index(arg3, lpC0)), Local1)
			if (LNotEqual(Local0, Local1)) {
				err(ts, z177, __LINE__, 0, 0, Local0, Local1)
				Store(arg0, Debug)
				Store(lpC0, Debug)
			}
			Decrement(lpN0)
			Increment(lpC0)
		}

		Switch (arg0) {
			Case (1) {
				if (LNotEqual(ind1, n100)) {
					err(ts, z177, __LINE__, 0, 0, ind1, n100)
				}
			}
			Case (2) {
				if (LNotEqual(ind2, n200)) {
					err(ts, z177, __LINE__, 0, 0, ind2, n200)
				}
			}
			Case (3) {
				if (LNotEqual(ind3, n300)) {
					err(ts, z177, __LINE__, 0, 0, ind3, n300)
				}
			}
			Case (4) {
				if (LNotEqual(ind4, n400)) {
					err(ts, z177, __LINE__, 0, 0, ind4, n400)
				}
			}
		}
	}

	/*
	 * Arguments of methods:
	 * arg0 - 0 - the first call, otherwise - recursive calls
	 */

	Name(c000, 3)

	Method(m100)
	{
		Name(ii00, 0)

		Name(c100, 3)
		Method(m200)
		{
			Name(ii00, 0)

			Name(c200, 3)
			Method(m300)
			{
				Name(ii00, 0)

				Name(c300, 3)
				Method(m400)
				{
					Name(ii00, 0)

					Store(ind4, ii00)
					Store(ix00, Local0)
					m800(4, "m400")
					Decrement(c300)
					Switch (c300) {
						Case (0) {
							m300()
						}
						Default {
							m400()
						}
					}
					m801(4)
					Add(cnt1, Local0, cnt1)
					Store(DerefOf(Index(p400, ii00)), ii00)
					if (LNotEqual(ii00, Local0)) {
						err(ts, z177, __LINE__, 0, 0, ii00, Local0)
					}
				}
				Store(ind3, ii00)
				Store(ix00, Local0)
				m800(3, "m300")
				Decrement(c200)
				Switch (c200) {
					Case (0) {
						m200()
					}
					Default {
						m400()
					}
				}
				m801(3)
				Add(cnt1, Local0, cnt1)
				Store(DerefOf(Index(p300, ii00)), ii00)
				if (LNotEqual(ii00, Local0)) {
					err(ts, z177, __LINE__, 0, 0, ii00, Local0)
				}
			}
			Store(ind2, ii00)
			Store(ix00, Local0)
			m800(2, "m200")
			Decrement(c100)
			Switch (c100) {
				Case (0) {
					m100()
				}
				Default {
					m300()
				}
			}
			m801(2)
			Add(cnt1, Local0, cnt1)
			Store(DerefOf(Index(p200, ii00)), ii00)
			if (LNotEqual(ii00, Local0)) {
				err(ts, z177, __LINE__, 0, 0, ii00, Local0)
			}
		}
		Store(ind1, ii00)
		Store(ix00, Local0)
		m800(1, "m100")
		Decrement(c000)
		Switch (c000) {
			Case (0) {
				// m000()
			}
			Default {
				m200()
			}
		}
		m801(1)
		Add(cnt1, Local0, cnt1)
		Store(DerefOf(Index(p100, ii00)), ii00)
		if (LNotEqual(ii00, Local0)) {
			err(ts, z177, __LINE__, 0, 0, ii00, Local0)
		}
	}

	CH03(ts, z177, 0x00d, __LINE__, 0)

	m100()

	Concatenate("Maximal number of methods being in progress simultaneously ", max0, Debug)

	/* Check Maximal number of methods being in progress simultaneously */
	if (LNotEqual(max0, 45)) {
		err(ts, z177, __LINE__, 0, 0, max0, 45)
	}

	/* Overall got out of methods the same number as got into methods */
	if (LNotEqual(cnt0, 0)) {
		err(ts, z177, __LINE__, 0, 0, cnt0, 0)
	}

	/* Check indexes */
	m802(1, n100, p100, b1b0)
	m802(2, n200, p200, b2b0)
	m802(3, n300, p300, b3b0)
	m802(4, n400, p400, b4b0)


	/* Check the overall sum of total indexes */
	if (LNotEqual(cnt1, 0x3DE)) {
		err(ts, z177, __LINE__, 0, 0, cnt1, 0x3DE)
	}

	CH03(ts, z177, 0x011, __LINE__, 0)
}

/*
 * The same hierarchy of recursive calls like m0ef
 * but deeper.
 */
Method(m0ff, 1, Serialized)
{
	Name(ts, "m0ff")

	Name(rpt0, 0)

	Name(i000, 0)

	/*
	 * Total number of calls of the same Recursively Called method (RCM),
	 * the first call is counted there too.
	 */
	Name(n000, 3)

	Name(cnt0, 0) // how many methods are in progress simultaneously
	Name(max0, 0) // maximal number of methods being in progress simultaneously

	/*
	 * Open method execution
	 *
	 * arg0 - ID of method (1,2,3...)
	 * arg1 - the message to be reported
	 */
	Method(m800, 2)
	{
		if (rpt0) {
			Store(arg1, Debug)
		}
		Increment(cnt0)

		if (LGreater(cnt0, max0)) {
			Store(cnt0, max0)
		}
	}

	/*
	 * Close method execution
	 *
	 * arg0 - ID of method (1,2,3...)
	 */
	Method(m801, 1)
	{
		Decrement(cnt0)
	}

	/*
	 * Arguments of methods:
	 * arg0 - 0 - the first call, otherwise - recursive calls
	 */

	Name(c000, 3)

	Method(m100,, Serialized)
	{
		Name(c100, 3)
		Method(m200,, Serialized)
		{
			Name(c200, 3)
			Method(m300,, Serialized)
			{
				Name(c300, 3)
				Method(m400,, Serialized)
				{
					Name(c400, 3)
					Method(m500,, Serialized)
					{
						Name(c500, 4)
						Method(m600)
						{
							m800(6, "m600")
							Decrement(c500)
							if (LEqual(c500, 0)) {
								m500()
							} else {
								m600()
							}
							m801(6)
						}
						m800(5, "m500")
						Decrement(c400)
						if (LEqual(c400, 0)) {
							m400()
						} else {
							m600()
						}
						m801(5)
					}
					if (i000) {
						Store(4, c400)
					}
					m800(4, "m400")
					Decrement(c300)
					if (LEqual(c300, 0)) {
						m300()
					} else {
						m500()
					}
					m801(4)
				}
				m800(3, "m300")
				Decrement(c200)
				if (LEqual(c200, 0)) {
					m200()
				} else {
					m400()
				}
				m801(3)
			}
			m800(2, "m200")
			Decrement(c100)
			if (LEqual(c100, 0)) {
				m100()
			} else {
				m300()
			}
			m801(2)
		}
		m800(1, "m100")
		Decrement(c000)
		if (LEqual(c000, 0)) {
			// m000()
		} else {
			m200()
		}
		m801(1)
	}

	CH03(ts, z177, 0x012, __LINE__, 0)

	Store(arg0, i000)

	m100()

	if (arg0) {
		CH04(ts, 0, 84, z177, __LINE__, 0, 0)	// AE_AML_METHOD_LIMIT
	} else {
		Concatenate("Maximal number of methods being in progress simultaneously ", max0, Debug)

		/* Check Maximal number of methods being in progress simultaneously */
		if (LNotEqual(max0, 221)) {
			err(ts, z177, __LINE__, 0, 0, max0, 221)
		}

		/* Overall got out of methods the same number as got into methods */
		if (LNotEqual(cnt0, 0)) {
			err(ts, z177, __LINE__, 0, 0, cnt0, 0)
		}
	}

	CH03(ts, z177, 0x016, __LINE__, 0)
}

/*
 * Similar to m0fb but
 * all methods are Serialized (0 level all)
 * and no internal objects (including Methods) or Switches in those Serialized methods
 *
 * Check that Serialized method being invoked recursively on the same thread
 * works well (no exceptions) in case it has none either internal objects
 * (including Methods) or Switches.
 */
Method(m18a, 1, Serialized)
{
	Name(ts, "m18a")

	Name(rpt0, 0)
	Name(i000, 0)

	/*
	 * Total number of calls of the same Recursively Called method (RCM),
	 * the first call is counted there too.
	 */
	Name(n000, 3)

	Name(cnt0, 0) // how many methods are in progress simultaneously
	Name(max0, 0) // maximal number of methods being in progress simultaneously
	Name(cnt1, 0) // summary of total indexes

	Name(ix00, 0) // total index of current call
	Name(ind1, 0) // index of call to m100
	Name(ind2, 0) // index of call to m200
	Name(ind3, 0) // index of call to m300
	Name(ind4, 0) // index of call to m400

	Name(n100,  3) // number of calls to m100
	Name(n200,  6) // number of calls to m200
	Name(n300, 12) // number of calls to m300
	Name(n400, 24) // number of calls to m400

	Name(p100, Package(n100) {}) // Package to keep total indexes of call to m100
	Name(p200, Package(n200) {}) // Package to keep total indexes of call to m200
	Name(p300, Package(n300) {}) // Package to keep total indexes of call to m300
	Name(p400, Package(0x100) {}) // Package to keep total indexes of call to m400

	// Benchmarks of indexes
	Name(b1b0, Buffer(n100) {0,22,44})
	Name(b2b0, Buffer(n200) {1,11,21,  23,33,43})
	Name(b3b0, Buffer(n300) {2, 6,10,  12,16,20,  24,28,32,  34,38,42})
	Name(b4b0, Buffer(0x100) {3, 4, 5,   7, 8, 9,  13,14,15,  17,18,19,
					25,26,27,  29,30,31,  35,36,37,  39,40,41})

	/*
	 * Open method execution
	 *
	 * arg0 - ID of method (1,2,3...)
	 * arg1 - the message to be reported
	 */
	Method(m800, 2)
	{
		if (rpt0) {
			Store(arg1, Debug)
		}
		Increment(cnt0)

		if (LGreater(cnt0, max0)) {
			Store(cnt0, max0)
		}

		Switch (arg0) {
			Case (1) {
				Store(ix00, Index(p100, ind1))
				Increment(ind1)
			}
			Case (2) {
				Store(ix00, Index(p200, ind2))
				Increment(ind2)
			}
			Case (3) {
				Store(ix00, Index(p300, ind3))
				Increment(ind3)
			}
			Case (4) {
				Store(ix00, Index(p400, ind4))
				Increment(ind4)
			}
		}

		Increment(ix00) // total index
	}

	/*
	 * Close method execution
	 *
	 * arg0 - ID of method (1,2,3...)
	 */
	Method(m801, 1)
	{
		Decrement(cnt0)
	}

	/*
	 * arg0 - ID of method (1,2,3...)
	 * arg1 - number of elements to be compared
	 * arg2 - Package
	 * arg3 - Package with the benchmark values
	 */
	Method(m802, 4) {
		Name(lpN0, 0)
		Name(lpC0, 0)

		Store(arg1, lpN0)
		Store(0, lpC0)

		While (lpN0) {

			Store(DeRefOf(Index(arg2, lpC0)), Local0)
			Store(DeRefOf(Index(arg3, lpC0)), Local1)
			if (LNotEqual(Local0, Local1)) {
				err(ts, z177, __LINE__, 0, 0, Local0, Local1)
				Store(arg0, Debug)
				Store(lpC0, Debug)
			}
			Decrement(lpN0)
			Increment(lpC0)
		}

		Switch (arg0) {
			Case (1) {
				if (LNotEqual(ind1, n100)) {
					err(ts, z177, __LINE__, 0, 0, ind1, n100)
				}
			}
			Case (2) {
				if (LNotEqual(ind2, n200)) {
					err(ts, z177, __LINE__, 0, 0, ind2, n200)
				}
			}
			Case (3) {
				if (LNotEqual(ind3, n300)) {
					err(ts, z177, __LINE__, 0, 0, ind3, n300)
				}
			}
			Case (4) {
				if (LNotEqual(ind4, n400)) {
					err(ts, z177, __LINE__, 0, 0, ind4, n400)
				}
			}
		}
	}

	/*
	 * Arguments of methods:
	 * arg0 - 0 - the first call, otherwise - recursive calls
	 */

	Name(c000, 3)
	Name(c100, 3)
	Name(c200, 3)
	Name(c300, 3)

	/*
	 * None internal objects (including Methods) or Switches in Serialized methods below
	 *
	 * Note: if Serialized method has internal objects (including Methods and Switches)
	 *       it could not be invoked recursively by the same thread.
	 */
	Method(m100, 0, Serialized, 0)
	{
		Store(3, c100)
		Store(ind1, Local1)
		Store(ix00, Local0)
		m800(1, "m100")
		Decrement(c000)
		if (LEqual(c000, 0)) {
			// m000()
		} else {
			m200()
		}
		m801(1)
		Add(cnt1, Local0, cnt1)
		Store(DerefOf(Index(p100, Local1)), Local1)
		if (LNotEqual(Local1, Local0)) {
			err(ts, z177, __LINE__, 0, 0, Local1, Local0)
		}
	}
	Method(m200, 0, Serialized, 0)
	{
		Store(3, c200)
		Store(ind2, Local1)
		Store(ix00, Local0)
		m800(2, "m200")
		Decrement(c100)
		if (LEqual(c100, 0)) {
			m100()
		} else {
			m300()
		}
		m801(2)
		Add(cnt1, Local0, cnt1)
		Store(DerefOf(Index(p200, Local1)), Local1)
		if (LNotEqual(Local1, Local0)) {
			err(ts, z177, __LINE__, 0, 0, Local1, Local0)
		}
	}
	Method(m300, 0, Serialized, 0)
	{
		if (i000) {
			Store(31, c300)
		} else {
			Store(3, c300)
		}

		Store(ind3, Local1)
		Store(ix00, Local0)
		m800(3, "m300")
		Decrement(c200)
		if (LEqual(c200, 0)) {
			m200()
		} else {
			m400()
		}
		m801(3)
		Add(cnt1, Local0, cnt1)
		Store(DerefOf(Index(p300, Local1)), Local1)
		if (LNotEqual(Local1, Local0)) {
			err(ts, z177, __LINE__, 0, 0, Local1, Local0)
		}
	}
	Method(m400, 0, Serialized, 0)
	{
		Store(ind4, Local1)
		Store(ix00, Local0)
		m800(4, "m400")
		Decrement(c300)
		if (LEqual(c300, 0)) {
			m300()
		} else {
			m400()
		}
		m801(4)
		Add(cnt1, Local0, cnt1)
		Store(DerefOf(Index(p400, Local1)), Local1)
		if (LNotEqual(Local1, Local0)) {
			err(ts, z177, __LINE__, 0, 0, Local1, Local0)
		}
	}

	CH03(ts, z177, 0x020, __LINE__, 0)

	Store(arg0, i000)

	m100()

	Concatenate("Maximal number of methods being in progress simultaneously ", max0, Debug)

	if (arg0) {
		CH04(ts, 0, 84, z177, __LINE__, 0, 0)	// AE_AML_METHOD_LIMIT
	} else {

		/* Check Maximal number of methods being in progress simultaneously */
		if (LNotEqual(max0, 45)) {
			err(ts, z177, __LINE__, 0, 0, max0, 45)
		}

		/* Overall got out of methods the same number as got into methods */
		if (LNotEqual(cnt0, 0)) {
			err(ts, z177, __LINE__, 0, 0, cnt0, 0)
		}

		/* Check indexes */
		m802(1, n100, p100, b1b0)
		m802(2, n200, p200, b2b0)
		m802(3, n300, p300, b3b0)
		m802(4, n400, p400, b4b0)


		/* Check the overall sum of total indexes */
		if (LNotEqual(cnt1, 0x3DE)) {
			err(ts, z177, __LINE__, 0, 0, cnt1, 0x3DE)
		}
	}
	CH03(ts, z177, 0x024, __LINE__, 0)
}

/*
 * The same as m18a the level of Serialized methods is non-zero (7 level all)
 */
Method(m18b, 1, Serialized)
{
	Name(ts, "m18b")
	Name(i000, 0)

	Name(rpt0, 0)

	/*
	 * Total number of calls of the same Recursively Called method (RCM),
	 * the first call is counted there too.
	 */
	Name(n000, 3)

	Name(cnt0, 0) // how many methods are in progress simultaneously
	Name(max0, 0) // maximal number of methods being in progress simultaneously
	Name(cnt1, 0) // summary of total indexes

	Name(ix00, 0) // total index of current call
	Name(ind1, 0) // index of call to m100
	Name(ind2, 0) // index of call to m200
	Name(ind3, 0) // index of call to m300
	Name(ind4, 0) // index of call to m400

	Name(n100,  3) // number of calls to m100
	Name(n200,  6) // number of calls to m200
	Name(n300, 12) // number of calls to m300
	Name(n400, 24) // number of calls to m400

	Name(p100, Package(n100) {}) // Package to keep total indexes of call to m100
	Name(p200, Package(n200) {}) // Package to keep total indexes of call to m200
	Name(p300, Package(n300) {}) // Package to keep total indexes of call to m300
	Name(p400, Package(0x100) {}) // Package to keep total indexes of call to m400

	// Benchmarks of indexes
	Name(b1b0, Buffer(n100) {0,22,44})
	Name(b2b0, Buffer(n200) {1,11,21,  23,33,43})
	Name(b3b0, Buffer(n300) {2, 6,10,  12,16,20,  24,28,32,  34,38,42})
	Name(b4b0, Buffer(0x100) {3, 4, 5,   7, 8, 9,  13,14,15,  17,18,19,
					25,26,27,  29,30,31,  35,36,37,  39,40,41})

	/*
	 * Open method execution
	 *
	 * arg0 - ID of method (1,2,3...)
	 * arg1 - the message to be reported
	 */
	Method(m800, 2)
	{
		if (rpt0) {
			Store(arg1, Debug)
		}
		Increment(cnt0)

		if (LGreater(cnt0, max0)) {
			Store(cnt0, max0)
		}

		/*
		 * Don't use Switch() here because we want this method to
		 * be reentrant.
		 */
		if (LEqual(arg0, 1)) {
			Store(ix00, Index(p100, ind1))
			Increment(ind1)
		} else {
			if (LEqual(arg0, 2)) {
				Store(ix00, Index(p200, ind2))
				Increment(ind2)
			} else {
				if (LEqual(arg0, 3)) {
					Store(ix00, Index(p300, ind3))
					Increment(ind3)
				} else {
					if (LEqual(arg0, 4)) {
						Store(ix00, Index(p400, ind4))
						Increment(ind4)
					}
				}
			}
		}

		Increment(ix00) // total index
	}

	/*
	 * Close method execution
	 *
	 * arg0 - ID of method (1,2,3...)
	 */
	Method(m801, 1)
	{
		Decrement(cnt0)
	}

	/*
	 * arg0 - ID of method (1,2,3...)
	 * arg1 - number of elements to be compared
	 * arg2 - Package
	 * arg3 - Package with the benchmark values
	 */
	Method(m802, 4) {
		Name(lpN0, 0)
		Name(lpC0, 0)

		Store(arg1, lpN0)
		Store(0, lpC0)

		While (lpN0) {

			Store(DeRefOf(Index(arg2, lpC0)), Local0)
			Store(DeRefOf(Index(arg3, lpC0)), Local1)
			if (LNotEqual(Local0, Local1)) {
				err(ts, z177, __LINE__, 0, 0, Local0, Local1)
				Store(arg0, Debug)
				Store(lpC0, Debug)
			}
			Decrement(lpN0)
			Increment(lpC0)
		}

		Switch (arg0) {
			Case (1) {
				if (LNotEqual(ind1, n100)) {
					err(ts, z177, __LINE__, 0, 0, ind1, n100)
				}
			}
			Case (2) {
				if (LNotEqual(ind2, n200)) {
					err(ts, z177, __LINE__, 0, 0, ind2, n200)
				}
			}
			Case (3) {
				if (LNotEqual(ind3, n300)) {
					err(ts, z177, __LINE__, 0, 0, ind3, n300)
				}
			}
			Case (4) {
				if (LNotEqual(ind4, n400)) {
					err(ts, z177, __LINE__, 0, 0, ind4, n400)
				}
			}
		}
	}

	/*
	 * Arguments of methods:
	 * arg0 - 0 - the first call, otherwise - recursive calls
	 */

	Name(c000, 3)
	Name(c100, 3)
	Name(c200, 3)
	Name(c300, 3)

	/*
	 * None internal objects (including Methods) or Switches in Serialized methods below
	 *
	 * Note: if Serialized method has internal objects (including Methods and Switches)
	 *       it could not be invoked recursively by the same thread.
	 */
	Method(m100, 0, Serialized, 7)
	{
		Store(3, c100)
		Store(ind1, Local1)
		Store(ix00, Local0)
		m800(1, "m100")
		Decrement(c000)
		if (LEqual(c000, 0)) {
			// m000()
		} else {
			m200()
		}
		m801(1)
		Add(cnt1, Local0, cnt1)
		Store(DerefOf(Index(p100, Local1)), Local1)
		if (LNotEqual(Local1, Local0)) {
			err(ts, z177, __LINE__, 0, 0, Local1, Local0)
		}
	}
	Method(m200, 0, Serialized, 7)
	{
		Store(3, c200)
		Store(ind2, Local1)
		Store(ix00, Local0)
		m800(2, "m200")
		Decrement(c100)
		if (LEqual(c100, 0)) {
			m100()
		} else {
			m300()
		}
		m801(2)
		Add(cnt1, Local0, cnt1)
		Store(DerefOf(Index(p200, Local1)), Local1)
		if (LNotEqual(Local1, Local0)) {
			err(ts, z177, __LINE__, 0, 0, Local1, Local0)
		}
	}
	Method(m300, 0, Serialized, 7)
	{
		if (i000) {
			Store(31, c300)
		} else {
			Store(3, c300)
		}

		Store(ind3, Local1)
		Store(ix00, Local0)
		m800(3, "m300")
		Decrement(c200)
		if (LEqual(c200, 0)) {
			m200()
		} else {
			m400()
		}
		m801(3)
		Add(cnt1, Local0, cnt1)
		Store(DerefOf(Index(p300, Local1)), Local1)
		if (LNotEqual(Local1, Local0)) {
			err(ts, z177, __LINE__, 0, 0, Local1, Local0)
		}
	}
	Method(m400, 0, Serialized, 7)
	{
		Store(ind4, Local1)
		Store(ix00, Local0)
		m800(4, "m400")
		Decrement(c300)
		if (LEqual(c300, 0)) {
			m300()
		} else {
			m400()
		}
		m801(4)
		Add(cnt1, Local0, cnt1)
		Store(DerefOf(Index(p400, Local1)), Local1)
		if (LNotEqual(Local1, Local0)) {
			err(ts, z177, __LINE__, 0, 0, Local1, Local0)
		}
	}

	CH03(ts, z177, 0x02e, __LINE__, 0)

	Store(arg0, i000)

	m100()

	Concatenate("Maximal number of methods being in progress simultaneously ", max0, Debug)

	if (arg0) {
		CH04(ts, 0, 84, z177, __LINE__, 0, 0)	// AE_AML_METHOD_LIMIT
	} else {

		/* Check Maximal number of methods being in progress simultaneously */
		if (LNotEqual(max0, 45)) {
			err(ts, z177, __LINE__, 0, 0, max0, 45)
		}

		/* Overall got out of methods the same number as got into methods */
		if (LNotEqual(cnt0, 0)) {
			err(ts, z177, __LINE__, 0, 0, cnt0, 0)
		}

		/* Check indexes */
		m802(1, n100, p100, b1b0)
		m802(2, n200, p200, b2b0)
		m802(3, n300, p300, b3b0)
		m802(4, n400, p400, b4b0)


		/* Check the overall sum of total indexes */
		if (LNotEqual(cnt1, 0x3DE)) {
			err(ts, z177, __LINE__, 0, 0, cnt1, 0x3DE)
		}
	}

	CH03(ts, z177, 0x032, __LINE__, 0)
}


/*
 * Check that Serialized method being invoked recursively on the same thread
 * (causes/ doesn't cause)
 * exception in case it has either internal objects (including Methods) or Switches.
 */


/*
 * No internal objects in Serialized method (including Methods and Switches),
 * so no exceptions are expected on recursive calls.
 */
Method(m18d,, Serialized)
{
	Name(ts, "m18d")

	Method(m000, 1, Serialized, 7)
	{
		if (LNot(arg0)) {
			m000(1)
		}
	}

	CH03(ts, z177, 0x033, __LINE__, 0)
	m000(0)
	CH03(ts, z177, 0x034, __LINE__, 0)
}

/*
 * Serialized method has internal object (Named Integer),
 * so AE_ALREADY_EXISTS exception is expected on recursive call.
 */
Method(m18e,, Serialized)
{
	Name(ts, "m18e")

	Method(m000, 1, Serialized, 7)
	{
		Name(i000, 0xabcd0000)

		if (LNot(arg0)) {
			m000(1)
		}
	}

	CH03(ts, z177, 0x035, __LINE__, 0)
	m000(0)
	if (y902) {
		CH04(ts, 0, 7, z177, __LINE__, 0, 0)	// AE_ALREADY_EXISTS
	} else {
		CH03(ts, z177, 0x037, __LINE__, 0)
	}
}

/*
 * Serialized method has internal Switch,
 * so AE_ALREADY_EXISTS exception is expected on recursive call.
 */
Method(m18f,, Serialized)
{
	Name(ts, "m18f")

	Method(m000, 1, Serialized, 7)
	{
		Switch (0) {
			Case (0) {
				Store("m18f", Debug)
			}
		}

		if (LNot(arg0)) {
			m000(1)
		}
	}

	CH03(ts, z177, 0x038, __LINE__, 0)
	m000(0)
	if (y902) {
		CH04(ts, 0, 7, z177, __LINE__, 0, 0)	// AE_ALREADY_EXISTS
	} else {
		CH03(ts, z177, 0x03a, __LINE__, 0)
	}
}

/*
 * Serialized method has internal declaration of Method,
 * so AE_ALREADY_EXISTS exception is expected on recursive call.
 */
Method(m19a,, Serialized)
{
	Name(ts, "m19a")

	Method(m000, 1, Serialized, 7)
	{
		Method(m100) {}

		if (LNot(arg0)) {
			m000(1)
		}
	}

	CH03(ts, z177, 0x03b, __LINE__, 0)
	m000(0)
	if (y902) {
		CH04(ts, 0, 7, z177, __LINE__, 0, 0)	// AE_ALREADY_EXISTS
	} else {
		CH03(ts, z177, 0x03d, __LINE__, 0)
	}
}

/*
 * Serialized method has internal declaration of Device,
 * so AE_ALREADY_EXISTS exception is expected on recursive call.
 */
Method(m19b,, Serialized)
{
	Name(ts, "m19b")

	Method(m000, 1, Serialized, 7)
	{
		Device(d000) {}

		if (LNot(arg0)) {
			m000(1)
		}
	}

	CH03(ts, z177, 0x03e, __LINE__, 0)
	m000(0)
	if (y902) {
		CH04(ts, 0, 7, z177, __LINE__, 0, 0)	// AE_ALREADY_EXISTS
	} else {
		CH03(ts, z177, 0x040, __LINE__, 0)
	}
}

/*
 * It is m0ef but all the relevant methods are Serialized.
 * Exceptions are expected.
 * Now we have crash there.
 */
Method(m19c,, Serialized)
{
	Name(ts, "m19c")

	Name(rpt0, 0)

	/*
	 * Total number of calls of the same Recursively Called method (RCM),
	 * the first call is counted there too.
	 */
	Name(n000, 3)

	Name(cnt0, 0) // how many methods are in progress simultaneously
	Name(max0, 0) // maximal number of methods being in progress simultaneously

	/*
	 * Open method execution
	 *
	 * arg0 - ID of method (1,2,3...)
	 * arg1 - the message to be reported
	 */
	Method(m800, 2)
	{
		if (rpt0) {
			Store(arg1, Debug)
		}
		Increment(cnt0)

		if (LGreater(cnt0, max0)) {
			Store(cnt0, max0)
		}
	}

	/*
	 * Close method execution
	 *
	 * arg0 - ID of method (1,2,3...)
	 */
	Method(m801, 1)
	{
		Decrement(cnt0)
	}

	/*
	 * Arguments of methods:
	 * arg0 - 0 - the first call, otherwise - recursive calls
	 */

	Name(c000, 3)

	Method(m100, 0, Serialized, 9)
	{
		Name(c100, 3)
		Method(m200, 0, Serialized, 9)
		{
			Name(c200, 3)
			Method(m300, 0, Serialized, 9)
			{
				Name(c300, 3)
				Method(m400, 0, Serialized, 9)
				{
					m800(4, "m400")
					Decrement(c300)
					if (LEqual(c300, 0)) {
						m300()
					} else {
						m400()
					}
					m801(4)
				}
				m800(3, "m300")
				Decrement(c200)
				if (LEqual(c200, 0)) {
					m200()
				} else {
					m400()
				}
				m801(3)
			}
			m800(2, "m200")
			Decrement(c100)
			if (LEqual(c100, 0)) {
				m100()
			} else {
				m300()
			}
			m801(2)
		}
		m800(1, "m100")
		Decrement(c000)
		if (LEqual(c000, 0)) {
			// m000()
		} else {
			m200()
		}
		m801(1)
	}

	CH03(ts, z177, 0x041, __LINE__, 0)
	m100()
	if (y902) {
		CH04(ts, 0, 7, z177, __LINE__, 0, 0)	// AE_ALREADY_EXISTS
	} else {
		CH03(ts, z177, 0x043, __LINE__, 0)
	}
}


/*
 * Full-path declarations
 */


/*
 * Non-Serialized method has full-path declaration
 */
Method(m19d,, Serialized)
{
	Name(ts, "m19d")

	Method(m000, 1, Serialized)
	{
		Name(\i2z0, 0xabcd0000)

		if (LNotEqual(i2z0, 0xabcd0000)) {
			err(ts, z177, __LINE__, 0, 0, i2z0, 0xabcd0000)
		}
		if (LNotEqual(\i2z0, 0xabcd0000)) {
			err(ts, z177, __LINE__, 0, 0, \i2z0, 0xabcd0000)
		}

		Store(0x12345678, i2z0)
		if (LNotEqual(i2z0, 0x12345678)) {
			err(ts, z177, __LINE__, 0, 0, i2z0, 0x12345678)
		}
		if (LNotEqual(\i2z0, 0x12345678)) {
			err(ts, z177, __LINE__, 0, 0, \i2z0, 0x12345678)
		}

		Store(0x11112222, \i2z0)
		if (LNotEqual(i2z0, 0x11112222)) {
			err(ts, z177, __LINE__, 0, 0, i2z0, 0x11112222)
		}
		if (LNotEqual(\i2z0, 0x11112222)) {
			err(ts, z177, __LINE__, 0, 0, \i2z0, 0x11112222)
		}
	}
	CH03(ts, z177, 0x04a, __LINE__, 0)
	m000(0)
	CH03(ts, z177, 0x04b, __LINE__, 0)

	Store(0x11112222, i2z0)

	CH04(ts, 1, 5, z177, __LINE__, 0, 0)	// AE_NOT_FOUND

	Store(0x11112222, \i2z0)

	CH04(ts, 1, 5, z177, __LINE__, 0, 0)	// AE_NOT_FOUND
}

/*
 * Serialized method has full-path declaration
 */
Method(m19e,, Serialized)
{
	Name(ts, "m19e")

	Method(m000, 1, Serialized, 7)
	{
		Name(\i2z1, 0xabcd0000)

		if (LNotEqual(i2z1, 0xabcd0000)) {
			err(ts, z177, __LINE__, 0, 0, i2z1, 0xabcd0000)
		}
		if (LNotEqual(\i2z1, 0xabcd0000)) {
			err(ts, z177, __LINE__, 0, 0, \i2z1, 0xabcd0000)
		}

		Store(0x12345678, i2z1)
		if (LNotEqual(i2z1, 0x12345678)) {
			err(ts, z177, __LINE__, 0, 0, i2z1, 0x12345678)
		}
		if (LNotEqual(\i2z1, 0x12345678)) {
			err(ts, z177, __LINE__, 0, 0, \i2z1, 0x12345678)
		}

		Store(0x22223333, \i2z1)
		if (LNotEqual(i2z1, 0x22223333)) {
			err(ts, z177, __LINE__, 0, 0, i2z1, 0x22223333)
		}
		if (LNotEqual(\i2z1, 0x22223333)) {
			err(ts, z177, __LINE__, 0, 0, \i2z1, 0x22223333)
		}
	}
	CH03(ts, z177, 0x054, __LINE__, 0)
	m000(0)
	CH03(ts, z177, 0x055, __LINE__, 0)

	Store(0x11112222, i2z1)

	CH04(ts, 1, 5, z177, __LINE__, 0, 0)	// AE_NOT_FOUND

	Store(0x11112222, \i2z1)

	CH04(ts, 1, 5, z177, __LINE__, 0, 0)	// AE_NOT_FOUND
}

/*
 * Non-Serialized method has full-path declaration,
 * so AE_ALREADY_EXISTS exception is expected on recursive call.
 */
Method(m19f,, Serialized)
{
	Name(ts, "m19f")

	Method(m000, 1, Serialized)
	{
		Name(\i2z2, 0xabcd0002)

		if (LNot(arg0)) {
			m000(1)
		}
	}

	CH03(ts, z177, 0x058, __LINE__, 0)
	m000(0)
	CH04(ts, 0, 7, z177, __LINE__, 0, 0)	// AE_ALREADY_EXISTS
}

/*
 * Serialized method has full-path declaration,
 * so AE_ALREADY_EXISTS exception is expected on recursive call.
 */
Method(m1b8,, Serialized)
{
	Name(ts, "m1b8")

	Method(m000, 1, Serialized, 7)
	{
		Name(\i2z3, 0xabcd0003)

		if (LNot(arg0)) {
			m000(1)
		}
	}

	CH03(ts, z177, 0x05a, __LINE__, 0)
	m000(0)
	CH04(ts, 0, 7, z177, __LINE__, 0, 0)	// AE_ALREADY_EXISTS
}


/*
 * Scope declarations
 */


/*
 * Non-Serialized method has Scope declaration
 */
Method(m1b9,, Serialized)
{
	Name(ts, "m1b9")

	Method(m000, 1, Serialized)
	{
		Scope(\_SB) { Name(i2z4, 0xabcd0004) }
	}

	CH03(ts, z177, 0x05c, __LINE__, 0)
	m000(0)
	CH03(ts, z177, 0x05d, __LINE__, 0)
}

/*
 * Serialized method has Scope declaration,
 * so AE_ALREADY_EXISTS exception is expected on recursive call.
 */
Method(m1ba,, Serialized)
{
	Name(ts, "m1ba")

	Method(m000, 1, Serialized, 7)
	{
		Scope(\_SB) { Name(i2z5, 0xabcd0005) }
	}

	CH03(ts, z177, 0x05e, __LINE__, 0)
	m000(0)
	CH03(ts, z177, 0x05f, __LINE__, 0)
}

/*
 * Non-Serialized method has Scope declaration,
 * so AE_ALREADY_EXISTS exception is expected on recursive call.
 */
Method(m1bb,, Serialized)
{
	Name(ts, "m1bb")

	Method(m000, 1, Serialized)
	{
		Scope(\_SB) { Name(i2z6, 0xabcd0006) }

		if (LNot(arg0)) {
			m000(1)
		}
	}

	CH03(ts, z177, 0x060, __LINE__, 0)
	m000(0)
	CH04(ts, 0, 7, z177, __LINE__, 0, 0)	// AE_ALREADY_EXISTS
}

/*
 * Serialized method has Scope declaration,
 * so AE_ALREADY_EXISTS exception is expected on recursive call.
 */
Method(m1bc,, Serialized)
{
	Name(ts, "m1bc")

	Method(m000, 1, Serialized, 7)
	{
		Scope(\_SB) { Name(i2z7, 0xabcd0007) }

		if (LNot(arg0)) {
			m000(1)
		}
	}

	CH03(ts, z177, 0x062, __LINE__, 0)
	m000(0)
	CH04(ts, 0, 7, z177, __LINE__, 0, 0)	// AE_ALREADY_EXISTS
}

/*
 * Non-Serialized method declares full-path name on first call,
 * and allows proper access for the second recursive call too.
 */
Method(m1bd,, Serialized)
{
	Name(ts, "m1bd")

	Method(m000, 1, Serialized)
	{
		if (LNot(arg0)) {

			Name(\i2z8, 0xabcd0108)

			if (LNotEqual(i2z8, 0xabcd0108)) {
				err(ts, z177, __LINE__, 0, 0, i2z8, 0xabcd0108)
			}
			if (LNotEqual(\i2z8, 0xabcd0108)) {
				err(ts, z177, __LINE__, 0, 0, \i2z8, 0xabcd0108)
			}
		} else {
			if (LNotEqual(i2z8, 0x22223333)) {
				err(ts, z177, __LINE__, 0, 0, i2z8, 0x22223333)
			}
			if (LNotEqual(\i2z8, 0x22223333)) {
				err(ts, z177, __LINE__, 0, 0, \i2z8, 0x22223333)
			}
		}

		Store(0x12345678, i2z8)
		if (LNotEqual(i2z8, 0x12345678)) {
			err(ts, z177, __LINE__, 0, 0, i2z8, 0x12345678)
		}
		if (LNotEqual(\i2z8, 0x12345678)) {
			err(ts, z177, __LINE__, 0, 0, \i2z8, 0x12345678)
		}

		Store(0x22223333, \i2z8)
		if (LNotEqual(i2z8, 0x22223333)) {
			err(ts, z177, __LINE__, 0, 0, i2z8, 0x22223333)
		}
		if (LNotEqual(\i2z8, 0x22223333)) {
			err(ts, z177, __LINE__, 0, 0, \i2z8, 0x22223333)
		}

		if (LNot(arg0)) {
			m000(1)
		}

		if (arg0) {
			if (LNotEqual(i2z8, 0x22223333)) {
				err(ts, z177, __LINE__, 0, 0, i2z8, 0x22223333)
			}
			if (LNotEqual(\i2z8, 0x22223333)) {
				err(ts, z177, __LINE__, 0, 0, \i2z8, 0x22223333)
			}
		} else {
			if (LNotEqual(i2z8, 0x66667777)) {
				err(ts, z177, __LINE__, 0, 0, i2z8, 0x66667777)
			}
			if (LNotEqual(\i2z8, 0x66667777)) {
				err(ts, z177, __LINE__, 0, 0, \i2z8, 0x66667777)
			}
		}

		if (arg0) {
			Store(0x66667777, i2z8)
		} else {
			Store(0x44445555, i2z8)
		}
	}

	CH03(ts, z177, 0x070, __LINE__, 0)
	m000(0)
	CH03(ts, z177, 0x071, __LINE__, 0)
}

/*
 * Serialized method declares full-path name on first call,
 * and allows proper access for the second recursive call too.
 */
Method(m1be,, Serialized)
{
	Name(ts, "m1be")

	Method(m000, 1, Serialized, 7)
	{
		if (LNot(arg0)) {

			Name(\i2z9, 0xabcd0109)

			if (LNotEqual(i2z9, 0xabcd0109)) {
				err(ts, z177, __LINE__, 0, 0, i2z9, 0xabcd0109)
			}
			if (LNotEqual(\i2z9, 0xabcd0109)) {
				err(ts, z177, __LINE__, 0, 0, \i2z9, 0xabcd0109)
			}
		} else {
			if (LNotEqual(i2z9, 0x22223333)) {
				err(ts, z177, __LINE__, 0, 0, i2z9, 0x22223333)
			}
			if (LNotEqual(\i2z9, 0x22223333)) {
				err(ts, z177, __LINE__, 0, 0, \i2z9, 0x22223333)
			}
		}

		Store(0x12345678, i2z9)
		if (LNotEqual(i2z9, 0x12345678)) {
			err(ts, z177, __LINE__, 0, 0, i2z9, 0x12345678)
		}
		if (LNotEqual(\i2z9, 0x12345678)) {
			err(ts, z177, __LINE__, 0, 0, \i2z9, 0x12345678)
		}

		Store(0x22223333, \i2z9)
		if (LNotEqual(i2z9, 0x22223333)) {
			err(ts, z177, __LINE__, 0, 0, i2z9, 0x22223333)
		}
		if (LNotEqual(\i2z9, 0x22223333)) {
			err(ts, z177, __LINE__, 0, 0, \i2z9, 0x22223333)
		}

		if (LNot(arg0)) {
			m000(1)
		}

		if (arg0) {
			if (LNotEqual(i2z9, 0x22223333)) {
				err(ts, z177, __LINE__, 0, 0, i2z9, 0x22223333)
			}
			if (LNotEqual(\i2z9, 0x22223333)) {
				err(ts, z177, __LINE__, 0, 0, \i2z9, 0x22223333)
			}
		} else {
			if (LNotEqual(i2z9, 0x66667777)) {
				err(ts, z177, __LINE__, 0, 0, i2z9, 0x66667777)
			}
			if (LNotEqual(\i2z9, 0x66667777)) {
				err(ts, z177, __LINE__, 0, 0, \i2z9, 0x66667777)
			}
		}

		if (arg0) {
			Store(0x66667777, i2z9)
		} else {
			Store(0x44445555, i2z9)
		}
	}

	CH03(ts, z177, 0x07e, __LINE__, 0)
	m000(0)
	CH03(ts, z177, 0x07f, __LINE__, 0)
}

/*
 * Non-Serialized method provides access to the upper level named object,
 * for the second recursive call too.
 */
Method(m1de,, Serialized)
{
	Name(ts, "m1de")
	Name(i3z0, 0xabcd0000)

	Method(m000, 1)
	{
		if (LNot(arg0)) {
			if (LNotEqual(i3z0, 0xabcd0000)) {
				err(ts, z177, __LINE__, 0, 0, i3z0, 0xabcd0000)
			}
		} else {
			if (LNotEqual(i3z0, 0x12345678)) {
				err(ts, z177, __LINE__, 0, 0, i3z0, 0x12345678)
			}
		}

		Store(0x12345678, i3z0)
		if (LNotEqual(i3z0, 0x12345678)) {
			err(ts, z177, __LINE__, 0, 0, i3z0, 0x12345678)
		}

		if (LNot(arg0)) {
			m000(1)
		}

		if (arg0) {
			if (LNotEqual(i3z0, 0x12345678)) {
				err(ts, z177, __LINE__, 0, 0, i3z0, 0x12345678)
			}
		} else {
			if (LNotEqual(i3z0, 0x66667777)) {
				err(ts, z177, __LINE__, 0, 0, i3z0, 0x66667777)
			}
		}

		if (arg0) {
			Store(0x66667777, i3z0)
		} else {
			Store(0x44445555, i3z0)
		}
	}

	CH03(ts, z177, 0x085, __LINE__, 0)
	m000(0)
	CH03(ts, z177, 0x086, __LINE__, 0)
}

/*
 * Serialized method provides access to the upper level named object,
 * for the second recursive call too.
 */
Method(m1df,, Serialized)
{
	Name(ts, "m1df")
	Name(i3z0, 0xabcd0000)

	Method(m000, 1, Serialized, 7)
	{
		if (LNot(arg0)) {
			if (LNotEqual(i3z0, 0xabcd0000)) {
				err(ts, z177, __LINE__, 0, 0, i3z0, 0xabcd0000)
			}
		} else {
			if (LNotEqual(i3z0, 0x12345678)) {
				err(ts, z177, __LINE__, 0, 0, i3z0, 0x12345678)
			}
		}

		Store(0x12345678, i3z0)
		if (LNotEqual(i3z0, 0x12345678)) {
			err(ts, z177, __LINE__, 0, 0, i3z0, 0x12345678)
		}

		if (LNot(arg0)) {
			m000(1)
		}

		if (arg0) {
			if (LNotEqual(i3z0, 0x12345678)) {
				err(ts, z177, __LINE__, 0, 0, i3z0, 0x12345678)
			}
		} else {
			if (LNotEqual(i3z0, 0x66667777)) {
				err(ts, z177, __LINE__, 0, 0, i3z0, 0x66667777)
			}
		}

		if (arg0) {
			Store(0x66667777, i3z0)
		} else {
			Store(0x44445555, i3z0)
		}
	}

	CH03(ts, z177, 0x08c, __LINE__, 0)
	m000(0)
	CH03(ts, z177, 0x08d, __LINE__, 0)
}

/*
 * Non-Serialized method declares full-path name on first call,
 * and allows proper access for the second recursive call too.
 */
Method(m1ee,, Serialized)
{
	Name(ts, "m1ee")

	Method(m000, 1, Serialized)
	{
		if (LNot(arg0)) {
			Name(\_SB.i0q8, 0xabcd0008)

			if (LNotEqual(\_SB.i0q8, 0xabcd0008)) {
				err(ts, z177, __LINE__, 0, 0, \_SB.i0q8, 0xabcd0008)
			}
		} else {
			if (LNotEqual(\_SB.i0q8, 0x22223333)) {
				err(ts, z177, __LINE__, 0, 0, \_SB.i0q8, 0x22223333)
			}
		}
		Store(0x22223333, \_SB.i0q8)
		if (LNotEqual(\_SB.i0q8, 0x22223333)) {
			err(ts, z177, __LINE__, 0, 0, \_SB.i0q8, 0x22223333)
		}

		if (LNot(arg0)) {
			m000(1)
		}

		if (arg0) {
			if (LNotEqual(\_SB.i0q8, 0x22223333)) {
				err(ts, z177, __LINE__, 0, 0, \_SB.i0q8, 0x22223333)
			}
		} else {
			if (LNotEqual(\_SB.i0q8, 0x66667777)) {
				err(ts, z177, __LINE__, 0, 0, \_SB.i0q8, 0x66667777)
			}
		}
		if (arg0) {
			Store(0x66667777, \_SB.i0q8)
		} else {
			Store(0x44445555, \_SB.i0q8)
		}
	}

	CH03(ts, z177, 0x093, __LINE__, 0)
	m000(0)
	CH03(ts, z177, 0x094, __LINE__, 0)
}

/*
 * Serialized method declares full-path name on first call,
 * and allows proper access for the second recursive call too.
 */
Method(m1ef,, Serialized)
{
	Name(ts, "m1ef")

	Method(m000, 1, Serialized, 7)
	{
		if (LNot(arg0)) {

			Name(\_SB.i0q9, 0xabcd0009)

			if (LNotEqual(\_SB.i0q9, 0xabcd0009)) {
				err(ts, z177, __LINE__, 0, 0, \_SB.i0q9, 0xabcd0009)
			}
		} else {
			if (LNotEqual(\_SB.i0q9, 0x22223333)) {
				err(ts, z177, __LINE__, 0, 0, \_SB.i0q9, 0x22223333)
			}
		}

		Store(0x22223333, \_SB.i0q9)
		if (LNotEqual(\_SB.i0q9, 0x22223333)) {
			err(ts, z177, __LINE__, 0, 0, \_SB.i0q9, 0x22223333)
		}

		if (LNot(arg0)) {
			m000(1)
		}

		if (arg0) {
			if (LNotEqual(\_SB.i0q9, 0x22223333)) {
				err(ts, z177, __LINE__, 0, 0, \_SB.i0q9, 0x22223333)
			}
		} else {
			if (LNotEqual(\_SB.i0q9, 0x66667777)) {
				err(ts, z177, __LINE__, 0, 0, \_SB.i0q9, 0x66667777)
			}
		}

		if (arg0) {
			Store(0x66667777, \_SB.i0q9)
		} else {
			Store(0x44445555, \_SB.i0q9)
		}
	}

	CH03(ts, z177, 0x093, __LINE__, 0)
	m000(0)
	CH03(ts, z177, 0x094, __LINE__, 0)
}

/*
 * Non-Serialized method declares Scope(\_SB) on first call,
 * and allows proper access for the second recursive call too.
 */
Method(m1bf,, Serialized)
{
	Name(ts, "m1bf")

	Method(m000, 1, Serialized)
	{
		if (LNot(arg0)) {

			Scope(\_SB) { Name(i1q8, 0xabcd0008) }

			if (LNotEqual(\_SB.i1q8, 0xabcd0008)) {
				err(ts, z177, __LINE__, 0, 0, \_SB.i1q8, 0xabcd0008)
			}
		} else {
			if (LNotEqual(\_SB.i1q8, 0x22223333)) {
				err(ts, z177, __LINE__, 0, 0, \_SB.i1q8, 0x22223333)
			}
		}

		Store(0x22223333, \_SB.i1q8)
		if (LNotEqual(\_SB.i1q8, 0x22223333)) {
			err(ts, z177, __LINE__, 0, 0, \_SB.i1q8, 0x22223333)
		}

		if (LNot(arg0)) {
			m000(1)
		}

		if (arg0) {
			if (LNotEqual(\_SB.i1q8, 0x22223333)) {
				err(ts, z177, __LINE__, 0, 0, \_SB.i1q8, 0x22223333)
			}
		} else {
			if (LNotEqual(\_SB.i1q8, 0x66667777)) {
				err(ts, z177, __LINE__, 0, 0, \_SB.i1q8, 0x66667777)
			}
		}
		if (arg0) {
			Store(0x66667777, \_SB.i1q8)
		} else {
			Store(0x44445555, \_SB.i1q8)
		}
	}

	CH03(ts, z177, 0x09a, __LINE__, 0)
	m000(0)
	CH03(ts, z177, 0x09b, __LINE__, 0)
}

/*
 * Serialized method declares Scope(\_SB) on first call,
 * and allows proper access for the second recursive call too.
 */
Method(m1dd,, Serialized)
{
	Name(ts, "m1dd")

	Method(m000, 1, Serialized, 7)
	{
		if (LNot(arg0)) {

			Scope(\_SB) { Name(i1q9, 0xabcd0008) }

			if (LNotEqual(\_SB.i1q9, 0xabcd0008)) {
				err(ts, z177, __LINE__, 0, 0, \_SB.i1q9, 0xabcd0008)
			}
		} else {
			if (LNotEqual(\_SB.i1q9, 0x22223333)) {
				err(ts, z177, __LINE__, 0, 0, \_SB.i1q9, 0x22223333)
			}
		}

		Store(0x22223333, \_SB.i1q9)
		if (LNotEqual(\_SB.i1q9, 0x22223333)) {
			err(ts, z177, __LINE__, 0, 0, \_SB.i1q9, 0x22223333)
		}

		if (LNot(arg0)) {
			m000(1)
		}

		if (arg0) {
			if (LNotEqual(\_SB.i1q9, 0x22223333)) {
				err(ts, z177, __LINE__, 0, 0, \_SB.i1q9, 0x22223333)
			}
		} else {
			if (LNotEqual(\_SB.i1q9, 0x66667777)) {
				err(ts, z177, __LINE__, 0, 0, \_SB.i1q9, 0x66667777)
			}
		}
		if (arg0) {
			Store(0x66667777, \_SB.i1q9)
		} else {
			Store(0x44445555, \_SB.i1q9)
		}
	}

	CH03(ts, z177, 0x0a1, __LINE__, 0)
	m000(0)
	CH03(ts, z177, 0x0a2, __LINE__, 0)
}


/*
 * Non-Serialized method declares Scope(\) on first call,
 * and allows proper access for the second recursive call too.
 */
Method(m277,, Serialized)
{
	Name(ts, "m277")

	Method(m000, 1, Serialized)
	{
		if (LNot(arg0)) {

			Scope(\) { Name(i3z1, 0xabcd0208) }

			if (LNotEqual(i3z1, 0xabcd0208)) {
				err(ts, z177, __LINE__, 0, 0, i3z1, 0xabcd0208)
			}
			if (LNotEqual(\i3z1, 0xabcd0208)) {
				err(ts, z177, __LINE__, 0, 0, \i3z1, 0xabcd0208)
			}
		} else {
			if (LNotEqual(i3z1, 0x22223333)) {
				err(ts, z177, __LINE__, 0, 0, i3z1, 0x22223333)
			}
			if (LNotEqual(\i3z1, 0x22223333)) {
				err(ts, z177, __LINE__, 0, 0, \i3z1, 0x22223333)
			}
		}

		Store(0x12345678, i3z1)
		if (LNotEqual(i3z1, 0x12345678)) {
			err(ts, z177, __LINE__, 0, 0, i3z1, 0x12345678)
		}
		if (LNotEqual(\i3z1, 0x12345678)) {
			err(ts, z177, __LINE__, 0, 0, \i3z1, 0x12345678)
		}

		Store(0x22223333, \i3z1)
		if (LNotEqual(i3z1, 0x22223333)) {
			err(ts, z177, __LINE__, 0, 0, i3z1, 0x22223333)
		}
		if (LNotEqual(\i3z1, 0x22223333)) {
			err(ts, z177, __LINE__, 0, 0, \i3z1, 0x22223333)
		}

		if (LNot(arg0)) {
			m000(1)
		}

		if (arg0) {
			if (LNotEqual(i3z1, 0x22223333)) {
				err(ts, z177, __LINE__, 0, 0, i3z1, 0x22223333)
			}
			if (LNotEqual(\i3z1, 0x22223333)) {
				err(ts, z177, __LINE__, 0, 0, \i3z1, 0x22223333)
			}
		} else {
			if (LNotEqual(i3z1, 0x66667777)) {
				err(ts, z177, __LINE__, 0, 0, i3z1, 0x66667777)
			}
			if (LNotEqual(\i3z1, 0x66667777)) {
				err(ts, z177, __LINE__, 0, 0, \i3z1, 0x66667777)
			}
		}

		if (arg0) {
			Store(0x66667777, i3z1)
		} else {
			Store(0x44445555, i3z1)
		}
	}

	CH03(ts, z177, 0x070, __LINE__, 0)
	m000(0)
	CH03(ts, z177, 0x071, __LINE__, 0)
}

/*
 * Serialized method declares Scope(\) on first call,
 * and allows proper access for the second recursive call too.
 */
Method(m27d,, Serialized)
{
	Name(ts, "m27d")

	Method(m000, 1, Serialized, 7)
	{
		if (LNot(arg0)) {

			Scope(\) { Name(i3z2, 0xabcd0209) }

			if (LNotEqual(i3z2, 0xabcd0209)) {
				err(ts, z177, __LINE__, 0, 0, i3z2, 0xabcd0209)
			}
			if (LNotEqual(\i3z2, 0xabcd0209)) {
				err(ts, z177, __LINE__, 0, 0, \i3z2, 0xabcd0209)
			}
		} else {
			if (LNotEqual(i3z2, 0x22223333)) {
				err(ts, z177, __LINE__, 0, 0, i3z2, 0x22223333)
			}
			if (LNotEqual(\i3z2, 0x22223333)) {
				err(ts, z177, __LINE__, 0, 0, \i3z2, 0x22223333)
			}
		}

		Store(0x12345678, i3z2)
		if (LNotEqual(i3z2, 0x12345678)) {
			err(ts, z177, __LINE__, 0, 0, i3z2, 0x12345678)
		}
		if (LNotEqual(\i3z2, 0x12345678)) {
			err(ts, z177, __LINE__, 0, 0, \i3z2, 0x12345678)
		}

		Store(0x22223333, \i3z2)
		if (LNotEqual(i3z2, 0x22223333)) {
			err(ts, z177, __LINE__, 0, 0, i3z2, 0x22223333)
		}
		if (LNotEqual(\i3z2, 0x22223333)) {
			err(ts, z177, __LINE__, 0, 0, \i3z2, 0x22223333)
		}

		if (LNot(arg0)) {
			m000(1)
		}

		if (arg0) {
			if (LNotEqual(i3z2, 0x22223333)) {
				err(ts, z177, __LINE__, 0, 0, i3z2, 0x22223333)
			}
			if (LNotEqual(\i3z2, 0x22223333)) {
				err(ts, z177, __LINE__, 0, 0, \i3z2, 0x22223333)
			}
		} else {
			if (LNotEqual(i3z2, 0x66667777)) {
				err(ts, z177, __LINE__, 0, 0, i3z2, 0x66667777)
			}
			if (LNotEqual(\i3z2, 0x66667777)) {
				err(ts, z177, __LINE__, 0, 0, \i3z2, 0x66667777)
			}
		}

		if (arg0) {
			Store(0x66667777, i3z2)
		} else {
			Store(0x44445555, i3z2)
		}
	}

	CH03(ts, z177, 0x07e, __LINE__, 0)
	m000(0)
	CH03(ts, z177, 0x07f, __LINE__, 0)
}


Method(m0ed)
{

/*
SRMT("m0ff-1")
m0ff(1)
return

SRMT("m1ee")
m1ee()

SRMT("m1ef")
m1ef()

return
*/

	SRMT("m0ef")
	if (y300) {
		m0ef()
	} else {
		BLCK()
	}

	SRMT("m0fb")
	if (y300) {
		m0fb()
	} else {
		BLCK()
	}

	SRMT("m0ff-0")
	if (y300) {
		m0ff(0)
	} else {
		BLCK()
	}

	SRMT("m0ff-1")
	if (LAnd(y300, y200)) {
		m0ff(1)
	} else {
		BLCK()
	}

	SRMT("m18a-0")
	m18a(0)

	SRMT("m18a-1")
	if (LAnd(y300, y200)) {
		m18a(1)
	} else {
		BLCK()
	}

	SRMT("m18b-0")
	m18b(0)

	SRMT("m18b-1")
	if (LAnd(y300, y200)) {
		m18b(1)
	} else {
		BLCK()
	}

	SRMT("m18d")
	m18d()

	SRMT("m18e")
	m18e()

	SRMT("m18f")
	m18f()

	SRMT("m19a")
	m19a()

	SRMT("m19b")
	m19b()

	SRMT("m19c")
	if (LOr(y301, LNot(y902))) {
		m19c()
	} else {
		BLCK()
	}

	SRMT("m19d")
	m19d()

	SRMT("m19e")
	m19e()

	SRMT("m19f")
	m19f()

	SRMT("m1b8")
	m1b8()

	SRMT("m1b9")
	m1b9()

	SRMT("m1ba")
	m1ba()

	SRMT("m1bb")
	m1bb()

	SRMT("m1bc")
	m1bc()

	SRMT("m1bd")
	m1bd()

	SRMT("m1be")
	m1be()

	SRMT("m1de")
	m1de()

	SRMT("m1df")
	m1df()

	SRMT("m1ee")
	m1ee()

	SRMT("m1ef")
	m1ef()

	SRMT("m1bf")
	m1bf()

	SRMT("m1dd")
	m1dd()

	SRMT("m277")
	if (y200) {
		m277()
	} else {
		BLCK()
	}

	SRMT("m27d")
	if (y200) {
		m27d()
	} else {
		BLCK()
	}
}
