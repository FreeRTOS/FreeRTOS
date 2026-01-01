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
 * Test of Impllicit Return
 *
 * The last operation of Methods is Store.
 */

Name(z138, 138)

Method(mf6c,, Serialized)
{
	Name(fl00, 0)
	Name(i000, 0xabcd0000)
	Name(i001, 0xabcd0001)

	Method(m000)
	{
		Store(0xabcd0002, i001)
		if (fl00) {
			Store(0xdddd0000, i001)
			Return (0)
		}
	}

	Method(m001)
	{
		if (fl00) {
			Store(0xdddd0001, i001)
			Return (0)
		}
		Store(0xabcd0003, i001)
	}

	Method(m002, 1)
	{
		if (fl00) {
			Store(0xdddd0002, i001)
			Return (0)
		}
		if (fl00) {
			Return (0)
		}
		if (arg0) {
			Store(0xabcd0004, i001)
		}
	}

	Method(m003, 1)
	{
		if (fl00) {
			Store(0xdddd0003, i001)
			Return (0)
		}
		if (fl00) {
			Return (0)
		}
		if (arg0) {
			Store(0xabcd0005, i001)
		} else {
			Store(0xabcd0006, i001)
		}
	}

	Method(m004, 1)
	{
		if (fl00) {
			Return (0)
		}

		switch (arg0) {
			case (0) {
				Store(0xabcd0007, i001)
			}
			case (0x12345678) {
				Store(0xabcd0008, i001)
			}
			default {
				Store(0xabcd0009, i001)
			}
		}
	}

	Method(m005)
	{
		if (fl00) {
			Return (0)
		}

		While (1) {
			Store(0xabcd000a, i001)
			Break
		}
	}

	Method(m006)
	{
		if (fl00) {
			Return (0)
		}

		Store(0xabcd000b, i001)
		While (1) {
			Break
		}
	}

	Method(m007,, Serialized)
	{
		Name(i000, 0)
		Name(num, 0)
		Name(lpN0, 0)
		Name(lpC0, 0)

		Store(10, num)

		Store(num, lpN0)
		Store(0, lpC0)

		if (fl00) {
			Return (0)
		}

		While (lpN0) {
			if (i000) {
				Break
			}
			Decrement(lpN0)
			Increment(lpC0)
			Store(1, i000)
			Store(0xabcd000c, i001)
			Continue
		}
	}

	Method(m008)
	{
		Method(m000)
		{
			Store(0xabcd000d, i001)
		}

		if (fl00) {
			Return (0)
		}

		m000()
	}


	// m000

	Store(0xabcd9000, i000)

	CH03("", z138, 0x000, __LINE__, 0)

	Store(m000(), i000)

	if (SLCK) {
		CH03("", z138, 0x001, __LINE__, 0)
		if (y901) {
			Store(0, Local0)
		} else {
			Store(0xabcd0002, Local0)
		}
		if (LNotEqual(i000, Local0)) {
			err("", z138, __LINE__, 0, 0, i000, Local0)
		}
	} else {
		CH04("", 0, 0xff, z138, __LINE__, 0, 0)
	}

	// m001

	Store(0xabcd9001, i000)

	CH03("", z138, 0x004, __LINE__, 0)

	Store(m001(), i000)

	if (SLCK) {
		CH03("", z138, 0x005, __LINE__, 0)
		if (LNotEqual(i000, 0xabcd0003)) {
			err("", z138, __LINE__, 0, 0, i000, 0xabcd0003)
		}
	} else {
		CH04("", 0, 0xff, z138, __LINE__, 0, 0)
	}

	// m002

	Store(0xabcd9002, i000)

	CH03("", z138, 0x008, __LINE__, 0)

	Store(m002(1), i000)

	if (SLCK) {
		CH03("", z138, 0x009, __LINE__, 0)
		if (LNotEqual(i000, 0xabcd0004)) {
			err("", z138, __LINE__, 0, 0, i000, 0xabcd0004)
		}
	} else {
		CH04("", 0, 0xff, z138, __LINE__, 0, 0)
	}

	// m003

	Store(0xabcd9003, i000)

	CH03("", z138, 0x00c, __LINE__, 0)

	Store(m003(0), i000)

	if (SLCK) {
		CH03("", z138, 0x00d, __LINE__, 0)
		if (LNotEqual(i000, 0xabcd0006)) {
			err("", z138, __LINE__, 0, 0, i000, 0xabcd0006)
		}
	} else {
		CH04("", 0, 0xff, z138, __LINE__, 0, 0)
	}

	// m004(0)

	Store(0xabcd9004, i000)

	CH03("", z138, 0x010, __LINE__, 0)

	Store(m004(0), i000)

	if (SLCK) {
		CH03("", z138, 0x011, __LINE__, 0)
		if (LNotEqual(i000, 0xabcd0007)) {
			err("", z138, __LINE__, 0, 0, i000, 0xabcd0007)
		}
	} else {
		CH04("", 0, 0xff, z138, __LINE__, 0, 0)
	}

	// m004(0x12345678)

	Store(0xabcd9005, i000)

	CH03("", z138, 0x014, __LINE__, 0)

	Store(m004(0x12345678), i000)

	if (SLCK) {
		CH03("", z138, 0x015, __LINE__, 0)
		if (LNotEqual(i000, 0xabcd0008)) {
			err("", z138, __LINE__, 0, 0, i000, 0xabcd0008)
		}
	} else {
		CH04("", 0, 0xff, z138, __LINE__, 0, 0)
	}

	// m004(Default)

	Store(0xabcd9006, i000)

	CH03("", z138, 0x018, __LINE__, 0)

	Store(m004(1111), i000)

	if (SLCK) {
		CH03("", z138, 0x019, __LINE__, 0)
		if (LNotEqual(i000, 0xabcd0009)) {
			err("", z138, __LINE__, 0, 0, i000, 0xabcd0009)
		}
	} else {
		CH04("", 0, 0xff, z138, __LINE__, 0, 0)
	}

	// m005

	Store(0xabcd9007, i000)

	CH03("", z138, 0x01c, __LINE__, 0)

	Store(m005(), i000)

	if (SLCK) {
		CH03("", z138, 0x01d, __LINE__, 0)
		if (LNotEqual(i000, 0xabcd000a)) {
			err("", z138, __LINE__, 0, 0, i000, 0xabcd000a)
		}
	} else {
		CH04("", 0, 0xff, z138, __LINE__, 0, 0)
	}

	// m006

	Store(0xabcd9008, i000)

	CH03("", z138, 0x020, __LINE__, 0)

	Store(m006(), i000)

	if (SLCK) {
		CH03("", z138, 0x021, __LINE__, 0)
		if (y901) {
			Store(1, Local0)
		} else {
			Store(0xabcd000b, Local0)
		}
		if (LNotEqual(i000, Local0)) {
			err("", z138, __LINE__, 0, 0, i000, Local0)
		}
	} else {
		CH04("", 0, 0xff, z138, __LINE__, 0, 0)
	}

	// m007

	Store(0xabcd9009, i000)

	CH03("", z138, 0x024, __LINE__, 0)

	Store(m007(), i000)

	if (SLCK) {
		CH03("", z138, 0x025, __LINE__, 0)
		if (y901) {
			Store(1, Local0)
		} else {
			Store(0xabcd000c, Local0)
		}
		if (LNotEqual(i000, Local0)) {
			err("", z138, __LINE__, 0, 0, i000, Local0)
		}
	} else {
		CH04("", 0, 0xff, z138, __LINE__, 0, 0)
	}

	// m008

	Store(0xabcd900a, i000)

	CH03("", z138, 0x028, __LINE__, 0)

	Store(m008(), i000)

	if (SLCK) {
		CH03("", z138, 0x029, __LINE__, 0)
		if (LNotEqual(i000, 0xabcd000d)) {
			err("", z138, __LINE__, 0, 0, i000, 0xabcd000d)
		}
	} else {
		CH04("", 0, 0xff, z138, __LINE__, 0, 0)
	}
}

Method(mf6e,, Serialized)
{
	Name(fl00, 0)
	Name(i000, 0xaaaa0000)
	Name(i001, 0xaaaa0001)
	Name(i002, 0xaaaa0002)
	Name(i003, 0xaaaa0003)

	Method(m000)
	{
		if (fl00) {
			Return (0)
		}
		Increment(i002)
		Store(Add(0xaaaa0003, 0), Local1)
		Store(Subtract(0xaaaa0004, 0), Local1)
		Store(Multiply(0xaaaa0005, 1), Local1)
		Store(0xaaaa0006, i001)
	}

	Method(m001)
	{
		if (fl00) {
			Return (0)
		}
		if (Store(0xaaaa0007, i001)) {
			Increment(i002)
			Store(Add(0xaaaa0008, 0), Local1)
			Store(Subtract(0xaaaa0009, 0), Local1)
			Store(Multiply(0xaaaa000a, 1), Local1)
			Store(0xaaaa000d, i001)
			Decrement(i001)
		}
	}

	Method(m002)
	{
		if (fl00) {
			Return (0)
		}
		if (Add(0xaaaa000d, 0)) {
		if (0xaaaa000e) {
			Increment(i002)
			Store(Add(0xaaaa000f, 0), Local1)
			Store(Subtract(0xaaaa0010, 0), Local1)
			Store(Multiply(0xaaaa0011, 1), Local1)
			Store(0xaaaa0012, i001)
			Increment(i001)
		}}
	}

	Method(m003)
	{
		if (fl00) {
			Return (0)
		}
		while (Subtract(0xaaaa0014, 0)) {
			Increment(i002)
			Store(Add(0xaaaa0015, 0), Local1)
			Store(Subtract(0xaaaa0016, 0), Local1)
			Store(Multiply(0xaaaa0017, 1), Local1)
			Store(0xaaaa0018, i001)
			Store(Multiply(0xaaaa0019, 1), Local1)
			Break
		}
	}

	Method(m004)
	{
		if (fl00) {
			Return (0)
		}
		switch (Multiply(0xaaaa001a, 1)) {
			case (0) {
				Store(0xaaaa001b, i001)
			}
			case (0xaaaa001a) {
				Store(0xaaaa001c, i001)
			}
			default {
				Store(0xaaaa001d, i001)
			}
		}
	}

	// Predicates of If


	Method(m006)
	{
		if (fl00) {
			return (0xabcd0000)
		}
	}

	Method(m007)
	{
		if (0) {
			return (0xabcd0000)
		}
	}

	Method(m008)
	{
		if (0) {
			return (0xabcd0001)
		}
		if (0xabcd0000) {
		}
	}

	Method(m009,, Serialized)
	{
		Name(i000, 0xabcd0000)

		if (0) {
			return (0xabcd0001)
		}
		if (i000) {
		}
	}

	Name(i004, 0xabcd0008)

	Method(m00a)
	{
		if (0) {
			return (0xabcd0001)
		}
		if (i004) {
		}
	}

	Method(m00b)
	{
		if (0) {
			return (0xabcd0005)
		}
		if (LEqual(0xabcd0008, i004)) {
		}
	}

	Method(m00c)
	{
		if (0) {
			return (0xabcd0005)
		}
		if (LEqual(0xabcd0009, i004)) {
		}
	}

	// Predicates of While

	Method(m00d)
	{
		if (0) {
			return (0xabcd0005)
		}
		While (0xabcd0009) {
			Break
		}
	}

	Method(m00e)
	{
		if (0) {
			return (0xabcd0005)
		}
		While (LEqual(0xabcd0008, i004)) {
			Break
		}
	}

	Method(m00f)
	{
		if (0) {
			return (0xabcd0005)
		}
		While (LEqual(0xabcd0009, i004)) {
			Break
		}
	}

	Method(m010)
	{
		if (0) {
			return (0xabcd0005)
		}
		While (i004) {
			Break
		}
	}

	// Predicates of Switch

	Method(m011)
	{
		if (0) {
			return (0xabcd0005)
		}
		Switch (0xabcd0009) {
			Case (0xabcd0007) {
			}
			Case (0xabcd0008) {
			}
		}
	}

	Method(m012)
	{
		if (0) {
			return (0xabcd0005)
		}
		Switch (0xabcd0009) {
			Case (0xabcd0007) {
			}
			Case (0xabcd0009) {
			}
			Case (0xabcd0008) {
			}
		}
	}

	Name(i006, 0x11220000)
	Name(i007, 0x33440000)

	Method(m005, 1, Serialized)
	{
          Name(r001, 1)
          Name(r002, 1)
          Name(r003, 1)
          Name(brk0, 0)
          Name(tmp0, 0)

          if (LEqual(arg0, 1)) {
              Store(0, r001)
          }
          if (LEqual(arg0, 2)) {
              Store(0, r002)
              Store(i006, brk0)
          }
          if (LEqual(arg0, 3)) {
              Store(0, r003)
              Store(i007, brk0)
          }

          Store(0xdddd0000, i000)
          CH03("", z138, 0x02c, __LINE__, 0)
          Store(m000(), i000)
          if (SLCK) {
              CH03("", z138, 0x02d, __LINE__, 0)
              Store(0xaaaa0006, Local0)
              if (LNotEqual(i000, Local0)) {
                  err("", z138, __LINE__, 0, 0, i000, Local0)
              }
          } else {
              CH04("", 0, 0xff, z138, __LINE__, 0, 0)
          }

          Store(0xdddd0000, i000)
          CH03("", z138, 0x030, __LINE__, 0)
          Store(m001(), i000)
          if (SLCK) {
              CH03("", z138, 0x031, __LINE__, 0)
              Store(0xaaaa000c, Local0)
              if (LNotEqual(i000, Local0)) {
                  err("", z138, __LINE__, 0, 0, i000, Local0)
              }
          } else {
              CH04("", 0, 0xff, z138, __LINE__, 0, 0)
          }

          Store(0xdddd0000, i000)
          CH03("", z138, 0x034, __LINE__, 0)
          Store(m002(), i000)
          if (SLCK) {
              CH03("", z138, 0x035, __LINE__, 0)
              Store(0xaaaa0013, Local0)
              if (LNotEqual(i000, Local0)) {
                  err("", z138, __LINE__, 0, 0, i000, Local0)
              }
          } else {
              CH04("", 0, 0xff, z138, __LINE__, 0, 0)
          }

          Store(0xdddd0000, i000)
          CH03("", z138, 0x038, __LINE__, 0)
          Store(m003(), i000)
          if (SLCK) {
              CH03("", z138, 0x039, __LINE__, 0)
              Store(0xaaaa0019, Local0)
              if (LNotEqual(i000, Local0)) {
                  err("", z138, __LINE__, 0, 0, i000, Local0)
              }
          } else {
              CH04("", 0, 0xff, z138, __LINE__, 0, 0)
          }


		// Predicates


          Store(0xdddd0000, i000)
          CH03("", z138, 0x03c, __LINE__, 0)
          Store(m006(), i000)
          if (LAnd(SLCK, y901)) {
              CH03("", z138, 0x03d, __LINE__, 0)
              Store(0, Local0)
              if (LNotEqual(i000, Local0)) {
                  err("", z138, __LINE__, 0, 0, i000, Local0)
              }
          } else {
              CH04("", 0, 0xff, z138, __LINE__, 0, 0)
          }

          Store(0xdddd0000, i000)
          CH03("", z138, 0x040, __LINE__, 0)
          Store(m007(), i000)
          if (LAnd(SLCK, y901)) {
              CH03("", z138, 0x041, __LINE__, 0)
              Store(0, Local0)
              if (LNotEqual(i000, Local0)) {
                  err("", z138, __LINE__, 0, 0, i000, Local0)
              }
          } else {
              CH04("", 0, 0xff, z138, __LINE__, 0, 0)
          }

          Store(0xdddd0000, i000)
          CH03("", z138, 0x044, __LINE__, 0)
          Store(m008(), i000)
          if (LAnd(SLCK, y901)) {
              CH03("", z138, 0x045, __LINE__, 0)
              Store(0xabcd0000, Local0)
              if (LNotEqual(i000, Local0)) {
                  err("", z138, __LINE__, 0, 0, i000, Local0)
              }
          } else {
              CH04("", 0, 0xff, z138, __LINE__, 0, 0)
          }

          Store(0xdddd0000, i000)
          CH03("", z138, 0x048, __LINE__, 0)
          Store(m009(), i000)
          if (LAnd(SLCK, y901)) {
              CH03("", z138, 0x049, __LINE__, 0)
              Store(0xabcd0000, Local0)
              if (LNotEqual(i000, Local0)) {
                  err("", z138, __LINE__, 0, 0, i000, Local0)
              }
          } else {
              CH04("", 0, 0xff, z138, __LINE__, 0, 0)
          }

          Store(0xdddd0000, i000)
          CH03("", z138, 0x04c, __LINE__, 0)
          Store(m00a(), i000)
          if (LAnd(SLCK, y901)) {
              CH03("", z138, 0x04d, __LINE__, 0)
              Store(0xabcd0008, Local0)
              if (LNotEqual(i000, Local0)) {
                  err("", z138, __LINE__, 0, 0, i000, Local0)
              }
          } else {
              CH04("", 0, 0xff, z138, __LINE__, 0, 0)
          }

          Store(0, tmp0)
          if (LAnd(SLCK, LOr(y901, y263))) {
              Store(1, tmp0)
          }
          Store(0xdddd0000, i000)
          CH03("", z138, 0x050, __LINE__, 0)
          Store(m00b(), i000)
          if (tmp0) {
              CH03("", z138, 0x051, __LINE__, 0)
              // Oct 2013, David Box
              // Implicit return for logical operations (LNot, LEqual, ...)
              // returns logical value of the operation
              Store(Ones, Local0)
              if (LNotEqual(i000, Local0)) {
                  err("", z138, __LINE__, 0, 0, i000, Local0)
              }
          } else {
              CH04("", 0, 0xff, z138, __LINE__, 0, 0)
          }

          Store(0, tmp0)
          if (LAnd(SLCK, LOr(y901, y263))) {
              Store(1, tmp0)
          }
          Store(0xdddd0000, i000)
          CH03("", z138, 0x054, __LINE__, 0)
          Store(m00c(), i000)
          if (tmp0) {
              CH03("", z138, 0x055, __LINE__, 0)
              // Oct 2013, David Box
              // Implicit return for logical operations (LNot, LEqual, ...)
              // returns logical value of the operation
              Store(Zero, Local0)
              if (LNotEqual(i000, Local0)) {
                  err("", z138, __LINE__, 0, 0, i000, Local0)
              }
          } else {
              CH04("", 0, 0xff, z138, __LINE__, 0, 0)
          }

          Store(0xdddd0000, i000)
          CH03("", z138, 0x058, __LINE__, 0)
          Store(m00d(), i000)
          if (LAnd(SLCK, y901)) {
              CH03("", z138, 0x059, __LINE__, 0)
              Store(0xabcd0009, Local0)
              if (LNotEqual(i000, Local0)) {
                  err("", z138, __LINE__, 0, 0, i000, Local0)
              }
          } else {
              CH04("", 0, 0xff, z138, __LINE__, 0, 0)
          }

          Store(0, tmp0)
          if (LAnd(SLCK, LOr(y901, y263))) {
              Store(1, tmp0)
          }
          Store(0xdddd0000, i000)
          CH03("", z138, 0x05c, __LINE__, 0)
          Store(m00e(), i000)
          if (tmp0) {
              CH03("", z138, 0x05d, __LINE__, 0)
              // Oct 2013, David Box
              // Implicit return for logical operations (LNot, LEqual, ...)
              // returns logical value of the operation
              Store(Ones, Local0)
              if (LNotEqual(i000, Local0)) {
                  err("", z138, __LINE__, 0, 0, i000, Local0)
              }
          } else {
              CH04("", 0, 0xff, z138, __LINE__, 0, 0)
          }

          Store(0, tmp0)
          if (LAnd(SLCK, LOr(y901, y263))) {
              Store(1, tmp0)
          }
          Store(0xdddd0000, i000)
          CH03("", z138, 0x060, __LINE__, 0)
          Store(m00f(), i000)
          if (tmp0) {
              CH03("", z138, 0x061, __LINE__, 0)
              // Oct 2013, David Box
              // Implicit return for logical operations (LNot, LEqual, ...)
              // returns logical value of the operation
              Store(Zero, Local0)
              if (LNotEqual(i000, Local0)) {
                  err("", z138, __LINE__, 0, 0, i000, Local0)
              }
          } else {
              CH04("", 0, 0xff, z138, __LINE__, 0, 0)
          }

          Store(0xdddd0000, i000)
          CH03("", z138, 0x064, __LINE__, 0)
          Store(m010(), i000)
          if (LAnd(SLCK, y901)) {
              CH03("", z138, 0x065, __LINE__, 0)
              Store(0xabcd0008, Local0)
              if (LNotEqual(i000, Local0)) {
                  err("", z138, __LINE__, 0, 0, i000, Local0)
              }
          } else {
              CH04("", 0, 0xff, z138, __LINE__, 0, 0)
          }

          if (y901) {

          Store(0xdddd0000, i000)
          CH03("", z138, 0x068, __LINE__, 0)
          Store(m011(), i000)
          if (LAnd(SLCK, y901)) {
              CH03("", z138, 0x069, __LINE__, 0)
              Store(Zero, Local0)
              if (LNotEqual(i000, Local0)) {
                  err("", z138, __LINE__, 0, 0, i000, Local0)
              }
          } else {
              CH04("", 0, 0xff, z138, __LINE__, 0, 0)
          }

          Store(0xdddd0000, i000)
          CH03("", z138, 0x06c, __LINE__, 0)
          Store(m012(), i000)
          if (LAnd(SLCK, y901)) {
              CH03("", z138, 0x06d, __LINE__, 0)
              Store(Ones, Local0)
              if (LNotEqual(i000, Local0)) {
                  err("", z138, __LINE__, 0, 0, i000, Local0)
              }
          } else {
              CH04("", 0, 0xff, z138, __LINE__, 0, 0)
          }
          } /* if (y901) */

		// Should be the last

          Store(0xdddd0000, i000)
          CH03("", z138, 0x070, __LINE__, 0)
          Store(m004(), i000)
          if (SLCK) {
              CH03("", z138, 0x071, __LINE__, 0)
              Store(0xaaaa001c, Local0)
              if (LNotEqual(i000, Local0)) {
                  err("", z138, __LINE__, 0, 0, i000, Local0)
              }
          } else {
              CH04("", 0, 0xff, z138, __LINE__, 0, 0)
          }


          if (r001) {

          while (0xabcd0000) {
            m000()
            m001()
            m002()
            m003()
            m004()
            if (0xabcd0001) {
              while (0xabcd0002) {
                if (0xabcd0003) {
                  while (0xabcd0004) {
                    if (0xabcd0005) {
                      while (0xabcd0006) {
                        if (0xabcd0007) {

                          Store(0xdddd0000, i000)
                          CH03("", z138, 0x040, __LINE__, 0)
                          Store(m000(), i000)

                          if (r002) {

                          if (SLCK) {
                              CH03("", z138, 0x041, __LINE__, 0)
                              if (LNotEqual(i000, 0xaaaa0006)) {
                                  err("", z138, __LINE__, 0, 0, i000, 0xaaaa0006)
                              }
                          } else {
                              CH04("", 0, 0xff, z138, __LINE__, 0, 0)
                          }

                          Store(0xdddd0000, i000)
                          CH03("", z138, 0x044, __LINE__, 0)
                          Store(m001(), i000)
                          if (SLCK) {
                              CH03("", z138, 0x045, __LINE__, 0)
                              if (LNotEqual(i000, 0xaaaa000c)) {
                                  err("", z138, __LINE__, 0, 0, i000, 0xaaaa000c)
                              }
                          } else {
                              CH04("", 0, 0xff, z138, __LINE__, 0, 0)
                          }

                          Store(0xdddd0123, i000)

                          if (r003) {

                          CH03("", z138, 0x048, __LINE__, 0)
                          Store(m002(), i000)
                          if (SLCK) {
                              CH03("", z138, 0x049, __LINE__, 0)
                              if (LNotEqual(i000, 0xaaaa0013)) {
                                  err("", z138, __LINE__, 0, 0, i000, 0xaaaa0013)
                              }
                          } else {
                              CH04("", 0, 0xff, z138, __LINE__, 0, 0)
                          }

                          Store(0xdddd0000, i000)
                          CH03("", z138, 0x04c, __LINE__, 0)
                          Store(m003(), i000)
                          if (SLCK) {
                              CH03("", z138, 0x04d, __LINE__, 0)
                              if (LNotEqual(i000, 0xaaaa0019)) {
                                  err("", z138, __LINE__, 0, 0, i000, 0xaaaa0019)
                              }
                          } else {
                              CH04("", 0, 0xff, z138, __LINE__, 0, 0)
                          }

                          Store(0xdddd0000, i000)
                          CH03("", z138, 0x050, __LINE__, 0)
                          Store(m004(), i000)
                          if (SLCK) {
                              CH03("", z138, 0x051, __LINE__, 0)
                              if (LNotEqual(i000, 0xaaaa001c)) {
                                  err("", z138, __LINE__, 0, 0, i000, 0xaaaa001c)
                              }
                          } else {
                              CH04("", 0, 0xff, z138, __LINE__, 0, 0)
                          }

                          while (0xabcd0008) {
                            if (0xabcd0009) {
                              while (0xabcd000a) {
                                if (0xabcd000b) {
                                  while (0xabcd000c) {
                                    if (0xabcd000d) {
                                      while (0xabcd000e) {
                                        if (0xabcd000f) {

                                            if (0) {
                                              Store("Impossible 0", Debug)
                                            } else {
                                              if (0xabcd0010) {
                                                  return (0xabcd0030)
                                              }
                                            }
                     }}}}
                     m000()
                     m001()
                     m002()
                     m003()
                     m004()
              }}}}
              m000()
              m001()
              m002()
              m003()
              m004()
              } else {
                  Break
              } /* r003 */
              } else {
                  Break
              } /* r002 */
            }
            if (brk0) {
                  Break
            }
            }}
            if (brk0) {
                  Break
            }
            }}
            if (brk0) {
                  Break
            }
            }}
            if (brk0) {
                  Break
            }
            }
          } /* if (r001) */
	}

	// 0000

	Store(0xdddd0000, i003)
	CH03("", z138, 0x054, __LINE__, 0)
	Store(m005(0), i003)
	if (SLCK) {
		CH03("", z138, 0x055, __LINE__, 0)
		if (LNotEqual(i003, 0xabcd0030)) {
			err("", z138, __LINE__, 0, 0, i003, 0xabcd0030)
		}
	} else {
		CH03("", z138, 0x057, __LINE__, 0)
	}

	// r001

	Store(0xdddd0000, i003)
	CH03("", z138, 0x058, __LINE__, 0)
	Store(m005(1), i003)
	if (SLCK) {
		CH03("", z138, 0x059, __LINE__, 0)
		if (y901) {
			Store(0, Local0)
		} else {
			Store(Ones, Local0)
		}
		if (LNotEqual(i003, Local0)) {
			err("", z138, __LINE__, 0, 0, i003, Local0)
		}
	} else {
		CH04("", 0, 0xff, z138, __LINE__, 0, 0)
	}

	// r002

	Store(0xdddd0000, i003)
	CH03("", z138, 0x05c, __LINE__, 0)
	Store(m005(2), i003)
	if (SLCK) {
		CH03("", z138, 0x05d, __LINE__, 0)
		if (y901) {
			Store(i006, Local0)
		} else {
			Store(0xaaaa0006, Local0)
		}
		if (LNotEqual(i003, Local0)) {
			err("", z138, __LINE__, 0, 0, i003, Local0)
		}
	} else {
		CH04("", 0, 0xff, z138, __LINE__, 0, 0)
	}

	// r003

	Store(0xdddd0000, i003)
	CH03("", z138, 0x060, __LINE__, 0)
	Store(m005(3), i003)
	if (SLCK) {
		CH03("", z138, 0x061, __LINE__, 0)
		if (y901) {
			Store(i007, Local0)
		} else {
			Store(0xdddd0123, Local0)
		}
		if (LNotEqual(i003, Local0)) {
			err("", z138, __LINE__, 0, 0, i003, Local0)
		}
	} else {
		CH04("", 0, 0xff, z138, __LINE__, 0, 0)
	}
}

// Reproduces specific implicit return conditions
Method(mff1,, Serialized)
{
	Name(fl00, 0)
	Name(i000, 0)
	Name(i001, 0)
	Name(i002, 0)
	Name(i003, 0)
	Name(i004, 0)
	Name(i005, 0)
	Name(i006, 0)
	Name(i007, 0)
	Name(i008, 0)

    Method (m000, 1)
    {
		if (fl00) {
			Return ("m000")
		}
        Store (Arg0, i000)
		m001 (Arg0)
    }

    Method (m001, 1)
    {
        Store (Arg0, i001)
    }

	Method(m002)
	{
		if (fl00) {
			Return ("m002")
		}
		Or (0xf2, 0x01, Local0)
		m000 (Local0)
	}

	// Case to call AcpiDsDoImplicitReturn with AddReference == 1 and
	// WalkState->ImplicitReturnObj == NULL

    Method (m003)
    {
		Store(0xfabec, Local0)
    }

	Method(m004)
	{
		if (fl00) {
			Return ("m004")
		}
		m003()
	}

	// Case to call AcpiDsDoImplicitReturn with AddReference == 1 and
	// WalkState->ImplicitReturnObj == NULL, then check which a case of
	// AcpiDsClearImplicitReturn will be called when a new result appears.

    Method (m005)
    {
		Store(0xfabec, Local0)
    }

	Method(m006)
	{
		if (fl00) {
			Return ("m006")
		}

		m005()

		Store(0xcedab, Local0)
	}

	// Case to call AcpiDsDoImplicitReturn with AddReference == 1 and
	// ReturnDesc != NULL && (WalkState->ImplicitReturnObj == ReturnDesc)
	// Case when Result is used

    Method (m007)
    {
		Store(Store(Store(0xabcd, i002), i003), i004)
    }


	Method(m008)
	{
		if (fl00) {
			Return ("m008")
		}
		m007()
	}

	// Case to call AcpiDsDoImplicitReturn with AddReference == 1 and
	// ReturnDesc != NULL && (WalkState->ImplicitReturnObj == ReturnDesc)
	// Case when Result is not used

    Method (m009, 1)
    {
		if (arg0) {
			Store(Store(0x1234, i005), i006)
		} else {
			Store(Store(0x5678, i007), i008)
		}
    }

	Method(m00a)
	{
		if (fl00) {
			Return ("m00a")
		}
		m009(0)
		m009(1)
	}

	Method(m00b)
	{
		if (fl00) {
			Return ("m00b")
		}
		m009(1)
		m009(0)
	}

	// m002

	Store(0, Local0)
	CH03("", z138, 0x064, __LINE__, 0)
	Store(m002(), Local0)
	if (SLCK) {
		CH03("", z138, 0x065, __LINE__, 0)
		if (LNotEqual(Local0, 0xf3)) {
			err("", z138, __LINE__, 0, 0, Local0, 0xf3)
		}
	} else {
		CH04("", 0, 0xff, z138, __LINE__, 0, 0)
	}

	// m004

	Store(0, Local0)
	CH03("", z138, 0x068, __LINE__, 0)
	Store(m004(), Local0)
	if (SLCK) {
		CH03("", z138, 0x069, __LINE__, 0)
		if (LNotEqual(Local0, 0xfabec)) {
			err("", z138, __LINE__, 0, 0, Local0, 0xfabec)
		}
	} else {
		CH04("", 0, 0xff, z138, __LINE__, 0, 0)
	}

	// m006

	Store(0, Local0)
	CH03("", z138, 0x06e, __LINE__, 0)
	Store(m006(), Local0)
	if (SLCK) {
		CH03("", z138, 0x06f, __LINE__, 0)
		if (LNotEqual(Local0, 0xcedab)) {
			err("", z138, __LINE__, 0, 0, Local0, 0xcedab)
		}
	} else {
		CH04("", 0, 0xff, z138, __LINE__, 0, 0)
	}

	// m008

	Store(0, Local0)
	CH03("", z138, 0x072, __LINE__, 0)
	Store(m008(), Local0)
	if (SLCK) {
		CH03("", z138, 0x073, __LINE__, 0)
		if (LNotEqual(Local0, 0xabcd)) {
			err("", z138, __LINE__, 0, 0, Local0, 0xabcd)
		}
	} else {
		CH04("", 0, 0xff, z138, __LINE__, 0, 0)
	}

	// m00a

	Store(0, Local0)
	CH03("", z138, 0x076, __LINE__, 0)
	Store(m00a(), Local0)
	if (SLCK) {
		CH03("", z138, 0x077, __LINE__, 0)
		if (LNotEqual(Local0, 0x1234)) {
			err("", z138, __LINE__, 0, 0, Local0, 0x1234)
		}
	} else {
		CH04("", 0, 0xff, z138, __LINE__, 0, 0)
	}

	// m00b

	Store(0, Local0)
	CH03("", z138, 0x080, __LINE__, 0)
	Store(m00b(), Local0)
	if (SLCK) {
		CH03("", z138, 0x081, __LINE__, 0)
		if (LNotEqual(Local0, 0x5678)) {
			err("", z138, __LINE__, 0, 0, Local0, 0x5678)
		}
	} else {
		CH04("", 0, 0xff, z138, __LINE__, 0, 0)
	}

	if (LNotEqual(i000, 0xf3)) {
		err("", z138, __LINE__, 0, 0, i000, 0xf3)
	}
	if (LNotEqual(i001, 0xf3)) {
		err("", z138, __LINE__, 0, 0, i001, 0xf3)
	}
	if (LNotEqual(i002, 0xabcd)) {
		err("", z138, __LINE__, 0, 0, i002, 0xabcd)
	}
	if (LNotEqual(i003, 0xabcd)) {
		err("", z138, __LINE__, 0, 0, i003, 0xabcd)
	}
	if (LNotEqual(i004, 0xabcd)) {
		err("", z138, __LINE__, 0, 0, i004, 0xabcd)
	}
	if (LNotEqual(i005, 0x1234)) {
		err("", z138, __LINE__, 0, 0, i005, 0x1234)
	}
	if (LNotEqual(i006, 0x1234)) {
		err("", z138, __LINE__, 0, 0, i006, 0x1234)
	}
	if (LNotEqual(i007, 0x5678)) {
		err("", z138, __LINE__, 0, 0, i007, 0x5678)
	}
	if (LNotEqual(i008, 0x5678)) {
		err("", z138, __LINE__, 0, 0, i008, 0x5678)
	}
}
