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
 * Method invocations do add layers of Packages processing
 *
 * 0x1 Outstanding allocations because of
 * AcpiExec doesn't run the unload of the table have been processed.
 * All they are caused by call to SRMT Method.
 *
 * Outstanding: 0x1 allocations after execution.
 */

/*
 * Web of references performed by several method invocations
 */
Method(mfd9,, Serialized)
{
	Name(sz, 32)	// full size of Package applied in algorithm
	Name(szzz, 64)	// full size of Package
	Name(prt, 16)	// number of different parts
	Name(nm16, 0)	// 1/16 of size
	Name(i1, 0)		// 1/16 of size
	Name(i2, 0)		// 2/16 of size
	Name(i3, 0)
	Name(i4, 0)
	Name(i5, 0)
	Name(i6, 0)
	Name(i8, 0)
	Name(i9, 0)
	Name(i10, 0)
	Name(i11, 0)
	Name(i12, 0)
	Name(i13, 0)
	Name(i14, 0)
	Name(i16, 0)

	Name(p000, Package(szzz) {})
	Name(p001, Package(szzz) {})
	Name(p002, Package(szzz) {})
	Name(p003, Package(szzz) {})
	Name(p004, Package(szzz) {})
	Name(p005, Package(szzz) {})
	Name(p006, Package(szzz) {})
	Name(p007, Package(szzz) {})

	Name(i000, 0xabcd0000)
	Name(i001, 0xabcd0100)
	Name(i002, 0xabcd0200)
	Name(i003, 0xabcd0300)
	Name(i004, 0xabcd0400)
	Name(i005, 0xabcd0500)
	Name(i006, 0xabcd0600)
	Name(i007, 0xabcd0700)

	Divide(sz, prt, Local0, nm16)

	Store(nm16, i1)
	Multiply(nm16, 2, i2)
	Multiply(nm16, 3, i3)
	Multiply(nm16, 4, i4)
	Multiply(nm16, 5, i5)
	Multiply(nm16, 6, i6)
	Multiply(nm16, 8, i8)
	Multiply(nm16, 9, i9)
	Multiply(nm16, 10, i10)
	Multiply(nm16, 11, i11)
	Multiply(nm16, 12, i12)
	Multiply(nm16, 13, i13)
	Multiply(nm16, 14, i14)
	Multiply(nm16, 16, i16)


	/* Initializing full Packages with monotone increasing Integers */
	Method(m000,, Serialized)
	{
		Name(qq00, 0)
		Name(qq01, 0)

		Method(m000)
		{
			mfc7(p000, 0, sz, i000)
			mfc7(p001, 0, sz, i001)
		}
		Method(m001)
		{
			if (qq00) {
				m000()
			}

			mfc7(p002, 0, sz, i002)
			mfc7(p003, 0, sz, i003)
			mfc7(p004, 0, sz, i004)
		}
		Method(m002)
		{
			mfc7(p005, 0, sz, i005)
			if (qq01) {
				Store("never", Debug)
			} else {
				mfc7(p006, 0, sz, i006)
			}
		}

		Store(1, qq00)
		if (qq00) {
			m001()
		}
		m002()
		if (qq00) {
			mfc7(p007, 0, sz, i007)
		}
	}

	/* Initializing the Package with IRefs */

	/* Generate two-directional ring of references */

	Method(m001,, Serialized)
	{
		Name(uu00, 0xeeff0000)
		Name(ii00, 0xabcd0000)
		Name(pp00, Package(sz) {})

		Name(qq00, 0)

		Method(m001)
		{
			mfc8(p000, p001, 0, i8, nm16, 0, 0)
		}
		Method(m002)
		{
			mfc8(p001, p002, 0, i8, nm16, 0, 0)
		}
		Method(m003)
		{
			m001()
			m002()
			mfc8(p002, p003, 0, i8, nm16, 0, 0)
		}
		Method(m004)
		{
			m003()
			mfc8(p003, p004, 0, i8, nm16, 0, 0)
		}
		Method(m005)
		{
			m004()
			mfc8(p004, p005, 0, i8, nm16, 0, 0)
		}
		Method(m006)
		{
			mfc8(p005, p006, 0, i8, nm16, 0, 0)
		}
		Method(m007)
		{
			if (qq00) {
				mfc8(p006, p007, 0, i8, nm16, 0, 0)
			}
		}
		Method(m008)
		{
			if (qq00) {
				m005()
				m006()
				m007()
				mfc8(p007, p000, 0, i8, nm16, 0, 0)
			}
		}


		Method(m009)
		{
			if (qq00) {
				mfc8(p007, p006, i1, i9, nm16, 0, 0)
			}
		}
		Method(m00a)
		{
			if (qq00) {
				mfc8(p006, p005, i1, i9, nm16, 0, 0)
			}
		}
		Method(m00b)
		{
			if (qq00) {
				mfc8(p005, p004, i1, i9, nm16, 0, 0)
			}
		}
		Method(m00c)
		{
			if (qq00) {
				mfc8(p004, p003, i1, i9, nm16, 0, 0)
			}
		}
		Method(m00d)
		{
			if (qq00) {
				mfc8(p003, p002, i1, i9, nm16, 0, 0)
			}
		}
		Method(m00e)
		{
			if (qq00) {
				mfc8(p002, p001, i1, i9, nm16, 0, 0)
			}
		}
		Method(m00f)
		{
			if (qq00) {
				mfc8(p001, p000, i1, i9, nm16, 0, 0)
			}
		}
		Method(m010)
		{
			m00b()
			m00c()
			m00d()
			m00e()
			m00f()
			mfc8(p000, p007, i1, i9, nm16, 0, 0)
		}

		Store(1, qq00)

		m000()

		if (qq00) {
			m008()
			m009()
			m00a()
		}

		mfc7(pp00, 0, sz, uu00)

		// Causes Outstanding allocations
		mfc8(p000, pp00, 0, i8, nm16, 0, 0)

		mfc8(pp00, p000, 0, i16, nm16, 0, 0)

		m010()

		mfcc(pp00, i8, nm16, ii00, 0, 0x100)
		mfcc(p000, i16, nm16, uu00, 0, 0x101)
	}

	/*
	 * Join all other packages
	 * (two directions for each two points)
	 */
	Method(m002,, Serialized)
	{
		Name(qq01, 0)

		m001()

		if (qq01) {
			Store("never", Debug)
		} else {
			mfc8(p002, p000, i2, i10, nm16, 0, 0)
			mfc8(p003, p000, i3, i11, nm16, 0, 0)
			if (qq01) {
				Store("never", Debug)
			} else {
				mfc8(p004, p000, i4, i12, nm16, 0, 0)
				mfc8(p005, p000, i5, i13, nm16, 0, 0)
			}
			mfc8(p006, p000, i6, i14, nm16, 0, 0)
		}

		mfc8(p003, p001, i3, i11, nm16, 0, 0)
		mfc8(p004, p001, i4, i12, nm16, 0, 0)
		mfc8(p005, p001, i5, i13, nm16, 0, 0)
		mfc8(p006, p001, i6, i14, nm16, 0, 0)
		mfc8(p007, p001, i2, i10, nm16, 0, 0)

		mfc8(p004, p002, i4, i12, nm16, 0, 0)
		mfc8(p005, p002, i5, i13, nm16, 0, 0)
		mfc8(p006, p002, i6, i14, nm16, 0, 0)
		mfc8(p007, p002, i2, i10, nm16, 0, 0)
		mfc8(p000, p002, i3, i11, nm16, 0, 0)

		mfc8(p005, p003, i5, i13, nm16, 0, 0)
		mfc8(p006, p003, i6, i14, nm16, 0, 0)
		mfc8(p007, p003, i2, i10, nm16, 0, 0)
		mfc8(p000, p003, i3, i11, nm16, 0, 0)
		mfc8(p001, p003, i4, i12, nm16, 0, 0)

		mfc8(p006, p004, i6, i14, nm16, 0, 0)
		mfc8(p007, p004, i2, i10, nm16, 0, 0)
		mfc8(p000, p004, i3, i11, nm16, 0, 0)
		mfc8(p001, p004, i4, i12, nm16, 0, 0)
		mfc8(p002, p004, i5, i13, nm16, 0, 0)

		mfc8(p007, p005, i2, i10, nm16, 0, 0)
		mfc8(p000, p005, i3, i11, nm16, 0, 0)
		mfc8(p001, p005, i4, i12, nm16, 0, 0)
		mfc8(p002, p005, i5, i13, nm16, 0, 0)
		mfc8(p003, p005, i6, i14, nm16, 0, 0)

		mfc8(p000, p006, i3, i11, nm16, 0, 0)
		mfc8(p001, p006, i4, i12, nm16, 0, 0)
		mfc8(p002, p006, i5, i13, nm16, 0, 0)
		mfc8(p003, p006, i6, i14, nm16, 0, 0)
		mfc8(p004, p006, i2, i10, nm16, 0, 0)

		mfc8(p001, p007, i4, i12, nm16, 0, 0)
		mfc8(p002, p007, i5, i13, nm16, 0, 0)
		mfc8(p003, p007, i6, i14, nm16, 0, 0)
		mfc8(p004, p007, i2, i10, nm16, 0, 0)
		mfc8(p005, p007, i3, i11, nm16, 0, 0)
	}

	/* Verifying access to Packages through the IRefs */

	/* Two-directional ring of references */

	Method(m003)
	{
		m002()

		mfcc(p001, i8, nm16, i000, 0, 0x102)
		mfcc(p002, i8, nm16, i001, 0, 0x103)
		mfcc(p003, i8, nm16, i002, 0, 0x104)
		mfcc(p004, i8, nm16, i003, 0, 0x105)
		mfcc(p005, i8, nm16, i004, 0, 0x106)
		mfcc(p006, i8, nm16, i005, 0, 0x107)
		mfcc(p007, i8, nm16, i006, 0, 0x108)
		mfcc(p000, i8, nm16, i007, 0, 0x109)
	}

	Method(m004)
	{
		Method(m000)
		{
			Add(i002, nm16, i002)
			Add(i001, nm16, i001)
			Add(i000, nm16, i000)

			mfcc(p006, i9, nm16, i007, 0, 0x10a)
			mfcc(p005, i9, nm16, i006, 0, 0x10b)
		}

		m003()

		Add(i007, nm16, i007)
		Add(i006, nm16, i006)
		Add(i005, nm16, i005)
		Add(i004, nm16, i004)
		Add(i003, nm16, i003)

		m000()

		mfcc(p004, i9, nm16, i005, 0, 0x10c)
		mfcc(p003, i9, nm16, i004, 0, 0x10d)
		mfcc(p002, i9, nm16, i003, 0, 0x10e)
		mfcc(p001, i9, nm16, i002, 0, 0x10f)
		mfcc(p000, i9, nm16, i001, 0, 0x110)
		mfcc(p007, i9, nm16, i000, 0, 0x111)
	}

	/* Verify other references */

	Method(m005)
	{
            Method(m000)
            {
             Method(m000)
             {
              Method(m000)
              {
               Method(m000)
               {
                Method(m000)
                {
                 Method(m000)
                 {
                  Method(m000)
                  {
                   Method(m000)
                   {
                    Method(m000)
                    {
                     Method(m000)
                     {
                      Method(m000)
                      {
                       Method(m000)
                       {
                        Method(m000)
                        {
                         Method(m000)
                         {
                          Method(m000)
                          {
                           mfcc(p006, i10, nm16, i004, 0, 0x112)
                           mfcc(p007, i10, nm16, i004, 0, 0x113)
                          }
                          mfcc(p005, i10, nm16, i007, 0, 0x114)
                          m000()
                         }
                         mfcc(p004, i10, nm16, i007, 0, 0x115)
                         m000()
                        }
                        mfcc(p003, i10, nm16, i007, 0, 0x116)
                        m000()
                       }
                       mfcc(p002, i10, nm16, i007, 0, 0x117)
                       m000()
                      }
                      mfcc(p001, i10, nm16, i007, 0, 0x118)
                      m000()
                     }
                     mfcc(p000, i10, nm16, i002, 0, 0x119)
                     m000()
                    }
                    Add(i000, nm16, i000)
                    m000()
                   }
                   Add(i001, nm16, i001)
                   m000()
                  }
                  Add(i002, nm16, i002)
                  m000()
                 }
                 Add(i003, nm16, i003)
                 m000()
                }
                Add(i004, nm16, i004)
                m000()
               }
               Add(i005, nm16, i005)
               m000()
              }
              Add(i006, nm16, i006)
              m000()
             }
             Add(i007, nm16, i007)
             m000()
		}

		m004()

		m000()
	}

	Method(m006)
	{
		m005()

		Add(i007, nm16, i007)
		Add(i006, nm16, i006)
		Add(i005, nm16, i005)
		Add(i004, nm16, i004)
		Add(i003, nm16, i003)
		Add(i002, nm16, i002)
		Add(i001, nm16, i001)
		Add(i000, nm16, i000)

		mfcc(p000, i11, nm16, i003, 0, 0x11a)
		mfcc(p001, i11, nm16, i003, 0, 0x11b)
		mfcc(p002, i11, nm16, i000, 0, 0x11c)
		mfcc(p003, i11, nm16, i000, 0, 0x11d)
		mfcc(p004, i11, nm16, i000, 0, 0x11e)
		mfcc(p005, i11, nm16, i000, 0, 0x11f)
		mfcc(p006, i11, nm16, i000, 0, 0x120)
		mfcc(p007, i11, nm16, i005, 0, 0x121)
	}

	Method(m007,, Serialized)
	{
		Name(qq00, 0)

		m006()

		Add(i007, nm16, i007)
		Add(i006, nm16, i006)
		Add(i005, nm16, i005)
		Add(i004, nm16, i004)
		Add(i003, nm16, i003)
		Add(i002, nm16, i002)
		Add(i001, nm16, i001)
		Add(i000, nm16, i000)

            if (qq00) {
			Store("never", Debug)
		} else {
			mfcc(p000, i12, nm16, i004, 0, 0x122)
			mfcc(p001, i12, nm16, i004, 0, 0x123)
			mfcc(p002, i12, nm16, i004, 0, 0x124)
			mfcc(p003, i12, nm16, i001, 0, 0x125)
			mfcc(p004, i12, nm16, i001, 0, 0x126)
			mfcc(p005, i12, nm16, i001, 0, 0x127)
			mfcc(p006, i12, nm16, i001, 0, 0x128)
			mfcc(p007, i12, nm16, i001, 0, 0x129)
            }
	}

	Method(m008)
	{
		m007()

		Add(i007, nm16, i007)
		Add(i006, nm16, i006)
		Add(i005, nm16, i005)
		Add(i004, nm16, i004)
		Add(i003, nm16, i003)
		Add(i002, nm16, i002)
		Add(i001, nm16, i001)
		Add(i000, nm16, i000)

		mfcc(p000, i13, nm16, i005, 0, 0x12a)
		mfcc(p001, i13, nm16, i005, 0, 0x12b)
		mfcc(p002, i13, nm16, i005, 0, 0x12c)
		mfcc(p003, i13, nm16, i005, 0, 0x12d)
		mfcc(p004, i13, nm16, i002, 0, 0x12e)
		mfcc(p005, i13, nm16, i002, 0, 0x12f)
		mfcc(p006, i13, nm16, i002, 0, 0x130)
		mfcc(p007, i13, nm16, i002, 0, 0x131)
	}

	Method(m009,, Serialized)
	{
		Name(uu00, 0xeeff0000)
		Name(ii00, 0xabcd0000)
		Name(pp00, Package(sz) {})

		m008()

		Add(i007, nm16, i007)
		Add(i006, nm16, i006)
		Add(i005, nm16, i005)
		Add(i004, nm16, i004)
		Add(i003, nm16, i003)
		Add(i002, nm16, i002)
		Add(i001, nm16, i001)
		Add(i000, nm16, i000)

		mfc7(pp00, 0, sz, uu00)
		mfc8(p000, pp00, 0, i8, nm16, 0, 0)
		mfc8(pp00, p000, 0, i16, nm16, 0, 0)

		mfcc(p000, i14, nm16, i006, 0, 0x132)
		mfcc(p001, i14, nm16, i006, 0, 0x133)
		mfcc(p002, i14, nm16, i006, 0, 0x134)
		mfcc(p003, i14, nm16, i006, 0, 0x135)
		mfcc(p004, i14, nm16, i006, 0, 0x136)
		mfcc(p005, i14, nm16, i003, 0, 0x137)
		mfcc(p006, i14, nm16, i003, 0, 0x138)
		mfcc(p007, i14, nm16, i003, 0, 0x139)

		mfcc(pp00, i8, nm16, ii00, 0, 0x13a)
		mfcc(p000, i16, nm16, uu00, 0, 0x13b)
	}

	m009()
}

Method(mfda)
{
	SRMT("mfd9")
	mfd9()
}
