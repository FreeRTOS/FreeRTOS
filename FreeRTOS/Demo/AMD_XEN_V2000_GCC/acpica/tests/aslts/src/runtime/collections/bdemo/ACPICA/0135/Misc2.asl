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
 * Outstanding: 0x1 allocations after execution.
 */

Name(id27, 64)

/* Create and write IRef */

Method(mf02, 6, Serialized)
{
	Name(i001, 0)
	Name(i002, 0)
	Name(i003, 0)
	Name(i004, 0)
	Name(ii01, 0)
	Name(ii02, 0)
	Name(ii03, 0)
	Name(ii04, 0)

	if (LEqual(arg1, 1)) {
		Store(DerefOf(Index(arg2, 0)), i001)
		Store(Index(arg0, i001), Local7)
	} elseif (LEqual(arg1, 2)) {
		Store(DerefOf(Index(arg2, 0)), i001)
		Store(DerefOf(Index(arg2, 1)), i002)
		Store(Index(DerefOf(Index(arg0, i001)), i002), Local7)
	} elseif (LEqual(arg1, 3)) {
		Store(DerefOf(Index(arg2, 0)), i001)
		Store(DerefOf(Index(arg2, 1)), i002)
		Store(DerefOf(Index(arg2, 2)), i003)
		Store(Index(DerefOf(Index(DerefOf(Index(arg0, i001)), i002)), i003), Local7)
	} elseif (LEqual(arg1, 4)) {
		Store(DerefOf(Index(arg2, 0)), i001)
		Store(DerefOf(Index(arg2, 1)), i002)
		Store(DerefOf(Index(arg2, 2)), i003)
		Store(DerefOf(Index(arg2, 3)), i004)
		Store(Index(DerefOf(Index(DerefOf(Index(DerefOf(Index(arg0,
				i001)), i002)), i003)), i004), Local7)
	} else {
		err("", zFFF, __LINE__, 0, 0, 0, 0)
		return
	}

	if (LEqual(arg4, 1)) {
		Store(DerefOf(Index(arg5, 0)), ii01)
		Store(Local7, Index(arg3, ii01))
	} elseif (LEqual(arg4, 2)) {
		Store(DerefOf(Index(arg5, 0)), ii01)
		Store(DerefOf(Index(arg5, 1)), ii02)
		Store(Local7, Index(DerefOf(Index(arg3, ii01)), ii02))
	} elseif (LEqual(arg4, 3)) {
		Store(DerefOf(Index(arg5, 0)), ii01)
		Store(DerefOf(Index(arg5, 1)), ii02)
		Store(DerefOf(Index(arg5, 2)), ii03)
		Store(Local7, Index(DerefOf(Index(DerefOf(Index(arg3, ii01)), ii02)), ii03))
	} elseif (LEqual(arg4, 4)) {
		Store(DerefOf(Index(arg5, 0)), ii01)
		Store(DerefOf(Index(arg5, 1)), ii02)
		Store(DerefOf(Index(arg5, 2)), ii03)
		Store(DerefOf(Index(arg5, 3)), ii04)
		Store(Local7, Index(DerefOf(Index(DerefOf(Index(DerefOf(Index(arg3,
				ii01)), ii02)), ii03)), ii04))
	} else {
		err("", zFFF, __LINE__, 0, 0, 0, 0)
		return
	}
}

/* Read by means of IRef-to-Integer */

Method(mfec, 4, Serialized)
{
	Name(i001, 0)
	Name(i002, 0)
	Name(i003, 0)
	Name(i004, 0)

	if (LEqual(arg1, 1)) {
		Store(DerefOf(Index(arg2, 0)), i001)
		Store(DerefOf(DerefOf(Index(arg0, i001))), Local7)
	} elseif (LEqual(arg1, 2)) {
		Store(DerefOf(Index(arg2, 0)), i001)
		Store(DerefOf(Index(arg2, 1)), i002)
		Store(DerefOf(DerefOf(Index(DerefOf(Index(arg0, i001)), i002))), Local7)
	} elseif (LEqual(arg1, 3)) {
		Store(DerefOf(Index(arg2, 0)), i001)
		Store(DerefOf(Index(arg2, 1)), i002)
		Store(DerefOf(Index(arg2, 2)), i003)
		Store(DerefOf(DerefOf(Index(DerefOf(Index(DerefOf(Index(arg0, i001)), i002)), i003))), Local7)
	} elseif (LEqual(arg1, 4)) {
		Store(DerefOf(Index(arg2, 0)), i001)
		Store(DerefOf(Index(arg2, 1)), i002)
		Store(DerefOf(Index(arg2, 2)), i003)
		Store(DerefOf(Index(arg2, 3)), i004)
		Store(DerefOf(DerefOf(Index(DerefOf(Index(DerefOf(Index(DerefOf(Index(arg0,
				i001)), i002)), i003)), i004))), Local7)
	} else {
		err("", zFFF, __LINE__, 0, 0, 0, 0)
		return
	}

	if (LNotEqual(Local7, arg3)) {
		err("", zFFF, __LINE__, 0, 0, Local7, arg3)
	}
}

/* Read by means of IRef-to-Package */

Method(mfed, 5, Serialized)
{
	Name(i001, 0)
	Name(i002, 0)
	Name(i003, 0)
	Name(i004, 0)

	if (LEqual(arg1, 1)) {
		Store(DerefOf(Index(arg2, 0)), i001)
		Store(DerefOf(DerefOf(Index(arg0, i001))), Local7)
	} elseif (LEqual(arg1, 2)) {
		Store(DerefOf(Index(arg2, 0)), i001)
		Store(DerefOf(Index(arg2, 1)), i002)
		Store(DerefOf(DerefOf(Index(DerefOf(Index(arg0, i001)), i002))), Local7)
	} elseif (LEqual(arg1, 3)) {
		Store(DerefOf(Index(arg2, 0)), i001)
		Store(DerefOf(Index(arg2, 1)), i002)
		Store(DerefOf(Index(arg2, 2)), i003)
		Store(DerefOf(DerefOf(Index(DerefOf(Index(DerefOf(Index(arg0, i001)), i002)), i003))), Local7)
	} elseif (LEqual(arg1, 4)) {
		Store(DerefOf(Index(arg2, 0)), i001)
		Store(DerefOf(Index(arg2, 1)), i002)
		Store(DerefOf(Index(arg2, 2)), i003)
		Store(DerefOf(Index(arg2, 3)), i004)
		Store(DerefOf(DerefOf(Index(DerefOf(Index(DerefOf(Index(DerefOf(Index(arg0,
				i001)), i002)), i003)), i004))), Local7)
	} else {
		err("", zFFF, __LINE__, 0, 0, 0, 0)
		return
	}

	Store(DerefOf(Index(Local7, arg3)), Local0)

	if (LNotEqual(Local0, arg4)) {
		err("", zFFF, __LINE__, 0, 0, Local0, arg4)
	}
}

Method(mfee,, Serialized)
{
		Name(p000, Package(id27) {
			Package(id27) {
				Package(id27) {
					Package(id27) {0x40000000},
					0x30000000,
					Package(id27) {0x40000001},
					0x30000001,
					0x30000002,
				},
				0x20000000,
				Package(id27) {
					Package(id27) {0x40000002},
					0x30000003,
					Package(id27) {0x40000003},
					0x30000004,
					0x30000005,
				},
				0x20000001,
				0x20000002,
			},
			0x10000000,
			Package(id27) {
				Package(id27) {
					Package(id27) {0x40000004},
					0x30000006,
					Package(id27) {0x40000005},
					0x30000007,
					0x30000008,
				},
				0x20000003,
				Package(id27) {
					Package(id27) {0x40000006},
					0x30000009,
					Package(id27) {0x40000007},
					0x3000000a,
					0x3000000b,
				},
				0x20000004,
				0x20000005,
			},
			0x10000001,
			0x10000002,
		})

		Name(p001, Package(id27) {
			Package(id27) {
				Package(id27) {
					Package(id27) {0x40000000},
					0x30000000,
					Package(id27) {0x40000001},
					0x30000001,
					0x30000002,
				},
				0x20000000,
				Package(id27) {
					Package(id27) {0x40000002},
					0x30000003,
					Package(id27) {0x40000003},
					0x30000004,
					0x30000005,
				},
				0x20000001,
				0x20000002,
			},
			0x10000000,
			Package(id27) {
				Package(id27) {
					Package(id27) {0x40000004},
					0x30000006,
					Package(id27) {0x40000005},
					0x30000007,
					0x30000008,
				},
				0x20000003,
				Package(id27) {
					Package(id27) {0x40000006},
					0x30000009,
					Package(id27) {0x40000007},
					0x3000000a,
					0x3000000b,
				},
				0x20000004,
				0x20000005,
			},
			0x10000001,
			0x10000002,
		})

		/* Write access */

		Method(mm04, 6)
		{
			Store(arg5, Index(DerefOf(Index(DerefOf(Index(DerefOf(Index(arg0,
								arg1)), arg2)), arg3)), arg4))
		}

		Method(mm03, 5)
		{
			Store(arg4, Index(DerefOf(Index(DerefOf(Index(arg0, arg1)), arg2)), arg3))
		}

		Method(mm02, 4)
		{
			Store(arg3, Index(DerefOf(Index(arg0, arg1)), arg2))
		}

		Method(mm01, 3)
		{
			Store(arg2, Index(arg0, arg1))
		}

		/* Read access */

		Method(m004, 6)
		{
			Store(DerefOf(Index(DerefOf(Index(DerefOf(Index(DerefOf(Index(arg0,
								arg1)), arg2)), arg3)), arg4)), Local0)
			if (LNotEqual(Local0, arg5)) {
				err("", zFFF, __LINE__, 0, 0, Local0, arg5)
			}
		}

		Method(m003, 5)
		{
			Store(DerefOf(Index(DerefOf(Index(DerefOf(Index(arg0,
								arg1)), arg2)), arg3)), Local0)
			if (LNotEqual(Local0, arg4)) {
				err("", zFFF, __LINE__, 0, 0, Local0, arg4)
			}
		}

		Method(m002, 4)
		{
			Store(DerefOf(Index(DerefOf(Index(arg0, arg1)), arg2)), Local0)
			if (LNotEqual(Local0, arg3)) {
				err("", zFFF, __LINE__, 0, 0, Local0, arg3)
			}
		}

		Method(m001, 3)
		{
			Store(DerefOf(Index(arg0, arg1)), Local0)
			if (LNotEqual(Local0, arg2)) {
				err("", zFFF, __LINE__, 0, 0, Local0, arg2)
			}
		}

		/*
		 * On each level from 1 to 4 create the following structure of data -
		 * create IRefs to all levels and alternate them with Packages.
		 * Verify access through the created IRefs.
		 *
		 * Refer packages p000 and p001 directly by names.
		 *
		 * arg0 - the start index inside arg1 where to store created objects.
		 */
		Method(mmm0, 1, Serialized)
		{
			Name(i000, 0)

			/*
                   * Create IRefs to all levels from 4-level Package.
                   * Alternate IRefs with Packages.
                   */

			Store(arg0, i000)
			mf02(p000, 4, Buffer(){0,0,0,0}, p000, 4, Package(){0,0,0,i000})
			mfec(p000, 4, Package(){0,0,0,i000}, 0x40000000)
			Increment(i000)
			mm04(p000, 0, 0, 0, i000, Package(){0x51000000})
			Increment(i000)

			mf02(p000, 3, Buffer(){0,0,4}, p000, 4, Package(){0,0,0,i000})
			mfec(p000, 4, Package(){0,0,0,i000}, 0x30000002)
			Increment(i000)
			mm04(p000, 0, 0, 0, i000, Package(){0x51000001})
			Increment(i000)

			mf02(p000, 2, Buffer(){0,4}, p000, 4, Package(){0,0,0,i000})
			mfec(p000, 4, Package(){0,0,0,i000}, 0x20000002)
			Increment(i000)
			mm04(p000, 0, 0, 0, i000, Package(){0x51000002})
			Increment(i000)

			mf02(p000, 1, Buffer(){4}, p000, 4, Package(){0,0,0,i000})
			mfec(p000, 4, Package(){0,0,0,i000}, 0x10000002)
			Increment(i000)
			mm04(p000, 0, 0, 0, i000, Package(){0x51000003})
			Increment(i000)

			/* Reference to Package */

			mf02(p000, 3, Buffer(){0,0,0}, p000, 4, Package(){0,0,0,i000})
			mfed(p000, 4, Package(){0,0,0,i000}, 0, 0x40000000)
			Increment(i000)

			/*
                   * Create IRefs to all levels from 3-level Package.
                   * Alternate IRefs with Packages.
                   */

			Store(arg0, i000)
			mf02(p000, 4, Buffer(){0,0,0,0}, p000, 3, Package(){0,0,i000})
			mfec(p000, 3, Package(){0,0,i000}, 0x40000000)
			Increment(i000)
			mm03(p000, 0, 0, i000, Package(){0x41000000})
			Increment(i000)

			mf02(p000, 3, Buffer(){0,0,4}, p000, 3, Package(){0,0,i000})
			mfec(p000, 3, Package(){0,0,i000}, 0x30000002)
			Increment(i000)
			mm03(p000, 0, 0, i000, Package(){0x41000001})
			Increment(i000)

			mf02(p000, 2, Buffer(){0,4}, p000, 3, Package(){0,0,i000})
			mfec(p000, 3, Package(){0,0,i000}, 0x20000002)
			Increment(i000)
			mm03(p000, 0, 0, i000, Package(){0x41000002})
			Increment(i000)

			mf02(p000, 1, Buffer(){4}, p000, 3, Package(){0,0,i000})
			mfec(p000, 3, Package(){0,0,i000}, 0x10000002)
			Increment(i000)
			mm03(p000, 0, 0, i000, Package(){0x41000003})
			Increment(i000)

			/*
                   * Create IRefs to all levels from 2-level Package.
                   * Alternate IRefs with Packages.
                   */

			Store(arg0, i000)
			mf02(p000, 4, Buffer(){0,0,0,0}, p000, 2, Package(){0,i000})
			mfec(p000, 2, Package(){0,i000}, 0x40000000)
			Increment(i000)
			mm02(p000, 0, i000, Package(){0x31000000})
			Increment(i000)

			mf02(p000, 3, Buffer(){0,0,4}, p000, 2, Package(){0,i000})
			mfec(p000, 2, Package(){0,i000}, 0x30000002)
			Increment(i000)
			mm02(p000, 0, i000, Package(){0x31000001})
			Increment(i000)

			mf02(p000, 2, Buffer(){0,4}, p000, 2, Package(){0,i000})
			mfec(p000, 2, Package(){0,i000}, 0x20000002)
			Increment(i000)
			mm02(p000, 0, i000, Package(){0x31000002})
			Increment(i000)

			mf02(p000, 1, Buffer(){4}, p000, 2, Package(){0,i000})
			mfec(p000, 2, Package(){0,i000}, 0x10000002)
			Increment(i000)
			mm02(p000, 0, i000, Package(){0x31000003})
			Increment(i000)

			/*
                   * Create IRefs to all levels from 1-level Package.
                   * Alternate IRefs with Packages.
                   */

			Store(arg0, i000)
			mf02(p000, 4, Buffer(){0,0,0,0}, p000, 1, Package(){i000})
			mfec(p000, 1, Package(){i000}, 0x40000000)
			Increment(i000)
			mm01(p000, i000, Package(){0x21000000})
			Increment(i000)

			mf02(p000, 3, Buffer(){0,0,4}, p000, 1, Package(){i000})
			mfec(p000, 1, Package(){i000}, 0x30000002)
			Increment(i000)
			mm01(p000, i000, Package(){0x21000001})
			Increment(i000)

			mf02(p000, 2, Buffer(){0,4}, p000, 1, Package(){i000})
			mfec(p000, 1, Package(){i000}, 0x20000002)
			Increment(i000)
			mm01(p000, i000, Package(){0x21000002})
			Increment(i000)

			mf02(p000, 1, Buffer(){4}, p000, 1, Package(){i000})
			mfec(p000, 1, Package(){i000}, 0x10000002)
			Increment(i000)
			mm01(p000, i000, Package(){0x21000003})
			Increment(i000)
		}

		/*
		 * On each level from 1 to 4 create the following structure of data -
		 * create IRefs to all levels and alternate them with Packages.
		 * Verify access through the created IRefs.
		 *
		 * arg0 - Package, IRefs are pointing to elements of this Package,
		 * arg1 - Package, IRefs alternated with Packages are stored as
		 *        elements of this Package,
		 * arg2 - the start index inside arg1 where to store created objects,
		 * arg3 - create structure,
		 * arg4 - read.
		 */
		Method(mmm1, 5, Serialized)
		{
			Name(i000, 0)

			/*
                   * Create IRefs to all levels from 4-level Package.
                   * Alternate IRefs with Packages.
                   */

			Store(arg2, i000)
			if (arg3) {
				mf02(arg0, 4, Buffer(){0,0,0,0}, arg1, 4, Package(){0,0,0,i000})
			}
			if (arg4) {
				mfec(arg1, 4, Package(){0,0,0,i000}, 0x40000000)
			}
			Increment(i000)
			if (arg3) {
				mm04(arg1, 0, 0, 0, i000, Package(){0x51000000})
			}
			Increment(i000)

			if (arg3) {
				mf02(arg0, 3, Buffer(){0,0,4}, arg1, 4, Package(){0,0,0,i000})
			}
			if (arg4) {
				mfec(arg1, 4, Package(){0,0,0,i000}, 0x30000002)
			}
			Increment(i000)
			if (arg3) {
				mm04(arg1, 0, 0, 0, i000, Package(){0x51000001})
			}
			Increment(i000)

			if (arg3) {
				mf02(arg0, 2, Buffer(){0,4}, arg1, 4, Package(){0,0,0,i000})
			}
			if (arg4) {
				mfec(arg1, 4, Package(){0,0,0,i000}, 0x20000002)
			}
			Increment(i000)
			if (arg3) {
				mm04(arg1, 0, 0, 0, i000, Package(){0x51000002})
			}
			Increment(i000)

			if (arg3) {
				mf02(arg0, 1, Buffer(){4}, arg1, 4, Package(){0,0,0,i000})
			}
			if (arg4) {
				mfec(arg1, 4, Package(){0,0,0,i000}, 0x10000002)
			}
			Increment(i000)
			if (arg3) {
				mm04(arg1, 0, 0, 0, i000, Package(){0x51000003})
			}
			Increment(i000)

			/* Reference to Package */

			if (arg3) {
				mf02(arg0, 3, Buffer(){0,0,0}, arg1, 4, Package(){0,0,0,i000})
			}
			if (arg4) {
				mfed(arg1, 4, Package(){0,0,0,i000}, 0, 0x40000000)
			}
			Increment(i000)

			/*
                   * Create IRefs to all levels from 3-level Package.
                   * Alternate IRefs with Packages.
                   */

			Store(arg2, i000)
			if (arg3) {
				mf02(arg0, 4, Buffer(){0,0,0,0}, arg1, 3, Package(){0,0,i000})
			}
			if (arg4) {
				mfec(arg1, 3, Package(){0,0,i000}, 0x40000000)
			}
			Increment(i000)
			if (arg3) {
				mm03(arg1, 0, 0, i000, Package(){0x41000000})
			}
			Increment(i000)

			if (arg3) {
				mf02(arg0, 3, Buffer(){0,0,4}, arg1, 3, Package(){0,0,i000})
			}
			if (arg4) {
				mfec(arg1, 3, Package(){0,0,i000}, 0x30000002)
			}
			Increment(i000)
			if (arg3) {
				mm03(arg1, 0, 0, i000, Package(){0x41000001})
			}
			Increment(i000)

			if (arg3) {
				mf02(arg0, 2, Buffer(){0,4}, arg1, 3, Package(){0,0,i000})
			}
			if (arg4) {
				mfec(arg1, 3, Package(){0,0,i000}, 0x20000002)
			}
			Increment(i000)
			if (arg3) {
				mm03(arg1, 0, 0, i000, Package(){0x41000002})
			}
			Increment(i000)

			if (arg3) {
				mf02(arg0, 1, Buffer(){4}, arg1, 3, Package(){0,0,i000})
			}
			if (arg4) {
				mfec(arg1, 3, Package(){0,0,i000}, 0x10000002)
			}
			Increment(i000)
			if (arg3) {
				mm03(arg1, 0, 0, i000, Package(){0x41000003})
			}
			Increment(i000)

			/*
                   * Create IRefs to all levels from 2-level Package.
                   * Alternate IRefs with Packages.
                   */

			Store(arg2, i000)
			if (arg3) {
				mf02(arg0, 4, Buffer(){0,0,0,0}, arg1, 2, Package(){0,i000})
			}
			if (arg4) {
				mfec(arg1, 2, Package(){0,i000}, 0x40000000)
			}
			Increment(i000)
			if (arg3) {
				mm02(arg1, 0, i000, Package(){0x31000000})
			}
			Increment(i000)

			if (arg3) {
				mf02(arg0, 3, Buffer(){0,0,4}, arg1, 2, Package(){0,i000})
			}
			if (arg4) {
				mfec(arg1, 2, Package(){0,i000}, 0x30000002)
			}
			Increment(i000)
			if (arg3) {
				mm02(arg1, 0, i000, Package(){0x31000001})
			}
			Increment(i000)

			if (arg3) {
				mf02(arg0, 2, Buffer(){0,4}, arg1, 2, Package(){0,i000})
			}
			if (arg4) {
				mfec(arg1, 2, Package(){0,i000}, 0x20000002)
			}
			Increment(i000)
			if (arg3) {
				mm02(arg1, 0, i000, Package(){0x31000002})
			}
			Increment(i000)

			if (arg3) {
				mf02(arg0, 1, Buffer(){4}, arg1, 2, Package(){0,i000})
			}
			if (arg4) {
				mfec(arg1, 2, Package(){0,i000}, 0x10000002)
			}
			Increment(i000)
			if (arg3) {
				mm02(arg1, 0, i000, Package(){0x31000003})
			}
			Increment(i000)

			/*
                   * Create IRefs to all levels from 1-level Package.
                   * Alternate IRefs with Packages.
                   */

			Store(arg2, i000)
			if (arg3) {
				mf02(arg0, 4, Buffer(){0,0,0,0}, arg1, 1, Package(){i000})
			}
			if (arg4) {
				mfec(arg1, 1, Package(){i000}, 0x40000000)
			}
			Increment(i000)
			if (arg3) {
				mm01(arg1, i000, Package(){0x21000000})
			}
			Increment(i000)

			if (arg3) {
				mf02(arg0, 3, Buffer(){0,0,4}, arg1, 1, Package(){i000})
			}
			if (arg4) {
				mfec(arg1, 1, Package(){i000}, 0x30000002)
			}
			Increment(i000)
			if (arg3) {
				mm01(arg1, i000, Package(){0x21000001})
			}
			Increment(i000)

			if (arg3) {
				mf02(arg0, 2, Buffer(){0,4}, arg1, 1, Package(){i000})
			}
			if (arg4) {
				mfec(arg1, 1, Package(){i000}, 0x20000002)
			}
			Increment(i000)
			if (arg3) {
				mm01(arg1, i000, Package(){0x21000002})
			}
			Increment(i000)

			if (arg3) {
				mf02(arg0, 1, Buffer(){4}, arg1, 1, Package(){i000})
			}
			if (arg4) {
				mfec(arg1, 1, Package(){i000}, 0x10000002)
			}
			Increment(i000)
			if (arg3) {
				mm01(arg1, i000, Package(){0x21000003})
			}
			Increment(i000)
		}

		/* Verification */
		Method(mmm2)
		{
			m004(p000, 0, 0, 0, 0, 0x40000000)
			m004(p000, 0, 0, 2, 0, 0x40000001)
			m004(p000, 0, 2, 0, 0, 0x40000002)
			m004(p000, 0, 2, 2, 0, 0x40000003)
			m004(p000, 2, 0, 0, 0, 0x40000004)
			m004(p000, 2, 0, 2, 0, 0x40000005)
			m004(p000, 2, 2, 0, 0, 0x40000006)
			m004(p000, 2, 2, 2, 0, 0x40000007)
			m003(p000, 0, 0, 4, 0x30000002)
			m003(p000, 0, 2, 4, 0x30000005)
			m003(p000, 2, 0, 4, 0x30000008)
			m003(p000, 2, 2, 4, 0x3000000b)
			m002(p000, 0, 4, 0x20000002)
			m002(p000, 2, 4, 0x20000005)
			m001(p000, 4, 0x10000002)
		}

		SRMT("mfee")

		mmm0(8)

		mmm1(p000, p000, 18, 1, 1)
		mmm1(p000, p001, 28, 1, 1)
		mmm1(p001, p001, 38, 1, 1)
		mmm1(p001, p000, 48, 1, 1)

		mmm1(0, p000, 18, 0, 1)
		mmm1(0, p001, 28, 0, 1)
		mmm1(0, p001, 38, 0, 1)
		mmm1(0, p000, 48, 0, 1)

		mmm2()

		/* Repeat the same */

		mmm0(8)

		mmm1(p000, p000, 18, 1, 1)
		mmm1(p000, p001, 28, 1, 1)
		mmm1(p001, p001, 38, 1, 1)
		mmm1(p001, p000, 48, 1, 1)

		mmm1(0, p000, 18, 0, 1)
		mmm1(0, p001, 28, 0, 1)
		mmm1(0, p001, 38, 0, 1)
		mmm1(0, p000, 48, 0, 1)

		mmm2()
}
