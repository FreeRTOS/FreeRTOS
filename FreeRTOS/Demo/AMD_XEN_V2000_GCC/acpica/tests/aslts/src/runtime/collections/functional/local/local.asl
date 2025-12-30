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
 * Control method objects
 */

/*
 * local.asl is not introduced in aslts.
 * See, if it should be advanced and introduced.
 */

Name(z999, 1)

Method(ma00, 7)
{
	Method(m000, 6)
	{
		Method(m000, 5)
		{
			Method(m000, 4)
			{
				Method(m000, 3)
				{
					Method(m000, 2)
					{
						Method(m000, 1)
						{
							Method(m000, 0)
							{
								Method(m000)
								{
								}
								m000()
							}
							m000()
						}
						m000(28)
					}
					m000(26,27)
				}
				m000(23,24,25)
			}
			m000(19,20,21,22)
		} // 5

		if (LNotEqual(arg0, 8)) {
			err(arg0, z999, __LINE__, 0, 0, arg0, 8)
		}
		if (LNotEqual(arg1, 9)) {
			err(arg0, z999, __LINE__, 0, 0, arg0, 9)
		}
		if (LNotEqual(arg2, 10)) {
			err(arg0, z999, __LINE__, 0, 0, arg0, 10)
		}
		if (LNotEqual(arg3, 11)) {
			err(arg0, z999, __LINE__, 0, 0, arg0, 11)
		}
		if (LNotEqual(arg4, 12)) {
			err(arg0, z999, __LINE__, 0, 0, arg0, 12)
		}
		if (LNotEqual(arg5, 13)) {
			err(arg0, z999, __LINE__, 0, 0, arg0, 13)
		}
//		if (LNotEqual(arg6, 7)) {
//			err(arg0, z999, __LINE__, 0, 0, arg0, 7)
//		}

		m000(14,15,16,17,18)

	} // 6

	if (LNotEqual(arg0, 1)) {
		err(arg0, z999, __LINE__, 0, 0, arg0, 1)
	}
	if (LNotEqual(arg1, 2)) {
		err(arg0, z999, __LINE__, 0, 0, arg0, 2)
	}
	if (LNotEqual(arg2, 3)) {
		err(arg0, z999, __LINE__, 0, 0, arg0, 3)
	}
	if (LNotEqual(arg3, 4)) {
		err(arg0, z999, __LINE__, 0, 0, arg0, 4)
	}
	if (LNotEqual(arg4, 5)) {
		err(arg0, z999, __LINE__, 0, 0, arg0, 5)
	}
	if (LNotEqual(arg5, 6)) {
		err(arg0, z999, __LINE__, 0, 0, arg0, 6)
	}
	if (LNotEqual(arg6, 7)) {
		err(arg0, z999, __LINE__, 0, 0, arg0, 7)
	}

	m000(8,9,10,11,12,13)

	if (LNotEqual(arg0, 1)) {
		err(arg0, z999, __LINE__, 0, 0, arg0, 1)
	}
	if (LNotEqual(arg1, 2)) {
		err(arg0, z999, __LINE__, 0, 0, arg0, 2)
	}
	if (LNotEqual(arg2, 3)) {
		err(arg0, z999, __LINE__, 0, 0, arg0, 3)
	}
	if (LNotEqual(arg3, 4)) {
		err(arg0, z999, __LINE__, 0, 0, arg0, 4)
	}
	if (LNotEqual(arg4, 5)) {
		err(arg0, z999, __LINE__, 0, 0, arg0, 5)
	}
	if (LNotEqual(arg5, 6)) {
		err(arg0, z999, __LINE__, 0, 0, arg0, 6)
	}
	if (LNotEqual(arg6, 7)) {
		err(arg0, z999, __LINE__, 0, 0, arg0, 7)
	}
}

// Run-method
Method(CMO0)
{
	ma00(1,2,3,4,5,6,7)
}
