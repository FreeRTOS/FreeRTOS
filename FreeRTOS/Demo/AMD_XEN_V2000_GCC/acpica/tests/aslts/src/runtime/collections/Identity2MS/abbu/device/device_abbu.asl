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
 * Aplicable for abbu only
 */

Name(z172, 172)

Method(dvf2,, Serialized)
{
	Name(ts, "dvf2")
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
			Return (Add(\_SB_.ABBU.dvf2.d000.i000, m003()))
		}
		Return (Add(\_SB_.ABBU.dvf2.d000.i000, m002()))
	}

	Store(Add(\_SB_.ABBU.dvf2.d000.i000, m001()), Local0)
	if (LNotEqual(Local0, 0xabcd0003)) {
		err(ts, z172, __LINE__, 0, 0, Local0, 0xabcd0003)
	}
}

/*
 * Named object as element of Package
 *
 *   Named element of Package, perhaps, is not implemented by MS,
 *   i000 in Package(){i000} is, on MS, the same as Package(){"i000"}.
 *
 * fail
 */
Method(mf26,, Serialized)
{
	Name(ts, "mf26")
	Name(i000, 0xabcd0000)
	Name(i001, 0xabcd0001)
	Name(i002, 0xabcd0002)
	Name(i003, 0xabcd0003)

	Name(ii00, 0x11112222)

	Name(p000, Package() {
		i000,
		i001,
		i002,
		"i000",
		\_SB_.ABBU.mf26.i003,
		0xabcd0004
		})

	Method(m001, 2)
	{
		Store(DerefOf(Index(arg0, 0)), Local0)
		if (LNotEqual(Local0, 0xabcd0000)) {
			err(ts, z164, __LINE__, 0, 0, Local0, 0xabcd0000)
		}
		Store(DerefOf(Index(arg0, 1)), Local0)
		if (LNotEqual(Local0, 0xabcd0001)) {
			err(ts, z164, __LINE__, 0, 0, Local0, 0xabcd0001)
		}
		Store(DerefOf(Index(arg0, 2)), Local0)
		if (LNotEqual(Local0, 0xabcd0002)) {
			err(ts, z164, __LINE__, 0, 0, Local0, 0xabcd0002)
		}
		Store(DerefOf(Index(arg0, 3)), Local0)
		if (LNotEqual(Local0, "i000")) {
			err(ts, z164, __LINE__, 0, 0, Local0, "i000")
		}
		Store(DerefOf(Index(arg0, 4)), Local0)
		if (LNotEqual(Local0, 0xabcd0003)) {
			err(ts, z164, __LINE__, 0, 0, Local0, 0xabcd0003)
		}
		Store(DerefOf(Index(arg0, 5)), Local0)
		if (LNotEqual(Local0, 0xabcd0004)) {
			err(ts, z164, __LINE__, 0, 0, Local0, 0xabcd0004)
		}

		Store(ii00, Index(arg0, 0))

		Store(DerefOf(Index(arg0, 0)), Local0)
		if (LNotEqual(Local0, 0x11112222)) {
			err(ts, z164, __LINE__, 0, 0, Local0, 0x11112222)
		}
	}

	if (0) {
		Store(DerefOf(Index(p000, 0)), Local0)
		OUTP(Local0)
		Store(DerefOf(Index(p000, 1)), Local0)
		OUTP(Local0)
		Store(DerefOf(Index(p000, 2)), Local0)
		OUTP(Local0)
		Store(DerefOf(Index(p000, 3)), Local0)
		OUTP(Local0)
		Store(DerefOf(Index(p000, 4)), Local0)
		OUTP(Local0)
		Store(DerefOf(Index(p000, 5)), Local0)
		OUTP(Local0)
	}

	m001(p000, RefOf(p000))

	Store(DerefOf(Index(p000, 0)), Local0)
	if (LNotEqual(Local0, 0x11112222)) {
		err(ts, z164, __LINE__, 0, 0, Local0, 0x11112222)
	}
	Store(DerefOf(Index(p000, 1)), Local0)
	if (LNotEqual(Local0, 0xabcd0001)) {
		err(ts, z164, __LINE__, 0, 0, Local0, 0xabcd0001)
	}

	Store(DerefOf(Index(p000, 2)), Local0)
	if (LNotEqual(Local0, 0xabcd0002)) {
		err(ts, z164, __LINE__, 0, 0, Local0, 0xabcd0002)
	}

	Store(DerefOf(Index(p000, 3)), Local0)
	if (LNotEqual(Local0, "i000")) {
		err(ts, z164, __LINE__, 0, 0, Local0, "i000")
	}

	Store(DerefOf(Index(p000, 4)), Local0)
	if (LNotEqual(Local0, 0xabcd0003)) {
		err(ts, z164, __LINE__, 0, 0, Local0, 0xabcd0003)
	}

	Store(DerefOf(Index(p000, 5)), Local0)
	if (LNotEqual(Local0, 0xabcd0004)) {
		err(ts, z164, __LINE__, 0, 0, Local0, 0xabcd0004)
	}
}
