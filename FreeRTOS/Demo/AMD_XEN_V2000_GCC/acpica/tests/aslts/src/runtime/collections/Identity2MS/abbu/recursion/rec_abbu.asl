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
 * Tests to check recursive calls of methods for different structure of
 * sub-trees containing the point from where the call is made and the point
 * which is just the invoked method, and different relative disposition of
 * those sub-trees containing the points.
 */

Name(z171, 171)


Processor(pr00, 0, 0x000, 0x008)
{
	Name(i000, 0xabcd0000)
}

Name(i000, 0)

Method(mr00,, Serialized)
{
	Name(ts, "mr00")

	Device(d100)
	{
		Name(i200, 0xabcd0200)
		Name(i201, 0xabcd0201)
	}

	Device(d101)
	{
		Name(i202, 0xabcd0202)
		Method(m203,, Serialized)
		{
			Name(i300, 0xabcd0300)
			Name(i301, 0xabcd0301)
			Store("---------------------------------------- Run m203", Debug)
			Increment(i000)
			if (LLess(i000, 3)) {
				m203()
			}
		}
		Name(i204, 0xabcd0204)
	}
	Device(d102)
	{
		Name(i205, 0xabcd0205)
		Name(i206, 0xabcd0206)
	}
	d101.m203()
}

Method(mr01)
{
/*
    CH03(ts, z169, 0x100, __LINE__, 0)

    mm00()

    if (LNotEqual(i000, 0xabcd0000)) {
        err(ts, z169, __LINE__, 0, 0, i000, 0xabcd0000)
    }

    CH03(ts, z169, 0x101, __LINE__, 0)
*/
}

Method(mrff,, Serialized)
{
	Name(run0, 1)

	SRMT("mr00")
	mr00()
}
