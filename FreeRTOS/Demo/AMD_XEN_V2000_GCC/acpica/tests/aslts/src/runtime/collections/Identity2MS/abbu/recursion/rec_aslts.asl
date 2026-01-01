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

Name(z172, 172)

Name(IG00, 0)
Name(IG01, 0)
Name(IG02, 0)
Name(IG03, 0) // Do anything once only

Name(RC00, 5)
Name(RCFF, 1)

Name(ts, "mr00")

Processor(pr00, 0, 0x000, 0x008)
{
	Name(i000, 0xabcd0000)
}

// Initialize sub-test
Method(mrfd)
{
    Store(0, IG00)
    Store(0, IG01)
    Store(0, IG02)
    Store(0, IG03)
}

// Printing
Method(mrfe, 1)
{
    if (RCFF) {
		Store(arg0, Debug)
    }
}

/*
 * 0-th level method M0 is recursively invoked from
 * the same M0 method.
 */
Method(mr00)
{
    Store("mr00", ts)
    mrfe(ts)

    Store(IG00, Local0)
    Increment(IG00)
    Increment(IG02)
    if (LLess(IG00, RC00)) {
        mr00()
    }

    Decrement(IG00)
    if (LNotEqual(Local0, IG00)) {
        err(ts, z172, __LINE__, 0, 0, Local0, IG00)
    }

    if (LNotEqual(IG02, RC00)) {
        if (LNot(IG03)) {
            Store(1, IG03)
            err(ts, z172, __LINE__, 0, 0, IG02, RC00)
        }
    }
}

/*
 * 0-th level method M0 invokes recursively 0-th level method M1
 * which, in its turn, invokes recursively M0
 * M0 and M1 are respectively the preceding and the following peers each to other
 */
Method(mr01, 1)
{
    Store("mr01", ts)

    mrfe(ts)

    Store(IG00, Local1)
    Store(arg0, Local2)
    Increment(IG00)
    Increment(IG02)
    if (LLess(IG00, RC00)) {
        mr02(IG00)
    }

    Decrement(IG00)
    if (LNotEqual(Local1, IG00)) {
        err(ts, z172, __LINE__, 0, 0, Local1, IG00)
    }
    if (LNotEqual(Local2, arg0)) {
        err(ts, z172, __LINE__, 0, 0, Local2, arg0)
    }

    Multiply(RC00, 2, Local0)
    Decrement(Local0)
    if (LNotEqual(IG02, Local0)) {
        if (LNot(IG03)) {
            Store(1, IG03)
            err(ts, z172, __LINE__, 0, 0, IG02, Local0)
        }
    }
}

Method(mr02, 1)
{
    Store("mr02", ts)

    mrfe(ts)

    Store(IG01, Local1)
    Store(arg0, Local2)
    Increment(IG01)
    Increment(IG02)
    if (LLess(IG01, RC00)) {
        mr01(IG01)
    }

    Decrement(IG01)
    if (LNotEqual(Local1, IG01)) {
        err(ts, z172, __LINE__, 0, 0, Local1, IG01)
    }
    if (LNotEqual(Local2, arg0)) {
        err(ts, z172, __LINE__, 0, 0, Local2, arg0)
    }

    Multiply(RC00, 2, Local0)
    Decrement(Local0)
    if (LNotEqual(IG02, Local0)) {
        if (LNot(IG03)) {
            Store(1, IG03)
            err(ts, z172, __LINE__, 0, 0, IG02, Local0)
        }
    }
}

/*
 * 2-th level method M0 is recursively invoked from
 * the same M0 method.
 */
Method(mr03,, Serialized)
{
    Store("mr03", ts)

    Device(d100)
    {
        Name(i200, 0xabcd0200)
        Name(i201, 0xabcd0201)
    }

    Device(d101)
    {
        Name(i202, 0xabcd0202)
        Method(m203)
        {
            mrfe("m203")

            Store(IG00, Local0)
            Increment(IG00)
            Increment(IG02)
            if (LLess(IG00, RC00)) {
                m203()
            }

            Decrement(IG00)
            if (LNotEqual(Local0, IG00)) {
                err(ts, z172, __LINE__, 0, 0, Local0, IG00)
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

    if (LNotEqual(IG02, RC00)) {
        if (LNot(IG03)) {
            Store(1, IG03)
            err(ts, z172, __LINE__, 0, 0, IG02, RC00)
        }
    }
}

/*
 * 2-th level method M0 invokes recursively 0-th level method M1,
 * which is not on a path of M0-sub-tree, M1, in its turn, invokes
 * recursively M0. It is capable because the sub-tree of M0 has been
 * created at the moment when M1 is invoked.
 * Note: we can't run M1 in the first turn by that same reason --
 * sub-tree of M0 would be not created in that case and we fall to
 * AE_NOT_FOUND exception.
 */
Method(mr04,, Serialized)
{
    Store("mr04", ts)

    Device(d100)
    {
        Name(i200, 0xabcd0200)
        Name(i201, 0xabcd0201)
    }

    Device(d101)
    {
        Name(i202, 0xabcd0202)
        Method(m203, 1)
        {
            mrfe("m203")

            Store(IG00, Local0)
            Increment(IG00)
            Increment(IG02)
            if (LLess(IG00, RC00)) {
                mr05(IG00)
            }

            Decrement(IG00)
            if (LNotEqual(Local0, IG00)) {
                err(ts, z172, __LINE__, 0, 0, Local0, IG00)
            }

        }
        Name(i204, 0xabcd0204)
    }
    Device(d102)
    {
        Name(i205, 0xabcd0205)
        Name(i206, 0xabcd0206)
    }

    d101.m203(0)

    Multiply(RC00, 2, Local0)
    Decrement(Local0)
    if (LNotEqual(IG02, Local0)) {
        if (LNot(IG03)) {
            Store(1, IG03)
            err(ts, z172, __LINE__, 0, 0, IG02, Local0)
        }
    }
}

Method(mr05, 1)
{
    Store("mr05", ts)

    mrfe(ts)

    Store(IG01, Local1)
    Store(arg0, Local2)
    Increment(IG01)
    Increment(IG02)
    if (LLess(IG01, RC00)) {
        ^mr04.d101.m203(IG01)
    }

    Decrement(IG01)
    if (LNotEqual(Local1, IG01)) {
        err(ts, z172, __LINE__, 0, 0, Local1, IG01)
    }
    if (LNotEqual(Local2, arg0)) {
        err(ts, z172, __LINE__, 0, 0, Local2, arg0)
    }

    Multiply(RC00, 2, Local0)
    Decrement(Local0)
    if (LNotEqual(IG02, Local0)) {
        if (LNot(IG03)) {
            Store(1, IG03)
            err(ts, z172, __LINE__, 0, 0, IG02, Local0)
        }
    }
}


Method(mrff,, Serialized)
{
    Name(ts, "mrff")
    Name(run0, 1)

    CH03(ts, z172, 0x000, __LINE__, 0)

    SRMT("mr00")
    mrfd()
    mr00()

    SRMT("mr01")
    mrfd()
    mr01(0)

    SRMT("mr02")
    mrfd()
    mr02(0)

    SRMT("mr03")
    mrfd()
    mr03()

    SRMT("mr04")
    mrfd()
    mr04()

/*
test --- run mr05 and expect exception
*/


    CH03(ts, z172, 0x000, __LINE__, 0)
}
