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
 * Method execution control
 *
 * Timing operators
 */

Name(z006, 6)
Name(MSLP, 2000)	// Max sleep (ms) defined in acconfig.h, Oct 2013

// Verifying 1-parameter, 0-result operator
//
// Arg5 - additional parameter (event...)
//
// Local0 - argument passed by test (MilliSeconds)
// Local4 - specified time to be delayed (in Timer units)
// Local6 - time actually was delayed (measured by Timer, in Timer units)
// Local7 - delta == (actual - specified) (in Timer units)
//
Method(m0c8, 6)
{
	Store(0, Local5)
	Store(arg1, Local3)

	While(Local3) {

		// Operand

		Store(DeRefOf(Index(arg3, Local5)), Local0)

		switch (arg4) {
			case (0) {
				if (LLess(MSLP, Local0)) {
					// Exceeding max allowable sleep time
					Store("m0c8: Note, argument exceeds max defined time for Sleep.",
					      Debug);
					Break
				}

				Store(Timer, Local1)
				Sleep(Local0)
				Store(Timer, Local2)
				Subtract(Local2, Local1, Local6)
				Multiply(Local0, 10000, Local4)

				if (LLess(Local6, Local4)) {
					Subtract(Local4, Local6, Local7)
					err(arg0, z006, __LINE__, 0, 0, Local5, arg2)
					Store(Local0, Debug)
					Store(Local4, Debug)
					Store(Local6, Debug)
					Store(Local7, Debug)
					return (1)
				} else {
					Subtract(Local6, Local4, Local7)
				}
			}
			case (1) {
				Store(Timer, Local1)
				Stall(Local0)
				Store(Timer, Local2)
				Subtract(Local2, Local1, Local6)
				Multiply(Local0, 10, Local4)

				if (LLess(Local6, Local4)) {
					Subtract(Local4, Local6, Local7)
					err(arg0, z006, __LINE__, 0, 0, Local5, arg2)
					Store(Local0, Debug)
					Store(Local4, Debug)
					Store(Local6, Debug)
					Store(Local7, Debug)
					return (1)
				} else {
					Subtract(Local6, Local4, Local7)
				}
			}
			case (2) {
				Store(Timer, Local1)
				Wait(arg5, Local0)
				Store(Timer, Local2)
				Subtract(Local2, Local1, Local6)
				Multiply(Local0, 10000, Local4)

				if (LLess(Local6, Local4)) {
					Subtract(Local4, Local6, Local7)
					err(arg0, z006, __LINE__, 0, 0, Local5, arg2)
					Store(Local0, Debug)
					Store(Local4, Debug)
					Store(Local6, Debug)
					Store(Local7, Debug)
					return (1)
				} else {
					Subtract(Local6, Local4, Local7)
				}
			}
		}

		if (0) {
			Store("====================:", Debug)
			Store(Local0, Debug)
			Store(Local4, Debug)
			Store(Local6, Debug)
			Store(Local7, Debug)
		}

		Increment(Local5)
		Decrement(Local3)
	}

	return (0)
}

// Sleep. Sleep n milliseconds (yields the processor)
Method(m0c9,, Serialized)
{
	Name(ts, "m0c9")

	Store("TEST: m0c9, Sleep, sleep n milliseconds (yields the processor)", Debug)

	Name(p000, Package() { 0, 1, 10, 100, 1000, 2000, 3456, 10000, 12345 })

	Store(1, Local0)
	While(Local0) {
		if (m0c8(ts, 9, "p000", p000, 0, 0)) {
			return (1)
		}
		Decrement(Local0)
	}
	return (0)
}

// Stall. Delay n microseconds (does not yield the processor)
Method(m0ca,, Serialized)
{
	Name(ts, "m0ca")

	Store("TEST: m0ca, Stall, delay n microseconds (does not yield the processor)", Debug)

	Name(p000, Package() { 0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
					10, 20, 30, 40, 50, 60, 70, 80, 90, 100,
					14, 23, 37, 49, 55, 62, 78, 81, 96, 100 })

	Store(5, Local0)
	While(Local0) {
		if (m0c8(ts, 30, "p000", p000, 1, 0)) {
			return (1)
		}
		Decrement(Local0)
	}
	return (0)
}

// Wait. The calling method blocks while waiting for the event to be signaled
Method(m0cb,, Serialized)
{
	Name(ts, "m0cb")

	Store("TEST: m0cb, Wait, waiting for the event to be signaled", Debug)

	Event(e000)

	Name(p000, Package() { 0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
					10, 20, 30, 40, 50, 60, 70, 80, 90, 100,
					14, 23, 37, 49, 55, 62, 78, 81, 96, 100 })

	Store(1, Local0)
	While(Local0) {
		if (m0c8(ts, 30, "p000", p000, 2, e000)) {
			return (1)
		}
		Decrement(Local0)
	}

	Name(p001, Package() { 0, 1, 10, 100, 1000, 2000, 3456, 10000, 12345 })

	Store(1, Local0)
	While(Local0) {
		if (m0c8(ts, 9, "p001", p001, 2, e000)) {
			return (1)
		}
		Decrement(Local0)
	}
	return (0)
}

// Handle and summarize the Timer-times package.
Method(m0cc, 3, Serialized)
{
	Name(n000, 0)
	Name(ncur, 0)

	// Size of p001=(p000-1)
	Name(n001, 0)
	Subtract(arg2, 1, n001)

	Name(p001, Package(n001) {})

	Name(nmin, 0)
	Name(nmax, 0)
	Name(ndcr, 0)
	Name(navr, 0)
	Name(nspl, 0)

	// Index for p001
	Name(ncu1, 0)

	// Obtain the adjacent deltas.

	Store(0, Local7)
	Store(arg2, n000)
	Store(0, ncur)
	Store(0, ncu1)

	While (n000) {
		Store(DeRefOf(Index(arg1, ncur)), Local0)
		if (ncur) {
			Subtract(Local0, Local7, Local6)
			Store(Local6, Index(p001, ncu1))
			Increment(ncu1)
			if (0) {
				Store(Local6, Debug)
			}
		}

		// Previous time

		Store(Local0, Local7)

		Decrement(n000)
		Increment(ncur)
	}

	// Summarize - min, max, average

	Store(0, Local6)
	Store(n001, n000)
	Store(0, ncur)

	Store(0, nmin)
	Store(0, nmax)
	Store(0, ndcr)
	Store(0, navr)

	While (n000) {
		Store(DeRefOf(Index(p001, ncur)), Local0)
		Add(Local6, Local0, Local6)
		if (ncur) {
			// New value less then previous
			if (LLess(Local0, Local7)) {
				Increment(ndcr)
			}
			if (LLess(Local0, nmin)) {
				Store(Local0, nmin)
			} elseif (LGreater(Local0, nmax)) {
				Store(Local0, nmax)
			}
		} else {
			Store(Local0, nmin)
			Store(Local0, nmax)
		}

		// Previous delta

		Store(Local0, Local7)

		Decrement(n000)
		Increment(ncur)
	}

	Divide(Local6, n001, Local0, navr)

	// Summarize - check monotony, no splashes
	// exceeding the adjacent points in times.

	Store(0, Local6)
	Store(n001, n000)
	Store(0, ncur)
	Store(0, nspl)

	While (n000) {
		Store(DeRefOf(Index(arg1, ncur)), Local0)
		if (ncur) {

			// Splashes different in times

			if (LLess(Local0, Local7)) {
				Divide(Local7, Local0, Local1, Local6)
			} else {
				Divide(Local0, Local7, Local1, Local6)
			}
			if (LGreater(Local6, 2)) {
				Increment(nspl)
			}
		}

		// Previous delta

		Store(Local0, Local7)

		Decrement(n000)
		Increment(ncur)
	}

	Store("Summary:", Debug)

	Store(nmin, Debug)
	Store(nmax, Debug)
	Store(navr, Debug)
	Store(ndcr, Debug)
	Store(nspl, Debug)
}

// Timer with Package - is not a test as such, but shows behaviour of Timer.
//
// Get Timer-time N times, store them into Package.
// Then, calculate the Timer-time between each adjacent points.
// Much time is spent on storing into Package.
//
// Summary of deltas between the adjacent points:
//
//  nmin - minimal
//  nmax - maximal
//  navr - average
//
//  Monotony:
//
//  ndcr - # lower than previous
//  nspl - # splashes exceeding the adjacent point by 2 or more times
Method(m0cd,, Serialized)
{
	Name(ts, "m0cd")

	Store("TEST: m0cd, Timer with Package", Debug)

	// nsz0 - size of p000
	// n000 - decr cur counter
	// ncur - incr cur counter

	Name(nsz0, 101)
	Name(n000, 0)
	Name(ncur, 0)

	Store(nsz0, n000)
	Store(0, ncur)

	Name(p000, Package(n000) {})

	// Obtain the time and store into Package.
	// Do as quickly as possible without any unnecessary actions.
	While (n000) {

		Store(Timer, Local0)
		Store(Local0, Index(p000, ncur))
		Decrement(n000)
		Increment(ncur)
	}

	m0cc(ts, p000, nsz0)
}

// Timer with Name
Method(m0ce,, Serialized)
{
	Name(ts, "m0ce")

	Store("TEST: m0ce, Timer with Name", Debug)

	Name(nsz0, 101)
	Name(p000, Package(nsz0) {})

	Name(tmp, 0)

	Name(n000, 0)
	Name(n001, 0)
	Name(n002, 0)
	Name(n003, 0)
	Name(n004, 0)
	Name(n005, 0)
	Name(n006, 0)
	Name(n007, 0)
	Name(n008, 0)
	Name(n009, 0)
	Name(n010, 0)
	Name(n011, 0)
	Name(n012, 0)
	Name(n013, 0)
	Name(n014, 0)
	Name(n015, 0)
	Name(n016, 0)
	Name(n017, 0)
	Name(n018, 0)
	Name(n019, 0)
	Name(n020, 0)
	Name(n021, 0)
	Name(n022, 0)
	Name(n023, 0)
	Name(n024, 0)
	Name(n025, 0)
	Name(n026, 0)
	Name(n027, 0)
	Name(n028, 0)
	Name(n029, 0)
	Name(n030, 0)
	Name(n031, 0)
	Name(n032, 0)
	Name(n033, 0)
	Name(n034, 0)
	Name(n035, 0)
	Name(n036, 0)
	Name(n037, 0)
	Name(n038, 0)
	Name(n039, 0)
	Name(n040, 0)
	Name(n041, 0)
	Name(n042, 0)
	Name(n043, 0)
	Name(n044, 0)
	Name(n045, 0)
	Name(n046, 0)
	Name(n047, 0)
	Name(n048, 0)
	Name(n049, 0)
	Name(n050, 0)
	Name(n051, 0)
	Name(n052, 0)
	Name(n053, 0)
	Name(n054, 0)
	Name(n055, 0)
	Name(n056, 0)
	Name(n057, 0)
	Name(n058, 0)
	Name(n059, 0)
	Name(n060, 0)
	Name(n061, 0)
	Name(n062, 0)
	Name(n063, 0)
	Name(n064, 0)
	Name(n065, 0)
	Name(n066, 0)
	Name(n067, 0)
	Name(n068, 0)
	Name(n069, 0)
	Name(n070, 0)
	Name(n071, 0)
	Name(n072, 0)
	Name(n073, 0)
	Name(n074, 0)
	Name(n075, 0)
	Name(n076, 0)
	Name(n077, 0)
	Name(n078, 0)
	Name(n079, 0)
	Name(n080, 0)
	Name(n081, 0)
	Name(n082, 0)
	Name(n083, 0)
	Name(n084, 0)
	Name(n085, 0)
	Name(n086, 0)
	Name(n087, 0)
	Name(n088, 0)
	Name(n089, 0)
	Name(n090, 0)
	Name(n091, 0)
	Name(n092, 0)
	Name(n093, 0)
	Name(n094, 0)
	Name(n095, 0)
	Name(n096, 0)
	Name(n097, 0)
	Name(n098, 0)
	Name(n099, 0)
	Name(n100, 0)

	Store(Timer, n000)
	Store(Timer, n001)
	Store(Timer, n002)
	Store(Timer, n003)
	Store(Timer, n004)
	Store(Timer, n005)
	Store(Timer, n006)
	Store(Timer, n007)
	Store(Timer, n008)
	Store(Timer, n009)
	Store(Timer, n010)
	Store(Timer, n011)
	Store(Timer, n012)
	Store(Timer, n013)
	Store(Timer, n014)
	Store(Timer, n015)
	Store(Timer, n016)
	Store(Timer, n017)
	Store(Timer, n018)
	Store(Timer, n019)
	Store(Timer, n020)
	Store(Timer, n021)
	Store(Timer, n022)
	Store(Timer, n023)
	Store(Timer, n024)
	Store(Timer, n025)
	Store(Timer, n026)
	Store(Timer, n027)
	Store(Timer, n028)
	Store(Timer, n029)
	Store(Timer, n030)
	Store(Timer, n031)
	Store(Timer, n032)
	Store(Timer, n033)
	Store(Timer, n034)
	Store(Timer, n035)
	Store(Timer, n036)
	Store(Timer, n037)
	Store(Timer, n038)
	Store(Timer, n039)
	Store(Timer, n040)
	Store(Timer, n041)
	Store(Timer, n042)
	Store(Timer, n043)
	Store(Timer, n044)
	Store(Timer, n045)
	Store(Timer, n046)
	Store(Timer, n047)
	Store(Timer, n048)
	Store(Timer, n049)
	Store(Timer, n050)
	Store(Timer, n051)
	Store(Timer, n052)
	Store(Timer, n053)
	Store(Timer, n054)
	Store(Timer, n055)
	Store(Timer, n056)
	Store(Timer, n057)
	Store(Timer, n058)
	Store(Timer, n059)
	Store(Timer, n060)
	Store(Timer, n061)
	Store(Timer, n062)
	Store(Timer, n063)
	Store(Timer, n064)
	Store(Timer, n065)
	Store(Timer, n066)
	Store(Timer, n067)
	Store(Timer, n068)
	Store(Timer, n069)
	Store(Timer, n070)
	Store(Timer, n071)
	Store(Timer, n072)
	Store(Timer, n073)
	Store(Timer, n074)
	Store(Timer, n075)
	Store(Timer, n076)
	Store(Timer, n077)
	Store(Timer, n078)
	Store(Timer, n079)
	Store(Timer, n080)
	Store(Timer, n081)
	Store(Timer, n082)
	Store(Timer, n083)
	Store(Timer, n084)
	Store(Timer, n085)
	Store(Timer, n086)
	Store(Timer, n087)
	Store(Timer, n088)
	Store(Timer, n089)
	Store(Timer, n090)
	Store(Timer, n091)
	Store(Timer, n092)
	Store(Timer, n093)
	Store(Timer, n094)
	Store(Timer, n095)
	Store(Timer, n096)
	Store(Timer, n097)
	Store(Timer, n098)
	Store(Timer, n099)
	Store(Timer, n100)


	Store(n000, Index(p000, tmp)) Increment(tmp)
	Store(n001, Index(p000, tmp)) Increment(tmp)
	Store(n002, Index(p000, tmp)) Increment(tmp)
	Store(n003, Index(p000, tmp)) Increment(tmp)
	Store(n004, Index(p000, tmp)) Increment(tmp)
	Store(n005, Index(p000, tmp)) Increment(tmp)
	Store(n006, Index(p000, tmp)) Increment(tmp)
	Store(n007, Index(p000, tmp)) Increment(tmp)
	Store(n008, Index(p000, tmp)) Increment(tmp)
	Store(n009, Index(p000, tmp)) Increment(tmp)
	Store(n010, Index(p000, tmp)) Increment(tmp)
	Store(n011, Index(p000, tmp)) Increment(tmp)
	Store(n012, Index(p000, tmp)) Increment(tmp)
	Store(n013, Index(p000, tmp)) Increment(tmp)
	Store(n014, Index(p000, tmp)) Increment(tmp)
	Store(n015, Index(p000, tmp)) Increment(tmp)
	Store(n016, Index(p000, tmp)) Increment(tmp)
	Store(n017, Index(p000, tmp)) Increment(tmp)
	Store(n018, Index(p000, tmp)) Increment(tmp)
	Store(n019, Index(p000, tmp)) Increment(tmp)
	Store(n020, Index(p000, tmp)) Increment(tmp)
	Store(n021, Index(p000, tmp)) Increment(tmp)
	Store(n022, Index(p000, tmp)) Increment(tmp)
	Store(n023, Index(p000, tmp)) Increment(tmp)
	Store(n024, Index(p000, tmp)) Increment(tmp)
	Store(n025, Index(p000, tmp)) Increment(tmp)
	Store(n026, Index(p000, tmp)) Increment(tmp)
	Store(n027, Index(p000, tmp)) Increment(tmp)
	Store(n028, Index(p000, tmp)) Increment(tmp)
	Store(n029, Index(p000, tmp)) Increment(tmp)
	Store(n030, Index(p000, tmp)) Increment(tmp)
	Store(n031, Index(p000, tmp)) Increment(tmp)
	Store(n032, Index(p000, tmp)) Increment(tmp)
	Store(n033, Index(p000, tmp)) Increment(tmp)
	Store(n034, Index(p000, tmp)) Increment(tmp)
	Store(n035, Index(p000, tmp)) Increment(tmp)
	Store(n036, Index(p000, tmp)) Increment(tmp)
	Store(n037, Index(p000, tmp)) Increment(tmp)
	Store(n038, Index(p000, tmp)) Increment(tmp)
	Store(n039, Index(p000, tmp)) Increment(tmp)
	Store(n040, Index(p000, tmp)) Increment(tmp)
	Store(n041, Index(p000, tmp)) Increment(tmp)
	Store(n042, Index(p000, tmp)) Increment(tmp)
	Store(n043, Index(p000, tmp)) Increment(tmp)
	Store(n044, Index(p000, tmp)) Increment(tmp)
	Store(n045, Index(p000, tmp)) Increment(tmp)
	Store(n046, Index(p000, tmp)) Increment(tmp)
	Store(n047, Index(p000, tmp)) Increment(tmp)
	Store(n048, Index(p000, tmp)) Increment(tmp)
	Store(n049, Index(p000, tmp)) Increment(tmp)
	Store(n050, Index(p000, tmp)) Increment(tmp)
	Store(n051, Index(p000, tmp)) Increment(tmp)
	Store(n052, Index(p000, tmp)) Increment(tmp)
	Store(n053, Index(p000, tmp)) Increment(tmp)
	Store(n054, Index(p000, tmp)) Increment(tmp)
	Store(n055, Index(p000, tmp)) Increment(tmp)
	Store(n056, Index(p000, tmp)) Increment(tmp)
	Store(n057, Index(p000, tmp)) Increment(tmp)
	Store(n058, Index(p000, tmp)) Increment(tmp)
	Store(n059, Index(p000, tmp)) Increment(tmp)
	Store(n060, Index(p000, tmp)) Increment(tmp)
	Store(n061, Index(p000, tmp)) Increment(tmp)
	Store(n062, Index(p000, tmp)) Increment(tmp)
	Store(n063, Index(p000, tmp)) Increment(tmp)
	Store(n064, Index(p000, tmp)) Increment(tmp)
	Store(n065, Index(p000, tmp)) Increment(tmp)
	Store(n066, Index(p000, tmp)) Increment(tmp)
	Store(n067, Index(p000, tmp)) Increment(tmp)
	Store(n068, Index(p000, tmp)) Increment(tmp)
	Store(n069, Index(p000, tmp)) Increment(tmp)
	Store(n070, Index(p000, tmp)) Increment(tmp)
	Store(n071, Index(p000, tmp)) Increment(tmp)
	Store(n072, Index(p000, tmp)) Increment(tmp)
	Store(n073, Index(p000, tmp)) Increment(tmp)
	Store(n074, Index(p000, tmp)) Increment(tmp)
	Store(n075, Index(p000, tmp)) Increment(tmp)
	Store(n076, Index(p000, tmp)) Increment(tmp)
	Store(n077, Index(p000, tmp)) Increment(tmp)
	Store(n078, Index(p000, tmp)) Increment(tmp)
	Store(n079, Index(p000, tmp)) Increment(tmp)
	Store(n080, Index(p000, tmp)) Increment(tmp)
	Store(n081, Index(p000, tmp)) Increment(tmp)
	Store(n082, Index(p000, tmp)) Increment(tmp)
	Store(n083, Index(p000, tmp)) Increment(tmp)
	Store(n084, Index(p000, tmp)) Increment(tmp)
	Store(n085, Index(p000, tmp)) Increment(tmp)
	Store(n086, Index(p000, tmp)) Increment(tmp)
	Store(n087, Index(p000, tmp)) Increment(tmp)
	Store(n088, Index(p000, tmp)) Increment(tmp)
	Store(n089, Index(p000, tmp)) Increment(tmp)
	Store(n090, Index(p000, tmp)) Increment(tmp)
	Store(n091, Index(p000, tmp)) Increment(tmp)
	Store(n092, Index(p000, tmp)) Increment(tmp)
	Store(n093, Index(p000, tmp)) Increment(tmp)
	Store(n094, Index(p000, tmp)) Increment(tmp)
	Store(n095, Index(p000, tmp)) Increment(tmp)
	Store(n096, Index(p000, tmp)) Increment(tmp)
	Store(n097, Index(p000, tmp)) Increment(tmp)
	Store(n098, Index(p000, tmp)) Increment(tmp)
	Store(n099, Index(p000, tmp)) Increment(tmp)
	Store(n100, Index(p000, tmp)) Increment(tmp)

	m0cc(ts, p000, nsz0)
}

// Timer with LocalX
Method(m0cf,, Serialized)
{
	Name(ts, "m0cf")

	Store("TEST: m0cf, Timer with LocalX", Debug)

	Name(nsz0, 101)
	Name(n000, 0)
	Name(tmp, 0)
	Name(last, 0)
	Name(dlta, 0)

	Store(nsz0, n000)

	Name(p000, Package(n000) {})

	While (n000) {

		Store(Timer, Local0)
		Store(Timer, Local1)
		Store(Timer, Local2)
		Store(Timer, Local3)
		Store(Timer, Local4)
		Store(Timer, Local5)
		Store(Timer, Local6)
		Store(Timer, Local7)

		// Eliminate delta due to the storage into Package

		if (last) {
			Subtract(Local0, last, dlta)

			Subtract(Local0, dlta, Local0)
			Subtract(Local1, dlta, Local1)
			Subtract(Local2, dlta, Local2)
			Subtract(Local3, dlta, Local3)
			Subtract(Local4, dlta, Local4)
			Subtract(Local5, dlta, Local5)
			Subtract(Local6, dlta, Local6)
			Subtract(Local7, dlta, Local7)
		}

		Store(Local0, Index(p000, tmp)) Increment(tmp)
		if (LGreaterEqual(tmp, nsz0)) {
			break
		}
		Store(Local1, Index(p000, tmp)) Increment(tmp)
		if (LGreaterEqual(tmp, nsz0)) {
			break
		}
		Store(Local2, Index(p000, tmp)) Increment(tmp)
		if (LGreaterEqual(tmp, nsz0)) {
			break
		}
		Store(Local3, Index(p000, tmp)) Increment(tmp)
		if (LGreaterEqual(tmp, nsz0)) {
			break
		}
		Store(Local4, Index(p000, tmp)) Increment(tmp)
		if (LGreaterEqual(tmp, nsz0)) {
			break
		}
		Store(Local5, Index(p000, tmp)) Increment(tmp)
		if (LGreaterEqual(tmp, nsz0)) {
			break
		}
		Store(Local6, Index(p000, tmp)) Increment(tmp)
		if (LGreaterEqual(tmp, nsz0)) {
			break
		}
		Store(Local7, Index(p000, tmp)) Increment(tmp)
		if (LGreaterEqual(tmp, nsz0)) {
			break
		}

		Store(Local7, last)

		Decrement(n000)
	}

	m0cc(ts, p000, nsz0)
}

// Run-method
Method(TIM0)
{
	Store("TEST: TIM0, Timing operators", Debug)

	m0c9()
	m0ca()
	m0cb()
	m0cd()
	m0ce()
	m0cf()
}
