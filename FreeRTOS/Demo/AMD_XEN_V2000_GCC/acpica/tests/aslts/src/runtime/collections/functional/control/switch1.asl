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
 * Switch, Case, Default operators
 */

Name(z068, 68)

Name(swi0, 0)
Name(swi1, 0)


/////////////// {if}

Method(m0d0)
{
	Store(2, Local0)

	Switch (swi0) {
	Case (0) {
	Store(1, Local0)
		Switch (swi1) {
		Case (0) {
		Store(0, Local0)
		}}
	}}
	return (Local0)
}

Method(m0d1)
{
	Store(3, Local0)

	Switch (swi0) {
	Case (0) {
	Store(12345678, Local0)
		Switch (swi1) {
		Case (0) {
		Store(0, Local0)
		}
		Case (1) {
		Store(1, Local0)
		}
		Default {
		Store(2, Local0)
		}}
	}}
	return (Local0)
}

/////////////// {if,else} {if}

Method(m0d2)
{
	Store(12345678, Local0)

	Switch (swi0) {
	Case (0) {
	Store(1, Local0)
		Switch (swi1) {
		Case (0) {
		Store(0, Local0)
		}}
	}
	Default {
	Store(3, Local0)
		Switch (swi1) {
		Case (0) {
		Store(2, Local0)
		}}
	}}
	return (Local0)
}

/////////////// {if,else} {if,else}

Method(m0d3)
{
	Store(12345678, Local0)

	Switch (swi0) {
	Case (0) {
	Store(12345678, Local0)
		Switch (swi1) {
		Case (0) {
		Store(0, Local0)
		}
		Default {
		Store(1, Local0)
		}}
	}
	Default {
	Store(12345678, Local0)
		Switch (swi1) {
		Case (0) {
		Store(2, Local0)
		}
		Default {
		Store(3, Local0)
		}}
	}}
	return (Local0)
}

/////////////// {if,else} {if,elseif}

Method(m0d4)
{
	Store(12345678, Local0)

	Switch (swi0) {
	Case (0) {
	Store(2, Local0)
		Switch (swi1) {
		Case (0) {
		Store(0, Local0)
		}
		Case (1) {
		Store(1, Local0)
		}}
	}
	Default {
	Store(5, Local0)
		Switch (swi1) {
		Case (0) {
		Store(3, Local0)
		}
		Case (1) {
		Store(4, Local0)
		}}
	}}
	return (Local0)
}

/////////////// {if,else} {if,elseif,else}

Method(m0d5)
{
	Store(12345678, Local0)

	Switch (swi0) {
	Case (0) {
	Store(12345678, Local0)
		Switch (swi1) {
		Case (0) {
		Store(0, Local0)
		}
		Case (1) {
		Store(1, Local0)
		}
		Default {
		Store(2, Local0)
		}}
	}
	Default {
	Store(12345678, Local0)
		Switch (swi1) {
		Case (0) {
		Store(3, Local0)
		}
		Case (1) {
		Store(4, Local0)
		}
		Default {
		Store(5, Local0)
		}}
	}}
	return (Local0)
}

/////////////// {if,elseif} {if}

Method(m0d6)
{
	Store(4, Local0)

	Switch (swi0) {
	Case (0) {
	Store(1, Local0)
		Switch (swi1) {
		Case (0) {
		Store(0, Local0)
		}}
	}
	Case (1) {
	Store(3, Local0)
		Switch (swi1) {
		Case (0) {
		Store(2, Local0)
		}}
	}}
	return (Local0)
}

/////////////// {if,elseif} {if,else}

Method(m0d7)
{
	Store(4, Local0)

	Switch (swi0) {
	Case (0) {
	Store(12345678, Local0)
		Switch (swi1) {
		Case (0) {
		Store(0, Local0)
		}
		Default {
		Store(1, Local0)
		}}
	}
	Case (1) {
	Store(12345678, Local0)
		Switch (swi1) {
		Case (0) {
		Store(2, Local0)
		}
		Default {
		Store(3, Local0)
		}}
	}}
	return (Local0)
}

/////////////// {if,elseif} {if,elseif}

Method(m0d8)
{
	Store(6, Local0)

	Switch (swi0) {
	Case (0) {
	Store(2, Local0)
		Switch (swi1) {
		Case (0) {
		Store(0, Local0)
		}
		Case (1) {
		Store(1, Local0)
		}}
	}
	Case (1) {
	Store(5, Local0)
		Switch (swi1) {
		Case (0) {
		Store(3, Local0)
		}
		Case (1) {
		Store(4, Local0)
		}}
	}}
	return (Local0)
}

/////////////// {if,elseif} {if,elseif,else}

Method(m0d9)
{
	Store(6, Local0)

	Switch (swi0) {
	Case (0) {
	Store(12345678, Local0)
		Switch (swi1) {
		Case (0) {
		Store(0, Local0)
		}
		Case (1) {
		Store(1, Local0)
		}
		Default {
		Store(2, Local0)
		}}
	}
	Case (1) {
	Store(12345678, Local0)
		Switch (swi1) {
		Case (0) {
		Store(3, Local0)
		}
		Case (1) {
		Store(4, Local0)
		}
		Default {
		Store(5, Local0)
		}}
	}}
	return (Local0)
}

/////////////// {if,elseif,else} {if} (restricted)

Method(m0da)
{
	Store(12345678, Local0)

	Switch (swi0) {
	Case (0) {
	Store(1, Local0)
		Switch (swi1) {
		Case (0) {
		Store(0, Local0)
		}}
	}
	Case (1) {
	Store(3, Local0)
		Switch (swi1) {
		Case (0) {
		Store(2, Local0)
		}}
	}
	Default {
	Store(5, Local0)
		Switch (swi1) {
		Case (0) {
		Store(4, Local0)
		}}
	}}
	return (Local0)
}

/////////////// {if,elseif,else} {if,else} (restricted)

Method(m0db)
{
	Store(12345678, Local0)

	Switch (swi0) {
	Case (0) {
	Store(12345678, Local0)
		Switch (swi1) {
		Case (0) {
		Store(0, Local0)
		}
		Default {
		Store(1, Local0)
		}}
	}
	Case (1) {
	Store(12345678, Local0)
		Switch (swi1) {
		Case (0) {
		Store(2, Local0)
		}
		Default {
		Store(3, Local0)
		}}
	}
	Default {
	Store(12345678, Local0)
		Switch (swi1) {
		Case (0) {
		Store(4, Local0)
		}
		Default {
		Store(5, Local0)
		}}
	}}
	return (Local0)
}

/////////////// {if,elseif,else} {if,elseif} (restricted)

Method(m0dc)
{
	Store(12345678, Local0)

	Switch (swi0) {
	Case (0) {
	Store(2, Local0)
		Switch (swi1) {
		Case (0) {
		Store(0, Local0)
		}
		Case (1) {
		Store(1, Local0)
		}}
	}
	Case (1) {
	Store(5, Local0)
		Switch (swi1) {
		Case (0) {
		Store(3, Local0)
		}
		Case (1) {
		Store(4, Local0)
		}}
	}
	Default {
	Store(8, Local0)
		Switch (swi1) {
		Case (0) {
		Store(6, Local0)
		}
		Case (1) {
		Store(7, Local0)
		}}
	}}
	return (Local0)
}

/////////////// {if,elseif,else} {if,elseif,else} (restricted)

Method(m0dd)
{
	Store(12345678, Local0)

	Switch (swi0) {
	Case (0) {
	Store(12345678, Local0)
		Switch (swi1) {
		Case (0) {
		Store(10, Local0)
		}
		Case (1) {
		Store(11, Local0)
		}
		Default {
		Store(12, Local0)
		}}
	}
	Case (1) {
	Store(12345678, Local0)
		Switch (swi1) {
		Case (0) {
		Store(13, Local0)
		}
		Case (1) {
		Store(14, Local0)
		}
		Default {
		Store(15, Local0)
		}}
	}
	Case (2) {
	Store(12345678, Local0)
		Switch (swi1) {
		Case (0) {
		Store(16, Local0)
		}
		Case (1) {
		Store(17, Local0)
		}
		Default {
		Store(18, Local0)
		}}
	}
	Default {
	Store(12345678, Local0)
		Switch (swi1) {
		Case (0) {
		Store(19, Local0)
		}
		Case (1) {
		Store(20, Local0)
		}
		Default {
		Store(21, Local0)
		}}
	}}
	return (Local0)
}

// Run the particular method
// (till the time the passing of pointer to method
// will be implemented)
Method(m0c6, 1)
{
	Store(0x12345678, Local0)

	switch (arg0) {
		case (0) {
			Store(m0d0(), Local0)
		}
		case (1) {
			Store(m0d1(), Local0)
		}
		case (2) {
			Store(m0d2(), Local0)
		}
		case (3) {
			Store(m0d3(), Local0)
		}
		case (4) {
			Store(m0d4(), Local0)
		}
		case (5) {
			Store(m0d5(), Local0)
		}
		case (6) {
			Store(m0d6(), Local0)
		}
		case (7) {
			Store(m0d7(), Local0)
		}
		case (8) {
			Store(m0d8(), Local0)
		}
		case (9) {
			Store(m0d9(), Local0)
		}
		case (10) {
			Store(m0da(), Local0)
		}
		case (11) {
			Store(m0db(), Local0)
		}
		case (12) {
			Store(m0dc(), Local0)
		}
		case (13) {
			Store(m0dd(), Local0)
		}
	}

	return (Local0)
}

// Verivication of ?????????????
Method(m0c7, 3, Serialized)
{
	Name(bs00, 0)
	Name(cnt0, 0)
	Name(cnt1, 0)
	Name(ind1, 0)
	Name(ix00, 0)

	Name(lpN0, 0)
	Name(lpC0, 0)
	Name(lpN1, 0)
	Name(lpC1, 0)

	Store(0, swi0)

	Store(DeRefOf(Index(arg2, 0)), ix00)
	Store(DeRefOf(Index(arg2, 1)), cnt0)

	Store(2, ind1)
	Store(cnt0, lpN0)
	Store(0, lpC0)
	While (lpN0) {
		Store(0, swi1)
		Store(DeRefOf(Index(arg2, ind1)), cnt1)
		Store(cnt1, lpN1)
		Store(0, lpC1)
		While (lpN1) {

			Store(m0c6(arg1), Local0)

			if (0) {
				Store("=============:", Debug)
				Store(swi0, Debug)
				Store(swi1, Debug)
				Store(ix00, Debug)
				Store(Local0, Debug)
				Store("=============.", Debug)
			}

			if (LNotEqual(Local0, ix00)){
				err(arg0, z068, __LINE__, 0, 0, Local0, ix00)
			}
			Increment(ix00)
			Increment(swi1)
			Decrement(lpN1)
			Increment(lpC1)
		}
		Increment(swi0)
		Increment(ind1)
		Decrement(lpN0)
		Increment(lpC0)
	}

	return (0)
}

// Run-method
Method(SW01,, Serialized)
{
	Store("TEST: SW01, Switch, Case, Default operators", Debug)

	Name(ts, "SW01")

	m0c7(ts, 0, Buffer() {0, 2, 2, 1})
	m0c7(ts, 1, Buffer() {0, 2, 3, 1})
	m0c7(ts, 2, Buffer() {0, 2, 2, 2})
	m0c7(ts, 3, Buffer() {0, 2, 2, 2})
	m0c7(ts, 4, Buffer() {0, 2, 3, 3})
	m0c7(ts, 5, Buffer() {0, 2, 3, 3})
	m0c7(ts, 6, Buffer() {0, 3, 2, 2, 1})
	m0c7(ts, 7, Buffer() {0, 3, 2, 2, 1})
	m0c7(ts, 8, Buffer() {0, 3, 3, 3, 1})
	m0c7(ts, 9, Buffer() {0, 3, 3, 3, 1})
	m0c7(ts, 10, Buffer() {0, 3, 2, 2, 2})
	m0c7(ts, 11, Buffer() {0, 3, 2, 2, 2})
	m0c7(ts, 12, Buffer() {0, 3, 3, 3, 3})
	m0c7(ts, 13, Buffer() {10, 4, 3, 3, 3, 3})

	return (0)
}
