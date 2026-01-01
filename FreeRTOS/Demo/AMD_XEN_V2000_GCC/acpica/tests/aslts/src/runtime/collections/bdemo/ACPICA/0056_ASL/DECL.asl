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
 * Bug 0056:
 *
 * SUMMARY: The ASL Compiler generates a one element descriptor for Interrupt macro with the empty InterruptList
 *
 * Compiler should return error...
 */

Method(mdec)
{
	// Compiler should return error

	Name(RT00,
		ResourceTemplate () {
			Interrupt (ResourceConsumer, Edge, ActiveLow, Shared) {}
		})
	Name(RT01,
		ResourceTemplate () {
			Interrupt (ResourceConsumer, Edge, ActiveLow, Shared) {0}
		})

	Store("The contents of the Interrupt(...){} Descriptor:", Debug)
	Store(RT00, Debug)
	Store("The contents of the Interrupt(...){0} Descriptor:", Debug)
	Store(RT01, Debug)
	if (LEqual(RT00, RT01)) {
		Store("Error: Descriptors are the same:", Debug)
	} else {
		Store("Ok: Descriptors differ each other:", Debug)
	}
}
Method(mded)
{
	// Compiler should return error

	Name(RT00,
		ResourceTemplate () {
			Interrupt (ResourceConsumer, Edge, ActiveLow, Shared) {0}
		})
	Store("The contents of the obtained Interrupt Descriptor:", Debug)
	Store(RT00, Debug)
}

Method(mdee)
{
	mdec()
	mded()
}
