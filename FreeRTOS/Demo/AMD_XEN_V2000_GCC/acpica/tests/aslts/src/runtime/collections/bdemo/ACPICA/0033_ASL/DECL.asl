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
 * Bug 0033:
 *
 * SUMMARY: The ASL-compiler doesn't refuse the same descriptor names present in the same scope (Method)
 *
 * The ASL-compiler doesn't refuse the same descriptor names
 * (Resource Descriptor Macros) present in the same scope (Method).
 */

Method(mdc8)
{
	Name(RT00,
		ResourceTemplate () {
			IRQ (Edge, ActiveLow, Shared, DN00) {}
			IRQ (Edge, ActiveLow, Shared, DN00) {}
		})
	Name(RT01,
		ResourceTemplate () {
			DMA (Compatibility, NotBusMaster, Transfer8, DN00) {}
			DMA (Compatibility, NotBusMaster, Transfer8, DN00) {}
		})
	Name(RT02,
		ResourceTemplate () {
			IO (Decode16, 0xf0f1, 0xf2f3, 0xf4, 0xf5, DN00)
			IO (Decode16, 0xf0f1, 0xf2f3, 0xf4, 0xf5, DN00)
		})
	Name(RT03,
		ResourceTemplate () {
			Memory24 (ReadOnly, 0x0000, 0xffff, 0x0001, 0xfffe, DN00)
			Memory24 (ReadOnly, 0x0000, 0xffff, 0x0001, 0xfffe, DN00)
		})
	Name(RT04,
		ResourceTemplate () {
			IO (Decode16, 0xf0f1, 0xf2f3, 0xf4, 0xf5, DN00)
			IO (Decode16, 0xf0f1, 0xf2f3, 0xf4, 0xf5, DN00)
		})
}

Method(m208)
{
	Name(RT00,
		ResourceTemplate () {
			IRQ (Edge, ActiveLow, Shared, DN01) {}
		})
	Name(RT01,
		ResourceTemplate () {
			DMA (Compatibility, NotBusMaster, Transfer8, DN01) {}
		})
	Name(RT02,
		ResourceTemplate () {
			IO (Decode16, 0xf0f1, 0xf2f3, 0xf4, 0xf5, DN01)
		})
	Name(RT03,
		ResourceTemplate () {
			Memory24 (ReadOnly, 0x0000, 0xffff, 0x0001, 0xfffe, DN01)
		})
	Name(RT04,
		ResourceTemplate () {
			IO (Decode16, 0xf0f1, 0xf2f3, 0xf4, 0xf5, DN01)
		})
}

Method(m209)
{
	Name(RT00,
		ResourceTemplate () {
			IRQ (Edge, ActiveLow, Shared, DN02) {}
		})
	Name(RT01,
		ResourceTemplate () {
			IRQ (Edge, ActiveLow, Shared, DN02) {}
		})
}
