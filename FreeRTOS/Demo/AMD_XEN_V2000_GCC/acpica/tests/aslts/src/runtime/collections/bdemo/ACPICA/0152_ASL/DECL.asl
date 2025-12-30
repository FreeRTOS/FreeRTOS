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
 * Bug 152:
 *
 * SUMMARY: Decrease severity of iASL error for non-Computational types in the Computational data positions
 *
 * Compiler should return error...
 */

	Method(mf42)
	{
		Name(INT0, 0xfedcba9876543210)
		Name(STR0, "source string")
		Name(BUF0, Buffer(9){9,8,7,6,5,4,3,2,1})
		Name(PAC0, Package(3) {"test package"})
		Device(DEV0) {Name(s000, "DEV0")}
		Event(EVE0)
		Method(MMM0) {Return ("ff0X")}
		Mutex(MTX0, 0)
		OperationRegion(OPR0, SystemMemory, 0, 48)
		PowerResource(PWR0, 0, 0) {Name(s000, "PWR0")}
		Processor(CPU0, 0x0, 0xFFFFFFFF, 0x0) {Name(s000, "CPU0")}
		ThermalZone(TZN0) {Name(s000, "TZN0")}
		Field(OPR0, ByteAcc, NoLock, Preserve) {FLU0, 69}
		Createfield(BUF0, 0, 69, BFL0)

		Add(INT0, 1)
		Add(STR0, 2)
		Add(BUF0, 3)
		Add(PAC0, 4)
		Add(FLU0, 4)
		Add(DEV0, 6)
		Add(EVE0, 7)
		Add(MMM0, 8)
		Add(MTX0, 9)
		Add(OPR0, 10)
		Add(PWR0, 11)
		Add(CPU0, 12)
		Add(TZN0, 13)
		Add(BFL0, 14)
	}
