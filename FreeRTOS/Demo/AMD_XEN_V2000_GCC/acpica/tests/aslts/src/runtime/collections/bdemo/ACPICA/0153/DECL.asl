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
 * Bug 153:
 *
 * SUMMARY: Source and Target objects after ACPI AML StoreOp behave identically
 *
 * Perform any available Store(OOO1, OOO2) operation such that
 * it changes the type of the target named object (OOO2). Then
 * Store anything into OOO2 once again. In a result of these
 * operations OOO1 is changed also identically to OOO2.
 *
 * That is the contents of bug, OOO1 must be unchanged.
 *
 * ROOT CAUSE
 *
 * Incorrectly implemented the case when the type of the target named
 * object is changed in result of the Store operation - the source object
 * itself but not a copy of it is attached to the namespace node of the
 * target object (previous one detached). So, in a result, the same internal
 * object is attached to two namespace nodes. Due to that, the following
 * storing into OOO2 appears like changing of OOO1 as well.
 *
 * OOO2 should be a duplicate of OOO1, see spec below.
 *
 *
 * Check storing of Computational and Package type data, Named and
 * immediate images, to all the available types.
 */

Include("../../../../../runtime/collections/bdemo/ACPICA/0153/Exc.asl")
Include("../../../../../runtime/collections/bdemo/ACPICA/0153/Mix.asl")
Include("../../../../../runtime/collections/bdemo/ACPICA/0153/ToBuffer.asl")
Include("../../../../../runtime/collections/bdemo/ACPICA/0153/ToDevice.asl")
Include("../../../../../runtime/collections/bdemo/ACPICA/0153/ToDeviceGlob.asl")
Include("../../../../../runtime/collections/bdemo/ACPICA/0153/ToEvent.asl")
Include("../../../../../runtime/collections/bdemo/ACPICA/0153/ToInteger.asl")
Include("../../../../../runtime/collections/bdemo/ACPICA/0153/ToMutex.asl")
Include("../../../../../runtime/collections/bdemo/ACPICA/0153/ToPackage.asl")
Include("../../../../../runtime/collections/bdemo/ACPICA/0153/ToPowerRes.asl")
Include("../../../../../runtime/collections/bdemo/ACPICA/0153/ToProcessor.asl")
Include("../../../../../runtime/collections/bdemo/ACPICA/0153/ToRegion.asl")
Include("../../../../../runtime/collections/bdemo/ACPICA/0153/ToString.asl")
Include("../../../../../runtime/collections/bdemo/ACPICA/0153/ToThermalZone.asl")
