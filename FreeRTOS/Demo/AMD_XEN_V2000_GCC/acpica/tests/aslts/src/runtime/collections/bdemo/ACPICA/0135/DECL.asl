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
 * Bug 135:
 *
 * SUMMARY: Store of Index reference to another element of the same Package causes hang
 *
 * DESCRIPTION: infinite loops for self and cross Index-References
 *			between Packages.
 *
 *
 * Checking the cross references of type (mostly) Index:
 *
 * 1. IRef type element of package refers to element of the same package.
 * 2. Cross references between Packages:
 *    - IRef0 type element of package P0 refers to element package P1
 *    - IRef1 type element of package P1 refers to element package P0
 */
Include("../../../../../runtime/collections/bdemo/ACPICA/0135/Common.asl")
Include("../../../../../runtime/collections/bdemo/ACPICA/0135/SimplePkgs.asl")
Include("../../../../../runtime/collections/bdemo/ACPICA/0135/PkgsHierarchy.asl")
Include("../../../../../runtime/collections/bdemo/ACPICA/0135/Misc1.asl")
Include("../../../../../runtime/collections/bdemo/ACPICA/0135/Misc2.asl")
Include("../../../../../runtime/collections/bdemo/ACPICA/0135/Mix.asl")
Include("../../../../../runtime/collections/bdemo/ACPICA/0135/Methods.asl")
Include("../../../../../runtime/collections/bdemo/ACPICA/0135/GrInvest.asl")
