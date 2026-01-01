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
 * Bug 00
 *
 * SUMMARY:
 *
 * COMPONENT: iASL
 *
 * Demo of ASL-incorrectness, - "// comment in the last line".
 *
 * If the last line of ASL-file ends with the comment (in our case
 * "} //") and there is no '\n' (new line) symbol after that comment
 * (check that before exercising the demo) then the iASL, mistakenly,
 * results in Error and reports the "Premature end-of-file reached"
 * (produced by AslCompiler.l->comment2() routine) message like below.
 *
 * If we remove the mentioned comment or insert the '\n' symbol
 * after it, or replace it by ** comment - all became Ok.
 * See details below:
 *
 * iasl.exe "gr4.asl"
 *
 * Intel ACPI Component Architecture
 * ASL Optimizing Compiler / AML Disassembler version 20040527 [May 27 2004]
 * Copyright (C) 2000 - 2004 Intel Corporation
 * Supports ACPI Specification Revision 2.0c
 *
 *                                                                 gr4.asl    35: } //
 * Error    1080 -                                     Premature end-of-file reached ^
 *
 * ASL Input:  gr4.asl - 36 lines, 1494 bytes, 0 keywords
 * Compilation complete. 1 Errors, 0 Warnings, 0 Remarks, 0 Optimizations
 */
DefinitionBlock (
    "grammar.aml",      //Output filename
    "DSDT",             //Signature
    0x01,               //DSDT Revision
    "Intel",            //OEMID
    "Many",             //TABLE ID
    0x00000001          //OEM Revision
    ) {
} //