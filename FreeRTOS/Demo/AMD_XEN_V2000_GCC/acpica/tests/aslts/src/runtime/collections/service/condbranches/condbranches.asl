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
     * (service-test)
     *
     * This service-test reports failures when
     * some conditional branches are disabled.
     *
     * Note: check periodically that all the relevant variables
     * are introduced here (see file runtime/ctl/runmode.asl).
     */
    Name (Z135, 0x87)
    Method (SRV0, 0, Serialized)
    {
        Name (I000, 0x00)
        Method (M280, 2, NotSerialized)
        {
            SRMT (Arg1)
            If (!Arg0)
            {
                ERR (Arg0, Z135, __LINE__, 0x00, 0x00, 0x00, 0x01)
            }

            I000++
        }

        M280 (EXCV, "EXCV")
        M280 (X104, "X104")
        M280 (X114, "X114")
        M280 (X127, "X127")
        M280 (X128, "X128")
        M280 (X131, "X131")
        M280 (X132, "X132")
        M280 (X133, "X133")
        M280 (X153, "X153")
        M280 (X170, "X170")
        M280 (X191, "X191")
        M280 (X192, "X192")
        M280 (X193, "X193")
        M280 (X194, "X194")
        /*
         * X195 is about Increment and Decrement of an either String or Buffer
         * Since object will not change the type of the Object to Integer
         * So this conditional branches should be disabled.
         */
        /*m280(X195, "X195") */
        M280 (Q001, "q001")
        M280 (Q002, "q002")
        M280 (Q003, "q003")
        M280 (Q004, "q004")
        M280 (Q005, "q005")
        M280 (Q006, "q006")
        M280 (Q007, "q007")
        M280 (Q008, "q008")
        M280 (Q009, "q009")
        M280 (Q00A, "q00a")
        M280 (Q00B, "q00b")
        M280 (RN00, "rn00")
        M280 (RN01, "rn01")
        M280 (RN02, "rn02")
        M280 (RN03, "rn03")
        M280 (RN04, "rn04")
        M280 (RN05, "rn05")
        M280 (RN06, "rn06")
        M280 (Y078, "y078")
        M280 (Y083, "y083")
        M280 (Y084, "y084")
        M280 (Y098, "y098")
        M280 (Y100, "y100")
        M280 (Y103, "y103")
        M280 (Y104, "y104")
        M280 (Y105, "y105")
        M280 (Y106, "y106")
        M280 (Y111, "y111")
        M280 (Y113, "y113")
        M280 (Y114, "y114")
        M280 (Y118, "y118")
        M280 (Y119, "y119")
        M280 (Y120, "y120")
        M280 (Y121, "y121")
        M280 (Y126, "y126")
        M280 (Y127, "y127")
        M280 (Y128, "y128")
        M280 (Y132, "y132")
        M280 (Y133, "y133")
        M280 (Y134, "y134")
        M280 (Y135, "y135")
        M280 (Y136, "y136")
        M280 (Y157, "y157")
        M280 (Y164, "y164")
        M280 (Y176, "y176")
        M280 (Y178, "y178")
        M280 (Y182, "y182")
        M280 (Y192, "y192")
        M280 (Y200, "y200")
        M280 (Y203, "y203")
        M280 (Y204, "y204")
        M280 (Y205, "y205")
        M280 (Y206, "y206")
        M280 (Y207, "y207")
        M280 (Y208, "y208")
        M280 (Y213, "y213")
        M280 (Y214, "y214")
        M280 (Y215, "y215")
        M280 (Y216, "y216")
        M280 (Y217, "y217")
        M280 (Y220, "y220")
        M280 (Y221, "y221")
        M280 (Y222, "y222")
        M280 (Y223, "y223")
        M280 (Y224, "y224")
        M280 (Y238, "y238")
        M280 (Y242, "y242")
        M280 (Y243, "y243")
        M280 (Y248, "y248")
        M280 (Y251, "y251")
        M280 (Y260, "y260")
        M280 (Y261, "y261")
        M280 (Y262, "y262")
        M280 (Y263, "y263")
        M280 (Y264, "y264")
        M280 (Y275, "y275")
        M280 (Y276, "y276")
        M280 (Y281, "y281")
        M280 (Y282, "y282")
        M280 (Y283, "y283")
        M280 (Y284, "y284")
        M280 (Y286, "y286")
        M280 (Y287, "y287")
        M280 (Y288, "y288")
        M280 (Y289, "y289")
        M280 (Y290, "y290")
        M280 (Y292, "y292")
        M280 (Y293, "y293")
        M280 (Y294, "y294")
        M280 (Y296, "y296")
        M280 (Y297, "y297")
        M280 (Y300, "y300")
        M280 (Y301, "y301")
        M280 (Y302, "y302")
        M280 (Y349, "y349")
        M280 (Y350, "y350")
        M280 (Y361, "y361")
        M280 (Y362, "y362")
        M280 (Y364, "y364")
        M280 (Y365, "y365")
        M280 (Y366, "y366")
        M280 (Y367, "y367")
        M280 (Y500, "y500")
        M280 (Y501, "y501")
        M280 (Y502, "y502")
        M280 (Y503, "y503")
        M280 (Y504, "y504")
        M280 (Y505, "y505")
        M280 (Y506, "y506")
        M280 (Y507, "y507")
        M280 (Y508, "y508")
        M280 (Y509, "y509")
        M280 (Y510, "y510")
        M280 (Y511, "y511")
        M280 (Y512, "y512")
        M280 (Y513, "y513")
        M280 (Y514, "y514")
        M280 (Y516, "y516")
        M280 (Y517, "y517")
        M280 (Y518, "y518")
        M280 (Y519, "y519")
        M280 (Y520, "y520")
        M280 (Y521, "y521")
        M280 (Y522, "y522")
        M280 (Y523, "y523")
        M280 (Y524, "y524")
        M280 (Y525, "y525")
        M280 (Y526, "y526")
        M280 (Y527, "y527")
        M280 (Y600, "y600")
        M280 (Y601, "y601")
        M280 (Y602, "y602")
        M280 (Y603, "y603")
        M280 (Y900, "y900")
        M280 (Y901, "y901")
    }
