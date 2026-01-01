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
     * Bug-demo tests collection, to be compiled all together as one module
     */
    /*
     * 162, (causes exception during the table load)
     */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0000/DECL.asl")
    /* 0001_ASL */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0002/DECL.asl")
    /* 0003_ASL */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0004/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0005/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0006/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0007/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0008/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0009/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0010/DECL.asl")
    /* 0011_ASL */
    /*Include("../../../../../runtime/collections/bdemo/ACPICA/0012/DECL.asl") */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0013/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0014/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0015/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0016/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0017/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0018/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0019/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0020/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0021/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0022/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0023/DECL.asl")
    /* 0024_ASL */
    /* 0025_SPEC */
    /* 0026_ASL_NOT_BUG_NOW */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0027/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0028/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0029/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0030/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0031_ASL_RUNTIME/DECL.asl")
    /* 0032_ASL */
    /* 0033_ASL */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0034/DECL.asl")
    /* 0035_ASL */
    /* 0036_ASL */
    /*Include("../../../../../runtime/collections/bdemo/ACPICA/0037/DECL.asl") */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0038/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0039_ASL_RUNTIME/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0040/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0041/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0042/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0043/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0044/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0045/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0046/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0047/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0048/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0049/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0050/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0051_ASL_RUNTIME/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0052/DECL.asl")
    /* 0053_ASL */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0054/DECL.asl")
    /* 0055_ASL */
    /* 0056_ASL */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0057/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0058/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0059/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0060/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0061/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0062_ASL_RUNTIME/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0063/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0064/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0065/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0066/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0067/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0068/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0069/DECL.asl")
    /* 0070_ASL */
    /* 0071_ASL */
    /* 0072_ASL */
    /* 0073_ASL */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0074/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0075/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0076/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0077/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0078/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0079/DECL.asl")
    /* 0080_ASL */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0081/DECL.asl")
    /* 0082_SPEC */
    /*Include("../../../../../runtime/collections/bdemo/ACPICA/0083/DECL.asl") */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0084/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0085/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0086/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0087/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0088/DECL.asl")
    /* 0089_SPEC */
    /* 0090_SPEC */
    /* 0091_SPEC */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0092/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0093/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0094/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0095/DECL.asl")
    /* 0096_ASL */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0097/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0098/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0099/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0100/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0101/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0102/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0103/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0104/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0105/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0106/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0107/DECL.asl")
    /* 0108_ASL */
    /* 0109_ASL */
    /* 0110_ML */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0111/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0112/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0113/DECL.asl")
    /* 0114_ASL */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0115/DECL.asl")
    /* 0116_ASL */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0117/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0118/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0119/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0120/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0121/DECL.asl")
    /* 0122_ASL */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0123/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0124/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0125/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0126/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0127/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0128/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0129/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0130/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0131/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0132/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0133/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0134/DECL.asl")
    /*Include("../../../../../runtime/collections/bdemo/ACPICA/0135/DECL.asl") */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0136/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0137/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0138/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0139/DECL.asl")
    /* 0140_ASL */
    /* 0141_SPEC */
    /* 0142_ASL */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0143/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0144/DECL.asl")
    /* 0145_ASL */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0146/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0147/DECL.asl")
    /* 0148_ASL */
    /* 0149_SPEC */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0150/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0151/DECL.asl")
    /* 0152_ASL */
    /*Include("../../../../../runtime/collections/bdemo/ACPICA/0153/DECL.asl") */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0154/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0155/DECL.asl")
    /* 0156_ML */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0157/DECL.asl")
    /* 0158_ML */
    /* 0159_ML */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0160/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0161/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0162/DECL.asl")
    /* 0163_ML */
    /* 0164_ACTION_REQUIRED */
    /* 0165_ML */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0166_ML/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0167/DECL.asl")
    /* 0168_ACT_REQ_NOPT */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0169/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0170/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0171_ACTION_REQUIRED/DECL.asl")
    /* 0172_OUTSTAND_ALLOC */
    /* 0173_DEMO_IMPOSSIBLE */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0174/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0175/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0176/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0177/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0178/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0179/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0180_ASL_RUNTIME/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0181_ASL_RUNTIME/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0182/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0183/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0184/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0185/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0186/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0187/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0188/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0189/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0190/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0191/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0192/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0193/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0194/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0195/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0196/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0197/DECL.asl")
    /*Include("../../../../../runtime/collections/bdemo/ACPICA/0198/DECL.asl") */
    /*Include("../../../../../runtime/collections/bdemo/ACPICA/0199/DECL.asl") */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0200/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0201_OUTSTAND_ALLOC/DECL.asl")
    /* 0202_SEE_129 */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0203/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0204/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0205/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0206/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0207/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0208/DECL.asl")
    /* 0209_ML_SEE_135 */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0210/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0211/DECL.asl")
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
     * Bug 212:
     *
     * SUMMARY: AML interpreter doesn't prevent dead RefOf-references
     *
     * DESCRIPTION: RefOf operation doesn't increment the ref count
     * of parent object which causes undefined results.
     */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0212/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0213/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0214/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0215/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0216/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0217/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0218/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0219/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0220/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0221/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0222/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0223/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0224/DECL.asl")
    /* 0225_ASL/DECL.asl") */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0226/DECL.asl")
    /* 0227_ASL */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0228/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0229/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0230/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0231/DECL.asl")
    /* 0232_F_OPTION */
    /* 0233_ASL */
    /* 0234_ASL_RUNTIME */
    /* 0235_ASL_RUNTIME */
    /* 0236_ASL */
    /* 0237_ASL */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0238/DECL.asl")
    /* 0239_ACTION_REQUIRED */
    /* 0240_ACTION_REQUIRED */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0241/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0242/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0243/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0244/DECL.asl")
    /* 0245_SPEC */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0246/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0247/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0248/DECL.asl")
    /* 0249_DEMO_IMPOSSIBLE */
    /* 0250_DEMO_IMPOSSIBLE */
    /* 0251_ACTION_REQUIRED */
    /* 0252_ASL */
    /* 0253_DEMO_IMPOSSIBLE */
    /* 0254_DEMO_IMPOSSIBLE */
    /* 0255_DEMO_IMPOSSIBLE */
    /* 0256_DEMO_IMPOSSIBLE */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0257/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0258/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0259/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0260/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0261/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0262/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0263/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0264/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0265/DECL.asl")
    /* 0266_DEMO_IMPOSSIBLE */
    /* 0267_DEMO_IMPOSSIBLE */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0268/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0269/DECL.asl")
    /* 0270_SPEC */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0271/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0272/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0273/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0274/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0275/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0276_LARGE_REF_COUNT/DECL.asl")
    /* 0277_ACTION_REQUIRED */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0278/DECL.asl")
    /* 0279_ASL_RUNTIME */
    /* 0280_ASL_RUNTIME */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0281/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0282/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0283/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0284/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0285/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0286/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0287/DECL.asl")
    /* 0288_ASL_RUNTIME */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0289/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0290/DECL.asl")
    /* 0291_ASL_RUNTIME */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0292/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0293/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0294/DECL.asl")
    /* 0295_ASL */
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0296/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0297_ACTIONS_REQUIRED/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0298_ACTIONS_REQUIRED/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0299_ACTIONS_REQUIRED/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0300/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0301/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0302/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0303/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0304/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0305/DECL.asl")
    Include ("../../../../../runtime/collections/bdemo/ACPICA/0306/DECL.asl")
