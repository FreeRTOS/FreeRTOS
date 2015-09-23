/***********************************************************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only intended for use with Renesas products.
* No other uses are authorized. This software is owned by Renesas Electronics Corporation and is protected under all
* applicable laws, including copyright laws. 
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIESREGARDING THIS SOFTWARE, WHETHER EXPRESS, IMPLIED
* OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
* NON-INFRINGEMENT.  ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED.TO THE MAXIMUM EXTENT PERMITTED NOT PROHIBITED BY
* LAW, NEITHER RENESAS ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES SHALL BE LIABLE FOR ANY DIRECT,
* INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR ANY REASON RELATED TO THIS SOFTWARE, EVEN IF RENESAS OR
* ITS AFFILIATES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software and to discontinue the availability 
* of this software. By using this software, you agree to the additional terms and conditions found by accessing the 
* following link:
* http://www.renesas.com/disclaimer
*
* Copyright (C) 2015 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/

/***********************************************************************************************************************
* File Name    : r_cg_vector_table.c
* Version      : Code Generator for RX231 V1.00.00.03 [10 Jul 2015]
* Device(s)    : R5F52318AxFP
* Tool-Chain   : GCCRX
* Description  : This file implements interrupt vector.
* Creation Date: 23/09/2015
***********************************************************************************************************************/

/***********************************************************************************************************************
Pragma directive
***********************************************************************************************************************/
/* Start user code for pragma. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */

/***********************************************************************************************************************
Includes
***********************************************************************************************************************/
#include "r_cg_macrodriver.h"
#include "r_cg_userdefine.h"

/***********************************************************************************************************************
Global variables and functions
***********************************************************************************************************************/
typedef void (*fp) (void);
extern void PowerON_Reset (void);
extern void stack (void);

#define OFS0_VAL 0xFFFFFFFFUL
#define OFS1_VAL 0xFFFFFFFFUL
#define EXVECT_SECT    __attribute__ ((section (".exvectors")))

const void *ExceptVectors[] EXVECT_SECT  = {
/* Start user code for adding. Do not edit comment generated here */
    /* 0xffffff80  MDE register */
#ifdef __RX_BIG_ENDIAN__
    /* Big endian */
    (fp)0xfffffff8,
#else
    /* Little endian */
    (fp)0xffffffff,
#endif
    /* 0xffffff84  Reserved */
    r_reserved_exception,
    /* 0xffffff88  OFS1 register */
    (fp) OFS1_VAL,
    /* 0xffffff8c  OFS0 register */
    (fp) OFS0_VAL,
    /* 0xffffff90  Reserved */
    r_reserved_exception,
    /* 0xffffff94  Reserved */
    r_reserved_exception,
    /* 0xffffff98  Reserved */
    r_reserved_exception,
    /* 0xffffff9c  Reserved */
    r_reserved_exception,
    /* 0xffffffa0  ID */
    (fp)0xffffffff,
    /* 0xffffffa4  ID */
    (fp)0xffffffff,
    /* 0xffffffa8  ID */
    (fp)0xffffffff,
    /* 0xffffffac  ID */
    (fp)0xffffffff,
    /* 0xffffffb0  Reserved */
    r_reserved_exception,
    /* 0xffffffb4  Reserved */
    r_reserved_exception,
    /* 0xffffffb8  Reserved */
    r_reserved_exception,
    /* 0xffffffbc  Reserved */
    r_reserved_exception,
    /* 0xffffffc0  Reserved */
    r_reserved_exception,
    /* 0xffffffc4  Reserved */
    r_reserved_exception,
    /* 0xffffffc8  Reserved */
    r_reserved_exception,
    /* 0xffffffcc  Reserved */
    r_reserved_exception,
    /* 0xffffffd0  Exception(Supervisor Instruction) */
    r_privileged_exception,
    /* 0xffffffd4  Exception(Access Instruction) */
    r_access_exception,
    /* 0xffffffd8  Reserved */
    r_undefined_exception,
    /* 0xffffffdc  Exception(Undefined Instruction) */
    r_undefined_exception,
    /* 0xffffffe0  Reserved */
    r_undefined_exception,
    /* 0xffffffe4  Exception(Floating Point) */
    r_floatingpoint_exception,
    /* 0xffffffe8  Reserved */
    r_undefined_exception,
    /* 0xffffffec  Reserved */
    r_undefined_exception,
    /* 0xfffffff0  Reserved */
    r_undefined_exception,
    /* 0xfffffff4  Reserved */
    r_undefined_exception,
    /* 0xfffffff8  NMI */
    r_nmi_exception
/* End user code. Do not edit comment generated here */
};

#define FVECT_SECT    __attribute__ ((section (".fvectors")))
const void *HardwareVectors[] FVECT_SECT  = {
    /* 0xfffffffc  RESET */
    /* <<VECTOR DATA START (POWER ON RESET)>> */
    /* Power On Reset PC */
    PowerON_Reset
    /* <<VECTOR DATA END (POWER ON RESET)>> */
};

#define RVECT_SECT __attribute__ ((section (".rvectors")))

const fp RelocatableVectors[] RVECT_SECT  = {
    /* 0x0000  Reserved */
    (fp)r_reserved_exception,
    /* 0x0004  Reserved */
    (fp)r_reserved_exception,
    /* 0x0008  Reserved */
    (fp)r_reserved_exception,
    /* 0x000C  Reserved */
    (fp)r_reserved_exception,
    /* 0x0010  Reserved */
    (fp)r_reserved_exception,
    /* 0x0014  Reserved */
    (fp)r_reserved_exception,
    /* 0x0018  Reserved */
    (fp)r_reserved_exception,
    /* 0x001C  Reserved */
    (fp)r_reserved_exception,
    /* 0x0020  Reserved */
    (fp)r_reserved_exception,
    /* 0x0024  Reserved */
    (fp)r_reserved_exception,
    /* 0x0028  Reserved */
    (fp)r_reserved_exception,
    /* 0x002C  Reserved */
    (fp)r_reserved_exception,
    /* 0x0030  Reserved */
    (fp)r_reserved_exception,
    /* 0x0034  Reserved */
    (fp)r_reserved_exception,
    /* 0x0038  Reserved */
    (fp)r_reserved_exception,
    /* 0x003C  Reserved */
    (fp)r_reserved_exception,
    /* 0x0040  BSC BUSERR */
    (fp)r_undefined_exception,
    /* 0x0044  Reserved */
    (fp)r_reserved_exception,
    /* 0x0048  Reserved */
    (fp)r_undefined_exception,
    /* 0x004C  Reserved */
    (fp)r_reserved_exception,
    /* 0x0050  Reserved */
    (fp)r_reserved_exception,
    /* 0x0054  Reserved */
    (fp)r_undefined_exception,
    /* 0x0058  Reserved */
    (fp)r_reserved_exception,
    /* 0x005C  Reserved */
    (fp)r_undefined_exception,
    /* 0x0060  Reserved */
    (fp)r_reserved_exception,
    /* 0x0064  Reserved */
    (fp)r_reserved_exception,
    /* 0x0068  ICU SWINT2 */
    (fp)r_undefined_exception,
    /* 0x006C  ICU SWINT */
    (fp)r_undefined_exception,
    /* 0x0070  CMT0 */
    (fp)r_undefined_exception,
    /* 0x0074  CMT1 */
    (fp)r_undefined_exception,
    /* 0x0078  CMTW0 */
    (fp)r_undefined_exception,
    /* 0x007C  CMTW1 */
    (fp)r_undefined_exception,
    /* 0x0080  USBA D0FIFO2 */
    (fp)r_undefined_exception,
    /* 0x0084  USBA D1FIFO2 */
    (fp)r_undefined_exception,
    /* 0x0088  USB0 D0FIFO0 */
    (fp)r_undefined_exception,
    /* 0x008C  USB0 D0FIFO0 */
    (fp)r_undefined_exception,
    /* 0x0090  Reserved */
    (fp)r_reserved_exception,
    /* 0x0094  Reserved */
    (fp)r_reserved_exception,
    /* 0x0098  RSPI0 SPRI0 */
    (fp)r_undefined_exception,
    /* 0x009C  RSPI0 SPTI0 */
    (fp)r_undefined_exception,
    /* 0x00A0  RSPI1 SPRI1 */
    (fp)r_undefined_exception,
    /* 0x00A4  RSPI1 SPTI1 */
    (fp)r_undefined_exception,
    /* 0x00A8  QSPI SPRI */
    (fp)r_undefined_exception,
    /* 0x00AC  QSPI SPTI */
    (fp)r_undefined_exception,
    /* 0x00B0  SDHI SBFAI */
    (fp)r_undefined_exception,
    /* 0x00B4  MMC MBFAI */
    (fp)r_undefined_exception,
    /* 0x00B8  SSI0 SSITX0 */
    (fp)r_undefined_exception,
    /* 0x00BC  SSI0 SSIRX0 */
    (fp)r_undefined_exception,
    /* 0x00C0  SSI1 SSIRTI1 */
    (fp)r_undefined_exception,
    /* 0x00C4  Reserved */
    (fp)r_reserved_exception,
    /* 0x00C8  SRC IDEI */
    (fp)r_undefined_exception,
    /* 0x00CC  SRC ODFI */
    (fp)r_undefined_exception,
    /* 0x00E0  Reserved */
    (fp)r_reserved_exception,
    /* 0x00E4  Reserved */
    (fp)r_reserved_exception,
    /* 0x00E8  SCI0 RXI0 */
    (fp)r_undefined_exception,
    /* 0x00EC  SCI0 TXI0 */
    (fp)r_undefined_exception,
    /* 0x00F0  SCI1 RXI1 */
    (fp)r_undefined_exception,
    /* 0x00F4  SCI1 TXI1 */
    (fp)r_undefined_exception,
    /* 0x00F8  SCI2 RXI2 */
    (fp)r_undefined_exception,
    /* 0x00FC  SCI2 TXI2 */
    (fp)r_undefined_exception,
    /* 0x0100  ICU IRQ0 */
    (fp)r_undefined_exception,
    /* 0x0104  ICU IRQ1 */
    (fp)r_undefined_exception,
    /* 0x0108  ICU IRQ2 */
    (fp)r_undefined_exception,
    /* 0x010C  ICU IRQ3 */
    (fp)r_undefined_exception,
    /* 0x0110  ICU IRQ4 */
    (fp)r_undefined_exception,
    /* 0x0114  ICU IRQ5 */
    (fp)r_undefined_exception,
    /* 0x0118  ICU IRQ6 */
    (fp)r_undefined_exception,
    /* 0x011C  ICU IRQ7 */
    (fp)r_undefined_exception,
    /* 0x0120  ICU IRQ8 */
    (fp)r_undefined_exception,
    /* 0x0124  ICU IRQ9 */
    (fp)r_undefined_exception,
    /* 0x0128  ICU IRQ10 */
    (fp)r_undefined_exception,
    /* 0x012C  ICU IRQ11 */
    (fp)r_undefined_exception,
    /* 0x0130  ICU IRQ12 */
    (fp)r_undefined_exception,
    /* 0x0134  ICU IRQ13 */
    (fp)r_undefined_exception,
    /* 0x0138  ICU IRQ14 */
    (fp)r_undefined_exception,
    /* 0x013C  ICU IRQ15 */
    (fp)r_undefined_exception,
    /* 0x0140  SCI3 RXI3 */
    (fp)r_undefined_exception,
    /* 0x0144  SCI3 TXI3 */
    (fp)r_undefined_exception,
    /* 0x0148  SCI4 RXI4 */
    (fp)r_undefined_exception,
    /* 0x014C  SCI4 TXI4 */
    (fp)r_undefined_exception,
    /* 0x0150  SCI5 RXI5 */
    (fp)r_undefined_exception,
    /* 0x0154  SCI5 TXI5 */
    (fp)r_undefined_exception,
    /* 0x0158  SCI6 RXI6 */
    (fp)r_undefined_exception,
    /* 0x015C  SCI6 TXI6 */
    (fp)r_undefined_exception,
    /* 0x0160  LVD LVD1 */
    (fp)r_undefined_exception,
    /* 0x0164  LVD LVD2 */
    (fp)r_undefined_exception,
    /* 0x0168  USB0 USBR0 */
    (fp)r_undefined_exception,
    /* 0x016C  Reserved */
    (fp)r_reserved_exception,
    /* 0x0170  RTC ALM */
    (fp)r_undefined_exception,
    /* 0x0174  RTC PRD */
    (fp)r_undefined_exception,
    /* 0x0178  USBA USBHSR */
    (fp)r_undefined_exception,
    /* 0x0184  PDC PCDFI */
    (fp)r_undefined_exception,
    /* 0x0188  SCI7 RXI7 */
    (fp)r_undefined_exception,
    /* 0x018C  SCI7 TXI7 */
    (fp)r_undefined_exception,
    /* 0x0190  SCIFA8 RXIF8 */
    (fp)r_undefined_exception,
    /* 0x0194  SCIF8 TXIF8 */
    (fp)r_undefined_exception,
    /* 0x0198  SCIF9 RXIF9 */
    (fp)r_undefined_exception,
    /* 0x019C  SCIF9 TXIF9 */
    (fp)r_undefined_exception,
    /* 0x01A0  SCIF10 RXIF10 */
    (fp)r_undefined_exception,
    /* 0x01A4  SCIF10 TXIF10 */
    (fp)r_undefined_exception,
    /* 0x01A8  ICU GROUP_BE0 */
    (fp)r_undefined_exception,
    /* 0x01AC  Reserved */
    (fp)r_reserved_exception,
    /* 0x01B0  Reserved */
    (fp)r_reserved_exception,
    /* 0x01B4  Reserved */
    (fp)r_reserved_exception,
    /* 0x01B8  ICU GROUP_BL0 */
    (fp)r_undefined_exception,
    /* 0x01BC  ICU GROUP_BL1 */
    (fp)r_undefined_exception,
    /* 0x01C0  ICU GROUP_AL0 */
    (fp)r_undefined_exception,
    /* 0x01C4  ICU GROUP_AL1 */
    (fp)r_undefined_exception,
    /* 0x01C8  SCIF11 RXIF11 */
    (fp)r_undefined_exception,
    /* 0x01CC  SCIF11 TXIF11 */
    (fp)r_undefined_exception,
    /* 0x01D0  SCI12 RXI12 */
    (fp)r_undefined_exception,
    /* 0x01D4  SCI12 TXI12 */
    (fp)r_undefined_exception,
    /* 0x01D8  Reserved */
    (fp)r_reserved_exception,
    /* 0x01DC  Reserved */
    (fp)r_reserved_exception,
    /* 0x01F4  OST OST */
    (fp)r_undefined_exception,
    /* 0x01F8  EXDMAC EXDMAC0I */
    (fp)r_undefined_exception,
    /* 0x01FC  EXDMAC EXDMAC1I */
    (fp)r_undefined_exception,
    /* 0x0318  DMAC DMAC0I */
    (fp)r_undefined_exception,
    /* 0x031C  DMAC DMAC1I */
    (fp)r_undefined_exception,
    /* 0x0320  DMAC DMAC2I */
    (fp)r_undefined_exception,
    /* 0x0324  DMAC DMAC3I */
    (fp)r_undefined_exception,
    /* 0x03D8  RIIC0 EEI0 */
    (fp)r_undefined_exception,
    /* 0x03DC  RIIC0 RXI0 */
    (fp)r_undefined_exception,
    /* 0x03E0  RIIC0 TXI0 */
    (fp)r_undefined_exception,
    /* 0x03E4  RIIC0 TEI0 */
    (fp)r_undefined_exception,

};

/***********************************************************************************************************************
* Function Name: r_undefined_exception
* Description  : None
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void r_undefined_exception(void)
{
    /* Start user code. Do not edit comment generated here */
    /* End user code. Do not edit comment generated here */
}
/***********************************************************************************************************************
* Function Name: r_reserved_exception
* Description  : None
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void r_reserved_exception(void)
{
    /* Start user code. Do not edit comment generated here */
    /* End user code. Do not edit comment generated here */
}
/***********************************************************************************************************************
* Function Name: r_nmi_exception
* Description  : None
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void r_nmi_exception(void)
{
    /* Start user code. Do not edit comment generated here */
    /* End user code. Do not edit comment generated here */
}
/***********************************************************************************************************************
* Function Name: r_brk_exception
* Description  : None
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void r_brk_exception(void)
{
    /* Start user code. Do not edit comment generated here */
    /* End user code. Do not edit comment generated here */
}
/***********************************************************************************************************************
* Function Name: r_privileged_exception
* Description  : None
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void r_privileged_exception(void)
{
    /* Start user code. Do not edit comment generated here */
    /* End user code. Do not edit comment generated here */
}
/***********************************************************************************************************************
* Function Name: r_access_exception
* Description  : None
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void r_access_exception(void)
{
    /* Start user code. Do not edit comment generated here */
    /* End user code. Do not edit comment generated here */
}
/***********************************************************************************************************************
* Function Name: r_floatingpoint_exception
* Description  : None
* Arguments    : None
* Return Value : None
***********************************************************************************************************************/
void r_floatingpoint_exception(void)
{
    /* Start user code. Do not edit comment generated here */
    /* End user code. Do not edit comment generated here */
}

