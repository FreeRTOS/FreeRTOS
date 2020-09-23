/***********************************************************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only intended for use with Renesas products. No 
* other uses are authorized. This software is owned by Renesas Electronics Corporation and is protected under all 
* applicable laws, including copyright laws. 
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES REGARDING
* THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, 
* FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT. ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED. TO THE MAXIMUM 
* EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES 
* SHALL BE LIABLE FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR ANY REASON RELATED TO THIS 
* SOFTWARE, EVEN IF RENESAS OR ITS AFFILIATES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software and to discontinue the availability of 
* this software. By using this software, you agree to the additional terms and conditions found by accessing the 
* following link:
* http://www.renesas.com/disclaimer 
*
* Copyright (C) 2016 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/
/***********************************************************************************************************************
* File Name    : r_sci_rx_platform.h
* Description  : Functions for using SCI on the RX devices.
************************************************************************************************************************
* History : DD.MM.YYYY Version Description
*           01.10.2016 1.80    Initial Release. (The remake of the r01an1815ju0170 to the base.)
*           19.12.2016 1.90    Added RX24U support
*           28.09.2018 2.10    Added RX66T support
*           01.02.2019 2.20    Added RX72T, RX65N-64pin support
*           28.06.2019 3.10    Added RX23W support
*           15.08.2019 3.20    Added RX72M support
*           25.11.2019 3.30    Added support RX13T.
*                              Removed support for Generation 1 devices.
*           30.12.2019 3.40    Added support RX66N, RX72N.
*           31.03.2020 3.50    Added support RX23E-A.
************************************************************************************************************************/

#ifndef SCI_RX_PLATFORM_H
#define SCI_RX_PLATFORM_H

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
#include "r_sci_rx_if.h"

#if defined(BSP_MCU_RX110) 
#include "./targets/rx110/r_sci_rx110_private.h"  /* RX110 */
#elif defined(BSP_MCU_RX111)
#include "./targets/rx111/r_sci_rx111_private.h"  /* RX111 */
#elif defined(BSP_MCU_RX113)
#include "./targets/rx113/r_sci_rx113_private.h"  /* RX113 */
#elif defined(BSP_MCU_RX130)
#include "./targets/rx130/r_sci_rx130_private.h"  /* RX130 */
#elif defined(BSP_MCU_RX13T)
#include "./targets/rx13t/r_sci_rx13t_private.h"  /* RX13T */
#elif defined(BSP_MCU_RX230)
#include "./targets/rx230/r_sci_rx230_private.h"  /* RX230 */
#elif defined(BSP_MCU_RX231)
#include "./targets/rx231/r_sci_rx231_private.h"  /* RX231 */
#elif defined(BSP_MCU_RX23E_A)
#include "./targets/rx23e-a/r_sci_rx23e-a_private.h"  /* RX23E-A */
#elif defined(BSP_MCU_RX23T)
#include "./targets/rx23t/r_sci_rx23t_private.h"  /* RX23T */
#elif defined(BSP_MCU_RX23W)
#include "./targets/rx23w/r_sci_rx23w_private.h"  /* RX23W */
#elif defined(BSP_MCU_RX24T)
#include "./targets/rx24t/r_sci_rx24t_private.h"  /* RX24T */
#elif defined(BSP_MCU_RX24U)
#include "./targets/rx24u/r_sci_rx24u_private.h"  /* RX24U */
#elif defined(BSP_MCU_RX64M)
#include "./targets/rx64m/r_sci_rx64m_private.h"  /* RX64M */
#elif defined(BSP_MCU_RX65N)
#include "./targets/rx65n/r_sci_rx65n_private.h"  /* RX65N */
#elif defined(BSP_MCU_RX66T)
#include "./targets/rx66t/r_sci_rx66t_private.h"  /* RX66T */
#elif defined(BSP_MCU_RX66N)
#include "./targets/rx66n/r_sci_rx66n_private.h"  /* RX66N */
#elif defined(BSP_MCU_RX71M)
#include "./targets/rx71m/r_sci_rx71m_private.h"  /* RX71M */
#elif defined(BSP_MCU_RX72T)
#include "./targets/rx72t/r_sci_rx72t_private.h"  /* RX72T */
#elif defined(BSP_MCU_RX72M)
#include "./targets/rx72m/r_sci_rx72m_private.h"  /* RX72M */
#elif defined(BSP_MCU_RX72N)
#include "./targets/rx72n/r_sci_rx72n_private.h"  /* RX72N */
#else
#error "ERROR - r_sci_rxXXX_private.h not included."
#endif

#endif /* SCI_RX_PLATFORM_H */

