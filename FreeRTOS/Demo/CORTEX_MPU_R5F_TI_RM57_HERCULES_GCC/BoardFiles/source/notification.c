/** @file notification.c
 *   @brief User Notification Definition File
 *   @date 11-Dec-2018
 *   @version 04.07.01
 *
 *   This file  defines  empty  notification  routines to avoid
 *   linker errors, Driver expects user to define the notification.
 *   The user needs to either remove this file and use their custom
 *   notification function or place their code sequence in this file
 *   between the provided USER CODE BEGIN and USER CODE END.
 *
 */

/*
 * Copyright (C) 2009-2018 Texas Instruments Incorporated - www.ti.com
 *
 *
 *  Redistribution and use in source and binary forms, with or without
 *  modification, are permitted provided that the following conditions
 *  are met:
 *
 *    Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 *    Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the
 *    distribution.
 *
 *    Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 *  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 *  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 *  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 *  A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 *  OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 *  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 *  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 *  DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 *  THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 *  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 *  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 */

/* Include Files */

#include <adc.h>
#include "esm.h"
#include "can.h"
#include "gio.h"
#include "lin.h"
#include "mibspi.h"
#include "sci.h"
#include "het.h"
#include "dcc.h"
#include "i2c.h"
#include "crc.h"
#include "etpwm.h"
#include "eqep.h"
#include "ecap.h"
#include "epc.h"
#include "emac.h"
#include "sys_dma.h"

/* USER CODE BEGIN (0) */
/* USER CODE END */
void esmGroup1Notification( esmBASE_t * esm, uint32 channel )
{
    /*  enter user code between the USER CODE BEGIN and USER CODE END. */
    /* USER CODE BEGIN (1) */
    /* USER CODE END */
}

/* USER CODE BEGIN (2) */
/* USER CODE END */
void esmGroup2Notification( esmBASE_t * esm, uint32 channel )
{
    /*  enter user code between the USER CODE BEGIN and USER CODE END. */
    /* USER CODE BEGIN (3) */
    /* USER CODE END */
}

/* USER CODE BEGIN (4) */
/* USER CODE END */
void esmGroup3Notification( esmBASE_t * esm, uint32 channel )
{
    /*  enter user code between the USER CODE BEGIN and USER CODE END. */
    /* USER CODE BEGIN (5) */
    /* USER CODE END */
    for( ;; )
    {
    } /* Wait */
    /* USER CODE BEGIN (6) */
    /* USER CODE END */
}

/* USER CODE BEGIN (7) */
/* USER CODE END */

void dmaGroupANotification( dmaInterrupt_t inttype, uint32 channel )
{
    /*  enter user code between the USER CODE BEGIN and USER CODE END. */
    /* USER CODE BEGIN (8) */
    /* USER CODE END */
}

/* USER CODE BEGIN (9) */
/* USER CODE END */

/* USER CODE BEGIN (10) */
/* USER CODE END */

/* USER CODE BEGIN (11) */
/* USER CODE END */
void adcNotification( adcBASE_t * adc, uint32 group )
{
    /*  enter user code between the USER CODE BEGIN and USER CODE END. */
    /* USER CODE BEGIN (14) */
    /* USER CODE END */
}

/* USER CODE BEGIN (15) */
/* USER CODE END */
void canErrorNotification( canBASE_t * node, uint32 notification )
{
    /*  enter user code between the USER CODE BEGIN and USER CODE END. */
    /* USER CODE BEGIN (16) */
    /* USER CODE END */
}

void canStatusChangeNotification( canBASE_t * node, uint32 notification )
{
    /*  enter user code between the USER CODE BEGIN and USER CODE END. */
    /* USER CODE BEGIN (17) */
    /* USER CODE END */
}

void canMessageNotification( canBASE_t * node, uint32 messageBox )
{
    /*  enter user code between the USER CODE BEGIN and USER CODE END. */
    /* USER CODE BEGIN (18) */
    /* USER CODE END */
}

/* USER CODE BEGIN (19) */
/* USER CODE END */
void dccNotification( dccBASE_t * dcc, uint32 flags )
{
    /*  enter user code between the USER CODE BEGIN and USER CODE END. */
    /* USER CODE BEGIN (20) */
    /* USER CODE END */
}

/* USER CODE BEGIN (21) */
/* USER CODE END */
void gioNotification( gioPORT_t * port, uint32 bit )
{
    /*  enter user code between the USER CODE BEGIN and USER CODE END. */
    /* USER CODE BEGIN (22) */
    /* USER CODE END */
}

/* USER CODE BEGIN (23) */
/* USER CODE END */
void i2cNotification( i2cBASE_t * i2c, uint32 flags )
{
    /*  enter user code between the USER CODE BEGIN and USER CODE END. */
    /* USER CODE BEGIN (24) */
    /* USER CODE END */
}

/* USER CODE BEGIN (25) */
/* USER CODE END */
void linNotification( linBASE_t * lin, uint32 flags )
{
    /*  enter user code between the USER CODE BEGIN and USER CODE END. */
    /* USER CODE BEGIN (26) */
    /* USER CODE END */
}

/* USER CODE BEGIN (27) */
/* USER CODE END */
void mibspiNotification( mibspiBASE_t * mibspi, uint32 flags )
{
    /*  enter user code between the USER CODE BEGIN and USER CODE END. */
    /* USER CODE BEGIN (28) */
    /* USER CODE END */
}

/* USER CODE BEGIN (29) */
/* USER CODE END */
void mibspiGroupNotification( mibspiBASE_t * mibspi, uint32 group )
{
    /*  enter user code between the USER CODE BEGIN and USER CODE END. */
    /* USER CODE BEGIN (30) */
    /* USER CODE END */
}
/* USER CODE BEGIN (31) */
/* USER CODE END */

void sciNotification( sciBASE_t * sci, uint32 flags )
{
    /*  enter user code between the USER CODE BEGIN and USER CODE END. */
    /* USER CODE BEGIN (32) */
    /* USER CODE END */
}

/* USER CODE BEGIN (33) */
/* USER CODE END */

void pwmNotification( hetBASE_t * hetREG, uint32 pwm, uint32 notification )
{
    /*  enter user code between the USER CODE BEGIN and USER CODE END. */
    /* USER CODE BEGIN (38) */
    /* USER CODE END */
}

/* USER CODE BEGIN (39) */
/* USER CODE END */
void edgeNotification( hetBASE_t * hetREG, uint32 edge )
{
    /*  enter user code between the USER CODE BEGIN and USER CODE END. */
    /* USER CODE BEGIN (40) */
    /* USER CODE END */
}

/* USER CODE BEGIN (41) */
/* USER CODE END */
void hetNotification( hetBASE_t * het, uint32 offset )
{
    /*  enter user code between the USER CODE BEGIN and USER CODE END. */
    /* USER CODE BEGIN (42) */
    /* USER CODE END */
}

/* USER CODE BEGIN (43) */
/* USER CODE END */

void crcNotification( crcBASE_t * crc, uint32 flags )
{
    /*  enter user code between the USER CODE BEGIN and USER CODE END. */
    /* USER CODE BEGIN (44) */
    /* USER CODE END */
}
/* USER CODE BEGIN (45) */
/* USER CODE END */

/* USER CODE BEGIN (46) */
/* USER CODE END */

void etpwmNotification( etpwmBASE_t * node )
{
    /*  enter user code between the USER CODE BEGIN and USER CODE END. */
    /* USER CODE BEGIN (47) */
    /* USER CODE END */
}
void etpwmTripNotification( etpwmBASE_t * node, uint16 flags )
{
    /*  enter user code between the USER CODE BEGIN and USER CODE END. */
    /* USER CODE BEGIN (48) */
    /* USER CODE END */
}

/* USER CODE BEGIN (49) */
/* USER CODE END */

/* USER CODE BEGIN (50) */
/* USER CODE END */

void eqepNotification( eqepBASE_t * eqep, uint16 flags )
{
    /*  enter user code between the USER CODE BEGIN and USER CODE END. */
    /* USER CODE BEGIN (51) */
    /* USER CODE END */
}
/* USER CODE BEGIN (52) */
/* USER CODE END */

/* USER CODE BEGIN (53) */
/* USER CODE END */

void ecapNotification( ecapBASE_t * ecap, uint16 flags )
{
    /*  enter user code between the USER CODE BEGIN and USER CODE END. */
    /* USER CODE BEGIN (54) */
    /* USER CODE END */
}
/* USER CODE BEGIN (55) */
/* USER CODE END */

/* USER CODE BEGIN (56) */
/* USER CODE END */

void epcCAMFullNotification( void )
{
    /*  enter user code between the USER CODE BEGIN and USER CODE END. */
    /* USER CODE BEGIN (57) */
    /* USER CODE END */
}
void epcFIFOFullNotification( uint32 epcFIFOStatus )
{
    /*  enter user code between the USER CODE BEGIN and USER CODE END. */
    /* USER CODE BEGIN (58) */
    /* USER CODE END */
}

/* USER CODE BEGIN (59) */
/* USER CODE END */

void emacTxNotification( hdkif_t * hdkif )
{
    /*  enter user code between the USER CODE BEGIN and USER CODE END. */
    /* USER CODE BEGIN (60) */
    /* USER CODE END */
}

/* USER CODE BEGIN (61) */
/* USER CODE END */
void emacRxNotification( hdkif_t * hdkif )
{
    /*  enter user code between the USER CODE BEGIN and USER CODE END. */
    /* USER CODE BEGIN (62) */
    /* USER CODE END */
}

/* USER CODE BEGIN (63) */
/* USER CODE END */
