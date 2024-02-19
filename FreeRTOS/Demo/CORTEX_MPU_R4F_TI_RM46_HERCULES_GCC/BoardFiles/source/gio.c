/** @file gio.c
 *   @brief GIO Driver Implementation File
 *   @date 11-Dec-2018
 *   @version 04.07.01
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

/* USER CODE BEGIN (0) */
/* USER CODE END */

#include "gio.h"
#include "sys_vim.h"

/* USER CODE BEGIN (1) */
/* USER CODE END */

/** @fn void gioInit(void)
 *   @brief Initializes the GIO Driver
 *
 *   This function initializes the GIO module and set the GIO ports
 *   to the initial values.
 */
/* SourceId : GIO_SourceId_001 */
/* DesignId : GIO_DesignId_001 */
/* Requirements : HL_SR26 */
void gioInit( void )
{
    /* USER CODE BEGIN (2) */
    /* USER CODE END */

    /** bring GIO module out of reset */
    gioREG->GCR0 = 1U;
    gioREG->ENACLR = 0xFFU;
    gioREG->LVLCLR = 0xFFU;

    /** @b initialize @b Port @b A */

    /** - Port A output values */
    gioPORTA->DOUT = ( uint32 ) ( ( uint32 ) 0U << 0U )  /* Bit 0 */
                   | ( uint32 ) ( ( uint32 ) 0U << 1U )  /* Bit 1 */
                   | ( uint32 ) ( ( uint32 ) 0U << 2U )  /* Bit 2 */
                   | ( uint32 ) ( ( uint32 ) 0U << 3U )  /* Bit 3 */
                   | ( uint32 ) ( ( uint32 ) 0U << 4U )  /* Bit 4 */
                   | ( uint32 ) ( ( uint32 ) 0U << 5U )  /* Bit 5 */
                   | ( uint32 ) ( ( uint32 ) 0U << 6U )  /* Bit 6 */
                   | ( uint32 ) ( ( uint32 ) 0U << 7U ); /* Bit 7 */

    /** - Port A direction */
    gioPORTA->DIR = ( uint32 ) ( ( uint32 ) 0U << 0U )  /* Bit 0 */
                  | ( uint32 ) ( ( uint32 ) 0U << 1U )  /* Bit 1 */
                  | ( uint32 ) ( ( uint32 ) 0U << 2U )  /* Bit 2 */
                  | ( uint32 ) ( ( uint32 ) 0U << 3U )  /* Bit 3 */
                  | ( uint32 ) ( ( uint32 ) 0U << 4U )  /* Bit 4 */
                  | ( uint32 ) ( ( uint32 ) 0U << 5U )  /* Bit 5 */
                  | ( uint32 ) ( ( uint32 ) 0U << 6U )  /* Bit 6 */
                  | ( uint32 ) ( ( uint32 ) 0U << 7U ); /* Bit 7 */

    /** - Port A open drain enable */
    gioPORTA->PDR = ( uint32 ) ( ( uint32 ) 0U << 0U )  /* Bit 0 */
                  | ( uint32 ) ( ( uint32 ) 0U << 1U )  /* Bit 1 */
                  | ( uint32 ) ( ( uint32 ) 0U << 2U )  /* Bit 2 */
                  | ( uint32 ) ( ( uint32 ) 0U << 3U )  /* Bit 3 */
                  | ( uint32 ) ( ( uint32 ) 0U << 4U )  /* Bit 4 */
                  | ( uint32 ) ( ( uint32 ) 0U << 5U )  /* Bit 5 */
                  | ( uint32 ) ( ( uint32 ) 0U << 6U )  /* Bit 6 */
                  | ( uint32 ) ( ( uint32 ) 0U << 7U ); /* Bit 7 */

    /** - Port A pullup / pulldown selection */
    gioPORTA->PSL = ( uint32 ) ( ( uint32 ) 0U << 0U )  /* Bit 0 */
                  | ( uint32 ) ( ( uint32 ) 0U << 1U )  /* Bit 1 */
                  | ( uint32 ) ( ( uint32 ) 0U << 2U )  /* Bit 2 */
                  | ( uint32 ) ( ( uint32 ) 0U << 3U )  /* Bit 3 */
                  | ( uint32 ) ( ( uint32 ) 0U << 4U )  /* Bit 4 */
                  | ( uint32 ) ( ( uint32 ) 0U << 5U )  /* Bit 5 */
                  | ( uint32 ) ( ( uint32 ) 0U << 6U )  /* Bit 6 */
                  | ( uint32 ) ( ( uint32 ) 0U << 7U ); /* Bit 7 */

    /** - Port A pullup / pulldown enable*/
    gioPORTA->PULDIS = ( uint32 ) ( ( uint32 ) 0U << 0U )  /* Bit 0 */
                     | ( uint32 ) ( ( uint32 ) 0U << 1U )  /* Bit 1 */
                     | ( uint32 ) ( ( uint32 ) 0U << 2U )  /* Bit 2 */
                     | ( uint32 ) ( ( uint32 ) 0U << 3U )  /* Bit 3 */
                     | ( uint32 ) ( ( uint32 ) 0U << 4U )  /* Bit 4 */
                     | ( uint32 ) ( ( uint32 ) 0U << 5U )  /* Bit 5 */
                     | ( uint32 ) ( ( uint32 ) 0U << 6U )  /* Bit 6 */
                     | ( uint32 ) ( ( uint32 ) 0U << 7U ); /* Bit 7 */

    /** @b initialize @b Port @b B */

    /** - Port B output values */
    gioPORTB->DOUT = ( uint32 ) ( ( uint32 ) 0U << 0U )  /* Bit 0 */
                   | ( uint32 ) ( ( uint32 ) 0U << 1U )  /* Bit 1 */
                   | ( uint32 ) ( ( uint32 ) 0U << 2U )  /* Bit 2 */
                   | ( uint32 ) ( ( uint32 ) 0U << 3U )  /* Bit 3 */
                   | ( uint32 ) ( ( uint32 ) 0U << 4U )  /* Bit 4 */
                   | ( uint32 ) ( ( uint32 ) 0U << 5U )  /* Bit 5 */
                   | ( uint32 ) ( ( uint32 ) 0U << 6U )  /* Bit 6 */
                   | ( uint32 ) ( ( uint32 ) 0U << 7U ); /* Bit 7 */

    /** - Port B direction */
    gioPORTB->DIR = ( uint32 ) ( ( uint32 ) 0U << 0U )  /* Bit 0 */
                  | ( uint32 ) ( ( uint32 ) 0U << 1U )  /* Bit 1 */
                  | ( uint32 ) ( ( uint32 ) 0U << 2U )  /* Bit 2 */
                  | ( uint32 ) ( ( uint32 ) 0U << 3U )  /* Bit 3 */
                  | ( uint32 ) ( ( uint32 ) 0U << 4U )  /* Bit 4 */
                  | ( uint32 ) ( ( uint32 ) 0U << 5U )  /* Bit 5 */
                  | ( uint32 ) ( ( uint32 ) 0U << 6U )  /* Bit 6 */
                  | ( uint32 ) ( ( uint32 ) 0U << 7U ); /* Bit 7 */

    /** - Port B open drain enable */
    gioPORTB->PDR = ( uint32 ) ( ( uint32 ) 0U << 0U )  /* Bit 0 */
                  | ( uint32 ) ( ( uint32 ) 0U << 1U )  /* Bit 1 */
                  | ( uint32 ) ( ( uint32 ) 0U << 2U )  /* Bit 2 */
                  | ( uint32 ) ( ( uint32 ) 0U << 3U )  /* Bit 3 */
                  | ( uint32 ) ( ( uint32 ) 0U << 4U )  /* Bit 4 */
                  | ( uint32 ) ( ( uint32 ) 0U << 5U )  /* Bit 5 */
                  | ( uint32 ) ( ( uint32 ) 0U << 6U )  /* Bit 6 */
                  | ( uint32 ) ( ( uint32 ) 0U << 7U ); /* Bit 7 */

    /** - Port B pullup / pulldown selection */
    gioPORTB->PSL = ( uint32 ) ( ( uint32 ) 0U << 0U )  /* Bit 0 */
                  | ( uint32 ) ( ( uint32 ) 0U << 1U )  /* Bit 1 */
                  | ( uint32 ) ( ( uint32 ) 0U << 2U )  /* Bit 2 */
                  | ( uint32 ) ( ( uint32 ) 0U << 3U )  /* Bit 3 */
                  | ( uint32 ) ( ( uint32 ) 0U << 4U )  /* Bit 4 */
                  | ( uint32 ) ( ( uint32 ) 0U << 5U )  /* Bit 5 */
                  | ( uint32 ) ( ( uint32 ) 0U << 6U )  /* Bit 6 */
                  | ( uint32 ) ( ( uint32 ) 0U << 7U ); /* Bit 7 */

    /** - Port B pullup / pulldown enable*/
    gioPORTB->PULDIS = ( uint32 ) ( ( uint32 ) 0U << 0U )  /* Bit 0 */
                     | ( uint32 ) ( ( uint32 ) 0U << 1U )  /* Bit 1 */
                     | ( uint32 ) ( ( uint32 ) 0U << 2U )  /* Bit 2 */
                     | ( uint32 ) ( ( uint32 ) 0U << 3U )  /* Bit 3 */
                     | ( uint32 ) ( ( uint32 ) 0U << 4U )  /* Bit 4 */
                     | ( uint32 ) ( ( uint32 ) 0U << 5U )  /* Bit 5 */
                     | ( uint32 ) ( ( uint32 ) 0U << 6U )  /* Bit 6 */
                     | ( uint32 ) ( ( uint32 ) 0U << 7U ); /* Bit 7 */

    /* USER CODE BEGIN (3) */
    /* USER CODE END */

    /** @b initialize @b interrupts */

    /** - interrupt polarity */
    gioREG->POL = ( uint32 ) ( ( uint32 ) 0U << 0U )   /* Bit 0 */
                | ( uint32 ) ( ( uint32 ) 0U << 1U )   /* Bit 1 */
                | ( uint32 ) ( ( uint32 ) 0U << 2U )   /* Bit 2 */
                | ( uint32 ) ( ( uint32 ) 0U << 3U )   /* Bit 3 */
                | ( uint32 ) ( ( uint32 ) 0U << 4U )   /* Bit 4 */
                | ( uint32 ) ( ( uint32 ) 0U << 5U )   /* Bit 5 */
                | ( uint32 ) ( ( uint32 ) 0U << 6U )   /* Bit 6 */
                | ( uint32 ) ( ( uint32 ) 0U << 7U )   /* Bit 7 */
                | ( uint32 ) ( ( uint32 ) 0U << 8U )   /* Bit 8  */
                | ( uint32 ) ( ( uint32 ) 0U << 9U )   /* Bit 9  */
                | ( uint32 ) ( ( uint32 ) 0U << 10U )  /* Bit 10 */
                | ( uint32 ) ( ( uint32 ) 0U << 11U )  /* Bit 11 */
                | ( uint32 ) ( ( uint32 ) 0U << 12U )  /* Bit 12 */
                | ( uint32 ) ( ( uint32 ) 0U << 13U )  /* Bit 13 */
                | ( uint32 ) ( ( uint32 ) 0U << 14U )  /* Bit 14 */
                | ( uint32 ) ( ( uint32 ) 0U << 15U ); /* Bit 15 */

    /** - interrupt level */
    gioREG->LVLSET = ( uint32 ) ( ( uint32 ) 0U << 0U )   /* Bit 0 */
                   | ( uint32 ) ( ( uint32 ) 0U << 1U )   /* Bit 1 */
                   | ( uint32 ) ( ( uint32 ) 0U << 2U )   /* Bit 2 */
                   | ( uint32 ) ( ( uint32 ) 0U << 3U )   /* Bit 3 */
                   | ( uint32 ) ( ( uint32 ) 0U << 4U )   /* Bit 4 */
                   | ( uint32 ) ( ( uint32 ) 0U << 5U )   /* Bit 5 */
                   | ( uint32 ) ( ( uint32 ) 0U << 6U )   /* Bit 6 */
                   | ( uint32 ) ( ( uint32 ) 0U << 7U )   /* Bit 7 */
                   | ( uint32 ) ( ( uint32 ) 0U << 8U )   /* Bit 8  */
                   | ( uint32 ) ( ( uint32 ) 0U << 9U )   /* Bit 9  */
                   | ( uint32 ) ( ( uint32 ) 0U << 10U )  /* Bit 10 */
                   | ( uint32 ) ( ( uint32 ) 0U << 11U )  /* Bit 11 */
                   | ( uint32 ) ( ( uint32 ) 0U << 12U )  /* Bit 12 */
                   | ( uint32 ) ( ( uint32 ) 0U << 13U )  /* Bit 13 */
                   | ( uint32 ) ( ( uint32 ) 0U << 14U )  /* Bit 14 */
                   | ( uint32 ) ( ( uint32 ) 0U << 15U ); /* Bit 15 */

    /** - clear all pending interrupts */
    gioREG->FLG = 0xFFU;

    /** - enable interrupts */
    gioREG->ENASET = ( uint32 ) ( ( uint32 ) 0U << 0U )   /* Bit 0 */
                   | ( uint32 ) ( ( uint32 ) 0U << 1U )   /* Bit 1 */
                   | ( uint32 ) ( ( uint32 ) 0U << 2U )   /* Bit 2 */
                   | ( uint32 ) ( ( uint32 ) 0U << 3U )   /* Bit 3 */
                   | ( uint32 ) ( ( uint32 ) 0U << 4U )   /* Bit 4 */
                   | ( uint32 ) ( ( uint32 ) 0U << 5U )   /* Bit 5 */
                   | ( uint32 ) ( ( uint32 ) 0U << 6U )   /* Bit 6 */
                   | ( uint32 ) ( ( uint32 ) 0U << 7U )   /* Bit 7 */
                   | ( uint32 ) ( ( uint32 ) 0U << 8U )   /* Bit 8  */
                   | ( uint32 ) ( ( uint32 ) 0U << 9U )   /* Bit 9  */
                   | ( uint32 ) ( ( uint32 ) 0U << 10U )  /* Bit 10 */
                   | ( uint32 ) ( ( uint32 ) 0U << 11U )  /* Bit 11 */
                   | ( uint32 ) ( ( uint32 ) 0U << 12U )  /* Bit 12 */
                   | ( uint32 ) ( ( uint32 ) 0U << 13U )  /* Bit 13 */
                   | ( uint32 ) ( ( uint32 ) 0U << 14U )  /* Bit 14 */
                   | ( uint32 ) ( ( uint32 ) 0U << 15U ); /* Bit 15 */

    /* USER CODE BEGIN (4) */
    /* USER CODE END */
}

/** @fn void gioSetDirection(gioPORT_t *port, uint32 dir)
 *   @brief Set Port Direction
 *   @param[in] port pointer to GIO port:
 *              - gioPORTA: PortA pointer
 *              - gioPORTB: PortB pointer
 *   @param[in] dir value to write to DIR register
 *
 *   Set the direction of GIO pins at runtime.
 */
/* SourceId : GIO_SourceId_002 */
/* DesignId : GIO_DesignId_002 */
/* Requirements : HL_SR27 */
void gioSetDirection( gioPORT_t * port, uint32 dir )
{
    port->DIR = dir;
}

/** @fn void gioSetBit(gioPORT_t *port, uint32 bit, uint32 value)
 *   @brief Write Bit
 *   @param[in] port pointer to GIO port:
 *              - gioPORTA: PortA pointer
 *              - gioPORTB: PortB pointer
 *   @param[in] bit number 0-7 that specifies the bit to be written to.
 *              - 0: LSB
 *              - 7: MSB
 *   @param[in] value binary value to write to bit
 *
 *   Writes a value to the specified pin of the given GIO port
 */
/* SourceId : GIO_SourceId_003 */
/* DesignId : GIO_DesignId_003 */
/* Requirements : HL_SR28 */
void gioSetBit( gioPORT_t * port, uint32 bit, uint32 value )
{
    /* USER CODE BEGIN (5) */
    /* USER CODE END */

    if( value != 0U )
    {
        port->DSET = ( uint32 ) 1U << bit;
    }
    else
    {
        port->DCLR = ( uint32 ) 1U << bit;
    }
}

/** @fn void gioSetPort(gioPORT_t *port, uint32 value)
 *   @brief Write Port Value
 *   @param[in] port pointer to GIO port:
 *              - gioPORTA: PortA pointer
 *              - gioPORTB: PortB pointer
 *   @param[in] value value to write to port
 *
 *   Writes a value to all pin of a given GIO port
 */
/* SourceId : GIO_SourceId_004 */
/* DesignId : GIO_DesignId_004 */
/* Requirements : HL_SR29 */
void gioSetPort( gioPORT_t * port, uint32 value )
{
    /* USER CODE BEGIN (6) */
    /* USER CODE END */

    port->DOUT = value;

    /* USER CODE BEGIN (7) */
    /* USER CODE END */
}

/** @fn uint32 gioGetBit(gioPORT_t *port, uint32 bit)
 *   @brief Read Bit
 *   @param[in] port pointer to GIO port:
 *              - gioPORTA: PortA pointer
 *              - gioPORTB: PortB pointer
 *   @param[in] bit number 0-7 that specifies the bit to be written to.
 *              - 0: LSB
 *              - 7: MSB
 *
 *   Reads a the current value from the specified pin of the given GIO port
 */
/* SourceId : GIO_SourceId_005 */
/* DesignId : GIO_DesignId_005 */
/* Requirements : HL_SR30 */
uint32 gioGetBit( gioPORT_t * port, uint32 bit )
{
    /* USER CODE BEGIN (8) */
    /* USER CODE END */

    return ( port->DIN >> bit ) & 1U;
}

/** @fn uint32 gioGetPort(gioPORT_t *port)
 *   @brief Read Port Value
 *   @param[in] port pointer to GIO port:
 *              - gioPORTA: PortA pointer
 *              - gioPORTB: PortB pointer
 *
 *   Reads a the current value of a given GIO port
 */
/* SourceId : GIO_SourceId_006 */
/* DesignId : GIO_DesignId_006 */
/* Requirements : HL_SR31 */
uint32 gioGetPort( gioPORT_t * port )
{
    /* USER CODE BEGIN (9) */
    /* USER CODE END */

    return port->DIN;
}

/** @fn void gioToggleBit(gioPORT_t *port, uint32 bit)
 *   @brief Write Bit
 *   @param[in] port pointer to GIO port:
 *              - gioPORTA: PortA pointer
 *              - gioPORTB: PortB pointer
 *   @param[in] bit number 0-7 that specifies the bit to be written to.
 *              - 0: LSB
 *              - 7: MSB
 *
 *   Toggle a value to the specified pin of the given GIO port
 */
/* SourceId : GIO_SourceId_007 */
/* DesignId : GIO_DesignId_007 */
/* Requirements : HL_SR32 */
void gioToggleBit( gioPORT_t * port, uint32 bit )
{
    /* USER CODE BEGIN (10) */
    /* USER CODE END */

    if( ( port->DIN & ( uint32 ) ( ( uint32 ) 1U << bit ) ) != 0U )
    {
        port->DCLR = ( uint32 ) 1U << bit;
    }
    else
    {
        port->DSET = ( uint32 ) 1U << bit;
    }
}

/** @fn void gioEnableNotification(uint32 bit)
 *   @brief Enable Interrupt
 *   @param[in] port pointer to GIO port:
 *              - gioPORTA: PortA pointer
 *              - gioPORTB: PortB pointer
 *   @param[in] bit interrupt pin to enable
 *              - 0: LSB
 *              - 7: MSB
 *
 *   Enables an interrupt pin of selected port
 */
/* SourceId : GIO_SourceId_008 */
/* DesignId : GIO_DesignId_008 */
/* Requirements : HL_SR33 */
void gioEnableNotification( gioPORT_t * port, uint32 bit )
{
    /* USER CODE BEGIN (11) */
    /* USER CODE END */

    if( port == gioPORTA )
    {
        gioREG->ENASET = ( uint32 ) 1U << bit;
    }
    else if( port == gioPORTB )
    {
        gioREG->ENASET = ( uint32 ) 1U << ( bit + 8U );
    }
    else
    {
        /* Empty */
    }
}

/** @fn void gioDisableNotification(uint32 bit)
 *   @brief Disable Interrupt
 *   @param[in] port pointer to GIO port:
 *              - gioPORTA: PortA pointer
 *              - gioPORTB: PortB pointer
 *   @param[in] bit interrupt pin to enable
 *              - 0: LSB
 *              - 7: MSB
 *
 *   Disables an interrupt pin of selected port
 */
/* SourceId : GIO_SourceId_009 */
/* DesignId : GIO_DesignId_009 */
/* Requirements : HL_SR34 */
void gioDisableNotification( gioPORT_t * port, uint32 bit )
{
    /* USER CODE BEGIN (12) */
    /* USER CODE END */

    if( port == gioPORTA )
    {
        gioREG->ENACLR = ( uint32 ) 1U << bit;
    }
    else if( port == gioPORTB )
    {
        gioREG->ENACLR = ( uint32 ) 1U << ( bit + 8U );
    }
    else
    {
        /* Empty */
    }
}

/** @fn void gioGetConfigValue(gio_config_reg_t *config_reg, config_value_type_t type)
 *   @brief Get the initial or current values of the configuration registers
 *
 *   @param[in] *config_reg: pointer to the struct to which the initial or current
 *                           value of the configuration registers need to be stored
 *   @param[in] type:    whether initial or current value of the configuration registers
 * need to be stored
 *                       - InitialValue: initial value of the configuration registers will
 * be stored in the struct pointed by config_reg
 *                       - CurrentValue: initial value of the configuration registers will
 * be stored in the struct pointed by config_reg
 *
 *   This function will copy the initial or current value (depending on the parameter
 * 'type') of the configuration registers to the struct pointed by config_reg
 *
 */
/* SourceId : GIO_SourceId_010 */
/* DesignId : GIO_DesignId_010 */
/* Requirements : HL_SR37 */
void gioGetConfigValue( gio_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    {
        config_reg->CONFIG_INTDET = GIO_INTDET_CONFIGVALUE;
        config_reg->CONFIG_POL = GIO_POL_CONFIGVALUE;
        config_reg->CONFIG_INTENASET = GIO_INTENASET_CONFIGVALUE;
        config_reg->CONFIG_LVLSET = GIO_LVLSET_CONFIGVALUE;

        config_reg->CONFIG_PORTADIR = GIO_PORTADIR_CONFIGVALUE;
        config_reg->CONFIG_PORTAPDR = GIO_PORTAPDR_CONFIGVALUE;
        config_reg->CONFIG_PORTAPSL = GIO_PORTAPSL_CONFIGVALUE;
        config_reg->CONFIG_PORTAPULDIS = GIO_PORTAPULDIS_CONFIGVALUE;

        config_reg->CONFIG_PORTBDIR = GIO_PORTBDIR_CONFIGVALUE;
        config_reg->CONFIG_PORTBPDR = GIO_PORTBPDR_CONFIGVALUE;
        config_reg->CONFIG_PORTBPSL = GIO_PORTBPSL_CONFIGVALUE;
        config_reg->CONFIG_PORTBPULDIS = GIO_PORTBPULDIS_CONFIGVALUE;
    }
    else
    {
        /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
        config_reg->CONFIG_INTDET = gioREG->INTDET;
        config_reg->CONFIG_POL = gioREG->POL;
        config_reg->CONFIG_INTENASET = gioREG->ENASET;
        config_reg->CONFIG_LVLSET = gioREG->LVLSET;

        config_reg->CONFIG_PORTADIR = gioPORTA->DIR;
        config_reg->CONFIG_PORTAPDR = gioPORTA->PDR;
        config_reg->CONFIG_PORTAPSL = gioPORTA->PSL;
        config_reg->CONFIG_PORTAPULDIS = gioPORTA->PULDIS;
        /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
        config_reg->CONFIG_PORTBDIR = gioPORTB->DIR;
        config_reg->CONFIG_PORTBPDR = gioPORTB->PDR;
        config_reg->CONFIG_PORTBPSL = gioPORTB->PSL;
        config_reg->CONFIG_PORTBPULDIS = gioPORTB->PULDIS;
    }
}

/* USER CODE BEGIN (19) */
/* USER CODE END */
