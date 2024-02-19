/** @file sys_pcr.c
 *   @brief PCR Driver Implementation File
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

#include "sys_pcr.h"

/* USER CODE BEGIN (0) */
/* USER CODE END */

/* USER CODE BEGIN (1) */
/* USER CODE END */

/** @fn void peripheral_Frame_Protection_Set(peripheral_Frame_Select_t peripheral_Frame)
 *   @brief Set the peripheral protection of the selected frame
 *   @param[in] peripheral_Frame - Peripheral frame to be protected
 *
 *   This function sets the protection for the selected frame.
 */
/* SourceId : PCR_SourceId_001 */
/* DesignId : PCR_DesignId_001 */
/* Requirements : HL_SR41 */
void peripheral_Frame_Protection_Set( peripheral_Frame_Select_t peripheral_Frame )
{
    /* USER CODE BEGIN (2) */
    /* USER CODE END */

    uint32 chip_select_grp;
    uint32 Quarant_selct;

    chip_select_grp = ( peripheral_Frame.Peripheral_CS >> 3U );
    Quarant_selct = ( uint32 ) ( peripheral_Frame.Peripheral_Quadrant
                                 << ( ( peripheral_Frame.Peripheral_CS & 7U ) << 2U ) );

    if( chip_select_grp >= 3U )
    {
        pcrREG->PPROTSET3 = Quarant_selct;
    }
    else if( chip_select_grp >= 2U )
    {
        pcrREG->PPROTSET2 = Quarant_selct;
    }
    else if( chip_select_grp >= 1U )
    {
        pcrREG->PPROTSET1 = Quarant_selct;
    }
    else
    {
        pcrREG->PPROTSET0 = Quarant_selct;
    }

    /* USER CODE BEGIN (3) */
    /* USER CODE END */
}

/* USER CODE BEGIN (4) */
/* USER CODE END */

/** @fn void peripheral_Frame_Protection_Clr(peripheral_Frame_Select_t peripheral_Frame)
 *   @brief Clear the peripheral protection of the selected frame
 *   @param[in] peripheral_Frame - Peripheral frame to be out of protection
 *
 *   This function clears the protection set for the selected frame.
 */
/* SourceId : PCR_SourceId_002 */
/* DesignId : PCR_DesignId_002 */
/* Requirements : HL_SR42 */
void peripheral_Frame_Protection_Clr( peripheral_Frame_Select_t peripheral_Frame )
{
    /* USER CODE BEGIN (5) */
    /* USER CODE END */

    uint32 chip_select_grp;
    uint32 Quarant_selct;

    chip_select_grp = ( peripheral_Frame.Peripheral_CS >> 3U );
    Quarant_selct = ( uint32 ) ( peripheral_Frame.Peripheral_Quadrant
                                 << ( ( peripheral_Frame.Peripheral_CS & 7U ) << 2U ) );

    if( chip_select_grp >= 3U )
    {
        pcrREG->PPROTCLR3 = Quarant_selct;
    }
    else if( chip_select_grp >= 2U )
    {
        pcrREG->PPROTCLR2 = Quarant_selct;
    }
    else if( chip_select_grp >= 1U )
    {
        pcrREG->PPROTCLR1 = Quarant_selct;
    }
    else
    {
        pcrREG->PPROTCLR0 = Quarant_selct;
    }

    /* USER CODE BEGIN (6) */
    /* USER CODE END */
}

/* USER CODE BEGIN (7) */
/* USER CODE END */

/** @fn void peripheral_Frame_Powerdown_Set(peripheral_Frame_Select_t peripheral_Frame)
 *   @brief Take the selected peripheral to powerdown
 *   @param[in] peripheral_Frame - Peripheral frame to be taken to powerdown
 *
 *   This function will set the selected peripheral frame to powerdown.
 */
/* SourceId : PCR_SourceId_003 */
/* DesignId : PCR_DesignId_003 */
/* Requirements : HL_SR43 */
void peripheral_Frame_Powerdown_Set( peripheral_Frame_Select_t peripheral_Frame )
{
    /* USER CODE BEGIN (8) */
    /* USER CODE END */

    uint32 chip_select_grp;
    uint32 Quarant_selct;

    chip_select_grp = ( peripheral_Frame.Peripheral_CS >> 3U );
    Quarant_selct = ( uint32 ) ( peripheral_Frame.Peripheral_Quadrant
                                 << ( ( peripheral_Frame.Peripheral_CS & 7U ) << 2U ) );

    if( chip_select_grp >= 3U )
    {
        pcrREG->PSPWRDWNSET3 = Quarant_selct;
    }
    else if( chip_select_grp >= 2U )
    {
        pcrREG->PSPWRDWNSET2 = Quarant_selct;
    }
    else if( chip_select_grp >= 1U )
    {
        pcrREG->PSPWRDWNSET1 = Quarant_selct;
    }
    else
    {
        pcrREG->PSPWRDWNSET0 = Quarant_selct;
    }

    /* USER CODE BEGIN (9) */
    /* USER CODE END */
}

/* USER CODE BEGIN (10) */
/* USER CODE END */

/** @fn void peripheral_Frame_Powerdown_Clr(peripheral_Frame_Select_t peripheral_Frame)
 *   @brief Bring the selected peripheral frame out of powerdown
 *   @param[in] peripheral_Frame - Peripheral frame to be taken out of powerdown
 *
 *   This function will bring the selected peripheral frame out of powerdown.
 */
/* SourceId : PCR_SourceId_004 */
/* DesignId : PCR_DesignId_004 */
/* Requirements : HL_SR44 */
void peripheral_Frame_Powerdown_Clr( peripheral_Frame_Select_t peripheral_Frame )
{
    /* USER CODE BEGIN (11) */
    /* USER CODE END */

    uint32 chip_select_grp;
    uint32 Quarant_selct;

    chip_select_grp = ( peripheral_Frame.Peripheral_CS >> 3U );
    Quarant_selct = ( uint32 ) ( peripheral_Frame.Peripheral_Quadrant
                                 << ( ( peripheral_Frame.Peripheral_CS & 7U ) << 2U ) );

    if( chip_select_grp >= 3U )
    {
        pcrREG->PSPWRDWNCLR3 = Quarant_selct;
    }
    else if( chip_select_grp >= 2U )
    {
        pcrREG->PSPWRDWNCLR2 = Quarant_selct;
    }
    else if( chip_select_grp >= 1U )
    {
        pcrREG->PSPWRDWNCLR1 = Quarant_selct;
    }
    else
    {
        pcrREG->PSPWRDWNCLR0 = Quarant_selct;
    }

    /* USER CODE BEGIN (12) */
    /* USER CODE END */
}

/* USER CODE BEGIN (13) */
/* USER CODE END */

/** @fn void peripheral_Mem_Frame_Prot_Set(peripheral_MemoryFrame_CS_t
 * peripheral_Memory_Frame_CS)
 *   @brief Set the peripheral memory protection of the selected frame
 *   @param[in] peripheral_Memory_Frame_CS - Peripheral memory frame to be protected
 *
 *   This function sets the protection for the selected peripheral memory frame.
 */
/* SourceId : PCR_SourceId_005 */
/* DesignId : PCR_DesignId_017 */
/* Requirements : HL_SR57 */
void peripheral_Mem_Frame_Prot_Set(
    peripheral_MemoryFrame_CS_t peripheral_Memory_Frame_CS )
{
    /* USER CODE BEGIN (14) */
    /* USER CODE END */

    uint32 chip_select_grp;

    chip_select_grp = ( peripheral_Memory_Frame_CS >> 5U );

    if( chip_select_grp >= 1U )
    {
        pcrREG->PMPROTSET1 = ( uint32 ) 1U << ( peripheral_Memory_Frame_CS & 0xFU );
    }
    else
    {
        pcrREG->PMPROTSET0 = ( uint32 ) 1U << peripheral_Memory_Frame_CS;
    }

    /* USER CODE BEGIN (15) */
    /* USER CODE END */
}

/* USER CODE BEGIN (16) */
/* USER CODE END */

/** @fn void peripheral_Mem_Frame_Prot_Clr(peripheral_MemoryFrame_CS_t
 * peripheral_Memory_Frame_CS)
 *   @brief Clear the peripheral memory protection of the selected frame
 *   @param[in] peripheral_Memory_Frame_CS - Peripheral memory frame to be cleared from
 * protection
 *
 *   This function clears the protection set for the selected peripheral memory frame.
 */
/* SourceId : PCR_SourceId_006 */
/* DesignId : PCR_DesignId_018 */
/* Requirements : HL_SR58 */
void peripheral_Mem_Frame_Prot_Clr(
    peripheral_MemoryFrame_CS_t peripheral_Memory_Frame_CS )
{
    /* USER CODE BEGIN (17) */
    /* USER CODE END */

    uint32 chip_select_grp;

    chip_select_grp = ( peripheral_Memory_Frame_CS >> 5U );

    if( chip_select_grp >= 1U )
    {
        pcrREG->PMPROTCLR1 = ( uint32 ) 1U << ( peripheral_Memory_Frame_CS & 0xFU );
    }
    else
    {
        pcrREG->PMPROTCLR0 = ( uint32 ) 1U << peripheral_Memory_Frame_CS;
    }

    /* USER CODE BEGIN (18) */
    /* USER CODE END */
}

/* USER CODE BEGIN (19) */
/* USER CODE END */

/** @fn void peripheral_Mem_Frame_Pwrdwn_Set(peripheral_MemoryFrame_CS_t
 * peripheral_Memory_Frame_CS)
 *   @brief Take the selected peripheral memory frame to powerdown
 *   @param[in] peripheral_Memory_Frame_CS - Peripheral memory frame to be taken to
 * powerdown
 *
 *   This function will set the selected peripheral memory frame to powerdown.
 */
/* SourceId : PCR_SourceId_007 */
/* DesignId : PCR_DesignId_019 */
/* Requirements : HL_SR59 */
void peripheral_Mem_Frame_Pwrdwn_Set(
    peripheral_MemoryFrame_CS_t peripheral_Memory_Frame_CS )
{
    /* USER CODE BEGIN (20) */
    /* USER CODE END */

    uint32 chip_select_grp;

    chip_select_grp = ( peripheral_Memory_Frame_CS >> 5U );

    if( chip_select_grp >= 1U )
    {
        pcrREG->PCSPWRDWNSET0 = ( uint32 ) 1U << ( peripheral_Memory_Frame_CS & 0xFU );
    }
    else
    {
        pcrREG->PCSPWRDWNSET1 = ( uint32 ) 1U << peripheral_Memory_Frame_CS;
    }

    /* USER CODE BEGIN (21) */
    /* USER CODE END */
}

/* USER CODE BEGIN (22) */
/* USER CODE END */

/** @fn void peripheral_Mem_Frame_Pwrdwn_Clr (peripheral_MemoryFrame_CS_t
 * peripheral_Memory_Frame_CS)
 *   @brief Bring the selected peripheral Memory frame out of powerdown
 *   @param[in] peripheral_Memory_Frame_CS - Peripheral memory frame to be taken out of
 * powerdown
 *
 *   This function will bring the selected peripheral memory frame out of powerdown.
 */
/* SourceId : PCR_SourceId_008 */
/* DesignId : PCR_DesignId_020 */
/* Requirements : HL_SR60 */
void peripheral_Mem_Frame_Pwrdwn_Clr(
    peripheral_MemoryFrame_CS_t peripheral_Memory_Frame_CS )
{
    /* USER CODE BEGIN (23) */
    /* USER CODE END */

    uint32 chip_select_grp;

    chip_select_grp = ( peripheral_Memory_Frame_CS >> 5U );

    if( chip_select_grp >= 1U )
    {
        pcrREG->PCSPWRDWNCLR0 = ( uint32 ) 1U << ( peripheral_Memory_Frame_CS & 0xFU );
    }
    else
    {
        pcrREG->PCSPWRDWNCLR1 = ( uint32 ) 1U << peripheral_Memory_Frame_CS;
    }

    /* USER CODE BEGIN (24) */
    /* USER CODE END */
}

/* USER CODE BEGIN (25) */
/* USER CODE END */

/** @fn void peripheral_Protection_Set(peripheral_Quad_ChipSelect_t peripheral_Quad_CS)
 *   @brief Set the peripheral protection of all the selected frames
 *   @param[in] peripheral_Quad_CS - All Peripheral frames to be protected
 *
 *   This function sets the protection for all the selected frames.
 */
/* SourceId : PCR_SourceId_009 */
/* DesignId : PCR_DesignId_005 */
/* Requirements : HL_SR45 */
void peripheral_Protection_Set( peripheral_Quad_ChipSelect_t peripheral_Quad_CS )
{
    /* USER CODE BEGIN (26) */
    /* USER CODE END */

    pcrREG->PPROTSET0 = peripheral_Quad_CS.Peripheral_Quad0_3_CS0_7;
    pcrREG->PPROTSET1 = peripheral_Quad_CS.Peripheral_Quad4_7_CS8_15;
    pcrREG->PPROTSET2 = peripheral_Quad_CS.Peripheral_Quad8_11_CS16_23;
    pcrREG->PPROTSET3 = peripheral_Quad_CS.Peripheral_Quad12_15_CS24_31;

    /* USER CODE BEGIN (27) */
    /* USER CODE END */
}

/* USER CODE BEGIN (28) */
/* USER CODE END */

/** @fn void peripheral_Protection_Clr(peripheral_Quad_ChipSelect_t peripheral_Quad_CS)
 *   @brief Clear the peripheral protection of all the selected frames
 *   @param[in] peripheral_Quad_CS - All Peripheral frames to be out of protection.
 *
 *   This function clears the protection set for all the selected frame.
 */
/* SourceId : PCR_SourceId_010 */
/* DesignId : PCR_DesignId_006 */
/* Requirements : HL_SR46 */
void peripheral_Protection_Clr( peripheral_Quad_ChipSelect_t peripheral_Quad_CS )
{
    /* USER CODE BEGIN (29) */
    /* USER CODE END */

    pcrREG->PPROTCLR0 = peripheral_Quad_CS.Peripheral_Quad0_3_CS0_7;
    pcrREG->PPROTCLR1 = peripheral_Quad_CS.Peripheral_Quad4_7_CS8_15;
    pcrREG->PPROTCLR2 = peripheral_Quad_CS.Peripheral_Quad8_11_CS16_23;
    pcrREG->PPROTCLR3 = peripheral_Quad_CS.Peripheral_Quad12_15_CS24_31;

    /* USER CODE BEGIN (30) */
    /* USER CODE END */
}

/* USER CODE BEGIN (31) */
/* USER CODE END */

/** @fn void peripheral_Powerdown_Set(peripheral_Quad_ChipSelect_t peripheral_Quad_CS)
 *   @brief Take all the selected peripheral frame to powerdown
 *   @param[in] peripheral_Quad_CS - Peripheral frames to be taken to powerdown
 *
 *   This function will set all the selected peripheral frame to powerdown.
 */
/* SourceId : PCR_SourceId_011 */
/* DesignId : PCR_DesignId_008 */
/* Requirements : HL_SR48 */
void peripheral_Powerdown_Set( peripheral_Quad_ChipSelect_t peripheral_Quad_CS )
{
    /* USER CODE BEGIN (32) */
    /* USER CODE END */

    pcrREG->PSPWRDWNSET0 = peripheral_Quad_CS.Peripheral_Quad0_3_CS0_7;
    pcrREG->PSPWRDWNSET1 = peripheral_Quad_CS.Peripheral_Quad4_7_CS8_15;
    pcrREG->PSPWRDWNSET2 = peripheral_Quad_CS.Peripheral_Quad8_11_CS16_23;
    pcrREG->PSPWRDWNSET3 = peripheral_Quad_CS.Peripheral_Quad12_15_CS24_31;

    /* USER CODE BEGIN (33) */
    /* USER CODE END */
}

/* USER CODE BEGIN (34) */
/* USER CODE END */

/** @fn void peripheral_Powerdown_Clr(peripheral_Quad_ChipSelect_t peripheral_Quad_CS)
 *   @brief Bring all the selected peripheral frame out of powerdown
 *   @param[in] peripheral_Quad_CS - Peripheral frames to be taken out of powerdown
 *
 *   This function will bring all the selected peripheral frame out of powerdown.
 */
/* SourceId : PCR_SourceId_012 */
/* DesignId : PCR_DesignId_009 */
/* Requirements : HL_SR49 */
void peripheral_Powerdown_Clr( peripheral_Quad_ChipSelect_t peripheral_Quad_CS )
{
    /* USER CODE BEGIN (35) */
    /* USER CODE END */

    pcrREG->PSPWRDWNCLR0 = peripheral_Quad_CS.Peripheral_Quad0_3_CS0_7;
    pcrREG->PSPWRDWNCLR1 = peripheral_Quad_CS.Peripheral_Quad4_7_CS8_15;
    pcrREG->PSPWRDWNCLR2 = peripheral_Quad_CS.Peripheral_Quad8_11_CS16_23;
    pcrREG->PSPWRDWNCLR3 = peripheral_Quad_CS.Peripheral_Quad12_15_CS24_31;

    /* USER CODE BEGIN (36) */
    /* USER CODE END */
}

/* USER CODE BEGIN (37) */
/* USER CODE END */

/** @fn void peripheral_Memory_Protection_Set(peripheral_Memory_ChipSelect_t
 * peripheral_Memory_CS)
 *   @brief Set the peripheral memory protection of all the selected frame
 *   @param[in] peripheral_Memory_CS - Peripheral memory frames to be protected
 *
 *   This function sets the protection for all the selected peripheral memory frame.
 */
/* SourceId : PCR_SourceId_013 */
/* DesignId : PCR_DesignId_011 */
/* Requirements : HL_SR51 */
void peripheral_Memory_Protection_Set(
    peripheral_Memory_ChipSelect_t peripheral_Memory_CS )
{
    /* USER CODE BEGIN (38) */
    /* USER CODE END */

    pcrREG->PMPROTSET0 = peripheral_Memory_CS.Peripheral_Mem_CS0_31;
    pcrREG->PMPROTSET1 = peripheral_Memory_CS.Peripheral_Mem_CS32_63;

    /* USER CODE BEGIN (39) */
    /* USER CODE END */
}

/* USER CODE BEGIN (40) */
/* USER CODE END */

/** @fn void peripheral_Memory_Protection_Clr(peripheral_Memory_ChipSelect_t
 * peripheral_Memory_CS)
 *   @brief Clear the peripheral memory protection of all the selected frame
 *   @param[in] peripheral_Memory_CS - Peripheral memory frames to be cleared from
 * protection
 *
 *   This function clears the protection set for all the selected peripheral memory frame.
 */
/* SourceId : PCR_SourceId_014 */
/* DesignId : PCR_DesignId_012 */
/* Requirements : HL_SR52 */
void peripheral_Memory_Protection_Clr(
    peripheral_Memory_ChipSelect_t peripheral_Memory_CS )
{
    /* USER CODE BEGIN (41) */
    /* USER CODE END */

    pcrREG->PMPROTCLR0 = peripheral_Memory_CS.Peripheral_Mem_CS0_31;
    pcrREG->PMPROTCLR1 = peripheral_Memory_CS.Peripheral_Mem_CS32_63;

    /* USER CODE BEGIN (42) */
    /* USER CODE END */
}

/* USER CODE BEGIN (43) */
/* USER CODE END */

/** @fn void peripheral_Memory_Powerdown_Set(peripheral_Memory_ChipSelect_t
 * peripheral_Memory_CS)
 *   @brief Take all the selected peripheral memory frame to powerdown
 *   @param[in] peripheral_Memory_CS - Peripheral memory frames to be taken to powerdown
 *
 *   This function will set all the selected peripheral memory frame to powerdown.
 */
/* SourceId : PCR_SourceId_015 */
/* DesignId : PCR_DesignId_014 */
/* Requirements : HL_SR54 */
void peripheral_Memory_Powerdown_Set( peripheral_Memory_ChipSelect_t peripheral_Memory_CS )
{
    /* USER CODE BEGIN (44) */
    /* USER CODE END */

    pcrREG->PCSPWRDWNSET0 = peripheral_Memory_CS.Peripheral_Mem_CS0_31;
    pcrREG->PCSPWRDWNSET1 = peripheral_Memory_CS.Peripheral_Mem_CS32_63;

    /* USER CODE BEGIN (45) */
    /* USER CODE END */
}

/* USER CODE BEGIN (46) */
/* USER CODE END */

/** @fn void peripheral_Memory_Powerdown_Clr(peripheral_Memory_ChipSelect_t
 * peripheral_Memory_CS)
 *   @brief Bring all the selected peripheral Memory frame out of powerdown
 *   @param[in] peripheral_Memory_CS - Peripheral memory frames to be taken out of
 * powerdown
 *
 *   This function will bring all the selected peripheral memory frame out of powerdown.
 */
/* SourceId : PCR_SourceId_016 */
/* DesignId : PCR_DesignId_015 */
/* Requirements : HL_SR55 */
void peripheral_Memory_Powerdown_Clr( peripheral_Memory_ChipSelect_t peripheral_Memory_CS )
{
    /* USER CODE BEGIN (47) */
    /* USER CODE END */

    pcrREG->PCSPWRDWNSET0 = peripheral_Memory_CS.Peripheral_Mem_CS0_31;
    pcrREG->PCSPWRDWNCLR0 = peripheral_Memory_CS.Peripheral_Mem_CS32_63;

    /* USER CODE BEGIN (48) */
    /* USER CODE END */
}

/* USER CODE BEGIN (49) */
/* USER CODE END */

/** @fn void peripheral_Powerdown_Status(peripheral_Quad_ChipSelect_t* peripheral_Quad_CS)
 *   @brief Get the powerdown status of the peripheral frames.
 *   @param[out] peripheral_Quad_CS Peripheral frames power down status
 *
 *   This function gets the powerdown status of the peripheral frames.
 */
/* SourceId : PCR_SourceId_017 */
/* DesignId : PCR_DesignId_010 */
/* Requirements : HL_SR50 */
void peripheral_Powerdown_Status( peripheral_Quad_ChipSelect_t * peripheral_Quad_CS )
{
    /* USER CODE BEGIN (50) */
    /* USER CODE END */

    peripheral_Quad_CS->Peripheral_Quad0_3_CS0_7 = pcrREG->PSPWRDWNSET0;
    peripheral_Quad_CS->Peripheral_Quad4_7_CS8_15 = pcrREG->PSPWRDWNSET1;
    peripheral_Quad_CS->Peripheral_Quad8_11_CS16_23 = pcrREG->PSPWRDWNSET2;
    peripheral_Quad_CS->Peripheral_Quad12_15_CS24_31 = pcrREG->PSPWRDWNSET3;

    /* USER CODE BEGIN (51) */
    /* USER CODE END */
}

/* USER CODE BEGIN (52) */
/* USER CODE END */

/** @fn void peripheral_Protection_Status(peripheral_Quad_ChipSelect_t* peripheral_Quad_CS
 * )
 *   @brief Get the protection status of the peripheral frames
 *   @param[out] peripheral_Quad_CS Peripheral frames protection status
 *
 *   This function gets the protection status of the peripheral frames.
 */
/* SourceId : PCR_SourceId_018 */
/* DesignId : PCR_DesignId_007 */
/* Requirements : HL_SR47 */
void peripheral_Protection_Status( peripheral_Quad_ChipSelect_t * peripheral_Quad_CS )
{
    /* USER CODE BEGIN (53) */
    /* USER CODE END */

    peripheral_Quad_CS->Peripheral_Quad0_3_CS0_7 = pcrREG->PPROTSET0;
    peripheral_Quad_CS->Peripheral_Quad4_7_CS8_15 = pcrREG->PPROTSET1;
    peripheral_Quad_CS->Peripheral_Quad8_11_CS16_23 = pcrREG->PPROTSET2;
    peripheral_Quad_CS->Peripheral_Quad12_15_CS24_31 = pcrREG->PPROTSET3;

    /* USER CODE BEGIN (54) */
    /* USER CODE END */
}

/* USER CODE BEGIN (55) */
/* USER CODE END */

/** @fn void peripheral_Memory_Protection_Status(peripheral_Memory_ChipSelect_t*
 * peripheral_Memory_CS)
 *   @brief Get the protection set of all the peripheral Memory frame
 *   @param[out] peripheral_Memory_CS Peripheral memory frames protection status
 *
 *   This function gets the protection status of all the peripheral Memory frame.
 */
/* SourceId : PCR_SourceId_019 */
/* DesignId : PCR_DesignId_013 */
/* Requirements : HL_SR53 */
void peripheral_Memory_Protection_Status(
    peripheral_Memory_ChipSelect_t * peripheral_Memory_CS )
{
    /* USER CODE BEGIN (56) */
    /* USER CODE END */

    /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "Hardware status bit read" */
    peripheral_Memory_CS->Peripheral_Mem_CS0_31 = pcrREG->PMPROTSET0;
    peripheral_Memory_CS->Peripheral_Mem_CS32_63 = pcrREG->PMPROTSET1;

    /* USER CODE BEGIN (57) */
    /* USER CODE END */
}

/* USER CODE BEGIN (58) */
/* USER CODE END */

/** @fn void peripheral_Memory_Powerdown_Status(peripheral_Memory_ChipSelect_t*
 * peripheral_Memory_CS)
 *   @brief Get the powerdown status of all the peripheral Memory frame
 *   @param[out] peripheral_Memory_CS Peripheral memory frames powerdown status
 *
 *   This function gets the powerdown status of all the peripheral Memory frame.
 */
/* SourceId : PCR_SourceId_020 */
/* DesignId : PCR_DesignId_016 */
/* Requirements : HL_SR56 */
void peripheral_Memory_Powerdown_Status(
    peripheral_Memory_ChipSelect_t * peripheral_Memory_CS )
{
    /* USER CODE BEGIN (59) */
    /* USER CODE END */

    peripheral_Memory_CS->Peripheral_Mem_CS0_31 = pcrREG->PCSPWRDWNSET0;
    peripheral_Memory_CS->Peripheral_Mem_CS32_63 = pcrREG->PCSPWRDWNSET1;

    /* USER CODE BEGIN (60) */
    /* USER CODE END */
}

/* USER CODE BEGIN (61) */
/* USER CODE END */

/** @fn void pcrGetConfigValue(pcr_config_reg_t *config_reg, config_value_type_t type)
 *   @brief Get the initial or current values of the configuration registers
 *
 *	@param[in] *config_reg: pointer to the struct to which the initial or current
 *                           value of the configuration registers need to be stored
 *	@param[in] type:    whether initial or current value of the configuration registers
 *need to be stored
 *						- InitialValue: initial value of the configuration registers will
 *be stored in the struct pointed by config_reg
 *						- CurrentValue: initial value of the configuration registers will
 *be stored in the struct pointed by config_reg
 *
 *   This function will copy the initial or current value (depending on the parameter
 *'type') of the configuration registers to the struct pointed by config_reg
 *
 */
/* SourceId : PCR_SourceId_021 */
/* DesignId : PCR_DesignId_021 */
/* Requirements : HL_SR61 */
void pcrGetConfigValue( pcr_config_reg_t * config_reg, config_value_type_t type )
{
    if( type == InitialValue )
    { /* Do not pass Initial value as parameter as there is no PCR initialization API */
    }
    else
    {
        /*SAFETYMCUSW 134 S MR:12.2 <APPROVED> "LDRA Tool issue" */
        config_reg->CONFIG_PMPROTSET0 = pcrREG->PMPROTSET0;
        config_reg->CONFIG_PMPROTSET1 = pcrREG->PMPROTSET1;
        config_reg->CONFIG_PPROTSET0 = pcrREG->PPROTSET0;
        config_reg->CONFIG_PPROTSET1 = pcrREG->PPROTSET1;
        config_reg->CONFIG_PPROTSET2 = pcrREG->PPROTSET2;
        config_reg->CONFIG_PPROTSET3 = pcrREG->PPROTSET3;
        config_reg->CONFIG_PCSPWRDWNSET0 = pcrREG->PCSPWRDWNSET0;
        config_reg->CONFIG_PCSPWRDWNSET1 = pcrREG->PCSPWRDWNSET1;
        config_reg->CONFIG_PSPWRDWNSET0 = pcrREG->PSPWRDWNSET0;
        config_reg->CONFIG_PSPWRDWNSET1 = pcrREG->PSPWRDWNSET1;
        config_reg->CONFIG_PSPWRDWNSET2 = pcrREG->PSPWRDWNSET2;
        config_reg->CONFIG_PSPWRDWNSET3 = pcrREG->PSPWRDWNSET3;
    }
}
