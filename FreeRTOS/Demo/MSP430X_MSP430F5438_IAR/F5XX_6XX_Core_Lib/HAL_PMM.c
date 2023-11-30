/*******************************************************************************
 *
 * HAL_PMM.c
 * Power Management Module Library for MSP430F5xx/6xx family
 *
 *
 * Copyright (C) 2010 Texas Instruments Incorporated - http://www.ti.com/
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
 ******************************************************************************/

#include "msp430.h"
#include "HAL_PMM.h"

/*******************************************************************************
 * \brief   Increase Vcore by one level
 *
 * \param level     Level to which Vcore needs to be increased
 * \return status   Success/failure
 ******************************************************************************/

static uint16_t SetVCoreUp(uint8_t level)
{
    uint16_t PMMRIE_backup, SVSMHCTL_backup, SVSMLCTL_backup;

    // The code flow for increasing the Vcore has been altered to work around
    // the erratum FLASH37.
    // Please refer to the Errata sheet to know if a specific device is affected
    // DO NOT ALTER THIS FUNCTION

    // Open PMM registers for write access
    PMMCTL0_H = 0xA5;

    // Disable dedicated Interrupts
    // Backup all registers
    PMMRIE_backup = PMMRIE;
    PMMRIE &= ~(SVMHVLRPE | SVSHPE | SVMLVLRPE | SVSLPE | SVMHVLRIE |
                SVMHIE | SVSMHDLYIE | SVMLVLRIE | SVMLIE | SVSMLDLYIE);
    SVSMHCTL_backup = SVSMHCTL;
    SVSMLCTL_backup = SVSMLCTL;

    // Clear flags
    PMMIFG = 0;

    // Set SVM highside to new level and check if a VCore increase is possible
    SVSMHCTL = SVMHE | SVSHE | (SVSMHRRL0 * level);

    // Wait until SVM highside is settled
    while ((PMMIFG & SVSMHDLYIFG) == 0) ;

    // Clear flag
    PMMIFG &= ~SVSMHDLYIFG;

    // Check if a VCore increase is possible
    if ((PMMIFG & SVMHIFG) == SVMHIFG){     // -> Vcc is too low for a Vcore increase
        // recover the previous settings
        PMMIFG &= ~SVSMHDLYIFG;
        SVSMHCTL = SVSMHCTL_backup;

        // Wait until SVM highside is settled
        while ((PMMIFG & SVSMHDLYIFG) == 0) ;

        // Clear all Flags
        PMMIFG &= ~(SVMHVLRIFG | SVMHIFG | SVSMHDLYIFG | SVMLVLRIFG | SVMLIFG | SVSMLDLYIFG);

        PMMRIE = PMMRIE_backup;             // Restore PMM interrupt enable register
        PMMCTL0_H = 0x00;                   // Lock PMM registers for write access
        return PMM_STATUS_ERROR;            // return: voltage not set
    }

    // Set also SVS highside to new level
    // Vcc is high enough for a Vcore increase
    SVSMHCTL |= (SVSHRVL0 * level);

    // Wait until SVM highside is settled
    while ((PMMIFG & SVSMHDLYIFG) == 0) ;

    // Clear flag
    PMMIFG &= ~SVSMHDLYIFG;

    // Set VCore to new level
    PMMCTL0_L = PMMCOREV0 * level;

    // Set SVM, SVS low side to new level
    SVSMLCTL = SVMLE | (SVSMLRRL0 * level) | SVSLE | (SVSLRVL0 * level);

    // Wait until SVM, SVS low side is settled
    while ((PMMIFG & SVSMLDLYIFG) == 0) ;

    // Clear flag
    PMMIFG &= ~SVSMLDLYIFG;
    // SVS, SVM core and high side are now set to protect for the new core level

    // Restore Low side settings
    // Clear all other bits _except_ level settings
    SVSMLCTL &= (SVSLRVL0 + SVSLRVL1 + SVSMLRRL0 + SVSMLRRL1 + SVSMLRRL2);

    // Clear level settings in the backup register,keep all other bits
    SVSMLCTL_backup &= ~(SVSLRVL0 + SVSLRVL1 + SVSMLRRL0 + SVSMLRRL1 + SVSMLRRL2);

    // Restore low-side SVS monitor settings
    SVSMLCTL |= SVSMLCTL_backup;

    // Restore High side settings
    // Clear all other bits except level settings
    SVSMHCTL &= (SVSHRVL0 + SVSHRVL1 + SVSMHRRL0 + SVSMHRRL1 + SVSMHRRL2);

    // Clear level settings in the backup register,keep all other bits
    SVSMHCTL_backup &= ~(SVSHRVL0 + SVSHRVL1 + SVSMHRRL0 + SVSMHRRL1 + SVSMHRRL2);

    // Restore backup
    SVSMHCTL |= SVSMHCTL_backup;

    // Wait until high side, low side settled
    while (((PMMIFG & SVSMLDLYIFG) == 0) && ((PMMIFG & SVSMHDLYIFG) == 0)) ;

    // Clear all Flags
    PMMIFG &= ~(SVMHVLRIFG | SVMHIFG | SVSMHDLYIFG | SVMLVLRIFG | SVMLIFG | SVSMLDLYIFG);

    PMMRIE = PMMRIE_backup;                 // Restore PMM interrupt enable register
    PMMCTL0_H = 0x00;                       // Lock PMM registers for write access

    return PMM_STATUS_OK;
}

/*******************************************************************************
 * \brief  Decrease Vcore by one level
 *
 * \param  level    Level to which Vcore needs to be decreased
 * \return status   Success/failure
 ******************************************************************************/

static uint16_t SetVCoreDown(uint8_t level)
{
    uint16_t PMMRIE_backup, SVSMHCTL_backup, SVSMLCTL_backup;

    // The code flow for decreasing the Vcore has been altered to work around
    // the erratum FLASH37.
    // Please refer to the Errata sheet to know if a specific device is affected
    // DO NOT ALTER THIS FUNCTION

    // Open PMM registers for write access
    PMMCTL0_H = 0xA5;

    // Disable dedicated Interrupts
    // Backup all registers
    PMMRIE_backup = PMMRIE;
    PMMRIE &= ~(SVMHVLRPE | SVSHPE | SVMLVLRPE | SVSLPE | SVMHVLRIE |
                SVMHIE | SVSMHDLYIE | SVMLVLRIE | SVMLIE | SVSMLDLYIE);
    SVSMHCTL_backup = SVSMHCTL;
    SVSMLCTL_backup = SVSMLCTL;

    // Clear flags
    PMMIFG &= ~(SVMHIFG | SVSMHDLYIFG | SVMLIFG | SVSMLDLYIFG);

    // Set SVM, SVS high & low side to new settings in normal mode
    SVSMHCTL = SVMHE | (SVSMHRRL0 * level) | SVSHE | (SVSHRVL0 * level);
    SVSMLCTL = SVMLE | (SVSMLRRL0 * level) | SVSLE | (SVSLRVL0 * level);

    // Wait until SVM high side and SVM low side is settled
    while ((PMMIFG & SVSMHDLYIFG) == 0 || (PMMIFG & SVSMLDLYIFG) == 0) ;

    // Clear flags
    PMMIFG &= ~(SVSMHDLYIFG + SVSMLDLYIFG);
    // SVS, SVM core and high side are now set to protect for the new core level

    // Set VCore to new level
    PMMCTL0_L = PMMCOREV0 * level;

    // Restore Low side settings
    // Clear all other bits _except_ level settings
    SVSMLCTL &= (SVSLRVL0 + SVSLRVL1 + SVSMLRRL0 + SVSMLRRL1 + SVSMLRRL2);

    // Clear level settings in the backup register,keep all other bits
    SVSMLCTL_backup &= ~(SVSLRVL0 + SVSLRVL1 + SVSMLRRL0 + SVSMLRRL1 + SVSMLRRL2);

    // Restore low-side SVS monitor settings
    SVSMLCTL |= SVSMLCTL_backup;

    // Restore High side settings
    // Clear all other bits except level settings
    SVSMHCTL &= (SVSHRVL0 + SVSHRVL1 + SVSMHRRL0 + SVSMHRRL1 + SVSMHRRL2);

    // Clear level settings in the backup register, keep all other bits
    SVSMHCTL_backup &= ~(SVSHRVL0 + SVSHRVL1 + SVSMHRRL0 + SVSMHRRL1 + SVSMHRRL2);

    // Restore backup
    SVSMHCTL |= SVSMHCTL_backup;

    // Wait until high side, low side settled
    while (((PMMIFG & SVSMLDLYIFG) == 0) && ((PMMIFG & SVSMHDLYIFG) == 0)) ;

    // Clear all Flags
    PMMIFG &= ~(SVMHVLRIFG | SVMHIFG | SVSMHDLYIFG | SVMLVLRIFG | SVMLIFG | SVSMLDLYIFG);

    PMMRIE = PMMRIE_backup;                // Restore PMM interrupt enable register
    PMMCTL0_H = 0x00;                      // Lock PMM registers for write access
    return PMM_STATUS_OK;                  // Return: OK
}

uint16_t SetVCore(uint8_t level)
{
    uint16_t actlevel;
    uint16_t status = 0;

    level &= PMMCOREV_3;                   // Set Mask for Max. level
    actlevel = (PMMCTL0 & PMMCOREV_3);     // Get actual VCore
                                           // step by step increase or decrease
    while ((level != actlevel) && (status == 0)) {
        if (level > actlevel){
            status = SetVCoreUp(++actlevel);
        }
        else {
            status = SetVCoreDown(--actlevel);
        }
    }

    return status;
}

