/*******************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only
* intended for use with Renesas products. No other uses are authorized. This
* software is owned by Renesas Electronics Corporation and is protected under
* all applicable laws, including copyright laws.
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES REGARDING
* THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY, INCLUDING BUT NOT
* LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE
* AND NON-INFRINGEMENT. ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED.
* TO THE MAXIMUM EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS
* ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES SHALL BE LIABLE
* FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR
* ANY REASON RELATED TO THIS SOFTWARE, EVEN IF RENESAS OR ITS AFFILIATES HAVE
* BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software
* and to discontinue the availability of this software. By using this software,
* you agree to the additional terms and conditions found by accessing the
* following link:
* http://www.renesas.com/disclaimer
*
* Copyright (C) 2014 Renesas Electronics Corporation. All rights reserved.
*******************************************************************************/

/*******************************************************************************
* File Name    : r_dtc_rx.c
* Description  : Functions for using DTC on RX devices.
*******************************************************************************/
/*******************************************************************************
* History : DD.MM.YYYY Version Description
*         : 17.03.2014 1.00    Initial revision
*         : 17.07.2014 2.00    Second  revision
*         : 12.11.2014 2.01    Added RX113.
*         : 30.01.2015 2.02    Added RX71M.
*         : 13.04.2015 2.03    Added RX231 and RX230.
*         : 24.12.2015 2.04    Changed Tool-Chain version.
*         :                    Modified #define name from "DTC_CFG_SHORT_ADDRRESS_MODE"
*         :                    to "DTC_CFG_SHORT_ADDRESS_MODE".
*         :                    Added RX130, RX23T and RX24T.
*         : 30.09.2016 2.05    Added RX65N.
*         :                    Supported to the register added in DTCb.
*         :                    Supported sequence transfer.
*         :                    Added R_DTC_CreateSeq() function.
*         :                    Added DTC_CMD_SEQUENCE_TRANSFER_ENABLE, 
*         :                    DTC_CMD_SEQUENCE_TRANSFER_DISABLE and DTC_CMD_SEQUENCE_TRANSFER_ABORT
*         :                    to R_DTC_Control().
*         : 31.01.2017 2.06    Added the default setting of "writeback_disable", "sequence_end",
*         :                    "refer_index_table_enable" and "disp_add_enable" in R_DTC_Create()
*         :                    if the DTC IP version is DTCb or later.
*         : 31.03.2017 2.07    Added RX24U and RX24T-512KB.
*         : 31.07.2017 2.08    Supported RX65N-2MB and RX130-512KB.
*         :                    Fixed to correspond to Renesas coding rule.
*         :                    Added DTC_CMD_CHANGING_DATA_FORCIBLY_SET command to R_DTC_Control().
*         : 28.09.2018 2.10    Supported RX66T.
*         :                    Fixed to correspond to Renesas coding rule.
*         :                    Add WAIT_LOOP comments.
*         : 01.02.2019 2.20    Supported RX72T, RX65N-64pin.
*                              Fixed DTC setting procedure.
*         : 28.06.2019 3.10    Added support for RX23W.
*         : 15.08.2019 3.20    Added support for RX72M.
                               Fixed warnings in IAR.
*         : 25.11.2019 3.30    Added support for RX13T.
*         :                    Modified comment of API function to Doxygen style.
*         :                    Fixed to comply with GSCE Coding Standards Rev.6.00.
*         : 30.12.2019 3.40    Added support for RX66N, RX72N.
*******************************************************************************/

/*******************************************************************************
Includes   <System Includes> , "Project Includes"
*******************************************************************************/
/* Defines for DTC support */
#include <stdlib.h>
#include "r_dtc_rx_if.h"
#include ".\src\r_dtc_rx_private.h"


/*******************************************************************************
Macro definitions
*******************************************************************************/
#define    DTC_PRV_ACT_BIT_MASK            (0x8000) /* DTC Active flag (DTCSTS.ACT) bit mask */
#define    DTC_PRV_VECT_NR_MASK            (0x00FF) /* DTC-Activating Vector Number bits mask */
#define    DTC_PRV_MAX_16BITS_COUNT_VAL    (65536)  /* The maximum value of 16bit count value */
#define    DTC_PRV_MAX_8BITS_COUNT_VAL     (256)    /* The maximum value of 8bit count value */
#define    DTC_PRV_MIN_COUNT_VAL           (1)      /* The minimum of count value  and block size */
#define    DTC_PRV_ESPSEL_BIT_MASK         (0x8000) /* DTC Sequence transfer vector number setting bit mask */

/*******************************************************************************
Typedef definitions
*******************************************************************************/

/*******************************************************************************
Exported global variables (to be accessed by other files)
*******************************************************************************/
extern const dtc_activation_source_t g_source_array[];
uint32_t    * gp_dtc_table_work[2];


/*******************************************************************************
Private variables and functions
*******************************************************************************/
static bool s_is_opened = false; /* Indicate whether DTC is opened. */

static dtc_err_t r_dtc_set_transfer_data(dtc_transfer_data_t *p_transfer_data,
                                         dtc_transfer_data_cfg_t *p_cfg);
static void r_dtc_clear_all_dtce_bits(void);
static bool r_dtc_abort_chain_transfer(uint32_t chain_transfer_nr);
static bool r_dtc_acquire_hw_lock(void);
static void r_dtc_release_hw_lock(void);
static bool r_dtc_check_dmac_locking_sw(void);
static dtc_err_t r_dtc_check_create_param(dtc_transfer_data_t *p_transfer_data, dtc_transfer_data_cfg_t *p_data_cfg);



/***********************************************************************************************************************
* Function Name: R_DTC_Open
********************************************************************************************************************//**
* @brief This function is run first when using the APIs of the DTC FIT module.
* @retval DTC_SUCCESS Successful operation
* @retval DTC_ERR_OPENED DTC has been initialized already.
* @retval DTC_ERR_BUSY Resource has been locked by other process.
* @details Locks*1 the DTC and starts supplying clock to DTC, then initializes DTC vector table, address mode,
* Data Transfer Read Skip. When setting DTC_CFG_DISABLE_ALL_ACT_SOURCE to DTC_ENABLE in r_dtc_rx_config.h, all DTCER
* registers are cleared. When setting DTC_CFG_USE_SEQUENCE_TRANSFER to DTC_ENABLE, the area used in DTC index table is
* secured.\n\n
* Note: 1. The DTC FIT module uses the r_bsp default lock function. As a result, the DTC is in the locked state after a
* successful end.
* @note Set \#define BSP_CFG_HEAP_BYTES in r_bsp_config.h to the value greater than \#define DTC_VECTOR_TABLE_SIZE_BYTES
* in r_dtc_rx_target.h. This is to secure the DTC Vector table area using the malloc() function in the DTC FIT module.
*/
dtc_err_t R_DTC_Open(void)
{
    uint8_t * p_dtc_table_work2 = 0;

    /* Check hw lock require */
    if (false == r_dtc_acquire_hw_lock())
    {
        /* Lock has already been acquired by another task. Need to try again later. */
        return DTC_ERR_BUSY;
    }

    if (true == s_is_opened) /* DTC is opened. */
    {
        r_dtc_release_hw_lock();
        return DTC_ERR_OPENED;
    }

    /* Allocate memory size */
    gp_dtc_table_work[0] = (uint32_t *)malloc(DTC_VECTOR_TABLE_SIZE_BYTES);

    if (0 == gp_dtc_table_work[0])
    {
        r_dtc_release_hw_lock();
        return DTC_ERR_OPENED;
    }

    gp_dtc_table_work[1] = gp_dtc_table_work[0];

    /* Cast type of "gp_dtc_table_work" to match type of "p_dtc_table_work2" */
    p_dtc_table_work2 = (uint8_t *)gp_dtc_table_work[1];
    p_dtc_table_work2 = (p_dtc_table_work2 + 0x400);

    /* Cast type of "p_dtc_table_work2" to match type of "p_dtc_table_work2" */
    p_dtc_table_work2 = (uint8_t *)((uint32_t)p_dtc_table_work2 & 0xfffffc00);

#if (DTC_ENABLE == DTC_CFG_DISABLE_ALL_ACT_SOURCE) /* Clear all DTCER registers. */

    r_dtc_clear_all_dtce_bits();

#endif /* DTC_ENABLE == DTC_CFG_DISABLE_ALL_ACT_SOURCE */

    /* Cancel module stop for DMAC and DTC. */
    r_dtc_module_enable();

    /* Set DTC Vector Table Base Register. */
    DTC.DTCVBR = p_dtc_table_work2;

#if (DTC_ENABLE == DTC_CFG_USE_SEQUENCE_TRANSFER)
    p_dtc_table_work2 = (p_dtc_table_work2 + 0x400);

    /* Set address of the dtc index table. */
    DTC.DTCIBR = p_dtc_table_work2;
#endif /* (DTC_ENABLE == DTC_CFG_USE_SEQUENCE_TRANSFER) */

    /* Set DTC address mode. */
#if (DTC_ENABLE == DTC_CFG_SHORT_ADDRESS_MODE)
    /*Turn on Short Address Mode*/
    DTC.DTCADMOD.BIT.SHORT = 1;
#else /* Full-address mode */
    DTC.DTCADMOD.BIT.SHORT = 0;
#endif /* DTC_CFG_SHORT_ADDRESS_MODE */

    /* Set the Transfer Data Read Skip bit. */
#if (DTC_ENABLE == DTC_CFG_TRANSFER_DATA_READ_SKIP_EN) /* Enable Data Read Skip. */
    DTC.DTCCR.BIT.RRS = 1;
#else /* Disable Data Read Skip. */
    DTC.DTCCR.BIT.RRS = 0;
#endif /* DTC_TRANSFER_DATA_READ_SKIP_EN */
    s_is_opened = true; /* DTC module is initialized successfully. */

    return DTC_SUCCESS;
}
/* End of function R_DTC_Open */

/***********************************************************************************************************************
* Function Name: R_DTC_Create
********************************************************************************************************************//**
* @brief This function is used to make DTC register settings and to specify the activation source.
* @param[in] act_source Activation source.
* @param[in] p_transfer_data Pointer to start address of Transfer data area on RAM.
* @param[in] p_data_cfg Pointer to settings for Transfer data. In the case of DTCb, the setting to the following
* structure members is invalid. This function sets the following values.\n
* p_data_cfg->writeback_disable = DTC_WRITEBACK_ENABLE;\n
* p_data_cfg->sequence_end = DTC_SEQUENCE_TRANSFER_CONTINUE;\n
* p_data_cfg->refer_index_table_enable = DTC_REFER_INDEX_TABLE_DISABLE;\n
* p_data_cfg->disp_add_enable = DTC_SRC_ADDR_DISP_ADD_DISABLE;\n
* @param[in] chain_transfer_nr Number of chain transfer.\n
* The number of Transfer data and corresponding configurations is (number of chain transfer + 1).
* Example: if chain_transfer_nr = 1, it means that there are 2 continuous Transfer data and 2 corresponding configurations
* and the first configuration enable the chain transfer.\n
* See Section 3 in application note for details.
* @retval DTC_SUCCESS Successful operation
* @retval DTC_ERR_NOT_OPEN DTC is not initialized yet.
* @retval DTC_ERR_INVALID_ARG Parameters are invalid.
* @retval DTC_ERR_NULL_PTR Argument pointers are NULL.
* @details Writes the configuration to Transfer data. Writes the start address of Transfer data corresponding to interrupt
* number into DTC vector table.
* @note Before calling R_DTC_Create(), user must disable the current interrupt request (the interrupt source is passed to
* R_DTC_Create()) by clearing Interrupt Request Enable bit IERm.IENj:\n\n
* ICU.IER[m].BIT.IENj = 0;\n\n
* Then, enable the interrupt request disabled after R_DTC_Create() is ended. The correspondence between IERm.IENj bit and
* interrupt source is described in Interrupt Vector Table, chapter Interrupt Controller (ICU) of User's Manual: Hardware.
*/
dtc_err_t R_DTC_Create(dtc_activation_source_t act_source, dtc_transfer_data_t *p_transfer_data,
                       dtc_transfer_data_cfg_t *p_data_cfg, uint32_t chain_transfer_nr)
{
    uint32_t  count                             = chain_transfer_nr + 1;
    uint32_t *p_ptr                             = NULL;
    uint8_t   dtce_backup                       = 0;
    uint8_t   rrs_backup                        = 0;
    dtc_err_t ret                               = DTC_SUCCESS;
    dtc_transfer_data_t *p_transfer_data_backup = NULL;

    ret = r_dtc_check_create_param(p_transfer_data, p_data_cfg);
    if (DTC_SUCCESS != ret)
    {
        return ret;
    }

    if (false == s_is_opened) /* DTC is not initialized yet. */
    {
        r_dtc_release_hw_lock();
        return DTC_ERR_NOT_OPEN;
    }

    /* Store start address of p_args->p_transfer_data. */
    p_transfer_data_backup = p_transfer_data;

    /* Store old value of DTCERn.DTCE bit. */
    dtce_backup = ICU.DTCER[act_source].BIT.DTCE;

    /* Disable the interrupt source. Clear the DTCER */
    ICU.DTCER[act_source].BIT.DTCE = 0;

    /* Store old value of DTCCR.RRS bit. */
    rrs_backup = DTC.DTCCR.BIT.RRS;

    /* Clear RRS bit. */
    DTC.DTCCR.BIT.RRS = 0;

    /* Apply configurations */
    /* WAIT_LOOP */
    while (count > 0)
    {

#if (DTC_IP_VER_DTCb <= DTC_IP)
        /* Set the 0 value. */
        p_data_cfg->writeback_disable        = DTC_WRITEBACK_ENABLE;
        p_data_cfg->sequence_end             = DTC_SEQUENCE_TRANSFER_CONTINUE;
        p_data_cfg->refer_index_table_enable = DTC_REFER_INDEX_TABLE_DISABLE;
        p_data_cfg->disp_add_enable          = DTC_SRC_ADDR_DISP_ADD_DISABLE;
#endif /* (DTC_IP_VER_DTCb <= DTC_IP) */

        if (r_dtc_set_transfer_data(p_transfer_data, p_data_cfg) != DTC_SUCCESS)
        {
            /* Fail to apply configurations for Transfer data. */
            /* Restore RRS bit */
            DTC.DTCCR.BIT.RRS = rrs_backup;

            /* Restore the DTCE bit. */
            ICU.DTCER[act_source].BIT.DTCE = dtce_backup;
            return DTC_ERR_INVALID_ARG;
        }
        else
        {
            p_data_cfg++;
            p_transfer_data++;
        }
        count--;
    }

    /* The row in Vector table corresponding to act_source */
    p_ptr = (uint32_t *)((uint32_t)DTC.DTCVBR + (4 * act_source));

    /* Write start address of Transfer data to Vector table. */
    *p_ptr = (uint32_t)p_transfer_data_backup;

    /* Restore RRS bit. */
    DTC.DTCCR.BIT.RRS = rrs_backup;

    /* Restore the DTCE bit. */
    ICU.DTCER[act_source].BIT.DTCE = dtce_backup;

    return DTC_SUCCESS;
}
/* End of function R_DTC_Create */

/***********************************************************************************************************************
* Function Name: R_DTC_CreateSeq
********************************************************************************************************************//**
* @brief This function performs the setting of the DTC register used in the sequence transfer and the activation source.
* @param[in] act_source Activation source
* @param[in] p_transfer_data Pointer to the start address in the transfer information area in RAM.
* @param[in] p_data_cfg Pointer to the transfer information setting\n
* Set the following structure members.\n
* p_data_cfg->writeback_disable\n
* p_data_cfg->sequence_end\n
* p_data_cfg->refer_index_table_enable\n
* p_data_cfg->disp_add_enable\n
* @param[in] sequence_transfer_nr Transfer information counts per sequence transfer (0 - 4294967295)\n
* See Section 3 in application note for details.\n\n
* @param[in] sequence_no Sequence number (0 - 255)\n
* The type definition of the transfer information and the data structure are the same as R_DTC_Create(). Total of 256 ways
* of the sequence information can be set.
* @retval DTC_SUCCESS Successful operation
* @retval DTC_ERR_NOT_OPEN DTC is not initialized yet.
* @retval DTC_ERR_INVALID_ARG Arguments are invalid.
* @retval DTC_ERR_NULL_PTR Argument pointers are NULL.
* @details This function writes the setting information to the transfer information. Start address of the transfer
* information for the sequence number is written to DTC index table.
* @note Before calling R_DTC_CreateSeq(), user must disable the current interrupt request (the interrupt source is passed
* to R_DTC_CreateSeq()) by clearing Interrupt Request Enable bit (IERm.IENj):\n\n
* ICU.IER[m].BIT.IENj = 0;\n\n
* Then, enable the interrupt request disabled after R_DTC_CreateSeq() is ended. The correspondence between IERm.IENj bit
* and interrupt source is described in Interrupt Vector Table, chapter Interrupt Controller (ICU) of User's Manual:
* Hardware.
*/
dtc_err_t R_DTC_CreateSeq(dtc_activation_source_t act_source, dtc_transfer_data_t *p_transfer_data,
                          dtc_transfer_data_cfg_t *p_data_cfg, uint32_t sequence_transfer_nr,
                          uint8_t sequence_no)
{
#if (DTC_DISABLE == DTC_CFG_USE_SEQUENCE_TRANSFER)
    return DTC_ERR_INVALID_ARG;
#else
    uint32_t  count                             = sequence_transfer_nr;
    uint32_t *p_ptr                             = NULL;
    uint8_t   dtce_backup                       = 0;
    uint8_t   rrs_backup                        = 0;
    dtc_err_t ret                               = DTC_SUCCESS;
    dtc_transfer_data_t *p_transfer_data_backup = NULL;

    if (0 != count)
    {
        ret = r_dtc_check_create_param(p_transfer_data, p_data_cfg);
        if (DTC_SUCCESS != ret)
        {
            return ret;
        }
    }

    if (false == s_is_opened) /* DTC is not initialized yet. */
    {
        r_dtc_release_hw_lock();
        return DTC_ERR_NOT_OPEN;
    }

    /* Store start address of p_args->p_transfer_data. */
    p_transfer_data_backup = p_transfer_data;

    /* Store old value of DTCERn.DTCE bit. */
    dtce_backup = ICU.DTCER[act_source].BIT.DTCE;

    /* Disable the interrupt source. Clear the DTCER */
    ICU.DTCER[act_source].BIT.DTCE = 0;

    /* Store old value of DTCCR.RRS bit. */
    rrs_backup = DTC.DTCCR.BIT.RRS;

    /* Clear RRS bit. */
    DTC.DTCCR.BIT.RRS = 0;

    /* The row in dtc index table corresponding to sequence_no. */
    p_ptr = (uint32_t *)((uint32_t)DTC.DTCIBR + (4 * sequence_no));

    if (0 == count)
    {
        /* Set the cpu interrupt to the sequence number. */
        *p_ptr = DTC_INVALID_CMND;
    }
    else
    {
        /* Apply configurations */
        /* WAIT_LOOP */
        while (count > 0)
        {
            /* Fail to apply configurations for Transfer data. */
            if (r_dtc_set_transfer_data(p_transfer_data, p_data_cfg) != DTC_SUCCESS)
            {
                /* Restore RRS bit */
                DTC.DTCCR.BIT.RRS = rrs_backup;

                /* Restore the DTCE bit. */
                ICU.DTCER[act_source].BIT.DTCE = dtce_backup;
                return DTC_ERR_INVALID_ARG;
            }
            else
            {
                p_data_cfg++;
                p_transfer_data++;
            }
            count--;
        }

        /* Write start address of Transfer data to dtc index table. */
        *p_ptr = (uint32_t)p_transfer_data_backup;
    }

    /* Restore RRS bit. */
    DTC.DTCCR.BIT.RRS = rrs_backup;

    /* Restore the DTCE bit. */
    ICU.DTCER[act_source].BIT.DTCE = dtce_backup;

    return DTC_SUCCESS;
#endif /* (DTC_DISABLE == DTC_CFG_USE_SEQUENCE_TRANSFER) */
}
/* End of function R_DTC_CreateSeq */

/***********************************************************************************************************************
* Function Name: R_DTC_Close
********************************************************************************************************************//**
* @brief This function is used to release the resources of the DTC.
* @retval DTC_SUCCESS Successful operation
* @retval DTC_SUCCESS_DMAC_BUSY Successful operation.One or some DMAC resources are locked.
* @details Unlocks*1 the DTC and disable all DTC activation source by clearing the DTC Activation Enable Register DTCERn;
* stop supplying clock to DTC and put it to Module stop state. If in addition all DMAC channels have been unlocked, the
* function sets the DMAC and DTC to the module stop state.*2\n\n
* Note:\n 1. The DTC FIT module uses the r_bsp default lock function. As a result, the DTC is in the unlocked state after
* a successful end.\n 2. Because a shared bit is used as both the DMAC module stop setting bit and the DTC module stop
* setting bit, the function confirms that all DMAC channels are unlocked before making the module stop setting. (For
* details, see the "Low Power Consumption" section in the User's Manual: Hardware.)\n
* See Section 3 in application note for details.
* @note When controlling the DMAC without using the DMAC FIT module, make sure to monitor the usage of the DMAC and
* control locking and unlocking of the DMAC so that calling this function does not set the DMAC to the module stop state.
* Note that even if the DMAC has not been activated, it is necessary to keep it in the locked state when not making DMAC
* transfer settings.
*/
dtc_err_t R_DTC_Close(void)
{
    /* Clear DTCE bits. */
    r_dtc_clear_all_dtce_bits();

    /* Stop DTC module. */
    DTC.DTCST.BIT.DTCST = 0;

    /* DTC is closed. */
    s_is_opened = false;

    /* Cast type of "gp_dtc_table_work" to match type of parameter in "free" function */
    free((void *)gp_dtc_table_work[1]);
    gp_dtc_table_work[1] = NULL;

    /* Check DMAC locking. */
    if (true == r_dtc_check_dmac_locking_sw())
    {
        /* Disable the power for DTC and DMAC module. */
        r_dtc_module_disable();

        /* Release hardware lock. */
        r_dtc_release_hw_lock();
    }
    else
    {
        /* Release hardware lock. */
        r_dtc_release_hw_lock();
        return DTC_SUCCESS_DMAC_BUSY;
    }

    return DTC_SUCCESS;
}
/* End of function R_DTC_Close */

/***********************************************************************************************************************
* Function Name: R_DTC_Control
********************************************************************************************************************//**
* @brief This function controls the operation of the DTC.
* @param[in] command DTC control command
* @param[in] p_stat Pointer to the status when command is DTC_CMD_STATUS_GET.\n
* See Section 3 in application note for details.
* @param[in] p_args Pointer to the argument structure when command is DTC_CMD_ACT_SRC_ENABLE,DTC_CMD_ACT_SRC_DISABLE,
* DTC_CMD_CHAIN_TRANSFER_ABORT, DTC_CMD_SEQUENCE_TRANSFER_ENABLE, or DTC_CMD_CHANGING_DATA_FORCIBLY_SET.\n
* See Section 3 in application note for details.
* @retval [DTC_SUCCESS] Successful operation
* @retval [DTC_ERR_NOT_OPEN] DTC is not initialized yet.
* @retval [DTC_ERR_INVALID_COMMAND] Command parameters are invalid or DTC_CMD_CHANGING_DATA_FORCIBLY_SET command error.
* @retval [DTC_ERR_NULL_PTR] Argument pointers are NULL.
* @retval [DTC_ERR_ACT] Data transfer is in progress.
* @details Processing is performed depending on the command.\n
* See Section 3 in application note for details.
* @note When the command is DTC_CMD_GET_STATUS, the vector number is valid if only the DTC is in the progress
* (p_stat->in_progress is true). With command DTC_CMD_ENABLE_ACT_SRC, DTC_CMD_DISABLE_ACT_SRC or
* DTC_CMD_SEQUENCE_TRANSFER_ABORT, before calling R_DTC_Control(), user must disable the current interrupt request
* (the interrupt source is passed to R_DTC_Control()) by clearing Interrupt Request Enable bit (IERm.IENj);\n\n
* ICU.IER[m].BIT.IENj = 0;\n\n
* After processing of R_DTC_Control() is ended, the interrupt request disabled is enabled. The correspondence between
* IERm.IENj bit and interrupt source is described in Interrupt Vector Table, chapter Interrupt Controller (ICU) of
* User's Manual: Hardware. With abort processing, user must re-create the Chain transfer data after the transfer is
* aborted because the old Transfer data are destroyed. If an invalid value is attempted to set with
* DTC_CMD_CHANGING_DATA_FORCIBLY_SET, R_DTC_Control() returns DTC_ERR_INVALID_COMMAND R_DTC_Control() may already update
* some registers before the invalid value is detected. This occurs only when users try
* to change FORCIBLY DTC with Invalid Value.
*/
dtc_err_t R_DTC_Control(dtc_command_t command, dtc_stat_t *p_stat, dtc_cmd_arg_t *p_args)
{
    uint32_t             count                   = 0;
    uint32_t            *p_ptr                   = NULL;
    uint8_t              dtce_backup             = 0;
    uint8_t              rrs_backup              = 0;
    dtc_transfer_data_t  *p_transfer_data_backup = NULL;

#if (1 == DTC_CFG_PARAM_CHECKING_ENABLE)

    if ((DTC_CMD_STATUS_GET == command) && (NULL == p_stat))
    {
        return DTC_ERR_NULL_PTR;
    }
    else if ((((DTC_CMD_ACT_SRC_ENABLE == command) || (DTC_CMD_ACT_SRC_DISABLE == command)) ||
             (DTC_CMD_CHAIN_TRANSFER_ABORT == command)) || (DTC_CMD_SEQUENCE_TRANSFER_ENABLE == command))
    {
        if (NULL == p_args) /* Require argument */
        {
            return DTC_ERR_NULL_PTR;
        }
    }
    else if (DTC_CMD_CHANGING_DATA_FORCIBLY_SET == command)
    {
        if (NULL == p_args) /* Require argument */
        {
            return DTC_ERR_INVALID_COMMAND;
        }
        if (r_dtc_check_create_param(p_args->p_transfer_data, p_args->p_data_cfg) != DTC_SUCCESS)
        {
            return DTC_ERR_INVALID_COMMAND;
        }
    }
    else
    {
        /* do nothing */
    }

#endif /* DTC_CFG_PARAM_CHECKING_ENABLE */

    if (false == s_is_opened)
    {
        r_dtc_release_hw_lock();
        return DTC_ERR_NOT_OPEN;
    }

    switch (command)
    {
        case DTC_CMD_DTC_START: /* Start DTC module. */
        {
            /* DTC Module start*/
            DTC.DTCST.BIT.DTCST = 1;
            break;
        }

        case DTC_CMD_DTC_STOP: /* Stop DTC module. */
        {
            /* DTC Module stop*/
            DTC.DTCST.BIT.DTCST = 0;
            break;
        }

        case DTC_CMD_DATA_READ_SKIP_ENABLE: /* Enable Transfer Data Read Skip. */
        {
            /* Set Read Skip Enable bit*/
            DTC.DTCCR.BIT.RRS = 1;
            break;
        }

        case DTC_CMD_DATA_READ_SKIP_DISABLE: /* Disable Transfer Data Read Skip. */
        {
            /* Clear Read Skip Enable bit*/
            DTC.DTCCR.BIT.RRS = 0;
            break;
        }

        case DTC_CMD_ACT_SRC_ENABLE: /* Select one interrupt as a DTC activation source. */
        {
            /* Set Activation source for DTC*/
            ICU.DTCER[p_args->act_src].BIT.DTCE = 1;
            break;
        }

        case DTC_CMD_ACT_SRC_DISABLE: /* Remove one interrupt as a DTC activation source. */
        {
            /* Clear Activation source*/
            ICU.DTCER[p_args->act_src].BIT.DTCE = 0;
            break;
        }

        case DTC_CMD_STATUS_GET:
        {
            /* Check DTC Status*/
            if (0 == (DTC.DTCSTS.WORD & DTC_PRV_ACT_BIT_MASK)) /* DTC transfer operation is not in progress. */
            {
                p_stat->in_progress = false;

                /* DTC is not in progress. -> vector number is invalid. */
            }
            else /* DTC transfer operation is in progress. */
            {
                p_stat->in_progress = true;

                /* Get the current vector number. */
                p_stat->vect_nr = (uint8_t)(DTC.DTCSTS.WORD & DTC_PRV_VECT_NR_MASK); /* get lower 8 bits: 0-7*/
            }
            break;
        }

        case DTC_CMD_CHAIN_TRANSFER_ABORT:
        {
            r_dtc_abort_chain_transfer(p_args->chain_transfer_nr);
            break;
        }

#if (DTC_IP_VER_DTCb <= DTC_IP)

        case DTC_CMD_SEQUENCE_TRANSFER_ENABLE:

            /* Set the sequence transfer vector number and sequence transfer is enabled. */
            DTC.DTCSQE.WORD = (DTC_PRV_ESPSEL_BIT_MASK | (uint16_t)p_args->act_src);
            break;

        case DTC_CMD_SEQUENCE_TRANSFER_DISABLE:

            /* Sequence transfer is disabled. */
            DTC.DTCSQE.WORD &= (~DTC_PRV_ESPSEL_BIT_MASK);
            break;

        case DTC_CMD_SEQUENCE_TRANSFER_ABORT:

            /* DTC transfer operation is in progress. */
            if (DTC.DTCSTS.WORD & DTC_PRV_ACT_BIT_MASK)
            {
                /* Store value of VECN of DTCSQE Register to "tmp" variable */
                uint16_t tmp = DTC.DTCSQE.BIT.VECN;

                /* Compare value of VECN of DTCSTS Register with "tmp" variable */
                if (DTC.DTCSTS.BIT.VECN == tmp)
                {
                    return DTC_ERR_ACT;
                }
            }

            /* Abort the sequence transfer. */
            DTC.DTCOR.BIT.SQTFRL = 1;
            break;

#endif /* (DTC_IP_VER_DTCb <= DTC_IP) */

        case DTC_CMD_CHANGING_DATA_FORCIBLY_SET:
        {
            /* Store start address of p_args->p_transfer_data. */
            p_transfer_data_backup = p_args->p_transfer_data;

            /* Store old value of DTCERn.DTCE bit. */
            dtce_backup = ICU.DTCER[p_args->act_src].BIT.DTCE;

            /* Disable the interrupt source. Clear the DTCER */
            ICU.DTCER[p_args->act_src].BIT.DTCE = 0;

            /* Store old value of DTCCR.RRS bit. */
            rrs_backup = DTC.DTCCR.BIT.RRS;

            /* Clear RRS bit. */
            DTC.DTCCR.BIT.RRS = 0;

            count = p_args->chain_transfer_nr + 1;

            /* Apply configurations */
            /* WAIT_LOOP */
            while (count > 0)
            {
                if (r_dtc_set_transfer_data(p_args->p_transfer_data, p_args->p_data_cfg) != DTC_SUCCESS)
                {
                    /* Fail to apply configurations for Transfer data. */
                    /* Restore RRS bit */
                    DTC.DTCCR.BIT.RRS = rrs_backup;

                    /* Restore the DTCE bit. */
                    ICU.DTCER[p_args->act_src].BIT.DTCE = dtce_backup;
                    return DTC_ERR_INVALID_COMMAND;
                }
                else
                {
                    p_args->p_transfer_data++;
                    p_args->p_data_cfg++;
                }
                count--;
            }

            /* The row in Vector table corresponding to act_source */
            p_ptr = (uint32_t *)((uint32_t)DTC.DTCVBR + (4 * p_args->act_src));

            /* Write start address of Transfer data to Vector table. */
            *p_ptr = (uint32_t)p_transfer_data_backup;

            /* Restore RRS bit */
            DTC.DTCCR.BIT.RRS = rrs_backup;

            /* Restore the DTCE bit. */
            ICU.DTCER[p_args->act_src].BIT.DTCE = dtce_backup;
            break;
        }
        default:
        {
            return DTC_ERR_INVALID_COMMAND;
            break;
        }
    }

    return DTC_SUCCESS;
}
/* End of function R_DTC_Control */

/*******************************************************************************
* Function Name: R_DTC_GetVersion
****************************************************************************//**
* @brief This function is used to get the driver version information.
* @return Version_number Upper 2 bytes: major version, lower 2 bytes: minor version
* @details Returns the version information.
* @note None
*/
uint32_t R_DTC_GetVersion(void)
{
    uint32_t version = 0;

    version = (DTC_VERSION_MAJOR << 16) | DTC_VERSION_MINOR;

    return version;
}
/* End of function R_DTC_GetVersion */

/*******************************************************************************
* Function Name: r_dtc_set_transfer_data
* Description  : Applies configurations to a Transfer data area, it is an internal
*                function called by R_DTC_Create(); and all arguments are validated
*                in R_DTC_Create()
* Arguments    : transfer_data -
*                    Start address of Transfer data
*                data_cfg -
*                    Contains configurations for the Transfer data
* Return Value : DTC_SUCCESS -
*                    Apply configurations for Transfer data successfully.
*                DTC_ERR_INVALID_ARG
*                    Fail to apply configurations for Transfer data.
*******************************************************************************/
static dtc_err_t r_dtc_set_transfer_data(dtc_transfer_data_t *p_transfer_data,
                                   dtc_transfer_data_cfg_t *p_cfg)
{
    dtc_mra_t                          t_mra;
    dtc_mrb_t                          t_mrb;
    dtc_cra_t                          t_cra;
    dtc_crb_t                          t_crb;

    /* Cast type of "p_transfer_data" to match type of "p_td_ptr" */
    volatile dtc_internal_registers_t *p_td_ptr = (volatile dtc_internal_registers_t *)p_transfer_data;

    /* Set for MRA - . */
#if (DTC_IP_VER_DTCb <= DTC_IP)
#if (DTC_ENABLE != DTC_CFG_SHORT_ADDRESS_MODE) /* Full-address mode */
    dtc_mrc_t                          t_mrc;

    /* Casting to match type of "t_mrc.BYTE" */
    t_mrc.BYTE = (uint8_t)(p_cfg->disp_add_enable);
#endif /* (DTC_ENABLE == DTC_CFG_SHORT_ADDRESS_MODE) */
    /* Casting to match type of "t_mra.BYTE" */
    t_mra.BYTE = ((((uint8_t)p_cfg->writeback_disable | (uint8_t)p_cfg->src_addr_mode) | (uint8_t)p_cfg->data_size) | (uint8_t)p_cfg->transfer_mode);

    /* Casting to match type of "t_mrb.BYTE" */
    t_mrb.BYTE = (((((((uint8_t)p_cfg->sequence_end |(uint8_t)p_cfg->refer_index_table_enable) | (uint8_t)p_cfg->dest_addr_mode) |
                           (uint8_t)p_cfg->repeat_block_side) | (uint8_t)p_cfg->response_interrupt) |
                           (uint8_t)p_cfg->chain_transfer_enable) | (uint8_t)p_cfg->chain_transfer_mode);
#else
    /* Casting to match type of "t_mra.BYTE" */
    t_mra.BYTE = (uint8_t)(p_cfg->src_addr_mode | p_cfg->data_size | p_cfg->transfer_mode);

    /* Casting to match type of "t_mrb.BYTE" */
    t_mrb.BYTE = (uint8_t)(p_cfg->dest_addr_mode | p_cfg->repeat_block_side | p_cfg->response_interrupt |
                           p_cfg->chain_transfer_enable | p_cfg->chain_transfer_mode);
#endif /* (DTC_IP_VER_DTCb <= DTC_IP) */

    switch (t_mra.BIT.MD) /* DTC transfer mode */
    {
        case 0x0: /* Normal mode */
        {
            if (DTC_PRV_MAX_16BITS_COUNT_VAL == p_cfg->transfer_count)/* Transfer count = 65536 */
            {
                t_cra.WORD = 0x0000;
            }
            else /* 1 - 65535 */
            {
                /* Cast type of "p_cfg->transfer_count" to uint16_t to match type of "t_cra.WORD" */
                t_cra.WORD = (uint16_t)p_cfg->transfer_count;
            }
            break;
        }

        case 0x1: /* Repeat mode */
        {
            /* Set counter. */
            if (p_cfg->transfer_count < DTC_PRV_MAX_8BITS_COUNT_VAL) /* count 1-255 */
            {
                /* Cast type of "p_cfg->transfer_count" to match type of "t_cra.BYTE.CRA_H" */
                t_cra.BYTE.CRA_H = (uint8_t)p_cfg->transfer_count;

                /* Cast type of "p_cfg->transfer_count" to match type of "t_cra.BYTE.CRA_L" */
                t_cra.BYTE.CRA_L = (uint8_t)p_cfg->transfer_count;
            }
            else if (DTC_PRV_MAX_8BITS_COUNT_VAL == p_cfg->transfer_count)
            {
                t_cra.BYTE.CRA_H = 0x00;
                t_cra.BYTE.CRA_L = 0x00;
            }
            else /* Transfer count > 256 */
            {
                return DTC_ERR_INVALID_ARG;
            }
            break;
        }

        case 0x2: /* DTC_TRANSFER_MODE_BLOCK - Block transfer mode */
        {
            /* Set counter. */
            if (DTC_PRV_MAX_16BITS_COUNT_VAL == p_cfg->transfer_count)/* Transfer count = 65536 */
            {
                t_crb.WORD = 0x0000;
            }
            else /* 1 - 65535 */
            {
                /* Cast type of "p_cfg->transfer_count" to uint16_t to match type of "t_cra.WORD" */
                t_crb.WORD = (uint16_t)p_cfg->transfer_count;
            }

            if (p_cfg->block_size < DTC_PRV_MAX_8BITS_COUNT_VAL) /* Block size 1-255 */
            {
                /* Cast type of "p_cfg->block_size" to match type of "t_cra.BYTE.CRA_H" */
                t_cra.BYTE.CRA_H = (uint8_t)p_cfg->block_size;

                /* Cast type of "p_cfg->block_size" to match type of "t_cra.BYTE.CRA_L" */
                t_cra.BYTE.CRA_L = (uint8_t)p_cfg->block_size;
            }
            else if (DTC_PRV_MAX_8BITS_COUNT_VAL == p_cfg->block_size) /* Block size = 256 */
            {
                t_cra.BYTE.CRA_H = 0;
                t_cra.BYTE.CRA_L = 0;
            }
            else /* Invalid block size */
            {
                return DTC_ERR_INVALID_ARG;
            }
            break;
        }

        default:
        {
            return DTC_ERR_INVALID_ARG;
            break;
        }
    }

#if (DTC_ENABLE == DTC_CFG_SHORT_ADDRESS_MODE) /* Short-address mode */
    /* settings for fist long word: MRA & SAR */
    p_td_ptr->FIRST_LWORD.LWORD   =  0; /* clear */
    p_td_ptr->FIRST_LWORD.REG.MRA =  t_mra; /* 1 byte MRA */
    p_td_ptr->FIRST_LWORD.LWORD   |= (p_cfg->source_addr & 0x00FFFFFF); /* 3 byte SAR */

    /* settings for second long word: MRB & DAR */
    p_td_ptr->SECOND_LWORD.LWORD   =  0; /* clear */
    p_td_ptr->SECOND_LWORD.REG.MRB =  t_mrb; /* 1 byte MRB */
    p_td_ptr->SECOND_LWORD.LWORD   |= (p_cfg->dest_addr & 0x00FFFFFF); /* 3 byte DAR */

    /* settings for third long word: CRA & CRB */
    p_td_ptr->THIRD_LWORD.REG.CRA.WORD = t_cra.WORD;
    p_td_ptr->THIRD_LWORD.REG.CRB.WORD = t_crb.WORD;

#else /* Full-address mode */
    /* settings for fist long word: MRA & MRB */
    p_td_ptr->FIRST_LWORD.REG.MRA.BYTE = t_mra.BYTE; /* 1 byte MRA */
    p_td_ptr->FIRST_LWORD.REG.MRB.BYTE = t_mrb.BYTE; /* 1 byte MRB */
#if (DTC_IP_VER_DTCb <= DTC_IP)
    p_td_ptr->FIRST_LWORD.REG.MRC.BYTE = t_mrc.BYTE; /* 1 byte MRC */
#endif /* (DTC_IP_VER_DTCb <= DTC_IP) */

    /* settings for second long word: SAR */
    p_td_ptr->SECOND_LWORD.SAR = p_cfg->source_addr; /* 4 byte SAR */

    /* settings for third long word: DAR */
    p_td_ptr->THIRD_LWORD.DAR = p_cfg->dest_addr; /* 4 byte DAR */

    /* settings for fourth long word: CRA & CRB */
    p_td_ptr->FOURTH_LWORD.REG.CRA.WORD = t_cra.WORD;
    p_td_ptr->FOURTH_LWORD.REG.CRB.WORD = t_crb.WORD;
#endif /* (DTC_ENABLE == DTC_CFG_SHORT_ADDRESS_MODE) */
    return DTC_SUCCESS;
}
/* End of function r_dtc_set_transfer_data */

/*******************************************************************************
* Function Name: r_dtc_clear_all_dtce_bits
* Description  : Clears all DTCERn.DTCE bit corresponding to the interrupt that
*                can be selected as DTC activation sources.
* Arguments    : addr -
*                  Address need to be validated
* Return Value : true -
*                  The address is valid.
*                false -
*                  The address is invalid.
*******************************************************************************/
static void r_dtc_clear_all_dtce_bits(void)
{
    volatile uint32_t dtce_cnt = 0;

    /* Clear all DTCER registers.
     * Scan through all available DTCER registers in Array.
     */
    /* WAIT_LOOP */
    while (dtce_cnt < DTC_NUM_INTERRUPT_SRC)
    {
        /* Clear Activation source*/
        ICU.DTCER[g_source_array[dtce_cnt]].BIT.DTCE = 0;
        dtce_cnt++;
    }

    return;
}
/* End of function r_dtc_clear_all_dtce_bits */

/*******************************************************************************
* Function Name: r_dtc_abort_chain_transfer
* Description  : Aborts the current active chain transfer.
* Arguments    : chain_transfer_nr -
*                   Number of chain transfer
* Return Value : true -
*                   Abort successfully.
*                false
*                   Can not abort.
*******************************************************************************/
static bool r_dtc_abort_chain_transfer(uint32_t chain_transfer_nr)
{
    volatile uint32_t cnt = 0;
    uint16_t          status_reg = 0;

    /* Set status register*/
    status_reg = DTC.DTCSTS.WORD;

    volatile dtc_internal_registers_t *p_td_ptr = NULL;

    if (0 == (status_reg & 0x8000)) /* DTC is not active. */
    {
        return false;
    }

    status_reg &= 0xFF; /* Get the vector number. */
    p_td_ptr = (((volatile dtc_internal_registers_t *)*((uint32_t *)DTC.DTCVBR + status_reg)) + chain_transfer_nr) - 1;

    /* Clear all CHNE bit */
    /* WAIT_LOOP */
    while (cnt < chain_transfer_nr)
    {
#if (DTC_DISABLE == DTC_CFG_SHORT_ADDRESS_MODE) /* Full address mode */
        p_td_ptr->FIRST_LWORD.REG.MRB.BIT.CHNE = 0;
#else /* Short address mode */
        p_td_ptr->SECOND_LWORD.REG.MRB.BIT.CHNE = 0;
#endif
        p_td_ptr--;
        cnt++;
    }

    return true;
}
/* End of function r_dtc_abort_chain_transfer */

/*******************************************************************************
* Function Name: r_dtc_acquire_hw_lock
* Description  : Gets the hardware lock BSP_LOCK_DTC.
* Arguments    : None.
* Return Value : true -
*                  The lock is acquired successfully
*                false -
*                  Fails to get the lock
*******************************************************************************/
static bool r_dtc_acquire_hw_lock(void)
{
    return R_BSP_HardwareLock(BSP_LOCK_DTC);
}
/* End of function r_dtc_acquire_hw_lock */

/*******************************************************************************
* Function Name: r_dtc_release_hw_lock
* Description  : release hardware lock BSP_LOCK_DTC.
* Arguments    : None.
* Return Value : None.
*******************************************************************************/
static void r_dtc_release_hw_lock(void)
{
    R_BSP_HardwareUnlock(BSP_LOCK_DTC);
    return;
}
/* End of function r_dtc_release_hw_lock */


/*******************************************************************************
* Function Name: r_dtc_check_dmac_locking_sw
* Description  : Checks all DMAC channel locking.
* Arguments    : none -
* Return Value : true -
*                    All DMAC channels are unlocked. 
*                false -
*                    One or some DMAC channels are locked.
*******************************************************************************/
static bool r_dtc_check_dmac_locking_sw(void)
{
    bool ret = true;

#if ((0 != BSP_CFG_USER_LOCKING_ENABLED) || (bsp_lock_t != BSP_CFG_USER_LOCKING_TYPE) \
      || (DTC_ENABLE != DTC_CFG_USE_DMAC_FIT_MODULE))
        /* defined(0 != BSP_CFG_USER_LOCKING_ENABLED) */
        /*  or defined(DTC_ENABLE !=DTC_CFG_USE_DMAC_FIT_MODULE) */
        /*  or defined(bsp_lock_t != BSP_CFG_USER_LOCKING_TYPE) */
        /* User has to do the locking check of DMAC by themselves. */
        ret = r_dtc_check_DMAC_locking_byUSER();
#else
    uint32_t channel;
    uint32_t dmac_lock_num = 0;

    /* Check locking status of all DMAC channels */
    /* WAIT_LOOP */
    for (channel = 0; channel < DMAC_NUM_CHANNELS; channel++)
    {
        /* Checks if DMAC channel is not locking */
        if (false == R_BSP_HardwareLock((mcu_lock_t)(BSP_LOCK_DMAC0 + channel)))
        {
            dmac_lock_num++;
        }
        else
        {
            /* Unlock DMAC channel */
            R_BSP_HardwareUnlock((mcu_lock_t)(BSP_LOCK_DMAC0 + channel));
        }
    }

    if (0 == dmac_lock_num)
    {
        ret = true;
    }
    else
    {
        ret = false;
    }
#endif

    return ret;
}
/* End of function r_dtc_check_dmac_locking_sw */

/*******************************************************************************
* Function Name: r_dtc_check_create_param
* Description  : Checks creating function parameter.
* Arguments    : none -
* Return Value : DTC_SUCCESS -
*                    Successful operation
*                DTC_ERR_INVALID_ARG -
*                    Parameters are invalid.
*                DTC_ERR_NULL_PTR -
*                    The pointers are NULL.
*******************************************************************************/
static dtc_err_t r_dtc_check_create_param(dtc_transfer_data_t *p_transfer_data,
                                          dtc_transfer_data_cfg_t *p_data_cfg)
{
#if (1 == DTC_CFG_PARAM_CHECKING_ENABLE)

    if ((NULL == p_data_cfg) || (NULL == p_transfer_data))
    {
        return DTC_ERR_NULL_PTR;
    }

    if ((p_data_cfg->transfer_count < DTC_PRV_MIN_COUNT_VAL) ||
        (p_data_cfg->transfer_count > DTC_PRV_MAX_16BITS_COUNT_VAL))
    {
        return DTC_ERR_INVALID_ARG;
    }

#if (DTC_ENABLE == DTC_CFG_SHORT_ADDRESS_MODE) /* Short-address mode */
/* Address must be in: 0x00000000h to 0x007FFFFF and 0xFF800000 to 0xFFFFFFFF */
    if ((p_data_cfg->source_addr > 0x007FFFFF) && (p_data_cfg->source_addr < 0xFF800000))
    {
        return DTC_ERR_INVALID_ARG;
    }

    if ((p_data_cfg->dest_addr > 0x007FFFFF) && (p_data_cfg->dest_addr < 0xFF800000))
    {
        return DTC_ERR_INVALID_ARG;
    }
    /* Casting to match type of "uint32_t" */
    if (((uint32_t)p_transfer_data > 0x007FFFFF) && ((uint32_t)p_transfer_data < 0xFF800000))
    {
        return DTC_ERR_INVALID_ARG;
    }
#endif /* (DTC_ENABLE == DTC_CFG_SHORT_ADDRESS_MODE) */
#endif /* (1 == DTC_CFG_PARAM_CHECKING_ENABLE) */
    return DTC_SUCCESS;
}
/* End of function r_dtc_check_create_param */

/* End of File */
