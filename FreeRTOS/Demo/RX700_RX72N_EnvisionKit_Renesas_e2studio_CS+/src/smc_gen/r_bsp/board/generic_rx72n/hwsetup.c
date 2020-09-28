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
* Copyright (C) 2019 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/
/***********************************************************************************************************************
* File Name    : hwsetup.c
* Device(s)    : RX
* H/W Platform : GENERIC_RX72N
* Description  : Defines the initialization routines used each time the MCU is restarted.
***********************************************************************************************************************/
/***********************************************************************************************************************
* History : DD.MM.YYYY Version  Description
*         : 08.10.2019 1.00     First Release
***********************************************************************************************************************/

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
/* I/O Register and board definitions */
#include "platform.h"
#if BSP_CFG_CONFIGURATOR_SELECT == 1
#include "r_cg_macrodriver.h"
#endif

/***********************************************************************************************************************
Typedef definitions
***********************************************************************************************************************/
R_BSP_PRAGMA_UNPACK
typedef struct bsp_bsc {
    union {
        uint32_t u_long;
        R_BSP_ATTRIB_STRUCT_BIT_ORDER_LEFT_13(
            uint32_t prerr:1,
            uint32_t :1,
            uint32_t rpstop:1,
            uint32_t :10,
            uint32_t pr5sel:3,
            uint32_t :1,
            uint32_t pr4sel:3,
            uint32_t :1,
            uint32_t pr3sel:3,
            uint32_t :1,
            uint32_t pr2sel:3,
            uint32_t :1,
            uint32_t pr1sel:3
        ) bit;
    } ebmapcr;
} st_bsp_bsc_t;
R_BSP_PRAGMA_PACKOPTION

/***********************************************************************************************************************
Private global variables and functions
***********************************************************************************************************************/
/* When using the user startup program, disable the following code. */
#if BSP_CFG_STARTUP_DISABLE == 0
/* ROM cache configuration function declaration */
#if BSP_CFG_ROM_CACHE_ENABLE == 1
static void rom_cache_function_set(void);
#if BSP_CFG_NONCACHEABLE_AREA0_ENABLE == 1
static void rom_cache_noncacheable_area0_set(void);
#endif /* BSP_CFG_NONCACHEABLE_AREA0_ENABLE == 1 */
#if BSP_CFG_NONCACHEABLE_AREA1_ENABLE == 1
static void rom_cache_noncacheable_area1_set(void);
#endif /* BSP_CFG_NONCACHEABLE_AREA1_ENABLE == 1 */
#endif /* BSP_CFG_ROM_CACHE_ENABLE == 1 */
#endif /* BSP_CFG_STARTUP_DISABLE == 0 */

/* MCU I/O port configuration function declaration */
static void output_ports_configure(void);

/* Interrupt configuration function declaration */
static void interrupts_configure(void);

/* MCU peripheral module configuration function declaration */
static void peripheral_modules_enable(void);

/* ADC initial configuration function declaration */
static void bsp_adc_initial_configure(void);

/* BUS initial configuration function declaration */
static void bsp_bsc_initial_configure(void);

/***********************************************************************************************************************
* Function name: hardware_setup
* Description  : Contains setup functions called at device restart
* Arguments    : none
* Return value : none
***********************************************************************************************************************/
void hardware_setup(void)
{
/* When using the user startup program, disable the following code. */
#if BSP_CFG_STARTUP_DISABLE == 0
#if BSP_CFG_ROM_CACHE_ENABLE == 1
    /* Initialize ROM cache function */
    rom_cache_function_set();
#endif /* BSP_CFG_ROM_CACHE_ENABLE == 1 */
#endif /* BSP_CFG_STARTUP_DISABLE == 0 */

    output_ports_configure();
    interrupts_configure();
    peripheral_modules_enable();
    bsp_non_existent_port_init();
    bsp_adc_initial_configure();
    bsp_bsc_initial_configure();
} /* End of function hardware_setup() */

/* When using the user startup program, disable the following code. */
#if BSP_CFG_STARTUP_DISABLE == 0
#if BSP_CFG_ROM_CACHE_ENABLE == 1
/***********************************************************************************************************************
* Function name: rom_cache_function_set
* Description  : Configures the rom cache function.
* Arguments    : none
* Return value : none
***********************************************************************************************************************/
static void rom_cache_function_set (void)
{
#if BSP_CFG_NONCACHEABLE_AREA0_ENABLE == 1
    rom_cache_noncacheable_area0_set();
#endif /* BSP_CFG_NONCACHEABLE_AREA0_ENABLE == 1 */

#if BSP_CFG_NONCACHEABLE_AREA1_ENABLE == 1
    rom_cache_noncacheable_area1_set();
#endif /* BSP_CFG_NONCACHEABLE_AREA1_ENABLE == 1 */

    /* Invalidates the contents of the ROM cache. */
    FLASH.ROMCIV.WORD = 0x0001;

    /* Enables the ROM cache. */
    FLASH.ROMCE.WORD = 0x0001;
} /* End of function rom_cache_function_set() */

#if BSP_CFG_NONCACHEABLE_AREA0_ENABLE == 1
/***********************************************************************************************************************
* Function name: rom_cache_noncacheable_area0_set
* Description  : Configures non-cacheable area 0 of the ROM cache function.
* Arguments    : none
* Return value : none
***********************************************************************************************************************/
static void rom_cache_noncacheable_area0_set (void)
{
    /* Used to specify the value written to the NCRC0 register. */
    uint32_t tmp_ncrc = 0;

    /* Disables the ROM cache. */
    FLASH.ROMCE.WORD = 0x0000;

    /* Makes settings to the NCRG0 register. */
#if (BSP_CFG_NONCACHEABLE_AREA0_ADDR >= 0xFFC00000) \
      && ((BSP_CFG_NONCACHEABLE_AREA0_ADDR & 0x0000000F) == 0x00000000)
    FLASH.NCRG0 = BSP_CFG_NONCACHEABLE_AREA0_ADDR;
#else
    #error "Error! Invalid setting for BSP_CFG_NONCACHEABLE_AREA0_ADDR in r_bsp_config.h"
#endif

    /* Sets the value of the NCSZ bits. */
#if   BSP_CFG_NONCACHEABLE_AREA0_SIZE == 0x0
    /* Do nothing since NCRC0 bits should be 0. */
#elif BSP_CFG_NONCACHEABLE_AREA0_SIZE == 0x1
    tmp_ncrc |= 0x00000010;
#elif BSP_CFG_NONCACHEABLE_AREA0_SIZE == 0x2
    tmp_ncrc |= 0x00000030;
#elif BSP_CFG_NONCACHEABLE_AREA0_SIZE == 0x3
    tmp_ncrc |= 0x00000070;
#elif BSP_CFG_NONCACHEABLE_AREA0_SIZE == 0x4
    tmp_ncrc |= 0x000000F0;
#elif BSP_CFG_NONCACHEABLE_AREA0_SIZE == 0x5
    tmp_ncrc |= 0x000001F0;
#elif BSP_CFG_NONCACHEABLE_AREA0_SIZE == 0x6
    tmp_ncrc |= 0x000003F0;
#elif BSP_CFG_NONCACHEABLE_AREA0_SIZE == 0x7
    tmp_ncrc |= 0x000007F0;
#elif BSP_CFG_NONCACHEABLE_AREA0_SIZE == 0x8
    tmp_ncrc |= 0x00000FF0;
#elif BSP_CFG_NONCACHEABLE_AREA0_SIZE == 0x9
    tmp_ncrc |= 0x00001FF0;
#elif BSP_CFG_NONCACHEABLE_AREA0_SIZE == 0xA
    tmp_ncrc |= 0x00003FF0;
#elif BSP_CFG_NONCACHEABLE_AREA0_SIZE == 0xB
    tmp_ncrc |= 0x00007FF0;
#elif BSP_CFG_NONCACHEABLE_AREA0_SIZE == 0xC
    tmp_ncrc |= 0x0000FFF0;
#elif BSP_CFG_NONCACHEABLE_AREA0_SIZE == 0xD
    tmp_ncrc |= 0x0001FFF0;
#elif BSP_CFG_NONCACHEABLE_AREA0_SIZE == 0xE
    tmp_ncrc |= 0x0003FFF0;
#elif BSP_CFG_NONCACHEABLE_AREA0_SIZE == 0xF
    tmp_ncrc |= 0x0007FFF0;
#elif BSP_CFG_NONCACHEABLE_AREA0_SIZE == 0x10
    tmp_ncrc |= 0x000FFFF0;
#elif BSP_CFG_NONCACHEABLE_AREA0_SIZE == 0x11
    tmp_ncrc |= 0x001FFFF0;
#else
    #error "Error! Invalid setting for BSP_CFG_NONCACHEABLE_AREA0_SIZE in r_bsp_config.h"
#endif

    /* Sets the value of the NC1E bits. */
#if BSP_CFG_NONCACHEABLE_AREA0_IF_ENABLE == 1
    tmp_ncrc |= 0x00000002;
#endif

    /* Sets the value of the NC2E bits. */
#if BSP_CFG_NONCACHEABLE_AREA0_OA_ENABLE == 1
    tmp_ncrc |= 0x00000004;
#endif

    /* Sets the value of the NC3E bits. */
#if BSP_CFG_NONCACHEABLE_AREA0_DM_ENABLE == 1
    tmp_ncrc |= 0x00000008;
#endif

    /* Makes settings to the NCRC0 register. */
    FLASH.NCRC0.LONG = tmp_ncrc;
} /* End of function rom_cache_noncacheable_area0_set() */
#endif /* BSP_CFG_NONCACHEABLE_AREA0_ENABLE == 1 */

#if BSP_CFG_NONCACHEABLE_AREA1_ENABLE == 1
/***********************************************************************************************************************
* Function name: rom_cache_noncacheable_area1_set
* Description  : Configures non-cacheable area 1 of the ROM cache function.
* Arguments    : none
* Return value : none
***********************************************************************************************************************/
static void rom_cache_noncacheable_area1_set (void)
{
    /* Used to specify the value written to the NCRC1 register. */
    uint32_t tmp_ncrc = 0;

    /* Disables the ROM cache. */
    FLASH.ROMCE.WORD = 0x0000;

    /* Makes settings to the NCRG1 register. */
#if (BSP_CFG_NONCACHEABLE_AREA1_ADDR >= 0xFFC00000) \
      && ((BSP_CFG_NONCACHEABLE_AREA1_ADDR & 0x0000000F) == 0x00000000)
    FLASH.NCRG1 = BSP_CFG_NONCACHEABLE_AREA1_ADDR;
#else
    #error "Error! Invalid setting for BSP_CFG_NONCACHEABLE_AREA1_ADDR in r_bsp_config.h"
#endif

    /* Sets the value of the NCSZ bits. */
#if   BSP_CFG_NONCACHEABLE_AREA1_SIZE == 0x0
    /* Do nothing since NCRC1 bits should be 0. */
#elif BSP_CFG_NONCACHEABLE_AREA1_SIZE == 0x1
    tmp_ncrc |= 0x00000010;
#elif BSP_CFG_NONCACHEABLE_AREA1_SIZE == 0x2
    tmp_ncrc |= 0x00000030;
#elif BSP_CFG_NONCACHEABLE_AREA1_SIZE == 0x3
    tmp_ncrc |= 0x00000070;
#elif BSP_CFG_NONCACHEABLE_AREA1_SIZE == 0x4
    tmp_ncrc |= 0x000000F0;
#elif BSP_CFG_NONCACHEABLE_AREA1_SIZE == 0x5
    tmp_ncrc |= 0x000001F0;
#elif BSP_CFG_NONCACHEABLE_AREA1_SIZE == 0x6
    tmp_ncrc |= 0x000003F0;
#elif BSP_CFG_NONCACHEABLE_AREA1_SIZE == 0x7
    tmp_ncrc |= 0x000007F0;
#elif BSP_CFG_NONCACHEABLE_AREA1_SIZE == 0x8
    tmp_ncrc |= 0x00000FF0;
#elif BSP_CFG_NONCACHEABLE_AREA1_SIZE == 0x9
    tmp_ncrc |= 0x00001FF0;
#elif BSP_CFG_NONCACHEABLE_AREA1_SIZE == 0xA
    tmp_ncrc |= 0x00003FF0;
#elif BSP_CFG_NONCACHEABLE_AREA1_SIZE == 0xB
    tmp_ncrc |= 0x00007FF0;
#elif BSP_CFG_NONCACHEABLE_AREA1_SIZE == 0xC
    tmp_ncrc |= 0x0000FFF0;
#elif BSP_CFG_NONCACHEABLE_AREA1_SIZE == 0xD
    tmp_ncrc |= 0x0001FFF0;
#elif BSP_CFG_NONCACHEABLE_AREA1_SIZE == 0xE
    tmp_ncrc |= 0x0003FFF0;
#elif BSP_CFG_NONCACHEABLE_AREA1_SIZE == 0xF
    tmp_ncrc |= 0x0007FFF0;
#elif BSP_CFG_NONCACHEABLE_AREA1_SIZE == 0x10
    tmp_ncrc |= 0x000FFFF0;
#elif BSP_CFG_NONCACHEABLE_AREA1_SIZE == 0x11
    tmp_ncrc |= 0x001FFFF0;
#else
    #error "Error! Invalid setting for BSP_CFG_NONCACHEABLE_AREA1_SIZE in r_bsp_config.h"
#endif

    /* Sets the value of the NC1E bits. */
#if BSP_CFG_NONCACHEABLE_AREA1_IF_ENABLE == 1
    tmp_ncrc |= 0x00000002;
#endif

    /* Sets the value of the NC2E bits. */
#if BSP_CFG_NONCACHEABLE_AREA1_OA_ENABLE == 1
    tmp_ncrc |= 0x00000004;
#endif

    /* Sets the value of the NC3E bits. */
#if BSP_CFG_NONCACHEABLE_AREA1_DM_ENABLE == 1
    tmp_ncrc |= 0x00000008;
#endif

    /* Makes settings to the NCRC1 register. */
    FLASH.NCRC1.LONG = tmp_ncrc;
} /* End of function rom_cache_noncacheable_area1_set() */
#endif /* BSP_CFG_NONCACHEABLE_AREA1_ENABLE == 1 */
#endif /* BSP_CFG_ROM_CACHE_ENABLE == 1 */
#endif /* BSP_CFG_STARTUP_DISABLE == 0 */

/***********************************************************************************************************************
* Function name: output_ports_configure
* Description  : Configures the port and pin direction settings, and sets the pin outputs to a safe level.
* Arguments    : none
* Return value : none
***********************************************************************************************************************/
static void output_ports_configure(void)
{
    /* Add code here to setup additional output ports */
    R_BSP_NOP();
} /* End of function output_ports_configure() */

/***********************************************************************************************************************
* Function name: interrupts_configure
* Description  : Configures interrupts used
* Arguments    : none
* Return value : none
***********************************************************************************************************************/
static void interrupts_configure(void)
{
    /* Add code here to setup additional interrupts */
    R_BSP_NOP();
} /* End of function interrupts_configure() */

/***********************************************************************************************************************
* Function name: peripheral_modules_enable
* Description  : Enables and configures peripheral devices on the MCU
* Arguments    : none
* Return value : none
***********************************************************************************************************************/
static void peripheral_modules_enable(void)
{
    /* Add code here to enable peripherals used by the application */
#if BSP_CFG_CONFIGURATOR_SELECT == 1
    /* Smart Configurator initialization function */
    R_Systeminit();
#endif
} /* End of function peripheral_modules_enable() */

/***********************************************************************************************************************
* Function name: bsp_adc_initial_configure
* Description  : Configures the ADC initial settings
* Arguments    : none
* Return value : none
* Note         : This function should be called when the PSW.I bit is 0 (interrupt disabled).
*                This function should be called when the ADCSR.ADST bit is 0.
***********************************************************************************************************************/
static void bsp_adc_initial_configure(void)
{
    uint32_t tmp_mstp;

    /* Protect off. */
    SYSTEM.PRCR.WORD = 0xA502;

    /* Store the value of the MSTPCR. */
    tmp_mstp = MSTP(S12AD1);

    /* Release from the module-stop state */
    MSTP(S12AD1) = 0;

    /* Writing to the A/D conversion time setting register is enabled. */
    S12AD1.ADSAMPR.BYTE = 0x03;

    /* Sets conversion time for middle-speed for S12AD unit 1. */
    S12AD1.ADSAM.WORD = 0x0020;

    /* Writing to the A/D conversion time setting register is disabled. */
    S12AD1.ADSAMPR.BYTE = 0x02;

    /* Restore the value of the MSTPCR. */
    MSTP(S12AD1) = tmp_mstp;

    /* Protect on. */
    SYSTEM.PRCR.WORD = 0xA500;
} /* End of function bsp_adc_initial_configure() */

/***********************************************************************************************************************
* Function name: bsp_bsc_initial_configure
* Description  : Configures the BUS initial settings
* Arguments    : none
* Return value : none
***********************************************************************************************************************/
static void bsp_bsc_initial_configure(void)
{
    st_bsp_bsc_t bsp_bsc;

    /* Setting priority when bus right request contention occurs. */
    bsp_bsc.ebmapcr.u_long     = BSC.EBMAPCR.LONG;
    bsp_bsc.ebmapcr.bit.pr1sel = BSP_CFG_EBMAPCR_1ST_PRIORITY;
    bsp_bsc.ebmapcr.bit.pr2sel = BSP_CFG_EBMAPCR_2ND_PRIORITY;
    bsp_bsc.ebmapcr.bit.pr3sel = BSP_CFG_EBMAPCR_3RD_PRIORITY;
    bsp_bsc.ebmapcr.bit.pr4sel = BSP_CFG_EBMAPCR_4TH_PRIORITY;
    bsp_bsc.ebmapcr.bit.pr5sel = BSP_CFG_EBMAPCR_5TH_PRIORITY;

    /* Set to EBMAPCR register */
    BSC.EBMAPCR.LONG = bsp_bsc.ebmapcr.u_long;
} /* End of function bsp_bsc_initial_configure() */

