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
* Copyright (C) 2013-2020 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/
/***********************************************************************************************************************
* File Name    : r_gpio_rx_if.h
* Description  : General Purpose I/O driver for RX MCUs. This interface file has everything the user needs to use this
*                module.
***********************************************************************************************************************/
/***********************************************************************************************************************
* History : DD.MM.YYYY Version Description           
*         : 17.07.2013 1.00    First Release
*         : 23.04.2014 1.20    Add support for RX63N, and RX110
*         : 28.05.2014 1.30    Add support for RX64M
*         : 28.11.2014 1.40    Add support for RX113
*         : 02.09.2015 1.50    Add support for RX71M, increased the minor version number to 50.
*         :                    Added GPIO_CMD_DSCR_DISABLE and GPIO_CMD_DSCR_ENABLE commands in gpio_cmd_t
*         : 06.04.2015 1.60    Add support for RX231
*         : 30.09.2015 1.70    Add support for RX23T
*         : 01.10.2015 1.80    Add support for RX130
*         : 01.12.2015 1.90    Add support for RX24T
*         : 01.02.2016 2.00    Add support for RX230
*         : 15.06.2016 2.01    Added the demo of the RX64M group.
*         : 01.10.2016 2.10    Add support for RX65N
*         : 19.12.2016 2.20    Add support for RX24U, RX24T(512KB)
*         : 21.07.2017 2.30    Add support for RX65N-2M, RX130-512KB
*         : 31.10.2017 2.31    Added the demo for RX65N, RX65N-2M
*         : 28.09.2018 2.40    Add support for RX66T
*         : 16.11.2018 2.41    Added XML document number
*         : 01.02.2019 2.50    Add support for RX72T, RX65N-64pin
*         : 20.05.2019 3.00    Added support for GNUC and ICCRX.
*         : 28.06.2019 3.10    Added support RX23W
*         : 15.08.2019 3.20    Added support RX72M
*         : 25.11.2019 3.30    Added support RX13T
*                              Removed support for Generation 1 devices.
*         : 30.12.2019 3.40    Added support RX72N, RX66N
*         : 31.03.2020 3.50    Added support for RX23E-A
***********************************************************************************************************************/

#ifndef GPIO_RX_INTERFACE_HEADER_FILE
#define GPIO_RX_INTERFACE_HEADER_FILE

/***********************************************************************************************************************
Includes   <System Includes> , "Project Includes"
***********************************************************************************************************************/
/* Includes board and MCU related header files. */
#include "platform.h"
/* Module configuration. */
#include "r_gpio_rx_config.h"

/* Include specifics for chosen MCU. Go to the header file for your MCU to see available ports and pins. */
#if defined(BSP_MCU_RX113)
    #include "./src/targets/rx113/r_gpio_rx113.h"
#elif   defined(BSP_MCU_RX110)
    #include "./src/targets/rx110/r_gpio_rx110.h"
#elif   defined(BSP_MCU_RX111)
    #include "./src/targets/rx111/r_gpio_rx111.h"
#elif   defined(BSP_MCU_RX130)
    #include "./src/targets/rx130/r_gpio_rx130.h"
#elif   defined(BSP_MCU_RX13T)
    #include "./src/targets/rx13t/r_gpio_rx13t.h"
#elif defined(BSP_MCU_RX230)
    #include "./src/targets/rx230/r_gpio_rx230.h"
#elif defined(BSP_MCU_RX231)
    #include "./src/targets/rx231/r_gpio_rx231.h"
#elif defined(BSP_MCU_RX23T)
    #include "./src/targets/rx23t/r_gpio_rx23t.h"
#elif defined(BSP_MCU_RX23W)
    #include "./src/targets/rx23w/r_gpio_rx23w.h"
#elif defined(BSP_MCU_RX23E_A)
    #include "./src/targets/rx23e-a/r_gpio_rx23e-a.h"
#elif defined(BSP_MCU_RX24T)
    #include "./src/targets/rx24t/r_gpio_rx24t.h"
#elif defined(BSP_MCU_RX24U)
    #include "./src/targets/rx24u/r_gpio_rx24u.h"
#elif defined(BSP_MCU_RX64M)
    #include "./src/targets/rx64m/r_gpio_rx64m.h"
#elif defined(BSP_MCU_RX65N)
    #include "./src/targets/rx65n/r_gpio_rx65n.h"
#elif defined(BSP_MCU_RX66T)
    #include "./src/targets/rx66t/r_gpio_rx66t.h"
#elif defined(BSP_MCU_RX66N)
    #include "./src/targets/rx66n/r_gpio_rx66n.h"
#elif defined(BSP_MCU_RX71M)
    #include "./src/targets/rx71m/r_gpio_rx71m.h"
#elif defined(BSP_MCU_RX72T)
    #include "./src/targets/rx72t/r_gpio_rx72t.h"
#elif defined(BSP_MCU_RX72M)
    #include "./src/targets/rx72m/r_gpio_rx72m.h"
#elif defined(BSP_MCU_RX72N)
    #include "./src/targets/rx72n/r_gpio_rx72n.h"
#else
    #error "This MCU is not supported by the current r_gpio_rx module."
#endif

/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/

#if R_BSP_VERSION_MAJOR < 5
    #error "This module must use BSP module of Rev.5.00 or higher. Please use the BSP module of Rev.5.00 or higher."
#endif

/* Version Number of API. */
#define GPIO_RX_VERSION_MAJOR           (3)
#define GPIO_RX_VERSION_MINOR           (50)

/***********************************************************************************************************************
Typedef definitions
***********************************************************************************************************************/
/* The gpio_port_t and gpio_port_pin_t enums are located in the 'targets' folder for each MCU. For example, to see
 * these enums for a RX111 look at the following file: r_gpio_rx/src/targets/rx111/r_gpio_rx111.h
 */

/* Levels that can be set and read for individual pins. */
typedef enum
{
    GPIO_LEVEL_LOW = 0,
    GPIO_LEVEL_HIGH
} gpio_level_t;

/* Options that can be used with the R_GPIO_PortDirectionSet() and R_GPIO_PinDirectionSet() functions. */
typedef enum
{
    GPIO_DIRECTION_INPUT = 0,
    GPIO_DIRECTION_OUTPUT
} gpio_dir_t;

/* Commands that can be used with the R_GPIO_PinControl() function. This list will vary depending on the MCU chosen. */
typedef enum
{
    GPIO_CMD_OUT_CMOS = 0,
    GPIO_CMD_OUT_OPEN_DRAIN_N_CHAN,
    GPIO_CMD_OUT_OPEN_DRAIN_P_CHAN,
    GPIO_CMD_IN_PULL_UP_DISABLE,
    GPIO_CMD_IN_PULL_UP_ENABLE,
    GPIO_CMD_ASSIGN_TO_PERIPHERAL,
    GPIO_CMD_ASSIGN_TO_GPIO,
    GPIO_CMD_DSCR_DISABLE,
    GPIO_CMD_DSCR_ENABLE,
    GPIO_CMD_DSCR2_DISABLE,
    GPIO_CMD_DSCR2_ENABLE
} gpio_cmd_t;

/* Function return type. */
typedef enum
{
    GPIO_SUCCESS = 0,
    GPIO_ERR_INVALID_MODE,  // The mode specified cannot be applied to this pin
    GPIO_ERR_INVALID_CMD    // The input command is not supported
} gpio_err_t;

/***********************************************************************************************************************
Exported global variables
***********************************************************************************************************************/

/***********************************************************************************************************************
Exported global functions (to be accessed by other files)
***********************************************************************************************************************/
void            R_GPIO_PortWrite(gpio_port_t port, uint8_t value);
uint8_t         R_GPIO_PortRead(gpio_port_t port);
void            R_GPIO_PortDirectionSet(gpio_port_t port, gpio_dir_t dir, uint8_t mask);
void            R_GPIO_PinWrite(gpio_port_pin_t pin, gpio_level_t level);
gpio_level_t    R_GPIO_PinRead(gpio_port_pin_t pin);
void            R_GPIO_PinDirectionSet(gpio_port_pin_t pin, gpio_dir_t dir);
gpio_err_t      R_GPIO_PinControl(gpio_port_pin_t pin, gpio_cmd_t cmd);
uint32_t        R_GPIO_GetVersion(void);

#endif /* GPIO_RX_INTERFACE_HEADER_FILE */


