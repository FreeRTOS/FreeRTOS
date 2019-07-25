/** @file sys_core.h
*   @brief System Core Header File
*   @date 23.July.2009
*   @version 1.00.000
*   
*   This file contains:
*   - Core Interface Functions
*   .
*   which are relevant for the System driver.
*/

/* (c) Texas Instruments 2009, All rights reserved. */

#ifndef __SYS_CORE_H__
#define __SYS_CORE_H__

/* System Core Interface Functions */

/** @fn void _coreInitRegisters_(void)
*   @brief Initialize Core register
*/
void _coreInitRegisters(void);

/** @fn void _coreInitStackPointer_(void)
*   @brief Initialize Core stack pointer
*/
void _coreInitStackPointer(void);

/** @fn void _coreEnableIrqVicOffset_(void)
*   @brief Enable Irq offset propagation via Vic controller
*/
void _coreEnableIrqVicOffset(void);


/** @fn void _coreEnableEventBusExport_(void)
*   @brief Enable event bus export for external monitoring modules
*   @note It is required to enable event bus export to process ecc issues.
*
*   This function enables event bus exports to external monitoring modules
*   like tightly coupled RAM wrapper, Flash wrapper and error signaling module.
*/
void _coreEnableEventBusExport(void);

/** @fn void _coreEnableRamEcc_(void)
*   @brief Enable external ecc error for RAM odd and even bank
*   @note It is required to enable event bus export to process ecc issues.
*/
void _coreEnableRamEcc(void);

/** @fn void _coreEnableFlashEcc_(void)
*   @brief Enable external ecc error for the Flash
*   @note It is required to enable event bus export to process ecc issues.
*/
void _coreEnableFlashEcc(void);

/** @fn void _coreEnableVfp(void)
*   @brief Enable Cortex-R4 FPU
*/
void _coreEnableVfp();

#endif
