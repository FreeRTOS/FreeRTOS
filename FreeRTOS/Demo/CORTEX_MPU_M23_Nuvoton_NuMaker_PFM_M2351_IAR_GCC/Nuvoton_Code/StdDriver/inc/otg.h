/**************************************************************************//**
 * @file     otg.h
 * @version  V3.00
 * @brief    M2351 series OTG driver header file
 *
 * @copyright (C) 2016 Nuvoton Technology Corp. All rights reserved.
 ******************************************************************************/
#ifndef __OTG_H__
#define __OTG_H__

/*---------------------------------------------------------------------------------------------------------*/
/* Include related headers                                                                                 */
/*---------------------------------------------------------------------------------------------------------*/
#include "M2351.h"

#ifdef __cplusplus
extern "C"
{
#endif


/** @addtogroup Standard_Driver Standard Driver
  @{
*/

/** @addtogroup OTG_Driver OTG Driver
  @{
*/


/** @addtogroup OTG_EXPORTED_CONSTANTS OTG Exported Constants
  @{
*/



/*---------------------------------------------------------------------------------------------------------*/
/* OTG constant definitions                                                                                */
/*---------------------------------------------------------------------------------------------------------*/
#define OTG_VBUS_EN_ACTIVE_HIGH      (0UL) /*!< USB VBUS power switch enable signal is active high. */
#define OTG_VBUS_EN_ACTIVE_LOW       (1UL) /*!< USB VBUS power switch enable signal is active low. */
#define OTG_VBUS_ST_VALID_HIGH       (0UL) /*!< USB VBUS power switch valid status is high. */
#define OTG_VBUS_ST_VALID_LOW        (1UL) /*!< USB VBUS power switch valid status is low. */


/*@}*/ /* end of group OTG_EXPORTED_CONSTANTS */


/** @addtogroup OTG_EXPORTED_FUNCTIONS OTG Exported Functions
  @{
*/

/*---------------------------------------------------------------------------------------------------------*/
/*  Define Macros and functions                                                                            */
/*---------------------------------------------------------------------------------------------------------*/


/**
  * @brief This macro is used to enable OTG function
  * @param None
  * @return None
  * @details This macro will set OTGEN bit of OTG_CTL register to enable OTG function.
  */
#define OTG_ENABLE()    (OTG->CTL |= OTG_CTL_OTGEN_Msk)

/**
  * @brief This macro is used to enable OTG function Macro for Non-Secure
  */
#define OTG_ENABLE_NS() (OTG_NS->CTL |= OTG_CTL_OTGEN_Msk)

/**
  * @brief This macro is used to disable OTG function
  * @param None
  * @return None
  * @details This macro will clear OTGEN bit of OTG_CTL register to disable OTG function.
  */
#define OTG_DISABLE()    (OTG->CTL &= ~OTG_CTL_OTGEN_Msk)

/**
  * @brief This macro is used to disable OTG function Macro for Non-Secure
  */
#define OTG_DISABLE_NS() (OTG_NS->CTL &= ~OTG_CTL_OTGEN_Msk)

/**
  * @brief This macro is used to enable USB PHY
  * @param None
  * @return None
  * @details When the USB role is selected as OTG device, use this macro to enable USB PHY.
  *          This macro will set OTGPHYEN bit of OTG_PHYCTL register to enable USB PHY.
  */
#define OTG_ENABLE_PHY()    (OTG->PHYCTL |= OTG_PHYCTL_OTGPHYEN_Msk)

/**
  * @brief This macro is used to enable USB PHY Macro for Non-Secure
  */
#define OTG_ENABLE_PHY_NS() (OTG_NS->PHYCTL |= OTG_PHYCTL_OTGPHYEN_Msk)

/**
  * @brief This macro is used to disable USB PHY
  * @param None
  * @return None
  * @details This macro will clear OTGPHYEN bit of OTG_PHYCTL register to disable USB PHY.
  */
#define OTG_DISABLE_PHY()    (OTG->PHYCTL &= ~OTG_PHYCTL_OTGPHYEN_Msk)

/**
  * @brief This macro is used to disable USB PHY Macro for Non-Secure
  */
#define OTG_DISABLE_PHY_NS() (OTG_NS->PHYCTL &= ~OTG_PHYCTL_OTGPHYEN_Msk)

/**
  * @brief This macro is used to enable ID detection function
  * @param None
  * @return None
  * @details This macro will set IDDETEN bit of OTG_PHYCTL register to enable ID detection function.
  */
#define OTG_ENABLE_ID_DETECT()    (OTG->PHYCTL |= OTG_PHYCTL_IDDETEN_Msk)

/**
  * @brief This macro is used to enable ID detection function Macro for Non-Secure
  */
#define OTG_ENABLE_ID_DETECT_NS() (OTG_NS->PHYCTL |= OTG_PHYCTL_IDDETEN_Msk)

/**
  * @brief This macro is used to disable ID detection function
  * @param None
  * @return None
  * @details This macro will clear IDDETEN bit of OTG_PHYCTL register to disable ID detection function.
  */
#define OTG_DISABLE_ID_DETECT()    (OTG->PHYCTL &= ~OTG_PHYCTL_IDDETEN_Msk)

/**
  * @brief This macro is used to disable ID detection function Macro for Non-Secure
  */
#define OTG_DISABLE_ID_DETECT_NS() (OTG_NS->PHYCTL &= ~OTG_PHYCTL_IDDETEN_Msk)

/**
  * @brief This macro is used to enable OTG wake-up function
  * @param None
  * @return None
  * @details This macro will set WKEN bit of OTG_CTL register to enable OTG wake-up function.
  */
#define OTG_ENABLE_WAKEUP()    (OTG->CTL |= OTG_CTL_WKEN_Msk)

/**
  * @brief This macro is used to enable OTG wake-up function Macro for Non-Secure
  */
#define OTG_ENABLE_WAKEUP_NS() (OTG_NS->CTL |= OTG_CTL_WKEN_Msk)

/**
  * @brief This macro is used to disable OTG wake-up function
  * @param None
  * @return None
  * @details This macro will clear WKEN bit of OTG_CTL register to disable OTG wake-up function.
  */
#define OTG_DISABLE_WAKEUP()    (OTG->CTL &= ~OTG_CTL_WKEN_Msk)

/**
  * @brief This macro is used to disable OTG wake-up function Macro for Non-Secure
  */
#define OTG_DISABLE_WAKEUP_NS() (OTG_NS->CTL &= ~OTG_CTL_WKEN_Msk)

/**
  * @brief This macro is used to set the polarity of USB_VBUS_EN pin
  * @param[in] u32Pol The polarity selection. Valid values are listed below.
  *                    - \ref OTG_VBUS_EN_ACTIVE_HIGH
  *                    - \ref OTG_VBUS_EN_ACTIVE_LOW
  * @return None
  * @details This macro is used to set the polarity of external USB VBUS power switch enable signal.
  */
#define OTG_SET_VBUS_EN_POL(u32Pol)    (OTG->PHYCTL = (OTG->PHYCTL & (~OTG_PHYCTL_VBENPOL_Msk)) | ((u32Pol)<<OTG_PHYCTL_VBENPOL_Pos))

/**
  * @brief This macro is used to set the polarity of USB_VBUS_EN pin Macro for Non-Secure
  */
#define OTG_SET_VBUS_EN_POL_NS(u32Pol) (OTG_NS->PHYCTL = (OTG_NS->PHYCTL & (~OTG_PHYCTL_VBENPOL_Msk)) | ((u32Pol)<<OTG_PHYCTL_VBENPOL_Pos))

/**
  * @brief This macro is used to set the polarity of USB_VBUS_ST pin
  * @param[in] u32Pol The polarity selection. Valid values are listed below.
  *                    - \ref OTG_VBUS_ST_VALID_HIGH
  *                    - \ref OTG_VBUS_ST_VALID_LOW
  * @return None
  * @details This macro is used to set the polarity of external USB VBUS power switch status signal.
  */
#define OTG_SET_VBUS_STS_POL(u32Pol)    (OTG->PHYCTL = (OTG->PHYCTL & (~OTG_PHYCTL_VBSTSPOL_Msk)) | ((u32Pol)<<OTG_PHYCTL_VBSTSPOL_Pos))

/**
  * @brief This macro is used to set the polarity of USB_VBUS_ST pin Macro for Non-Secure
  */
#define OTG_SET_VBUS_STS_POL_NS(u32Pol) (OTG_NS->PHYCTL = (OTG_NS->PHYCTL & (~OTG_PHYCTL_VBSTSPOL_Msk)) | ((u32Pol)<<OTG_PHYCTL_VBSTSPOL_Pos))

/**
  * @brief This macro is used to enable OTG related interrupts
  * @param[in] u32Mask The combination of interrupt source. Each bit corresponds to a interrupt source. Valid values are listed below.
  *                    - \ref OTG_INTEN_ROLECHGIEN_Msk
  *                    - \ref OTG_INTEN_VBEIEN_Msk
  *                    - \ref OTG_INTEN_SRPFIEN_Msk
  *                    - \ref OTG_INTEN_HNPFIEN_Msk
  *                    - \ref OTG_INTEN_GOIDLEIEN_Msk
  *                    - \ref OTG_INTEN_IDCHGIEN_Msk
  *                    - \ref OTG_INTEN_PDEVIEN_Msk
  *                    - \ref OTG_INTEN_HOSTIEN_Msk
  *                    - \ref OTG_INTEN_BVLDCHGIEN_Msk
  *                    - \ref OTG_INTEN_AVLDCHGIEN_Msk
  *                    - \ref OTG_INTEN_VBCHGIEN_Msk
  *                    - \ref OTG_INTEN_SECHGIEN_Msk
  *                    - \ref OTG_INTEN_SRPDETIEN_Msk
  * @return None
  * @details This macro will enable OTG related interrupts specified by u32Mask parameter.
  */
#define OTG_ENABLE_INT(u32Mask)    (OTG->INTEN |= (u32Mask))

/**
  * @brief This macro is used to enable OTG related interrupts Macro for Non-Secure
  */
#define OTG_ENABLE_INT_NS(u32Mask) (OTG_NS->INTEN |= (u32Mask))

/**
  * @brief This macro is used to disable OTG related interrupts
  * @param[in] u32Mask The combination of interrupt source. Each bit corresponds to a interrupt source. Valid values are listed below.
  *                    - \ref OTG_INTEN_ROLECHGIEN_Msk
  *                    - \ref OTG_INTEN_VBEIEN_Msk
  *                    - \ref OTG_INTEN_SRPFIEN_Msk
  *                    - \ref OTG_INTEN_HNPFIEN_Msk
  *                    - \ref OTG_INTEN_GOIDLEIEN_Msk
  *                    - \ref OTG_INTEN_IDCHGIEN_Msk
  *                    - \ref OTG_INTEN_PDEVIEN_Msk
  *                    - \ref OTG_INTEN_HOSTIEN_Msk
  *                    - \ref OTG_INTEN_BVLDCHGIEN_Msk
  *                    - \ref OTG_INTEN_AVLDCHGIEN_Msk
  *                    - \ref OTG_INTEN_VBCHGIEN_Msk
  *                    - \ref OTG_INTEN_SECHGIEN_Msk
  *                    - \ref OTG_INTEN_SRPDETIEN_Msk
  * @return None
  * @details This macro will disable OTG related interrupts specified by u32Mask parameter.
  */
#define OTG_DISABLE_INT(u32Mask)    (OTG->INTEN &= ~(u32Mask))

/**
  * @brief This macro is used to disable OTG related interrupts Macro for Non-Secure
  */
#define OTG_DISABLE_INT_NS(u32Mask) (OTG_NS->INTEN &= ~(u32Mask))

/**
  * @brief This macro is used to get OTG related interrupt flags
  * @param[in] u32Mask The combination of interrupt source. Each bit corresponds to a interrupt source. Valid values are listed below.
  *                    - \ref OTG_INTSTS_ROLECHGIF_Msk
  *                    - \ref OTG_INTSTS_VBEIF_Msk
  *                    - \ref OTG_INTSTS_SRPFIF_Msk
  *                    - \ref OTG_INTSTS_HNPFIF_Msk
  *                    - \ref OTG_INTSTS_GOIDLEIF_Msk
  *                    - \ref OTG_INTSTS_IDCHGIF_Msk
  *                    - \ref OTG_INTSTS_PDEVIF_Msk
  *                    - \ref OTG_INTSTS_HOSTIF_Msk
  *                    - \ref OTG_INTSTS_BVLDCHGIF_Msk
  *                    - \ref OTG_INTSTS_AVLDCHGIF_Msk
  *                    - \ref OTG_INTSTS_VBCHGIF_Msk
  *                    - \ref OTG_INTSTS_SECHGIF_Msk
  *                    - \ref OTG_INTSTS_SRPDETIF_Msk
  * @return Interrupt flags of selected sources.
  * @details This macro will return OTG related interrupt flags specified by u32Mask parameter.
  */
#define OTG_GET_INT_FLAG(u32Mask)    (OTG->INTSTS & (u32Mask))

/**
  * @brief This macro is used to get OTG related interrupt flags Macro for Non-Secure
  */
#define OTG_GET_INT_FLAG_NS(u32Mask) (OTG_NS->INTSTS & (u32Mask))

/**
  * @brief This macro is used to clear OTG related interrupt flags
  * @param[in] u32Mask The combination of interrupt source. Each bit corresponds to a interrupt source. Valid values are listed below.
  *                    - \ref OTG_INTSTS_ROLECHGIF_Msk
  *                    - \ref OTG_INTSTS_VBEIF_Msk
  *                    - \ref OTG_INTSTS_SRPFIF_Msk
  *                    - \ref OTG_INTSTS_HNPFIF_Msk
  *                    - \ref OTG_INTSTS_GOIDLEIF_Msk
  *                    - \ref OTG_INTSTS_IDCHGIF_Msk
  *                    - \ref OTG_INTSTS_PDEVIF_Msk
  *                    - \ref OTG_INTSTS_HOSTIF_Msk
  *                    - \ref OTG_INTSTS_BVLDCHGIF_Msk
  *                    - \ref OTG_INTSTS_AVLDCHGIF_Msk
  *                    - \ref OTG_INTSTS_VBCHGIF_Msk
  *                    - \ref OTG_INTSTS_SECHGIF_Msk
  *                    - \ref OTG_INTSTS_SRPDETIF_Msk
  * @return None
  * @details This macro will clear OTG related interrupt flags specified by u32Mask parameter.
  */
#define OTG_CLR_INT_FLAG(u32Mask)    (OTG->INTSTS = (u32Mask))

/**
  * @brief This macro is used to clear OTG related interrupt flags Macro for Non-Secure
  */
#define OTG_CLR_INT_FLAG_NS(u32Mask) (OTG_NS->INTSTS = (u32Mask))

/**
  * @brief This macro is used to get OTG related status
  * @param[in] u32Mask The combination of user specified source. Valid values are listed below.
  *                    - \ref OTG_STATUS_OVERCUR_Msk
  *                    - \ref OTG_STATUS_IDSTS_Msk
  *                    - \ref OTG_STATUS_SESSEND_Msk
  *                    - \ref OTG_STATUS_BVLD_Msk
  *                    - \ref OTG_STATUS_AVLD_Msk
  *                    - \ref OTG_STATUS_VBUSVLD_Msk
  * @return The user specified status.
  * @details This macro will return OTG related status specified by u32Mask parameter.
  */
#define OTG_GET_STATUS(u32Mask)    (OTG->STATUS & (u32Mask))

/**
  * @brief This macro is used to get OTG related status Macro for Non-Secure
  */
#define OTG_GET_STATUS_NS(u32Mask) (OTG_NS->STATUS & (u32Mask))



/*@}*/ /* end of group OTG_EXPORTED_FUNCTIONS */

/*@}*/ /* end of group OTG_Driver */

/*@}*/ /* end of group Standard_Driver */

#ifdef __cplusplus
}
#endif


#endif /* __OTG_H__ */

/*** (C) COPYRIGHT 2016 Nuvoton Technology Corp. ***/
