/***********************************************************************
 * $Id: type.h 8242 2011-10-11 15:15:25Z nxp28536 $
 *
 * Project: LPC43xx Common
 *
 * Description:
 *	Type definition Header file for NXP LPC4300 Family
 *  Microprocessors
 *
 ***********************************************************************
 * Software that is described herein is for illustrative purposes only
 * which provides customers with programming information regarding the
 * products. This software is supplied "AS IS" without any warranties.
 * NXP Semiconductors assumes no responsibility or liability for the
 * use of the software, conveys no license or title under any patent,
 * copyright, or mask work right to the product. NXP Semiconductors
 * reserves the right to make changes in the software without
 * notification. NXP Semiconductors also make no representation or
 * warranty that such application will be suitable for the specified
 * use without further testing or modification.
 **********************************************************************/

#ifndef __TYPE_H__
#define __TYPE_H__

#ifndef NULL
#define NULL    ((void *)0)
#endif

#ifndef FALSE
#define FALSE   (0)
#endif

#ifndef TRUE
#define TRUE    (1)
#endif

#define ABS(value)	(value<0 ? -value : value)

/**
 * @brief Flag Status and Interrupt Flag Status type definition
 */
typedef enum {RESET = 0, SET = !RESET} FlagStatus, IntStatus, SetState;
#define PARAM_SETSTATE(State) ((State==RESET) || (State==SET))

/**
 * @brief Functional State Definition
 */
typedef enum {DISABLE = 0, ENABLE = !DISABLE} FunctionalState;
#define PARAM_FUNCTIONALSTATE(State) ((State==DISABLE) || (State==ENABLE))

/**
 * @ Status type definition
 */
typedef enum {ERROR = 0, SUCCESS = !ERROR} Status;

typedef unsigned char  BYTE;
typedef unsigned short WORD;
typedef unsigned long  DWORD;
typedef unsigned int   BOOL;

typedef union _BITS
{
	unsigned char value;
	struct _bits
	{
		unsigned char bit0:1;
		unsigned char bit1:1;
		unsigned char bit2:1;
		unsigned char bit3:1;
		unsigned char bit4:1;
		unsigned char bit5:1;
		unsigned char bit6:1;
		unsigned char bit7:1;
	}bits;
}BITS;

#endif  /* __TYPE_H__ */
