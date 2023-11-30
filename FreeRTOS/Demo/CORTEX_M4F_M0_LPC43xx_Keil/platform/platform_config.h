#ifndef __PLATFORM_CONFIG_H 
#define __PLATFORM_CONFIG_H

#include "stdint.h"

/****************************************************/
/* supported platforms list							*/
/* DO NOT CHANGE THESE DEFINITIONS 					*/
#define NXP_VALIDATION_BOARD	(1)
#define HITEX_A2_BOARD          (3)
/****************************************************/

/****************************************************/
/* used for the configuration checks */
/* DO NOT CHANGE THESE DEFINITIONS 					*/
/****************************************************/
#define YES	(1)
#define NO	(2)

/****************************************************/
/* USER CONFIGURATION SECTION						*/
/****************************************************/

/* choose the platform you want to build against 	*/
// #define PLATFORM NXP_VALIDATION_BOARD 
#define PLATFORM HITEX_A2_BOARD

/* these definitions are being taken from the build rule */
#ifdef EXT_FLASH
#define	USE_EXT_FLASH	(YES)
#else 
#define USE_EXT_FLASH	(NO)
#endif

#ifdef EXT_STAT_MEM
#define USE_EXT_STATIC_MEM	(YES)
#else
#define USE_EXT_STATIC_MEM	(NO)
#endif

#ifdef EXT_DYN_MEM
#define USE_EXT_DYNAMIC_MEM	(YES)
#else
#define USE_EXT_DYNAMIC_MEM	(NO)
#endif

/* define if the M4 should download and start the M0 application 	*/
/* set to YES if M4 should initialize M0 application	 			*/
/* set to NO if the debugger is downloading the M0 image, used for  */
/* dual core debugging sessions */
#define INITIALIZE_M0_IMAGE	(NO)

/* specify if need to prefill the M0 memory before download */
#define FILL_ROM_BEFORE_DOWNLOAD (NO)
#define FILL_RAM_BEFORE_DOWNLOAD (NO)

/* define if the M4 provides a mailbox system to the M0 */
/* M0 ---> M4 */
#define USE_M4_MAILBOX			(NO)
/* configure which priority the mailbox interrupt should have on the M4 side */
/* cmsis definition, priority from 0 to 7 */
#define M4_MAILBOX_PRIORITY		(0)

/* define if the M0 provides a mailbox system to the M4 */
/* M4 ---> M0 */
#define USE_M0_MAILBOX			(NO)
/* configure which priority the mailbox interrupt should have on the M0 side */
/* cmsis definition, priority from 0 to 3 */
#define M0_MAILBOX_PRIORITY	(0)


/* define if the system needs to exchange a parameter */
#define USE_MAILBOX_PARAMETER	(NO)

/* define if the system needs to hook a callback, or just notify */
#define USE_MAILBOX_CALLBACK	(NO)


/* memory map for the application */
/* !!! needs to be consistent with the scatter file !!! */
#ifdef EXT_FLASH

/************************************/
/* this is for the FLASH version 	*/
/************************************/
/*	0x1C000000	M4 ROM 4Mbytes		*/
/*	0x1C3FFFFF						*/
/*	0x10000000	M4 RAM 96K			*/
/*	0x10017FFF						*/
#define M4_ROM_START	0x1C000000
#define M4_ROM_LEN		0x400000	/* 4 Mbytes */

#define M4_RAM_START	0x10000000	/* 96 Kbytes */
#define M4_RAM_LEN		0x18000

/*	0x10080000	M0 ROM 32K	*/
/*	0x10087FFF				*/
/*	0x10088000 	M0 RAM 8K	*/
/*	0x10089FFF 				*/
#define M0_ROM_START	0x10080000
#define M0_ROM_LEN		0x8000

#define M0_RAM_START	0x10088000
#define M0_RAM_LEN		0x2000

/*	0x20000000  M4 BUF 16K	*/
/*	0x20003FFF				*/
/*	0x20004000	M0 BUF	16K	*/
/*	0x20007FFF				*/
#define M4_BUF_START	0x20000000
#define M4_BUF_LEN		0x4000

#define M0_BUF_START	0x20004000
#define M0_BUF_LEN		0x4000

/*	0x20008000	M4 MBX 8K	*/
/*	0x20009FFF				*/
/*	0x2000A000	M0 MBX 8K	*/
/*	0x2000BFFF				*/
#define M4_MBX_START	0x20008000
#define M4_MBX_LEN		0x2000

#define M0_MBX_START	0x2000A000
#define M0_MBX_LEN		0x2000

#else 

/*******************************/
/* this is for the ram version */
/*******************************/
/*	0x10000000	M4 ROM 64K	*/
/*	0x1000FFFF				*/
/*	0x10010000	M4 RAM 32K	*/
/*	0x10017FFF				*/
#define M4_ROM_START	0x10000000
#define M4_ROM_LEN		0x10000

#define M4_RAM_START	0x10010000
#define M4_RAM_LEN		0x8000

/*	0x10080000	M0 ROM 32K	*/
/*	0x10087FFF				*/
/*	0x10088000 	M0 RAM 8K	*/
/*	0x10089FFF 				*/
#define M0_ROM_START	0x10080000
#define M0_ROM_LEN		0x8000

#define M0_RAM_START	0x10088000
#define M0_RAM_LEN		0x2000

/*	0x20000000  M4 BUF 16K	*/
/*	0x20003FFF				*/
/*	0x20004000	M0 BUF	16K	*/
/*	0x20007FFF				*/
#define M4_BUF_START	0x20000000
#define M4_BUF_LEN		0x4000

#define M0_BUF_START	0x20004000
#define M0_BUF_LEN		0x4000

/*	0x20008000	M4 MBX 8K	*/
/*	0x20009FFF				*/
/*	0x2000A000	M0 MBX 8K	*/
/*	0x2000BFFF				*/
#define M4_MBX_START	0x20008000
#define M4_MBX_LEN		0x2000

#define M0_MBX_START	0x2000A000
#define M0_MBX_LEN		0x2000

#endif /* ifdef EXT_FLASH */

/****************************************************/
/* END OF USER CONFIGURATION 						*/
/* DO NOT EDIT BELOW THIS LINE						*/
/****************************************************/

#define M4_IPC_TABLE	M4_MBX_START
#define M0_IPC_TABLE	M0_MBX_START

/* configure defines for local mailbox */
#if defined (CORE_M0) && (USE_M0_MAILBOX == YES)
	#define PROVIDE_M0_LOCAL_MBX (1)
#endif

#if defined (CORE_M4) && (USE_M4_MAILBOX == YES)
	#define PROVIDE_M4_LOCAL_MBX  (1)
#endif

#if defined PROVIDE_M0_LOCAL_MBX || PROVIDE_M4_LOCAL_MBX
	  #define LOCAL_MAILBOX_ENABLED (1)
#endif


#if defined (CORE_M0) && (USE_M4_MAILBOX == YES)
	#define PROVIDE_M0_REMOTE_MBX (1)
#endif

#if defined (CORE_M4) && (USE_M0_MAILBOX == YES)
	#define PROVIDE_M4_REMOTE_MBX (1)
#endif

#if defined PROVIDE_M0_REMOTE_MBX || PROVIDE_M4_REMOTE_MBX
	  #define REMOTE_MAILBOX_ENABLED (1)
#endif


#if(USE_MAILBOX_PARAMETER == YES)
	#define MBX_PARAM_DEFAULT ,0x0
#else
	#define MBX_PARAM_DEFAULT 
#endif

#define DUMMY_CALLBACK ,(mbxCallback_t) &dummyCallback

#if (USE_MAILBOX_CALLBACK == YES)	
	#define MBX_CALLBACK_DEFAULT DUMMY_CALLBACK
#else
	#define MBX_CALLBACK_DEFAULT
#endif

/****************************************************/
/* platform wise initialization functions			*/
/****************************************************/
void platformInit(void);



#endif /* __PLATFORM_CONFIG_H */

