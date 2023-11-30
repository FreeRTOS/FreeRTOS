#ifndef __PLATFORM_CHECK_H
#define __PLATFORM_CHECK_H

#warning "************ PLATFORM CONFIG ************"

/* this is used to check the build platform */
#if (PLATFORM == NXP_VALIDATION_BOARD) 
	#warning "*** Building for NXP VALIDATION BOARD ***"	
#elif (PLATFORM == HITEX_A2_BOARD)
	#warning "Building for HITEX LPC4350EVA-2 platform"	
#else
	#error "Platform not supported, check platform_config.h"
#endif

/* this is to ensure memory ranges are defined */
#ifndef M4_ROM_START
	#error "M4_ROM_START not defined, check platform_config.h"
#endif
#ifndef M4_ROM_LEN
	#error "M4_ROM_LEN not defined, check platform_config.h"
#endif
#ifndef M4_RAM_START
	#error "M4_RAM_START not defined, check platform_config.h"
#endif
#ifndef M4_RAM_LEN
	#error "M4_RAM_LEN not defined, check platform_config.h"
#endif

#ifndef M0_ROM_START
	#error "M0_ROM_START not defined, check platform_config.h"
#endif
#ifndef M0_ROM_LEN
	#error "M0_ROM_LEN not defined, check platform_config.h"
#endif
#ifndef M0_RAM_START
	#error "M0_RAM_START not defined, check platform_config.h"
#endif
#ifndef M0_RAM_LEN
	#error "M0_RAM_LEN not defined, check platform_config.h"
#endif

/* feedback for mailboxes usage */

/* configuration checks for M0 */
#ifdef CORE_M4

#if (USE_M4_MAILBOX == YES)

	#warning "*** M4 mailbox: YES ***"

	#if (USE_MAILBOX_PARAMETER == YES)
		#warning "*** M4 mailbox parameter: YES ***"
	#elif (USE_MAILBOX_PARAMETER == NO)
		#warning "*** M4 mailbox parameter: NO ***"
	#else 
		#error "*** Specify if M4 mailbox parameter is required (YES/NO) ***"
	#endif
	
	#if (USE_MAILBOX_CALLBACK == YES)
		#warning "*** M4 mailbox callback: YES ***"
	#elif (USE_MAILBOX_CALLBACK == NO)
		#warning "*** M4 mailbox callback: NO ***"
	#else 
		#error "*** Specify if M4 mailbox callback is required (YES/NO) ***"
	#endif

#elif (USE_M4_MAILBOX == NO)
	#warning "*** M4 mailbox: NO ***"
#else 
	#error "*** Specify if M4 mailbox is required (YES/NO) ***"
#endif

#if (INITIALIZE_M0_IMAGE == YES) 
	#warning "*** M4 should download the M0 image: YES ***"
#elif (INITIALIZE_M0_IMAGE == NO)
	#warning "*** M4 should download the M0 image: NO ***"
#else
	#error "*** Specify if M4 should initialize the M0 image (YES/NO) ***"
#endif

/* check the build rules */
#if (USE_EXT_FLASH == YES)
	#warning "*** Building with external flash support: YES ***"
#elif (USE_EXT_FLASH == NO)
	#warning "*** Building with external flash support: NO ***"
#endif

#if (USE_EXT_STATIC_MEM == YES)
	#warning "*** Building with external static memory support: YES ***"
#elif (USE_EXT_STATIC_MEM == NO)
	#warning "*** Building with external static memory support: NO ***"
#endif

#if (USE_EXT_DYNAMIC_MEM == YES)
	#warning "*** Building for external dynamic memory support: YES ***"
#elif (USE_EXT_DYNAMIC_MEM == NO)
	#warning "*** Building for external dynamic memory support: NO ***"
#endif
	
#endif	/* CORE_M4 */

/* configuration checks for M0 */
#ifdef CORE_M0

#if (USE_M0_MAILBOX == YES)
	
	#warning "*** M0 mailbox: YES ***"

	#if (USE_MAILBOX_PARAMETER == YES)
		#warning "*** M0 mailbox parameter: YES ***"
	#elif (USE_MAILBOX_PARAMETER == NO)
		#warning "*** M0 mailbox parameter: NO ***"
	#else 
		#error "*** Specify if M0 mailbox parameter is required (YES/NO) ***"
	#endif
	
	#if (USE_MAILBOX_CALLBACK == YES)
		#warning "*** M0 mailbox callback: YES ***"
	#elif (USE_MAILBOX_CALLBACK == NO)
		#warning "*** M0 mailbox callback: NO ***"
	#else 
		#error "*** Specify if M0 mailbox callback is required (YES/NO) ***"
	#endif

#elif (USE_M0_MAILBOX == NO)
	#warning "*** M0 mailbox: NO ***"
#else 
	#error "*** Specify if M0 mailbox is required (YES/NO) ***"
#endif



#endif	 /* CORE_M0 */

#warning "************ PLATFORM CONFIG ************"

#endif /* platform check */



