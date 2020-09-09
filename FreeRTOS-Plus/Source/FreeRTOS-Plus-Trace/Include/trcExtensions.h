/*******************************************************************************
 * Trace Recorder Library for Tracealyzer v4.3.11
 * Percepio AB, www.percepio.com
 *
 * trcExtensions.h
 *
 * The extension interface of the recorder library, allowing for tracing
 * function calls to any API without modifications. All that is needed is a
 * single #include line in the .c files calling the API.
 *
 * This can be used to provide more detailed traces, including calls to e.g.
 * middleware, drivers or important APIs in your application code. This can be
 * applied selectively to specified functions and may include selected
 * parameters as well as the return value.
 *
 * Unlike the "User Event" concept, an extension is intended for systematic use
 * and can benefit from all powerful features in Tracealyzer via host-side XML
 * files that configure how Tracealyzer should interpret each event.
 *
 * Extensions are self-contained and easy to integrate, which makes them
 * convenient for distribution. Software vendors can thus develop such
 * extensions and provide trace support for their users.
 *
 * An extension consists of two files:
 *
 *  - An extension header file (e.g. "api.tzext.h") - this defines how to
 *  trace the API function calls.
 *
 *  - An XML file for the Tracealyzer application (e.g. "api-v1.0.0.xml").
 *  This needs to match the tracing setup in your extension header file.
 *
 *
 * USAGE
 *
 * This description assumes you already have the extension files for the APIs you
 * like to trace. To include them, follow these steps:
 *
 * 1. Update trcExtensions.h with respect to:
 *
 *    1.1. TRC_CFG_EXTENSION_COUNT: The number of extensions to enable (max 4).
 *
 *    1.2. The name(s) of the extension header file(s) to include.
 *
 *    1.3. The Extension Prefix, i.e., the first part of the definition names
 *         used in each header file.
 *
 * 2. Add #include "trcExtensions.h" in all .c files calling the API:
 *
 *    #include ...
 *    #include "api.h"  // The API you like to trace
 *    #include ...
 *    #include "trcExtensions.h"
 *
 *    We recommend to put this as the LAST #include statement.
 *
 *    HOWEVER, don't include "trcExtensions.h" in the .c files containing the
 *    functions you intend to trace. The compiler will then complain about
 *    multiple definitions of the trace wrapper function.
 *
 * 3. Copy the extension XML file to the "Tracealyzer 4/cfg" folder.
 *    On Windows this is typically
 *
 *    C:\Program Files\Percepio\Tracealyzer 4\cfg
 *
 *
 * HOW IT WORKS
 *
 * By including "trcExtensions.h" in your .c files, the preprocessor will
 * redefine all calls of the functions specified in the extension header file.
 * Calls to those functions will now instead call the "trace wrapper functions"
 * defined in the extension header. The trace wrapper functions then call the
 * original function as well as the trace recorder library.
 *
 * call foo(a) ----> foo__trace(a) -----> foo(a)
 *                                 -----> trace recorder library
 *
 * Note that the trace wrapper function should have the same declaration as the
 * original function (apart from the name) and also returns any return value
 * back to the original caller. So functionally this is completely transparent.
 *
 * This works also for calls via function pointers, as the assignments of the
 * function pointers will be affected, so the function pointers will point to
 * the trace wrapper function.
 *
 * It even works when calling binary libraries, since only the calling code
 * is modified, not the API itself.
 *
 * Extensions include a version code (Major.Minor.Patch), which is registered
 * in the trace and also part of the XML file name. This way, Tracealyzer
 * automatically finds the matching XML file, even if you open a old trace
 * recorded using a earlier version of the extension (e.g. if the API has
 * changed).
 *
 * LIMITATIONS
 *
 * The main limitation of this automatic approach is that it only allows for
 * tracing call between different .c files. Moreover, you can't trace multiple
 * APIs with calls between them. This since the calling file must include
 * trcExtensions.h, while the called file must NOT include this.
 *
 * It is however possible to get around this limitation. You need to add
 * #undef lines for each affected function to locally disable the redefinition,
 * and modify each function call to instead call the trace wrapper function.
 *
 *   #include "trcExtensions.h"
 *   #undef foo
 *   ...
 *   void foo(int a)
 *   {
 *     ...
 *   }
 *   ...
 *   foo__trace(a); // in another function - call foo and trace it
 *
 * These changes can remain in your code if you like, as the trace wrappers
 * works even if the recorder is disabled.
 *
 * MAKING YOUR OWN EXTENSIONS
 *
 * Examples are found in the extensions directory. We recommend that you start
 * by looking at aws_secure_sockets files (.h and .xml) that provides a basic
 * example. The aws_wifi files provides a more advanced example.
 * The header files include detailed documentation about how to design them,
 *
 * The XML files should have the same name as specified in the NAME property
 * in the header file, followed by the version, i.e.
 *
 * <NAME>-v<VERSION_MAJOR>.<<VERSION_MINOR>.<VERSION_PATCH>.xml
 *
 * Documentation for the XML file format is not yet available, but is under
 * development.
 *
 *
 * Terms of Use
 * This file is part of the trace recorder library (RECORDER), which is the
 * intellectual property of Percepio AB (PERCEPIO) and provided under a
 * license as follows.
 * The RECORDER may be used free of charge for the purpose of recording data
 * intended for analysis in PERCEPIO products. It may not be used or modified
 * for other purposes without explicit permission from PERCEPIO.
 * You may distribute the RECORDER in its original source code form, assuming
 * this text (terms of use, disclaimer, copyright notice) is unchanged. You are
 * allowed to distribute the RECORDER with minor modifications intended for
 * configuration or porting of the RECORDER, e.g., to allow using it on a
 * specific processor, processor family or with a specific communication
 * interface. Any such modifications should be documented directly below
 * this comment block.
 *
 * Disclaimer
 * The RECORDER is being delivered to you AS IS and PERCEPIO makes no warranty
 * as to its use or performance. PERCEPIO does not and cannot warrant the
 * performance or results you may obtain by using the RECORDER or documentation.
 * PERCEPIO make no warranties, express or implied, as to noninfringement of
 * third party rights, merchantability, or fitness for any particular purpose.
 * In no event will PERCEPIO, its technology partners, or distributors be liable
 * to you for any consequential, incidental or special damages, including any
 * lost profits or lost savings, even if a representative of PERCEPIO has been
 * advised of the possibility of such damages, or for any claim by any third
 * party. Some jurisdictions do not allow the exclusion or limitation of
 * incidental, consequential or special damages, or the exclusion of implied
 * warranties or limitations on how long an implied warranty may last, so the
 * above limitations may not apply to you.
 *
 * Tabs are used for indent in this file (1 tab = 4 spaces)
 *
 * Copyright Percepio AB, 2018.
 * www.percepio.com
 ******************************************************************************/

#ifndef TRCEXTENSIONS_H_
#define TRCEXTENSIONS_H_

#include "trcRecorder.h"

/******************************************************************************
 * TRC_CFG_EXTENSION_COUNT
 *
 * Defines the number of extensions included in the trace. Maximum 4 extensions
 * can be included.
 *
 * Default value is 0 (extension support disabled).
 *
 *****************************************************************************/
#define TRC_CFG_EXTENSION_COUNT 0

/******************************************************************************
 * TRC_CFG_EXT_MAX_NAME_LEN
 *
 * Defines the maximum length of extension name(s), i.e. the <EXTENSION>_NAME
 * macro(s) in trcExtensions.h.
 *
 * This value should will by rounded up to the nearest multiple of 4, and must
 * not be zero. To disable extension support, see TRC_CFG_EXTENSION_COUNT.
 *
 * It is important that this setting is large enough so extension names are
 * not truncated, otherwise the host-side Tracealyzer application won't be able
 * to find the corresponding XML file.
 *
 * You may adjust this to reduce memory usage, or increase it to allow for
 * longer extension names.
 *
 * Default value is 20.
 *****************************************************************************/
#define TRC_CFG_EXT_MAX_NAME_LEN	20

/******************************************************************************
 * TRC_EXTENSION_EVENTCODE_BASE
 *
 * The first event code used for the Extension system. This will be the first
 * event code of the first extension, and other event codes are relative to
 * this. This can be modified but this is normally not required.
 *****************************************************************************/
#define TRC_EXTENSION_EVENTCODE_BASE 256

/*** Included Extensions ******************************************************
 *
 * Below you specify what extensions to include. For each
 * extension you must define:
 *
 * - HEADER: The header file that defines the trace extension.
 *
 * - EXTENSION_PREFIX: The first part of the HEADER definition names.
 *
 *****************************************************************************/
#define TRC_EXT1_HEADER 	"aws_secure_sockets.tzext.h"
#define TRC_EXT1_PREFIX 	TRC_EXT_SOCKETS

#define TRC_EXT2_HEADER 	"aws_wifi.tzext.h"
#define TRC_EXT2_PREFIX 	TRC_EXT_WIFI

#define TRC_EXT3_HEADER		"Here you specify the header file for Extensions 3."
#define TRC_EXT3_PREFIX		NOT_DEFINED

#define TRC_EXT4_HEADER		"Here you specify the header file for Extensions 4."
#define TRC_EXT4_PREFIX		NOT_DEFINED

/*** Don't modify below ******************************************************/

#define ROUNDUP4(n) (4*((n+3)/4))

typedef struct{
	uint16_t firstEventCode;
	uint16_t lastEventCode;
	uint16_t patchVersion;
	uint8_t minorVersion;
	uint8_t majorVersion;
	char name[ROUNDUP4(TRC_CFG_EXT_MAX_NAME_LEN)];
} PSFExtensionEntryType;

typedef struct{
	uint16_t extensionEntryCount;
	uint16_t baseEventCode;
#if (TRC_CFG_EXTENSION_COUNT > 0)
	uint8_t extensionEntryNameMaxLength;
	uint8_t extensionEntrySize;
	PSFExtensionEntryType extension[TRC_CFG_EXTENSION_COUNT];
#endif
} PSFExtensionInfoType;


extern PSFExtensionInfoType PSFExtensionInfo;

#define CAT(a, ...) PRIMITIVE_CAT(a, __VA_ARGS__)
#define PRIMITIVE_CAT(a, ...) a ## __VA_ARGS__

#define TRC_EXT_BASECODE (PSFExtensionInfo.extension[TRC_EXT_NUMBER-1].firstEventCode)

#if (TRC_CFG_EXTENSION_COUNT >= 1)
	#ifdef TRC_EXT1_HEADER
		#define TRC_EXT_NUMBER 1
		#include TRC_EXT1_HEADER
		#undef TRC_EXT_NUMBER
	#endif
#endif

#if (TRC_CFG_EXTENSION_COUNT >= 2)
	#ifdef TRC_EXT2_HEADER
		#define TRC_EXT_NUMBER 2
		#include TRC_EXT2_HEADER
		#undef TRC_EXT_NUMBER
	#endif
#endif

#if (TRC_CFG_EXTENSION_COUNT >= 3)
	#ifdef TRC_EXT3_HEADER
		#define TRC_EXT_NUMBER 3
		#include TRC_EXT3_HEADER
		#undef TRC_EXT_NUMBER
	#endif
#endif

#if (TRC_CFG_EXTENSION_COUNT == 4)
	#ifdef TRC_EXT3_HEADER
		#define TRC_EXT_NUMBER 4
		#include TRC_EXT4_HEADER
		#undef TRC_EXT_NUMBER
	#endif
#endif

#define TRC_EXT1_COUNT CAT(TRC_EXT1_PREFIX, _COUNT)
#define TRC_EXT2_COUNT CAT(TRC_EXT2_PREFIX, _COUNT)
#define TRC_EXT3_COUNT CAT(TRC_EXT3_PREFIX, _COUNT)
#define TRC_EXT4_COUNT CAT(TRC_EXT4_PREFIX, _COUNT)

#define TRC_EXT1_NAME CAT(TRC_EXT1_PREFIX, _NAME)
#define TRC_EXT2_NAME CAT(TRC_EXT2_PREFIX, _NAME)
#define TRC_EXT3_NAME CAT(TRC_EXT3_PREFIX, _NAME)
#define TRC_EXT4_NAME CAT(TRC_EXT4_PREFIX, _NAME)

#define TRC_EXT1_VERSION_MAJOR CAT(TRC_EXT1_PREFIX, _VERSION_MAJOR)
#define TRC_EXT2_VERSION_MAJOR CAT(TRC_EXT2_PREFIX, _VERSION_MAJOR)
#define TRC_EXT3_VERSION_MAJOR CAT(TRC_EXT3_PREFIX, _VERSION_MAJOR)
#define TRC_EXT4_VERSION_MAJOR CAT(TRC_EXT4_PREFIX, _VERSION_MAJOR)

#define TRC_EXT1_VERSION_MINOR CAT(TRC_EXT1_PREFIX, _VERSION_MINOR)
#define TRC_EXT2_VERSION_MINOR CAT(TRC_EXT2_PREFIX, _VERSION_MINOR)
#define TRC_EXT3_VERSION_MINOR CAT(TRC_EXT3_PREFIX, _VERSION_MINOR)
#define TRC_EXT4_VERSION_MINOR CAT(TRC_EXT4_PREFIX, _VERSION_MINOR)

#define TRC_EXT1_VERSION_PATCH CAT(TRC_EXT1_PREFIX, _VERSION_PATCH)
#define TRC_EXT2_VERSION_PATCH CAT(TRC_EXT2_PREFIX, _VERSION_PATCH)
#define TRC_EXT3_VERSION_PATCH CAT(TRC_EXT3_PREFIX, _VERSION_PATCH)
#define TRC_EXT4_VERSION_PATCH CAT(TRC_EXT4_PREFIX, _VERSION_PATCH)

#if ((TRC_CFG_EXTENSION_COUNT > 4) || (TRC_CFG_EXTENSION_COUNT < 0))
	#error "TRC_CFG_EXTENSION_COUNT must be in range [0..4]"
#endif

#if (TRC_CFG_EXTENSION_COUNT == 0)
#define TRC_EXTENSIONS_DATA
#endif

#if (TRC_CFG_EXTENSION_COUNT == 1)
#define TRC_EXTENSIONS_DATA \
{ \
	{	TRC_EXTENSION_EVENTCODE_BASE, \
		TRC_EXTENSION_EVENTCODE_BASE + TRC_EXT1_COUNT-1, \
		TRC_EXT1_VERSION_PATCH, \
		TRC_EXT1_VERSION_MINOR, \
		TRC_EXT1_VERSION_MAJOR, \
		TRC_EXT1_NAME } \
}
#endif

#if (TRC_CFG_EXTENSION_COUNT == 2)
#define TRC_EXTENSIONS_DATA \
{ \
	{	TRC_EXTENSION_EVENTCODE_BASE, \
		TRC_EXTENSION_EVENTCODE_BASE + TRC_EXT1_COUNT-1, \
		TRC_EXT1_VERSION_PATCH, \
		TRC_EXT1_VERSION_MINOR, \
		TRC_EXT1_VERSION_MAJOR, \
		TRC_EXT1_NAME } \
	,{	TRC_EXTENSION_EVENTCODE_BASE + TRC_EXT1_COUNT, \
		TRC_EXTENSION_EVENTCODE_BASE + TRC_EXT1_COUNT + TRC_EXT2_COUNT-1, \
		TRC_EXT2_VERSION_PATCH, \
		TRC_EXT2_VERSION_MINOR, \
		TRC_EXT2_VERSION_MAJOR, \
		TRC_EXT2_NAME } \
}
#endif

#if (TRC_CFG_EXTENSION_COUNT == 3)
#define TRC_EXTENSIONS_DATA \
{ \
	{	TRC_EXTENSION_EVENTCODE_BASE, \
		TRC_EXTENSION_EVENTCODE_BASE + TRC_EXT1_COUNT-1, \
		TRC_EXT1_VERSION_PATCH, \
		TRC_EXT1_VERSION_MINOR, \
		TRC_EXT1_VERSION_MAJOR, \
		TRC_EXT1_NAME } \
	,{	TRC_EXTENSION_EVENTCODE_BASE + TRC_EXT1_COUNT, \
		TRC_EXTENSION_EVENTCODE_BASE + TRC_EXT1_COUNT + TRC_EXT2_COUNT-1, \
		TRC_EXT2_VERSION_PATCH, \
		TRC_EXT2_VERSION_MINOR, \
		TRC_EXT2_VERSION_MAJOR, \
		TRC_EXT2_NAME } \
	,{	TRC_EXTENSION_EVENTCODE_BASE + TRC_EXT1_COUNT + TRC_EXT2_COUNT, \
		TRC_EXTENSION_EVENTCODE_BASE + TRC_EXT1_COUNT + TRC_EXT2_COUNT + TRC_EXT3_COUNT - 1, \
		TRC_EXT3_VERSION_PATCH, \
		TRC_EXT3_VERSION_MINOR, \
		TRC_EXT3_VERSION_MAJOR, \
		TRC_EXT3_NAME } \
}
#endif
#if (TRC_CFG_EXTENSION_COUNT == 4)
#define TRC_EXTENSIONS_DATA \
{ \
	{	TRC_EXTENSION_EVENTCODE_BASE, \
		TRC_EXTENSION_EVENTCODE_BASE + TRC_EXT1_COUNT-1, \
		TRC_EXT1_VERSION_PATCH, \
		TRC_EXT1_VERSION_MINOR, \
		TRC_EXT1_VERSION_MAJOR, \
		TRC_EXT1_NAME } \
	,{	TRC_EXTENSION_EVENTCODE_BASE + TRC_EXT1_COUNT, \
		TRC_EXTENSION_EVENTCODE_BASE + TRC_EXT1_COUNT + TRC_EXT2_COUNT-1, \
		TRC_EXT2_VERSION_PATCH, \
		TRC_EXT2_VERSION_MINOR, \
		TRC_EXT2_VERSION_MAJOR, \
		TRC_EXT2_NAME } \
	,{	TRC_EXTENSION_EVENTCODE_BASE + TRC_EXT1_COUNT + TRC_EXT2_COUNT, \
		TRC_EXTENSION_EVENTCODE_BASE + TRC_EXT1_COUNT + TRC_EXT2_COUNT + TRC_EXT3_COUNT - 1, \
		TRC_EXT3_VERSION_PATCH, \
		TRC_EXT3_VERSION_MINOR, \
		TRC_EXT3_VERSION_MAJOR, \
		TRC_EXT3_NAME } \
	,{	TRC_EXTENSION_EVENTCODE_BASE + TRC_EXT1_COUNT + TRC_EXT2_COUNT + TRC_EXT3_COUNT, \
		TRC_EXTENSION_EVENTCODE_BASE + TRC_EXT1_COUNT + TRC_EXT2_COUNT + TRC_EXT3_COUNT + TRC_EXT4_COUNT- 1, \
		TRC_EXT4_VERSION_PATCH, \
		TRC_EXT4_VERSION_MINOR, \
		TRC_EXT4_VERSION_MAJOR, \
		TRC_EXT4_NAME } \
}
#endif

#if (TRC_CFG_EXTENSION_COUNT > 0)
#define TRC_EXTENSION_INFO {TRC_CFG_EXTENSION_COUNT, TRC_EXTENSION_EVENTCODE_BASE, ROUNDUP4(TRC_CFG_EXT_MAX_NAME_LEN), sizeof(PSFExtensionEntryType), TRC_EXTENSIONS_DATA}
#else
#define TRC_EXTENSION_INFO {TRC_CFG_EXTENSION_COUNT, TRC_EXTENSION_EVENTCODE_BASE}
#endif

#endif /* TRCEXTENSIONS_H_ */
