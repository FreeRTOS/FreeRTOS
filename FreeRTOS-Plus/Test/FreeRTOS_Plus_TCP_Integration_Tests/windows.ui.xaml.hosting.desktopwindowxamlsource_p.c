

/* this ALWAYS GENERATED file contains the proxy stub code */


 /* File created by MIDL compiler version 8.01.0622 */
/* at Mon Jan 18 19:14:07 2038
 */
/* Compiler settings for ..\..\..\..\..\..\..\..\Program Files (x86)\Windows Kits\10\Include\10.0.18362.0\um\windows.ui.xaml.hosting.desktopwindowxamlsource.idl:
    Oicf, W1, Zp8, env=Win32 (32b run), target_arch=X86 8.01.0622 
    protocol : dce , ms_ext, c_ext, robust
    error checks: allocation ref bounds_check enum stub_data 
    VC __declspec() decoration level: 
         __declspec(uuid()), __declspec(selectany), __declspec(novtable)
         DECLSPEC_UUID(), MIDL_INTERFACE()
*/
/* @@MIDL_FILE_HEADING(  ) */

#if !defined(_M_IA64) && !defined(_M_AMD64) && !defined(_ARM_)


#if _MSC_VER >= 1200
#pragma warning(push)
#endif

#pragma warning( disable: 4211 )  /* redefine extern to static */
#pragma warning( disable: 4232 )  /* dllimport identity*/
#pragma warning( disable: 4024 )  /* array to pointer mapping*/
#pragma warning( disable: 4152 )  /* function/data pointer conversion in expression */
#pragma warning( disable: 4100 ) /* unreferenced arguments in x86 call */

#pragma optimize("", off ) 

#define USE_STUBLESS_PROXY


/* verify that the <rpcproxy.h> version is high enough to compile this file*/
#ifndef __REDQ_RPCPROXY_H_VERSION__
#define __REQUIRED_RPCPROXY_H_VERSION__ 475
#endif


#include "rpcproxy.h"
#ifndef __RPCPROXY_H_VERSION__
#error this stub requires an updated version of <rpcproxy.h>
#endif /* __RPCPROXY_H_VERSION__ */


#include "windows.ui.xaml.hosting.desktopwindowxamlsource.h"

#define TYPE_FORMAT_STRING_SIZE   3                                 
#define PROC_FORMAT_STRING_SIZE   1                                 
#define EXPR_FORMAT_STRING_SIZE   1                                 
#define TRANSMIT_AS_TABLE_SIZE    0            
#define WIRE_MARSHAL_TABLE_SIZE   0            

typedef struct _windows2Eui2Examl2Ehosting2Edesktopwindowxamlsource_MIDL_TYPE_FORMAT_STRING
    {
    short          Pad;
    unsigned char  Format[ TYPE_FORMAT_STRING_SIZE ];
    } windows2Eui2Examl2Ehosting2Edesktopwindowxamlsource_MIDL_TYPE_FORMAT_STRING;

typedef struct _windows2Eui2Examl2Ehosting2Edesktopwindowxamlsource_MIDL_PROC_FORMAT_STRING
    {
    short          Pad;
    unsigned char  Format[ PROC_FORMAT_STRING_SIZE ];
    } windows2Eui2Examl2Ehosting2Edesktopwindowxamlsource_MIDL_PROC_FORMAT_STRING;

typedef struct _windows2Eui2Examl2Ehosting2Edesktopwindowxamlsource_MIDL_EXPR_FORMAT_STRING
    {
    long          Pad;
    unsigned char  Format[ EXPR_FORMAT_STRING_SIZE ];
    } windows2Eui2Examl2Ehosting2Edesktopwindowxamlsource_MIDL_EXPR_FORMAT_STRING;


static const RPC_SYNTAX_IDENTIFIER  _RpcTransferSyntax = 
{{0x8A885D04,0x1CEB,0x11C9,{0x9F,0xE8,0x08,0x00,0x2B,0x10,0x48,0x60}},{2,0}};


extern const windows2Eui2Examl2Ehosting2Edesktopwindowxamlsource_MIDL_TYPE_FORMAT_STRING windows2Eui2Examl2Ehosting2Edesktopwindowxamlsource__MIDL_TypeFormatString;
extern const windows2Eui2Examl2Ehosting2Edesktopwindowxamlsource_MIDL_PROC_FORMAT_STRING windows2Eui2Examl2Ehosting2Edesktopwindowxamlsource__MIDL_ProcFormatString;
extern const windows2Eui2Examl2Ehosting2Edesktopwindowxamlsource_MIDL_EXPR_FORMAT_STRING windows2Eui2Examl2Ehosting2Edesktopwindowxamlsource__MIDL_ExprFormatString;



#if !defined(__RPC_WIN32__)
#error  Invalid build platform for this stub.
#endif
#if !(TARGET_IS_NT60_OR_LATER)
#error You need Windows Vista or later to run this stub because it uses these features:
#error   compiled for Windows Vista.
#error However, your C/C++ compilation flags indicate you intend to run this app on earlier systems.
#error This app will fail with the RPC_X_WRONG_STUB_VERSION error.
#endif


static const windows2Eui2Examl2Ehosting2Edesktopwindowxamlsource_MIDL_PROC_FORMAT_STRING windows2Eui2Examl2Ehosting2Edesktopwindowxamlsource__MIDL_ProcFormatString =
    {
        0,
        {

			0x0
        }
    };

static const windows2Eui2Examl2Ehosting2Edesktopwindowxamlsource_MIDL_TYPE_FORMAT_STRING windows2Eui2Examl2Ehosting2Edesktopwindowxamlsource__MIDL_TypeFormatString =
    {
        0,
        {
			NdrFcShort( 0x0 ),	/* 0 */

			0x0
        }
    };


/* Standard interface: __MIDL_itf_windows2Eui2Examl2Ehosting2Edesktopwindowxamlsource_0000_0000, ver. 0.0,
   GUID={0x00000000,0x0000,0x0000,{0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00}} */


/* Object interface: IUnknown, ver. 0.0,
   GUID={0x00000000,0x0000,0x0000,{0xC0,0x00,0x00,0x00,0x00,0x00,0x00,0x46}} */


/* Object interface: IDesktopWindowXamlSourceNative, ver. 0.0,
   GUID={0x3cbcf1bf,0x2f76,0x4e9c,{0x96,0xab,0xe8,0x4b,0x37,0x97,0x25,0x54}} */


/* Standard interface: __MIDL_itf_windows2Eui2Examl2Ehosting2Edesktopwindowxamlsource_0000_0001, ver. 0.0,
   GUID={0x00000000,0x0000,0x0000,{0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00}} */


/* Object interface: IDesktopWindowXamlSourceNative2, ver. 0.0,
   GUID={0xe3dcd8c7,0x3057,0x4692,{0x99,0xc3,0x7b,0x77,0x20,0xaf,0xda,0x31}} */


/* Standard interface: __MIDL_itf_windows2Eui2Examl2Ehosting2Edesktopwindowxamlsource_0000_0002, ver. 0.0,
   GUID={0x00000000,0x0000,0x0000,{0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00}} */

static const MIDL_STUB_DESC Object_StubDesc = 
    {
    0,
    NdrOleAllocate,
    NdrOleFree,
    0,
    0,
    0,
    0,
    0,
    windows2Eui2Examl2Ehosting2Edesktopwindowxamlsource__MIDL_TypeFormatString.Format,
    1, /* -error bounds_check flag */
    0x60001, /* Ndr library version */
    0,
    0x801026e, /* MIDL Version 8.1.622 */
    0,
    0,
    0,  /* notify & notify_flag routine table */
    0x1, /* MIDL flag */
    0, /* cs routines */
    0,   /* proxy/server info */
    0
    };

const CInterfaceProxyVtbl * const _windows2Eui2Examl2Ehosting2Edesktopwindowxamlsource_ProxyVtblList[] = 
{
    0
};

const CInterfaceStubVtbl * const _windows2Eui2Examl2Ehosting2Edesktopwindowxamlsource_StubVtblList[] = 
{
    0
};

PCInterfaceName const _windows2Eui2Examl2Ehosting2Edesktopwindowxamlsource_InterfaceNamesList[] = 
{
    0
};


#define _windows2Eui2Examl2Ehosting2Edesktopwindowxamlsource_CHECK_IID(n)	IID_GENERIC_CHECK_IID( _windows2Eui2Examl2Ehosting2Edesktopwindowxamlsource, pIID, n)

int __stdcall _windows2Eui2Examl2Ehosting2Edesktopwindowxamlsource_IID_Lookup( const IID * pIID, int * pIndex )
{
    UNREFERENCED_PARAMETER(pIID);
    UNREFERENCED_PARAMETER(pIndex);
    return 0;
}

const ExtendedProxyFileInfo windows2Eui2Examl2Ehosting2Edesktopwindowxamlsource_ProxyFileInfo = 
{
    (PCInterfaceProxyVtblList *) & _windows2Eui2Examl2Ehosting2Edesktopwindowxamlsource_ProxyVtblList,
    (PCInterfaceStubVtblList *) & _windows2Eui2Examl2Ehosting2Edesktopwindowxamlsource_StubVtblList,
    (const PCInterfaceName * ) & _windows2Eui2Examl2Ehosting2Edesktopwindowxamlsource_InterfaceNamesList,
    0, /* no delegation */
    & _windows2Eui2Examl2Ehosting2Edesktopwindowxamlsource_IID_Lookup, 
    0,
    2,
    0, /* table of [async_uuid] interfaces */
    0, /* Filler1 */
    0, /* Filler2 */
    0  /* Filler3 */
};
#pragma optimize("", on )
#if _MSC_VER >= 1200
#pragma warning(pop)
#endif


#endif /* !defined(_M_IA64) && !defined(_M_AMD64) && !defined(_ARM_) */

