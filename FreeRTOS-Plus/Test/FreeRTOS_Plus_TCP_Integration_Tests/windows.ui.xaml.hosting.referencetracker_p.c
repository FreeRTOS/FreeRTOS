

/* this ALWAYS GENERATED file contains the proxy stub code */


 /* File created by MIDL compiler version 8.01.0622 */
/* at Mon Jan 18 19:14:07 2038
 */
/* Compiler settings for ..\..\..\..\..\..\..\..\Program Files (x86)\Windows Kits\10\Include\10.0.18362.0\um\windows.ui.xaml.hosting.referencetracker.idl:
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


#include "windows.ui.xaml.hosting.referencetracker.h"

#define TYPE_FORMAT_STRING_SIZE   3                                 
#define PROC_FORMAT_STRING_SIZE   1                                 
#define EXPR_FORMAT_STRING_SIZE   1                                 
#define TRANSMIT_AS_TABLE_SIZE    0            
#define WIRE_MARSHAL_TABLE_SIZE   0            

typedef struct _windows2Eui2Examl2Ehosting2Ereferencetracker_MIDL_TYPE_FORMAT_STRING
    {
    short          Pad;
    unsigned char  Format[ TYPE_FORMAT_STRING_SIZE ];
    } windows2Eui2Examl2Ehosting2Ereferencetracker_MIDL_TYPE_FORMAT_STRING;

typedef struct _windows2Eui2Examl2Ehosting2Ereferencetracker_MIDL_PROC_FORMAT_STRING
    {
    short          Pad;
    unsigned char  Format[ PROC_FORMAT_STRING_SIZE ];
    } windows2Eui2Examl2Ehosting2Ereferencetracker_MIDL_PROC_FORMAT_STRING;

typedef struct _windows2Eui2Examl2Ehosting2Ereferencetracker_MIDL_EXPR_FORMAT_STRING
    {
    long          Pad;
    unsigned char  Format[ EXPR_FORMAT_STRING_SIZE ];
    } windows2Eui2Examl2Ehosting2Ereferencetracker_MIDL_EXPR_FORMAT_STRING;


static const RPC_SYNTAX_IDENTIFIER  _RpcTransferSyntax = 
{{0x8A885D04,0x1CEB,0x11C9,{0x9F,0xE8,0x08,0x00,0x2B,0x10,0x48,0x60}},{2,0}};


extern const windows2Eui2Examl2Ehosting2Ereferencetracker_MIDL_TYPE_FORMAT_STRING windows2Eui2Examl2Ehosting2Ereferencetracker__MIDL_TypeFormatString;
extern const windows2Eui2Examl2Ehosting2Ereferencetracker_MIDL_PROC_FORMAT_STRING windows2Eui2Examl2Ehosting2Ereferencetracker__MIDL_ProcFormatString;
extern const windows2Eui2Examl2Ehosting2Ereferencetracker_MIDL_EXPR_FORMAT_STRING windows2Eui2Examl2Ehosting2Ereferencetracker__MIDL_ExprFormatString;



#if !defined(__RPC_WIN32__)
#error  Invalid build platform for this stub.
#endif
#if !(TARGET_IS_NT60_OR_LATER)
#error You need Windows Vista or later to run this stub because it uses these features:
#error   compiled for Windows Vista.
#error However, your C/C++ compilation flags indicate you intend to run this app on earlier systems.
#error This app will fail with the RPC_X_WRONG_STUB_VERSION error.
#endif


static const windows2Eui2Examl2Ehosting2Ereferencetracker_MIDL_PROC_FORMAT_STRING windows2Eui2Examl2Ehosting2Ereferencetracker__MIDL_ProcFormatString =
    {
        0,
        {

			0x0
        }
    };

static const windows2Eui2Examl2Ehosting2Ereferencetracker_MIDL_TYPE_FORMAT_STRING windows2Eui2Examl2Ehosting2Ereferencetracker__MIDL_TypeFormatString =
    {
        0,
        {
			NdrFcShort( 0x0 ),	/* 0 */

			0x0
        }
    };


/* Standard interface: __MIDL_itf_windows2Eui2Examl2Ehosting2Ereferencetracker_0000_0000, ver. 0.0,
   GUID={0x00000000,0x0000,0x0000,{0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00}} */


/* Object interface: IUnknown, ver. 0.0,
   GUID={0x00000000,0x0000,0x0000,{0xC0,0x00,0x00,0x00,0x00,0x00,0x00,0x46}} */


/* Object interface: IReferenceTrackerTarget, ver. 0.0,
   GUID={0x64bd43f8,0xbfee,0x4ec4,{0xb7,0xeb,0x29,0x35,0x15,0x8d,0xae,0x21}} */


/* Object interface: IReferenceTracker, ver. 0.0,
   GUID={0x11d3b13a,0x180e,0x4789,{0xa8,0xbe,0x77,0x12,0x88,0x28,0x93,0xe6}} */


/* Object interface: IReferenceTrackerManager, ver. 0.0,
   GUID={0x3cf184b4,0x7ccb,0x4dda,{0x84,0x55,0x7e,0x6c,0xe9,0x9a,0x32,0x98}} */


/* Object interface: IFindReferenceTargetsCallback, ver. 0.0,
   GUID={0x04b3486c,0x4687,0x4229,{0x8d,0x14,0x50,0x5a,0xb5,0x84,0xdd,0x88}} */


/* Standard interface: __MIDL_itf_windows2Eui2Examl2Ehosting2Ereferencetracker_0000_0004, ver. 0.0,
   GUID={0x00000000,0x0000,0x0000,{0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00}} */


/* Object interface: IReferenceTrackerHost, ver. 0.0,
   GUID={0x29a71c6a,0x3c42,0x4416,{0xa3,0x9d,0xe2,0x82,0x5a,0x07,0xa7,0x73}} */


/* Standard interface: __MIDL_itf_windows2Eui2Examl2Ehosting2Ereferencetracker_0000_0005, ver. 0.0,
   GUID={0x00000000,0x0000,0x0000,{0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00}} */


/* Object interface: IReferenceTrackerExtension, ver. 0.0,
   GUID={0x4e897caa,0x59d5,0x4613,{0x8f,0x8c,0xf7,0xeb,0xd1,0xf3,0x99,0xb0}} */


/* Standard interface: __MIDL_itf_windows2Eui2Examl2Ehosting2Ereferencetracker_0000_0006, ver. 0.0,
   GUID={0x00000000,0x0000,0x0000,{0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00}} */


/* Object interface: ITrackerOwner, ver. 0.0,
   GUID={0xeb24c20b,0x9816,0x4ac7,{0x8c,0xff,0x36,0xf6,0x7a,0x11,0x8f,0x4e}} */


/* Standard interface: __MIDL_itf_windows2Eui2Examl2Ehosting2Ereferencetracker_0000_0007, ver. 0.0,
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
    windows2Eui2Examl2Ehosting2Ereferencetracker__MIDL_TypeFormatString.Format,
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

const CInterfaceProxyVtbl * const _windows2Eui2Examl2Ehosting2Ereferencetracker_ProxyVtblList[] = 
{
    0
};

const CInterfaceStubVtbl * const _windows2Eui2Examl2Ehosting2Ereferencetracker_StubVtblList[] = 
{
    0
};

PCInterfaceName const _windows2Eui2Examl2Ehosting2Ereferencetracker_InterfaceNamesList[] = 
{
    0
};


#define _windows2Eui2Examl2Ehosting2Ereferencetracker_CHECK_IID(n)	IID_GENERIC_CHECK_IID( _windows2Eui2Examl2Ehosting2Ereferencetracker, pIID, n)

int __stdcall _windows2Eui2Examl2Ehosting2Ereferencetracker_IID_Lookup( const IID * pIID, int * pIndex )
{
    UNREFERENCED_PARAMETER(pIID);
    UNREFERENCED_PARAMETER(pIndex);
    return 0;
}

const ExtendedProxyFileInfo windows2Eui2Examl2Ehosting2Ereferencetracker_ProxyFileInfo = 
{
    (PCInterfaceProxyVtblList *) & _windows2Eui2Examl2Ehosting2Ereferencetracker_ProxyVtblList,
    (PCInterfaceStubVtblList *) & _windows2Eui2Examl2Ehosting2Ereferencetracker_StubVtblList,
    (const PCInterfaceName * ) & _windows2Eui2Examl2Ehosting2Ereferencetracker_InterfaceNamesList,
    0, /* no delegation */
    & _windows2Eui2Examl2Ehosting2Ereferencetracker_IID_Lookup, 
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

