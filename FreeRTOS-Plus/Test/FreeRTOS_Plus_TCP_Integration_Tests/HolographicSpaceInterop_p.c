

/* this ALWAYS GENERATED file contains the proxy stub code */


 /* File created by MIDL compiler version 8.01.0622 */
/* at Mon Jan 18 19:14:07 2038
 */
/* Compiler settings for ..\..\..\..\..\..\..\..\Program Files (x86)\Windows Kits\10\Include\10.0.18362.0\um\HolographicSpaceInterop.idl:
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


#include "HolographicSpaceInterop.h"

#define TYPE_FORMAT_STRING_SIZE   71                                
#define PROC_FORMAT_STRING_SIZE   49                                
#define EXPR_FORMAT_STRING_SIZE   1                                 
#define TRANSMIT_AS_TABLE_SIZE    0            
#define WIRE_MARSHAL_TABLE_SIZE   1            

typedef struct _HolographicSpaceInterop_MIDL_TYPE_FORMAT_STRING
    {
    short          Pad;
    unsigned char  Format[ TYPE_FORMAT_STRING_SIZE ];
    } HolographicSpaceInterop_MIDL_TYPE_FORMAT_STRING;

typedef struct _HolographicSpaceInterop_MIDL_PROC_FORMAT_STRING
    {
    short          Pad;
    unsigned char  Format[ PROC_FORMAT_STRING_SIZE ];
    } HolographicSpaceInterop_MIDL_PROC_FORMAT_STRING;

typedef struct _HolographicSpaceInterop_MIDL_EXPR_FORMAT_STRING
    {
    long          Pad;
    unsigned char  Format[ EXPR_FORMAT_STRING_SIZE ];
    } HolographicSpaceInterop_MIDL_EXPR_FORMAT_STRING;


static const RPC_SYNTAX_IDENTIFIER  _RpcTransferSyntax = 
{{0x8A885D04,0x1CEB,0x11C9,{0x9F,0xE8,0x08,0x00,0x2B,0x10,0x48,0x60}},{2,0}};


extern const HolographicSpaceInterop_MIDL_TYPE_FORMAT_STRING HolographicSpaceInterop__MIDL_TypeFormatString;
extern const HolographicSpaceInterop_MIDL_PROC_FORMAT_STRING HolographicSpaceInterop__MIDL_ProcFormatString;
extern const HolographicSpaceInterop_MIDL_EXPR_FORMAT_STRING HolographicSpaceInterop__MIDL_ExprFormatString;


extern const MIDL_STUB_DESC Object_StubDesc;


extern const MIDL_SERVER_INFO IHolographicSpaceInterop_ServerInfo;
extern const MIDL_STUBLESS_PROXY_INFO IHolographicSpaceInterop_ProxyInfo;


extern const USER_MARSHAL_ROUTINE_QUADRUPLE UserMarshalRoutines[ WIRE_MARSHAL_TABLE_SIZE ];

#if !defined(__RPC_WIN32__)
#error  Invalid build platform for this stub.
#endif
#if !(TARGET_IS_NT60_OR_LATER)
#error You need Windows Vista or later to run this stub because it uses these features:
#error   forced complex structure or array, compiled for Windows Vista.
#error However, your C/C++ compilation flags indicate you intend to run this app on earlier systems.
#error This app will fail with the RPC_X_WRONG_STUB_VERSION error.
#endif


static const HolographicSpaceInterop_MIDL_PROC_FORMAT_STRING HolographicSpaceInterop__MIDL_ProcFormatString =
    {
        0,
        {

	/* Procedure CreateForWindow */

			0x33,		/* FC_AUTO_HANDLE */
			0x6c,		/* Old Flags:  object, Oi2 */
/*  2 */	NdrFcLong( 0x0 ),	/* 0 */
/*  6 */	NdrFcShort( 0x6 ),	/* 6 */
/*  8 */	NdrFcShort( 0x14 ),	/* x86 Stack size/offset = 20 */
/* 10 */	NdrFcShort( 0x44 ),	/* 68 */
/* 12 */	NdrFcShort( 0x8 ),	/* 8 */
/* 14 */	0x47,		/* Oi2 Flags:  srv must size, clt must size, has return, has ext, */
			0x4,		/* 4 */
/* 16 */	0x8,		/* 8 */
			0x7,		/* Ext Flags:  new corr desc, clt corr check, srv corr check, */
/* 18 */	NdrFcShort( 0x1 ),	/* 1 */
/* 20 */	NdrFcShort( 0x1 ),	/* 1 */
/* 22 */	NdrFcShort( 0x0 ),	/* 0 */

	/* Parameter window */

/* 24 */	NdrFcShort( 0x8b ),	/* Flags:  must size, must free, in, by val, */
/* 26 */	NdrFcShort( 0x4 ),	/* x86 Stack size/offset = 4 */
/* 28 */	NdrFcShort( 0x1a ),	/* Type Offset=26 */

	/* Parameter riid */

/* 30 */	NdrFcShort( 0x10a ),	/* Flags:  must free, in, simple ref, */
/* 32 */	NdrFcShort( 0x8 ),	/* x86 Stack size/offset = 8 */
/* 34 */	NdrFcShort( 0x2e ),	/* Type Offset=46 */

	/* Parameter holographicSpace */

/* 36 */	NdrFcShort( 0x13 ),	/* Flags:  must size, must free, out, */
/* 38 */	NdrFcShort( 0xc ),	/* x86 Stack size/offset = 12 */
/* 40 */	NdrFcShort( 0x3a ),	/* Type Offset=58 */

	/* Return value */

/* 42 */	NdrFcShort( 0x70 ),	/* Flags:  out, return, base type, */
/* 44 */	NdrFcShort( 0x10 ),	/* x86 Stack size/offset = 16 */
/* 46 */	0x8,		/* FC_LONG */
			0x0,		/* 0 */

			0x0
        }
    };

static const HolographicSpaceInterop_MIDL_TYPE_FORMAT_STRING HolographicSpaceInterop__MIDL_TypeFormatString =
    {
        0,
        {
			NdrFcShort( 0x0 ),	/* 0 */
/*  2 */	
			0x12, 0x0,	/* FC_UP */
/*  4 */	NdrFcShort( 0x2 ),	/* Offset= 2 (6) */
/*  6 */	
			0x2a,		/* FC_ENCAPSULATED_UNION */
			0x48,		/* 72 */
/*  8 */	NdrFcShort( 0x4 ),	/* 4 */
/* 10 */	NdrFcShort( 0x2 ),	/* 2 */
/* 12 */	NdrFcLong( 0x48746457 ),	/* 1215587415 */
/* 16 */	NdrFcShort( 0x8008 ),	/* Simple arm type: FC_LONG */
/* 18 */	NdrFcLong( 0x52746457 ),	/* 1383359575 */
/* 22 */	NdrFcShort( 0x8008 ),	/* Simple arm type: FC_LONG */
/* 24 */	NdrFcShort( 0xffff ),	/* Offset= -1 (23) */
/* 26 */	0xb4,		/* FC_USER_MARSHAL */
			0x83,		/* 131 */
/* 28 */	NdrFcShort( 0x0 ),	/* 0 */
/* 30 */	NdrFcShort( 0x4 ),	/* 4 */
/* 32 */	NdrFcShort( 0x0 ),	/* 0 */
/* 34 */	NdrFcShort( 0xffe0 ),	/* Offset= -32 (2) */
/* 36 */	
			0x11, 0x0,	/* FC_RP */
/* 38 */	NdrFcShort( 0x8 ),	/* Offset= 8 (46) */
/* 40 */	
			0x1d,		/* FC_SMFARRAY */
			0x0,		/* 0 */
/* 42 */	NdrFcShort( 0x8 ),	/* 8 */
/* 44 */	0x1,		/* FC_BYTE */
			0x5b,		/* FC_END */
/* 46 */	
			0x15,		/* FC_STRUCT */
			0x3,		/* 3 */
/* 48 */	NdrFcShort( 0x10 ),	/* 16 */
/* 50 */	0x8,		/* FC_LONG */
			0x6,		/* FC_SHORT */
/* 52 */	0x6,		/* FC_SHORT */
			0x4c,		/* FC_EMBEDDED_COMPLEX */
/* 54 */	0x0,		/* 0 */
			NdrFcShort( 0xfff1 ),	/* Offset= -15 (40) */
			0x5b,		/* FC_END */
/* 58 */	
			0x11, 0x10,	/* FC_RP [pointer_deref] */
/* 60 */	NdrFcShort( 0x2 ),	/* Offset= 2 (62) */
/* 62 */	
			0x2f,		/* FC_IP */
			0x5c,		/* FC_PAD */
/* 64 */	0x28,		/* Corr desc:  parameter, FC_LONG */
			0x0,		/*  */
/* 66 */	NdrFcShort( 0x8 ),	/* x86 Stack size/offset = 8 */
/* 68 */	NdrFcShort( 0x5 ),	/* Corr flags:  early, iid_is, */

			0x0
        }
    };

static const USER_MARSHAL_ROUTINE_QUADRUPLE UserMarshalRoutines[ WIRE_MARSHAL_TABLE_SIZE ] = 
        {
            
            {
            HWND_UserSize
            ,HWND_UserMarshal
            ,HWND_UserUnmarshal
            ,HWND_UserFree
            }

        };



/* Standard interface: __MIDL_itf_HolographicSpaceInterop_0000_0000, ver. 0.0,
   GUID={0x00000000,0x0000,0x0000,{0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00}} */


/* Object interface: IUnknown, ver. 0.0,
   GUID={0x00000000,0x0000,0x0000,{0xC0,0x00,0x00,0x00,0x00,0x00,0x00,0x46}} */


/* Object interface: IInspectable, ver. 0.0,
   GUID={0xAF86E2E0,0xB12D,0x4c6a,{0x9C,0x5A,0xD7,0xAA,0x65,0x10,0x1E,0x90}} */


/* Object interface: IHolographicSpaceInterop, ver. 0.0,
   GUID={0x5C4EE536,0x6A98,0x4B86,{0xA1,0x70,0x58,0x70,0x13,0xD6,0xFD,0x4B}} */

#pragma code_seg(".orpc")
static const unsigned short IHolographicSpaceInterop_FormatStringOffsetTable[] =
    {
    (unsigned short) -1,
    (unsigned short) -1,
    (unsigned short) -1,
    0
    };

static const MIDL_STUBLESS_PROXY_INFO IHolographicSpaceInterop_ProxyInfo =
    {
    &Object_StubDesc,
    HolographicSpaceInterop__MIDL_ProcFormatString.Format,
    &IHolographicSpaceInterop_FormatStringOffsetTable[-3],
    0,
    0,
    0
    };


static const MIDL_SERVER_INFO IHolographicSpaceInterop_ServerInfo = 
    {
    &Object_StubDesc,
    0,
    HolographicSpaceInterop__MIDL_ProcFormatString.Format,
    &IHolographicSpaceInterop_FormatStringOffsetTable[-3],
    0,
    0,
    0,
    0};
CINTERFACE_PROXY_VTABLE(7) _IHolographicSpaceInteropProxyVtbl = 
{
    &IHolographicSpaceInterop_ProxyInfo,
    &IID_IHolographicSpaceInterop,
    IUnknown_QueryInterface_Proxy,
    IUnknown_AddRef_Proxy,
    IUnknown_Release_Proxy ,
    0 /* IInspectable::GetIids */ ,
    0 /* IInspectable::GetRuntimeClassName */ ,
    0 /* IInspectable::GetTrustLevel */ ,
    (void *) (INT_PTR) -1 /* IHolographicSpaceInterop::CreateForWindow */
};


static const PRPC_STUB_FUNCTION IHolographicSpaceInterop_table[] =
{
    STUB_FORWARDING_FUNCTION,
    STUB_FORWARDING_FUNCTION,
    STUB_FORWARDING_FUNCTION,
    NdrStubCall2
};

CInterfaceStubVtbl _IHolographicSpaceInteropStubVtbl =
{
    &IID_IHolographicSpaceInterop,
    &IHolographicSpaceInterop_ServerInfo,
    7,
    &IHolographicSpaceInterop_table[-3],
    CStdStubBuffer_DELEGATING_METHODS
};


/* Standard interface: __MIDL_itf_HolographicSpaceInterop_0000_0001, ver. 0.0,
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
    HolographicSpaceInterop__MIDL_TypeFormatString.Format,
    1, /* -error bounds_check flag */
    0x60001, /* Ndr library version */
    0,
    0x801026e, /* MIDL Version 8.1.622 */
    0,
    UserMarshalRoutines,
    0,  /* notify & notify_flag routine table */
    0x1, /* MIDL flag */
    0, /* cs routines */
    0,   /* proxy/server info */
    0
    };

const CInterfaceProxyVtbl * const _HolographicSpaceInterop_ProxyVtblList[] = 
{
    ( CInterfaceProxyVtbl *) &_IHolographicSpaceInteropProxyVtbl,
    0
};

const CInterfaceStubVtbl * const _HolographicSpaceInterop_StubVtblList[] = 
{
    ( CInterfaceStubVtbl *) &_IHolographicSpaceInteropStubVtbl,
    0
};

PCInterfaceName const _HolographicSpaceInterop_InterfaceNamesList[] = 
{
    "IHolographicSpaceInterop",
    0
};

const IID *  const _HolographicSpaceInterop_BaseIIDList[] = 
{
    &IID_IInspectable,
    0
};


#define _HolographicSpaceInterop_CHECK_IID(n)	IID_GENERIC_CHECK_IID( _HolographicSpaceInterop, pIID, n)

int __stdcall _HolographicSpaceInterop_IID_Lookup( const IID * pIID, int * pIndex )
{
    
    if(!_HolographicSpaceInterop_CHECK_IID(0))
        {
        *pIndex = 0;
        return 1;
        }

    return 0;
}

const ExtendedProxyFileInfo HolographicSpaceInterop_ProxyFileInfo = 
{
    (PCInterfaceProxyVtblList *) & _HolographicSpaceInterop_ProxyVtblList,
    (PCInterfaceStubVtblList *) & _HolographicSpaceInterop_StubVtblList,
    (const PCInterfaceName * ) & _HolographicSpaceInterop_InterfaceNamesList,
    (const IID ** ) & _HolographicSpaceInterop_BaseIIDList,
    & _HolographicSpaceInterop_IID_Lookup, 
    1,
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

