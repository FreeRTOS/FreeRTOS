/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "queue.h"
#include "FreeRTOS_Sockets.h"

/* FreeRTOS+TCP includes. */
#include "iot_https_client.h"
#include "iot_https_internal.h"

#include "../global_state_HTTP.c"

/****************************************************************
* Stub out snprintf so that it writes nothing but simply checks that
* the arguments are readable and writeable, and returns a length.
*
* The snprintf function is used by SendSync only to build a header
* whose length is bounded by HTTPS_MAX_CONTENT_LENGTH_LINE_LENGTH,
* so snprintf returns an unconstrained length between 0 and this
* bound.  This value is defined in iot_https_internal.h.
*
* MacOS header file /usr/include/secure/_stdio.h defines snprintf to
* use a builtin function supported by CBMC, so when this builtin is
* available, we stub out the builtin snprintf instead of the standard
* snprintf.
****************************************************************/

/* This is a clang macro not available on linux */
#ifndef __has_builtin
#define __has_builtin(x) 0
#endif

#if __has_builtin(__builtin___sprintf_chk)
int __builtin___snprintf_chk (char *buf, size_t size, int flag, size_t os,
			      const char *fmt, ...)
{
  int ret;
  __CPROVER_assert(__CPROVER_w_ok(buf, size), "sprintf output writeable");
  __CPROVER_assert(fmt, "sprintf format nonnull");
  __CPROVER_assume(ret >= 0 && ret <= HTTPS_MAX_CONTENT_LENGTH_LINE_LENGTH);
  return ret;
}

#else
int snprintf(char *buf, size_t size, const char *fmt, ...)
{
  int ret;
  __CPROVER_assert(__CPROVER_w_ok(buf, size), "sprintf output writeable");
  __CPROVER_assert(fmt, "sprintf format nonnull");
  __CPROVER_assume(ret >= 0 && ret <= HTTPS_MAX_CONTENT_LENGTH_LINE_LENGTH);
  return ret;
}
#endif

void harness() {
  IotHttpsConnectionHandle_t pConnHandle = allocate_IotConnectionHandle();
  IotHttpsRequestHandle_t reqHandle = allocate_IotRequestHandle();
  IotHttpsResponseHandle_t pRespHandle = allocate_IotResponseHandle();
  IotHttpsResponseInfo_t *pRespInfo = allocate_IotResponseInfo();
  uint32_t timeoutMs;

  initialize_IotConnectionHandle(pConnHandle);
  initialize_IotResponseHandle(pRespHandle);
  if (pRespInfo)
    __CPROVER_assume(is_valid_IotResponseInfo(pRespInfo));
  IotHttpsClient_SendSync(pConnHandle, reqHandle, &pRespHandle, pRespInfo, timeoutMs);
}
