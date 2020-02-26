/****************************************************************/

// TODO: Generate a header file for function declarations
IotHttpsResponseHandle_t allocate_IotResponseHandle();
IotHttpsRequestHandle_t allocate_IotRequestHandle();

/****************************************************************/

/* Implementation of safe malloc which returns NULL if the requested
 * size is 0.  Warning: The behavior of malloc(0) is platform
 * dependent.  It is possible for malloc(0) to return an address
 * without allocating memory.
 */
void *safeMalloc(size_t xWantedSize) {
  return nondet_bool() ? malloc(xWantedSize) : NULL;
}

/****************************************************************
 * HTTP parser stubs
 ****************************************************************/

/* Model the third party HTTP Parser. */
size_t http_parser_execute (http_parser *parser,
                            const http_parser_settings *settings,
                            const char *data,
                            size_t len) {
  __CPROVER_assert(parser, "http_parser_execute parser nonnull");
  __CPROVER_assert(settings, "http_parser_execute settings nonnull");
  __CPROVER_assert(data, "http_parser_execute data nonnull");

  _httpsResponse_t *_httpsResponse = (_httpsResponse_t *)(parser->data);
  // Choose whether the parser found the header
  _httpsResponse->foundHeaderField = nondet_bool();
  _httpsResponse->parserState = PARSER_STATE_BODY_COMPLETE;

  // Generate the header value found
  size_t valueLength;
  if (_httpsResponse->foundHeaderField) {
    __CPROVER_assume(valueLength <= len);
    _httpsResponse->pReadHeaderValue = malloc(valueLength+1);
    _httpsResponse->pReadHeaderValue[valueLength] = 0;
    _httpsResponse->readHeaderValueLength = valueLength;
  }

  // Return the number of characters in ReadHeaderValue
  return _httpsResponse->foundHeaderField ? valueLength : 0;
}

/****************************************************************
 * IotNetworkInterface constructor
 ****************************************************************/

IotNetworkError_t IotNetworkInterfaceCreate( void * pConnectionInfo,
					     void * pCredentialInfo,
					     void * pConnection ) {
  __CPROVER_assert(pConnectionInfo,
		   "IotNetworkInterfaceCreate pConnectionInfo");
  /* create accepts NULL credentials when there is no TLS configuration. */
  __CPROVER_assert(pConnection, "IotNetworkInterfaceCreate pConnection");

  /* The network connection created by this function is an opaque type
   * that is simply passed to the other network functions we are
   * stubbing out, so we just ensure that it points to a memory
   * object. */
  *(char **)pConnection = malloc(1); /* network connection is opaque.  */

  IotNetworkError_t error;
  return error;
}

size_t IotNetworkInterfaceSend( void * pConnection,
				const uint8_t * pMessage,
				size_t messageLength ) {
  __CPROVER_assert(pConnection, "IotNetworkInterfaceSend pConnection");
  __CPROVER_assert(pMessage, "IotNetworkInterfaceSend pMessage");

  size_t size;
  __CPROVER_assume(size <= messageLength);
  return size;
}

IotNetworkError_t IotNetworkInterfaceClose( void * pConnection ) {
  __CPROVER_assert(pConnection, "IotNetworkInterfaceClose pConnection");

  IotNetworkError_t error;
  return error;
}

size_t IotNetworkInterfaceReceive( void * pConnection,
				   uint8_t * pBuffer,
				   size_t bytesRequested ) {
  __CPROVER_assert(pConnection, "IotNetworkInterfaceReceive pConnection");
  __CPROVER_assert(pBuffer, "IotNetworkInterfaceReceive pBuffer");

  /* Fill the entire memory object pointed to by pBuffer with
   * unconstrained data.  This use of __CPROVER_array_copy with a
   * single byte is a common CBMC idiom. */
  uint8_t byte;
  __CPROVER_array_copy(pBuffer,&byte);

  size_t size;
  __CPROVER_assume(size <= bytesRequested);
  return size;
}

IotNetworkError_t IotNetworkInterfaceCallback( void * pConnection,
					       IotNetworkReceiveCallback_t
					         receiveCallback,
					       void * pContext ) {
  __CPROVER_assert(pConnection,
		   "IotNetworkInterfaceCallback pConnection");
  __CPROVER_assert(receiveCallback,
		   "IotNetworkInterfaceCallback receiveCallback");
  __CPROVER_assert(pContext,
		   "IotNetworkInterfaceCallback pContext");

  IotNetworkError_t error;
  return error;
}

IotNetworkError_t IotNetworkInterfaceDestroy( void * pConnection ) {
  __CPROVER_assert(pConnection, "IotNetworkInterfaceDestroy pConnection");

  IotNetworkError_t error;
  return error;
}

IotNetworkInterface_t IOTNI = {
  .create = IotNetworkInterfaceCreate,
  .close = IotNetworkInterfaceClose,
  .send = IotNetworkInterfaceSend,
  .receive = IotNetworkInterfaceReceive,
  .setReceiveCallback = IotNetworkInterfaceCallback,
  .destroy = IotNetworkInterfaceDestroy
};

/* Models the Network Interface. */
IotNetworkInterface_t *allocate_NetworkInterface() {
  return nondet_bool() ? &IOTNI : NULL;
}

int is_valid_NetworkInterface(IotNetworkInterface_t *netif) {
  return
    netif->create &&
    netif->close &&
    netif->send &&
    netif->receive &&
    netif->setReceiveCallback &&
    netif->destroy;
}

/* Use
 *   __CPROVER_assume(is_stubbed_NetworkInterface(netif));
 * to ensure the stubbed out functions are used.  The initializer for
 * IOTNI appears to be ignored when CBMC is run with
 * --nondet-static. */

int is_stubbed_NetworkInterface(IotNetworkInterface_t *netif) {
  return
    netif->create == IotNetworkInterfaceCreate &&
    netif->close == IotNetworkInterfaceClose &&
    netif->send == IotNetworkInterfaceSend &&
    netif->receive == IotNetworkInterfaceReceive &&
    netif->setReceiveCallback == IotNetworkInterfaceCallback &&
    netif->destroy == IotNetworkInterfaceDestroy;
}

/****************************************************************
 * IotHttpsConnectionInfo constructor
 ****************************************************************/

/* Creates a Connection Info and assigns memory accordingly. */
IotHttpsConnectionInfo_t * allocate_IotConnectionInfo() {
  IotHttpsConnectionInfo_t * pConnInfo =
    safeMalloc(sizeof(IotHttpsConnectionInfo_t));
  if(pConnInfo) {
    pConnInfo->pNetworkInterface = allocate_NetworkInterface();
    pConnInfo->pAddress = safeMalloc(pConnInfo->addressLen);
    pConnInfo->pAlpnProtocols = safeMalloc(pConnInfo->alpnProtocolsLen);
    pConnInfo->pCaCert = safeMalloc(sizeof(uint32_t));
    pConnInfo->pClientCert = safeMalloc(sizeof(uint32_t));
    pConnInfo->pPrivateKey = safeMalloc(sizeof(uint32_t));
    pConnInfo->userBuffer.pBuffer = safeMalloc(sizeof(struct _httpsConnection));
  }
  return pConnInfo;
}

int is_valid_IotConnectionInfo(IotHttpsConnectionInfo_t *pConnInfo) {
  return
    pConnInfo->pCaCert &&
    pConnInfo->pClientCert &&
    pConnInfo->pPrivateKey &&
    pConnInfo->userBuffer.pBuffer &&
    pConnInfo->pNetworkInterface &&
    is_valid_NetworkInterface(pConnInfo->pNetworkInterface);
}

/****************************************************************
 * IotHttpsConnectionHandle constructor
 ****************************************************************/

/* Creates a Connection Handle and assigns memory accordingly. */
IotHttpsConnectionHandle_t allocate_IotConnectionHandle () {
  IotHttpsConnectionHandle_t pConnectionHandle =
    safeMalloc(sizeof(struct _httpsConnection));
  if(pConnectionHandle) {
    // network connection just points to an allocated memory object
    pConnectionHandle->pNetworkConnection = safeMalloc(1);
    pConnectionHandle->pNetworkInterface = allocate_NetworkInterface();
  }
  return pConnectionHandle;
}

IotHttpsConnectionHandle_t
initialize_IotConnectionHandle (IotHttpsConnectionHandle_t
				pConnectionHandle) {
  if(pConnectionHandle) {
    IotListDouble_Create(&pConnectionHandle->reqQ);
    IotListDouble_Create(&pConnectionHandle->respQ);
    // Add zero or one element to response queue
    if (nondet_bool()) {
      IotHttpsResponseHandle_t resp = allocate_IotResponseHandle();
      __CPROVER_assume(resp);
      IotListDouble_InsertHead(&pConnectionHandle->respQ, &resp->link);
    }
    // Add zero or one element to request queue
    if (nondet_bool()) {
      IotHttpsRequestHandle_t req = allocate_IotRequestHandle();
      __CPROVER_assume(req);
      IotListDouble_InsertHead(&pConnectionHandle->reqQ, &req->link);
    }
 }
  return pConnectionHandle;
}

int is_valid_IotConnectionHandle(IotHttpsConnectionHandle_t handle) {
  return
    handle->pNetworkConnection &&
    handle->pNetworkInterface &&
    is_valid_NetworkInterface(handle->pNetworkInterface);
}

/****************************************************************
 * IotHttpsResponseHandle constructor
 ****************************************************************/

/* Creates a Response Handle and assigns memory accordingly. */
IotHttpsResponseHandle_t allocate_IotResponseHandle() {
  IotHttpsResponseHandle_t pResponseHandle =
    safeMalloc(sizeof(struct _httpsResponse));
  if(pResponseHandle) {
    size_t headerLen;
    size_t bodyLen;
    pResponseHandle->pHeaders = safeMalloc(headerLen);
    pResponseHandle->pBody = safeMalloc(bodyLen);
    pResponseHandle->pHttpsConnection = allocate_IotConnectionHandle();
    pResponseHandle->pReadHeaderField =
      safeMalloc(pResponseHandle->readHeaderFieldLength);
    pResponseHandle->pReadHeaderValue =
      safeMalloc(pResponseHandle->readHeaderValueLength);
  }
  return pResponseHandle;
}

// ???: Should be is_stubbed
IotHttpsResponseHandle_t
initialize_IotResponseHandle(IotHttpsResponseHandle_t pResponseHandle) {
  if(pResponseHandle) {
    pResponseHandle->httpParserInfo.parseFunc = http_parser_execute;
  }
  return pResponseHandle;
}

int is_valid_IotResponseHandle(IotHttpsResponseHandle_t pResponseHandle) {
  int required1 =
    __CPROVER_same_object(pResponseHandle->pHeaders,
			  pResponseHandle->pHeadersCur) &&
    __CPROVER_same_object(pResponseHandle->pHeaders,
			  pResponseHandle->pHeadersEnd);
  int required2 =
    __CPROVER_same_object(pResponseHandle->pBody,
			  pResponseHandle->pBodyCur) &&
    __CPROVER_same_object(pResponseHandle->pBody,
			  pResponseHandle->pBodyEnd);
  if (!required1 || !required2) return 0;

  int valid_headers =
    pResponseHandle->pHeaders != NULL;
  int valid_header_order =
    pResponseHandle->pHeaders <= pResponseHandle->pHeadersCur &&
    pResponseHandle->pHeadersCur <=  pResponseHandle->pHeadersEnd;
  int valid_body =
    pResponseHandle->pBody != NULL;
  int valid_body_order =
    pResponseHandle->pBody <= pResponseHandle->pBodyCur &&
    pResponseHandle->pBodyCur <=  pResponseHandle->pBodyEnd;
  int valid_parserdata =
    pResponseHandle->httpParserInfo.readHeaderParser.data == pResponseHandle;
  return
    valid_headers &&
    valid_header_order &&
    valid_body &&
    valid_body_order &&
    valid_parserdata &&
    // valid_order and short circuit evaluation prevents integer overflow
    __CPROVER_r_ok(pResponseHandle->pHeaders,
		   pResponseHandle->pHeadersEnd - pResponseHandle->pHeaders) &&
    __CPROVER_w_ok(pResponseHandle->pHeaders,
		   pResponseHandle->pHeadersEnd - pResponseHandle->pHeaders) &&
    __CPROVER_r_ok(pResponseHandle->pBody,
		   pResponseHandle->pBodyEnd - pResponseHandle->pBody) &&
    __CPROVER_w_ok(pResponseHandle->pBody,
		   pResponseHandle->pBodyEnd - pResponseHandle->pBody);
}

/****************************************************************
 * IotHttpsRequestHandle constructor
 ****************************************************************/

/* Creates a Request Handle and assigns memory accordingly. */
IotHttpsRequestHandle_t allocate_IotRequestHandle() {
  IotHttpsRequestHandle_t pRequestHandle =
    safeMalloc(sizeof(struct _httpsRequest));
  if (pRequestHandle) {
    uint32_t headerLen;
    pRequestHandle->pHttpsResponse = allocate_IotResponseHandle();
    pRequestHandle->pHttpsConnection = allocate_IotConnectionHandle();
    pRequestHandle->pHeaders = safeMalloc(headerLen);
    pRequestHandle->pBody = safeMalloc(pRequestHandle->bodyLength);
    pRequestHandle->pConnInfo = allocate_IotConnectionInfo();
  }
  return pRequestHandle;
}

int is_valid_IotRequestHandle(IotHttpsRequestHandle_t pRequestHandle) {
  int required =
    __CPROVER_same_object(pRequestHandle->pHeaders,
			  pRequestHandle->pHeadersCur) &&
    __CPROVER_same_object(pRequestHandle->pHeaders,
			  pRequestHandle->pHeadersEnd);
  if (!required) return 0;

  int valid_headers =
    pRequestHandle->pHeaders != NULL;
  int valid_order =
    pRequestHandle->pHeaders <= pRequestHandle->pHeadersCur &&
    pRequestHandle->pHeadersCur <=  pRequestHandle->pHeadersEnd;
  int valid_body =
    pRequestHandle->pBody != NULL;
  int bounded_header_buffer =
    __CPROVER_OBJECT_SIZE(pRequestHandle->pHeaders) < CBMC_MAX_OBJECT_SIZE;
  return
    valid_headers &&
    valid_order &&
    valid_body &&
    bounded_header_buffer &&
    // valid_order and short circuit evaluation prevents integer overflow
    __CPROVER_r_ok(pRequestHandle->pHeaders,
		   pRequestHandle->pHeadersEnd - pRequestHandle->pHeaders) &&
    __CPROVER_w_ok(pRequestHandle->pHeaders,
		   pRequestHandle->pHeadersEnd - pRequestHandle->pHeaders);
}

/****************************************************************
 * IotHttpsRequestInfo constructor
 * This is currently unusued and untested.
 ****************************************************************/

/* Creates a Request Info and assigns memory accordingly. */
IotHttpsRequestInfo_t * allocate_IotRequestInfo() {
  IotHttpsRequestInfo_t * pReqInfo
    = safeMalloc(sizeof(IotHttpsRequestInfo_t));
  if(pReqInfo) {
    pReqInfo->userBuffer.pBuffer = safeMalloc(pReqInfo->userBuffer.bufferLen);
    pReqInfo->pHost = safeMalloc(pReqInfo->hostLen);
  }
  return pReqInfo;
}

int is_valid_IotRequestInfo(IotHttpsRequestInfo_t * pReqInfo) {
  return
    pReqInfo->hostLen <= IOT_HTTPS_MAX_HOST_NAME_LENGTH + 1;
}

/****************************************************************
 * IotHttpsResponseInfo constructor
 ****************************************************************/

/* Creates a Response Info and assigns memory accordingly. */
IotHttpsResponseInfo_t * allocate_IotResponseInfo() {
  IotHttpsResponseInfo_t * pRespInfo =
    safeMalloc(sizeof(IotHttpsResponseInfo_t));
  if(pRespInfo) {
    pRespInfo->userBuffer.pBuffer = safeMalloc(pRespInfo->userBuffer.bufferLen);
    pRespInfo->pSyncInfo = safeMalloc(sizeof(IotHttpsSyncInfo_t));
    if (pRespInfo->pSyncInfo)
      pRespInfo->pSyncInfo->pBody = safeMalloc(pRespInfo->pSyncInfo->bodyLen);
  }
  return pRespInfo;
}

int is_valid_IotResponseInfo(IotHttpsResponseInfo_t * pRespInfo){
  return
    pRespInfo->pSyncInfo &&
    pRespInfo->pSyncInfo->pBody &&
    pRespInfo->pSyncInfo->bodyLen <= CBMC_MAX_OBJECT_SIZE &&
    pRespInfo->userBuffer.bufferLen <= CBMC_MAX_OBJECT_SIZE;
}
