#ifndef SIGV4_CONFIG_H_
#define SIGV4_CONFIG_H_

#include "logging_levels.h"

#ifndef LIBRARY_LOG_NAME
    #define LIBRARY_LOG_NAME    "SIGV4"
#endif

#ifndef LIBRARY_LOG_LEVEL
    #define LIBRARY_LOG_LEVEL    LOG_INFO
#endif

#include "logging_stack.h"

#define SIGV4_PROCESSING_BUFFER_LENGTH    1600U

#define SIGV4_MAX_HTTP_HEADER_COUNT       10U


#define SIGV4_MAX_QUERY_PAIR_COUNT        1U


#define SIGV4_HASH_MAX_BLOCK_LENGTH       64U


#define SIGV4_HASH_MAX_DIGEST_LENGTH      32U


#define SIGV4_USE_CANONICAL_SUPPORT       1

#endif 
