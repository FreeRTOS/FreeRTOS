/*******************************************************************************
 * (c) Copyright 2012 Microsemi SoC Products Group.  All rights reserved.
 *
 * SmartFusion2 system services.
 *
 * SVN $Revision: 5615 $
 * SVN $Date: 2013-04-05 14:48:10 +0100 (Fri, 05 Apr 2013) $
 */
#include "mss_sys_services.h"
#include "mss_comblk.h"
#include "../../CMSIS/mss_assert.h"
#include <string.h>

/*==============================================================================
 *
 */
/*
 * Service request command opcodes:
 */
#define DEVICE_CERTIFICATE_REQUEST_CMD      0u
#define SERIAL_NUMBER_REQUEST_CMD           1u
#define FLASH_FREEZE_REQUEST_CMD            2u
#define AES128_REQUEST_CMD                  3u
#define USERCODE_REQUEST_CMD                4u
#define DESIGNVER_REQUEST_CMD               5u
#define AES256_REQUEST_CMD                  6u
#define KEYTREE_REQUEST_CMD                 9u
#define SHA256_REQUEST_CMD                  10u
#define HMAC_REQUEST_CMD                    12u
#define PPUF_CHALLENGE_RESP_REQUEST_CMD     14u
#define ISP_PROGRAMMING_REQUEST_CMD         21u
#define DIGEST_CHECK_REQUEST_CMD            23u
#define NRBG_SELF_TEST_REQUEST_CMD          40u
#define NRBG_INSTANTIATE_REQUEST_CMD        41u
#define NRBG_GENERATE_REQUEST_CMD           42u
#define NRBG_RESEED_REQUEST_CMD             43u
#define NRBG_UNINSTANTIATE_REQUEST_CMD      44u
#define NRBG_RESET_REQUEST_CMD              45u
#define FLASHFREEZE_SHUTDOWN_CMD            224u
#define ZEROIZATION_REQUEST_CMD             240u

#define POWER_ON_RESET_DIGEST_ERROR_CMD     241u

/*
 * System Services requests length:
 */
#define FLASH_FREEZE_REQUEST_LENGTH         2u

/*
 * Service response lengths:
 */
#define STANDARD_SERV_RESP_LENGTH           6u

#define SERIAL_NUMBER_SERV_RESP_LENGTH      6u
#define USERCODE_SERV_RESP_LENGTH           6u
#define DESIGNVER_SERV_RESP_LENGTH          6u
#define DEVICE_CERT_SERV_RESP_LENGTH        6u
#define ISP_PROG_SERV_RESP_LENGTH           2u
#define NRBG_RESET_SERV_RESP_LENGTH         2u
#define NRBG_SELF_TEST_SERV_RESP_LENGTH     2u
#define NRBG_UNINST_SERV_RESP_LENGTH        3u

#define DIGEST_CHECK_SERV_RESP_LENGTH       2u
#define FLASH_FREEZE_SERV_RESP_LENGTH       2u

/*
 * Non Deterministic Random Bit Generator defines:
 */
#define INVALID_NRBG_HANDLE     0xFFu

/*
 * RTC_WAKEUP_CR system register bit masks:
 */
#define RTC_WAKEUP_G4C_EN_MASK      0x00000004u
#define RTC_WAKEUP_FAB_EN_MASK      0x00000002u

/*==============================================================================
 * Local functions.
 */
static void request_completion_handler(uint8_t * p_response, uint16_t response_size);
static void signal_request_start(void);
static uint16_t wait_for_request_completion(void);
static uint8_t execute_service
(
    uint8_t cmd_opcode,
    uint8_t * cmd_params_ptr,
    uint8_t * response,
    uint16_t response_length
);

static void asynchronous_event_handler(uint8_t event_opcode);

static void write_ptr_value_into_array
(
    const uint8_t * pointer,
    uint8_t target_array[],
    uint32_t array_index
);

/*==============================================================================
 * Global variables
 */
static volatile uint8_t g_request_in_progress = 0u;
static volatile uint16_t g_last_response_length = 0u;
static sys_serv_async_event_handler_t g_event_handler = 0;

/*==============================================================================
 *
 */
void MSS_SYS_init(sys_serv_async_event_handler_t event_handler)
{
    MSS_COMBLK_init(asynchronous_event_handler);
    
    g_event_handler = event_handler;
    
    g_request_in_progress = 0u;
    g_last_response_length = 0u;
}

/*==============================================================================
 *
 */
static void asynchronous_event_handler(uint8_t event_opcode)
{
    if(g_event_handler != 0)
    {
    switch(event_opcode)
        {
            case FLASH_FREEZE_SHUTDOWN_OPCODE:
            case FLASH_FREEZE_EXIT_OPCODE:
                g_event_handler(event_opcode);
            break;
            
            default:
                /* Ignore all other events. */
            break;
        }
    }
}

/*==============================================================================
 * See mss_sys_services.h for details.
 */
uint8_t MSS_SYS_get_serial_number
(
    uint8_t * p_serial_number
)
{
    uint8_t response[SERIAL_NUMBER_SERV_RESP_LENGTH];
    uint8_t status;
    
    status = execute_service(SERIAL_NUMBER_REQUEST_CMD,
                             p_serial_number,
                             response,
                             SERIAL_NUMBER_SERV_RESP_LENGTH);
    
    return status;
}

/*==============================================================================
 * See mss_sys_services.h for details.
 */
uint8_t MSS_SYS_get_user_code
(
    uint8_t * p_user_code
)
{
    uint8_t response[USERCODE_SERV_RESP_LENGTH];
    uint8_t status;
    
    status = execute_service(USERCODE_REQUEST_CMD,
                             p_user_code,
                             response,
                             USERCODE_SERV_RESP_LENGTH);
    
    return status;
}

/*==============================================================================
 * See mss_sys_services.h for details.
 */
uint8_t MSS_SYS_get_design_version
(
    uint8_t * p_design_version
)
{
    uint8_t response[DESIGNVER_SERV_RESP_LENGTH];
    uint8_t status;
    
    status = execute_service(DESIGNVER_REQUEST_CMD,
                             p_design_version,
                             response,
                             DESIGNVER_SERV_RESP_LENGTH);
    
    return status;
}

/*==============================================================================
 * See mss_sys_services.h for details.
 */
uint8_t MSS_SYS_get_device_certificate
(
    uint8_t * p_device_certificate
)
{
    uint8_t response[DEVICE_CERT_SERV_RESP_LENGTH];
    uint8_t status;
    
    status = execute_service(DEVICE_CERTIFICATE_REQUEST_CMD,
                             p_device_certificate,
                             response,
                             DEVICE_CERT_SERV_RESP_LENGTH);
    
    return status;
}

/*==============================================================================
 * See mss_sys_services.h for details.
 */
uint8_t MSS_SYS_flash_freeze(uint8_t options)
{
    uint8_t status;
    uint16_t actual_response_length;
    uint8_t flash_freeze_req[FLASH_FREEZE_REQUEST_LENGTH];
    uint8_t response[FLASH_FREEZE_SERV_RESP_LENGTH];

    /*
     * The Flash Freeze system service is not available on M2S050 rev A and rev B.
     */
    ASSERT(0x0000F802u != SYSREG->DEVICE_VERSION);
    ASSERT(0x0001F802u != SYSREG->DEVICE_VERSION);
    
    /*
     * Enable RTC wake-up interrupt to System Controller and FPGA fabric.
     */
    SYSREG->RTC_WAKEUP_CR |= (RTC_WAKEUP_G4C_EN_MASK | RTC_WAKEUP_FAB_EN_MASK);

    signal_request_start();

    flash_freeze_req[0] = FLASH_FREEZE_REQUEST_CMD;
    flash_freeze_req[1] = options;

    MSS_COMBLK_send_cmd(flash_freeze_req,               /* p_cmd */
                        FLASH_FREEZE_REQUEST_LENGTH,    /* cmd_size */
                        0,                              /* p_data */
                        0u,                             /* data_size */
                        response,                       /* p_response */
                        FLASH_FREEZE_SERV_RESP_LENGTH,  /* response_size */
                        request_completion_handler);    /* completion_handler */

    actual_response_length = wait_for_request_completion();
    
    if((FLASH_FREEZE_SERV_RESP_LENGTH == actual_response_length) &&
       (FLASH_FREEZE_REQUEST_CMD == response[0]))
    {
        status = response[1];
    }
    else
    {
        status = MSS_SYS_UNEXPECTED_ERROR;
    }
    
    return status;
}

/*==============================================================================
 * See mss_sys_services.h for details.
 */
#define AES128_KEY_LENGTH   16u
#define IV_LENGTH           16u

#define AES256_KEY_LENGTH   32u

#define HMAC_KEY_LENGTH     32u

uint8_t MSS_SYS_128bit_aes
(
    const uint8_t * key,
    const uint8_t * iv,
    uint16_t nb_blocks,
    uint8_t mode,
    uint8_t * dest_addr,
    const uint8_t * src_addr)
{
    uint8_t response[STANDARD_SERV_RESP_LENGTH];
    uint8_t params[44];
    uint8_t status;
    
    memcpy(&params[0], key, AES128_KEY_LENGTH);
    memcpy(&params[16], iv, IV_LENGTH);
    
    params[32] = (uint8_t)nb_blocks;
    params[33] = (uint8_t)(nb_blocks >> 8u);
    params[34] = mode;
    params[35] = 0u;
#if 1
    write_ptr_value_into_array(dest_addr, params, 36u);
    write_ptr_value_into_array(src_addr, params, 40u);
#else    
    params[36] = (uint8_t)((uint32_t)dest_addr);
    params[37] = (uint8_t)((uint32_t)dest_addr >> 8u);
    params[38] = (uint8_t)((uint32_t)dest_addr >> 16u);
    params[39] = (uint8_t)((uint32_t)dest_addr >> 24u);

    params[40] = (uint8_t)((uint32_t)src_addr);
    params[41] = (uint8_t)((uint32_t)src_addr >> 8u);
    params[42] = (uint8_t)((uint32_t)src_addr >> 16u);
    params[43] = (uint8_t)((uint32_t)src_addr >> 24u);
#endif
    status = execute_service(AES128_REQUEST_CMD,
                             params,
                             response,
                             STANDARD_SERV_RESP_LENGTH);
                             
    return status;
}

/*==============================================================================
 * See mss_sys_services.h for details.
 */
uint8_t MSS_SYS_256bit_aes
( 
    const uint8_t * key,
    const uint8_t * iv,
    uint16_t nb_blocks,
    uint8_t mode,
    uint8_t * dest_addr,
    const uint8_t * src_addr
)
{
    uint8_t response[STANDARD_SERV_RESP_LENGTH];
    uint8_t params[60];
    uint8_t status;
    
    memcpy(&params[0], key, AES256_KEY_LENGTH);
    memcpy(&params[32], iv, IV_LENGTH);
    
    params[48] = (uint8_t)nb_blocks;
    params[49] = (uint8_t)(nb_blocks >> 8u);
    params[50] = mode;
    params[51] = 0u;
#if 1
    write_ptr_value_into_array(dest_addr, params, 52u);
    write_ptr_value_into_array(src_addr, params, 56u);
#else    
    params[52] = (uint8_t)((uint32_t)dest_addr);
    params[53] = (uint8_t)((uint32_t)dest_addr >> 8u);
    params[54] = (uint8_t)((uint32_t)dest_addr >> 16u);
    params[55] = (uint8_t)((uint32_t)dest_addr >> 24u);

    params[56] = (uint8_t)((uint32_t)src_addr);
    params[57] = (uint8_t)((uint32_t)src_addr >> 8u);
    params[58] = (uint8_t)((uint32_t)src_addr >> 16u);
    params[59] = (uint8_t)((uint32_t)src_addr >> 24u);
#endif
    status = execute_service(AES256_REQUEST_CMD,
                             params,
                             response,
                             STANDARD_SERV_RESP_LENGTH);
                             
    return status;
}

/*==============================================================================
 * See mss_sys_services.h for details.
 */
uint8_t MSS_SYS_sha256
(
    const uint8_t * p_data_in,
    uint32_t length,
    uint8_t * result
)
{
    uint8_t response[STANDARD_SERV_RESP_LENGTH];
    uint8_t params[12];
    uint8_t status;
    
    params[0] = (uint8_t)((uint32_t)length);
    params[1] = (uint8_t)((uint32_t)length >> 8u);
    params[2] = (uint8_t)((uint32_t)length >> 16u);
    params[3] = (uint8_t)((uint32_t)length >> 24u);
    
#if 1
    write_ptr_value_into_array(result, params, 4u);
    write_ptr_value_into_array(p_data_in, params, 8u);
#else
    params[4] = (uint8_t)((uint32_t)result);
    params[5] = (uint8_t)((uint32_t)result >> 8u);
    params[6] = (uint8_t)((uint32_t)result >> 16u);
    params[7] = (uint8_t)((uint32_t)result >> 24u);

    params[8] = (uint8_t)((uint32_t)p_data_in);
    params[9] = (uint8_t)((uint32_t)p_data_in >> 8u);
    params[10] = (uint8_t)((uint32_t)p_data_in >> 16u);
    params[11] = (uint8_t)((uint32_t)p_data_in >> 24u);
#endif
    status = execute_service(SHA256_REQUEST_CMD,
                             params,
                             response,
                             STANDARD_SERV_RESP_LENGTH);
                             
    return status;
}

/*==============================================================================
 * See mss_sys_services.h for details.
 */
uint8_t MSS_SYS_hmac
(
    const uint8_t * key,
    const uint8_t * p_data_in,
    uint32_t length,
    uint8_t * p_result
)
{
    uint8_t response[STANDARD_SERV_RESP_LENGTH];
    uint8_t params[58];
    uint8_t status;
    
    memcpy(&params[0], key, HMAC_KEY_LENGTH);
    
    params[32] = (uint8_t)((uint32_t)length);
    params[33] = (uint8_t)((uint32_t)length >> 8u);
    params[34] = (uint8_t)((uint32_t)length >> 16u);
    params[35] = (uint8_t)((uint32_t)length >> 24u);
#if 1
    write_ptr_value_into_array(p_data_in, params, 36u);
    write_ptr_value_into_array(p_result, params, 40u);
#else    
    params[36] = (uint8_t)((uint32_t)p_data_in);
    params[37] = (uint8_t)((uint32_t)p_data_in >> 8u);
    params[38] = (uint8_t)((uint32_t)p_data_in >> 16u);
    params[39] = (uint8_t)((uint32_t)p_data_in >> 24u);

    params[40] = (uint8_t)((uint32_t)p_result);
    params[41] = (uint8_t)((uint32_t)p_result >> 8u);
    params[42] = (uint8_t)((uint32_t)p_result >> 16u);
    params[43] = (uint8_t)((uint32_t)p_result >> 24u);
#endif
    status = execute_service(HMAC_REQUEST_CMD,
                             params,
                             response,
                             STANDARD_SERV_RESP_LENGTH);
                             
    return status;
}

/*==============================================================================
 * See mss_sys_services.h for details.
 */
uint8_t MSS_SYS_nrbg_self_test(void)
{
    uint8_t status;
    uint16_t actual_response_length;
    uint8_t self_test;
    uint8_t response[NRBG_SELF_TEST_SERV_RESP_LENGTH];
    
    signal_request_start();
    
    self_test = NRBG_SELF_TEST_REQUEST_CMD;

    MSS_COMBLK_send_cmd(&self_test,                         /* p_cmd */
                        sizeof(self_test),                  /* cmd_size */
                        0,                                  /* p_data */
                        0,                                  /* data_size */
                        response,                           /* p_response */
                        NRBG_SELF_TEST_SERV_RESP_LENGTH,    /* response_size */
                        request_completion_handler);        /* completion_handler */
    
    actual_response_length = wait_for_request_completion();
    
    if((NRBG_SELF_TEST_SERV_RESP_LENGTH == actual_response_length) &&
       (NRBG_SELF_TEST_REQUEST_CMD == response[0]))
    {
        status = response[1];
    }
    else
    {
        status = MSS_SYS_UNEXPECTED_ERROR;
    }
    
    return status;
}

/*==============================================================================
 * See mss_sys_services.h for details.
 */
uint8_t MSS_SYS_nrbg_instantiate
(
    const uint8_t * personalization_str,
    uint16_t personalization_str_length,
    uint8_t * p_nrbg_handle
)
{
    uint8_t response[STANDARD_SERV_RESP_LENGTH];
    uint8_t intantiate_params[7];
    uint8_t status;
#if 1
    write_ptr_value_into_array(personalization_str, intantiate_params, 0u);
#else    
    intantiate_params[0] = (uint8_t)((uint32_t)personalization_str);
    intantiate_params[1] = (uint8_t)((uint32_t)personalization_str >> 8u);
    intantiate_params[2] = (uint8_t)((uint32_t)personalization_str >> 16u);
    intantiate_params[3] = (uint8_t)((uint32_t)personalization_str >> 24u);
#endif
    intantiate_params[4] = (uint8_t)personalization_str_length;
    intantiate_params[5] = (uint8_t)(personalization_str_length >> 8u);
    intantiate_params[6] = INVALID_NRBG_HANDLE;
    
    status = execute_service(NRBG_INSTANTIATE_REQUEST_CMD,
                             intantiate_params,
                             response,
                             STANDARD_SERV_RESP_LENGTH);
                             
    if(MSS_SYS_SUCCESS == status)
    {
        *p_nrbg_handle = intantiate_params[6];
    }
    
    return status;
}

/*==============================================================================
 * See mss_sys_services.h for details.
 */
uint8_t MSS_SYS_nrbg_generate
(
    const uint8_t * p_requested_data,
    const uint8_t * p_additional_input,
    uint8_t requested_length,
    uint8_t additional_input_length,
    uint8_t pr_req,
    uint8_t nrbg_handle
)
{
    uint8_t response[STANDARD_SERV_RESP_LENGTH];
    uint8_t generate_params[12];
    uint8_t status;
#if 1
    write_ptr_value_into_array(p_requested_data, generate_params, 0u);
    write_ptr_value_into_array(p_additional_input, generate_params, 4u);
#else
    generate_params[0] = (uint8_t)((uint32_t)p_requested_data);
    generate_params[1] = (uint8_t)((uint32_t)p_requested_data >> 8u);
    generate_params[2] = (uint8_t)((uint32_t)p_requested_data >> 16u);
    generate_params[3] = (uint8_t)((uint32_t)p_requested_data >> 24u);
    generate_params[4] = (uint8_t)((uint32_t)p_additional_input);
    generate_params[5] = (uint8_t)((uint32_t)p_additional_input >> 8u);
    generate_params[6] = (uint8_t)((uint32_t)p_additional_input >> 16u);
    generate_params[7] = (uint8_t)((uint32_t)p_additional_input >> 24u);
#endif
    generate_params[8] = requested_length;
    generate_params[9] = additional_input_length;
    generate_params[10] = pr_req;
    generate_params[11] = nrbg_handle;
    
    status = execute_service(NRBG_GENERATE_REQUEST_CMD,
                             generate_params,
                             response,
                             STANDARD_SERV_RESP_LENGTH);
    
    return status;
}

/*==============================================================================
 * See mss_sys_services.h for details.
 */
uint8_t MSS_SYS_nrbg_reseed
(
    const uint8_t * p_additional_input,
    uint8_t additional_input_length,
    uint8_t nrbg_handle
)
{
    uint8_t response[STANDARD_SERV_RESP_LENGTH];
    uint8_t params[6];
    uint8_t status;
#if 1
    write_ptr_value_into_array(p_additional_input, params, 0u);
#else
    params[0] = (uint8_t)((uint32_t)p_additional_input);
    params[1] = (uint8_t)((uint32_t)p_additional_input >> 8u);
    params[2] = (uint8_t)((uint32_t)p_additional_input >> 16u);
    params[3] = (uint8_t)((uint32_t)p_additional_input >> 24u);
#endif
    params[4] = (uint8_t)additional_input_length;
    params[5] = nrbg_handle;
    
    status = execute_service(NRBG_RESEED_REQUEST_CMD,
                             params,
                             response,
                             STANDARD_SERV_RESP_LENGTH);
    
    return status;
}

/*==============================================================================
 * See mss_sys_services.h for details.
 */
uint8_t MSS_SYS_nrbg_uninstantiate
(
    uint8_t nrbg_handle
)
{
    uint8_t status;
    uint16_t actual_response_length;
    uint8_t uninstantiate_req[2];
    uint8_t response[NRBG_UNINST_SERV_RESP_LENGTH];
    
    signal_request_start();
    
    uninstantiate_req[0] = NRBG_UNINSTANTIATE_REQUEST_CMD;
    uninstantiate_req[1] = nrbg_handle;

    MSS_COMBLK_send_cmd(uninstantiate_req,              /* p_cmd */
                        sizeof(uninstantiate_req),      /* cmd_size */
                        0,                              /* p_data */
                        0,                              /* data_size */
                        response,                       /* p_response */
                        NRBG_UNINST_SERV_RESP_LENGTH,   /* response_size */
                        request_completion_handler);    /* completion_handler */
    
    actual_response_length = wait_for_request_completion();
    
    if((NRBG_UNINST_SERV_RESP_LENGTH == actual_response_length) &&
       (NRBG_UNINSTANTIATE_REQUEST_CMD == response[0]))
    {
        status = response[1];
    }
    else
    {
        status = MSS_SYS_UNEXPECTED_ERROR;
    }
    
    return status;
}

/*==============================================================================
 * See mss_sys_services.h for details.
 */
static uint8_t g_isp_response[ISP_PROG_SERV_RESP_LENGTH];
void (*g_isp_completion_handler)(uint32_t) = 0;

static void isp_sys_completion_handler
(
    uint8_t * p_response, 
    uint16_t length
)
{
    if(g_isp_completion_handler != 0)
    {
        g_isp_completion_handler(p_response[1]);
    }
}

void MSS_SYS_start_isp
(
    uint8_t mode,
    uint32_t (*page_read_handler)(uint8_t const **),
    void (*isp_completion_handler)(uint32_t)
)
{
    uint8_t isp_prog_request[2];
    
    signal_request_start();
    
    isp_prog_request[0] = ISP_PROGRAMMING_REQUEST_CMD;
    isp_prog_request[1] = mode;
    
    g_isp_completion_handler = isp_completion_handler;

    MSS_COMBLK_send_paged_cmd(isp_prog_request,                 /* p_cmd */
                              sizeof(isp_prog_request),         /* cmd_size */
                              g_isp_response,                   /* p_response */
                              ISP_PROG_SERV_RESP_LENGTH, /* response_size */
                              page_read_handler,                /* page_handler */
                              isp_sys_completion_handler);      /* completion_handler */
}

/*==============================================================================
 * See mss_sys_services.h for details.
 */
uint8_t MSS_SYS_check_digest
(
    uint8_t options
)
{
    uint8_t status;
    uint16_t actual_response_length;
    uint8_t digest_check_req[2];
    uint8_t response[DIGEST_CHECK_SERV_RESP_LENGTH];
    
    signal_request_start();
    
    digest_check_req[0] = DIGEST_CHECK_REQUEST_CMD;
    digest_check_req[1] = options;

    MSS_COMBLK_send_cmd(digest_check_req,               /* p_cmd */
                        sizeof(digest_check_req),       /* cmd_size */
                        0,                              /* p_data */
                        0u,                             /* data_size */
                        response,                       /* p_response */
                        DIGEST_CHECK_SERV_RESP_LENGTH,  /* response_size */
                        request_completion_handler);    /* completion_handler */
    
    actual_response_length = wait_for_request_completion();
    
    if((DIGEST_CHECK_SERV_RESP_LENGTH == actual_response_length) &&
       (DIGEST_CHECK_REQUEST_CMD == response[0]))
    {
        status = response[1];
    }
    else
    {
        status = MSS_SYS_UNEXPECTED_ERROR;
    }
    
    return status;
}

/*==============================================================================
 *
 */
static uint8_t execute_service
(
    uint8_t cmd_opcode,
    uint8_t * cmd_params_ptr,
    uint8_t * response,
    uint16_t response_length
)
{
    uint8_t status;
    uint16_t actual_response_length;
    
    signal_request_start();
    
    MSS_COMBLK_send_cmd_with_ptr(cmd_opcode,                    /* cmd_opcode */
                                 (uint32_t)cmd_params_ptr,      /* cmd_params_ptr */
                                 response,                      /* p_response */
                                 response_length,               /* response_size */
                                 request_completion_handler);   /* completion_handler */
    
    actual_response_length = wait_for_request_completion();
    
    if((response_length == actual_response_length) && (cmd_opcode == response[0]))
    {
        status = response[1];
    }
    else
    {
        status = MSS_SYS_UNEXPECTED_ERROR;
    }
    
    return status;
}

/*==============================================================================
 *
 */
static void request_completion_handler
(
    uint8_t * p_response,
    uint16_t response_size
)
{
    g_request_in_progress = 0u;
    g_last_response_length = response_size;
}

/*==============================================================================
 *
 */
static void signal_request_start(void)
{
    /* Wait for current request to complete. */
    while(g_request_in_progress)
    {
        ;
    }
    
    g_request_in_progress = 1u;
    g_last_response_length = 0u;
}

/*==============================================================================
 *
 */
static uint16_t wait_for_request_completion(void)
{
    while(g_request_in_progress)
    {
        ;
    }
    
    return g_last_response_length;
}

/*==============================================================================
 *
 */
static void write_ptr_value_into_array
(
    const uint8_t * pointer,
    uint8_t target_array[],
    uint32_t array_index
)
{
    target_array[array_index] = (uint8_t)((uint32_t)pointer);
    target_array[array_index + 1] = (uint8_t)((uint32_t)pointer >> 8u);
    target_array[array_index + 2] = (uint8_t)((uint32_t)pointer >> 16u);
    target_array[array_index + 3] = (uint8_t)((uint32_t)pointer >> 24u);
}

