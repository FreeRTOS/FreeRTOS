/**
 * Copyright (C) 2016 CSI Project. All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#ifndef __CSI_WIFI_H__
#define __CSI_WIFI_H__

#ifdef __cplusplus
extern "C" {
#endif

#ifndef bool
#define bool        int8_t
#define false       0        ///< XOS definition of 'false'
#define true        1        ///< XOS definition of 'true'
#endif

typedef enum {
    WIFI_EVENT_WIFI_READY = 0,           /**< WiFi ready */
    WIFI_EVENT_SCAN_DONE,                /**< finish scanning AP */
    WIFI_EVENT_STA_START,                /**< station start */
    WIFI_EVENT_STA_STOP,                 /**< station stop */
    WIFI_EVENT_STA_CONNECTED,            /**< station connected to AP */
    WIFI_EVENT_STA_DISCONNECTED,         /**< station disconnected from AP */
    WIFI_EVENT_STA_AUTHMODE_CHANGE,      /**< the auth mode of AP connected by station changed */
    WIFI_EVENT_STA_GOT_IP,               /**< station got IP from connected AP */
    WIFI_EVENT_STA_WPS_ER_SUCCESS,       /**< station wps succeeds in enrollee mode */
    WIFI_EVENT_STA_WPS_ER_FAILED,        /**< station wps fails in enrollee mode */
    WIFI_EVENT_STA_WPS_ER_TIMEOUT,       /**< station wps timeout in enrollee mode */
    WIFI_EVENT_STA_WPS_ER_PIN,           /**< station wps pin code in enrollee mode */
    WIFI_EVENT_AP_START,                 /**< soft-AP start */
    WIFI_EVENT_AP_STOP,                  /**< soft-AP stop */
    WIFI_EVENT_AP_STACONNECTED,          /**< a station connected to soft-AP */
    WIFI_EVENT_AP_STADISCONNECTED,       /**< a station disconnected from soft-AP */
    WIFI_EVENT_AP_PROBEREQRECVED,        /**< Receive probe request packet in soft-AP interface */
    WIFI_EVENT_AP_STA_GOT_IP6,           /**< station or ap interface v6IP addr is preferred */
    WIFI_EVENT_ETH_START,                /**< ethernet start */
    WIFI_EVENT_ETH_STOP,                 /**< ethernet stop */
    WIFI_EVENT_ETH_CONNECTED,            /**< ethernet phy link up */
    WIFI_EVENT_ETH_DISCONNECTED,         /**< ethernet phy link down */
    WIFI_EVENT_ETH_GOT_IP,               /**< ethernet got IP from connected AP */
    WIFI_EVENT_MAX
} wifi_event_id_t;


typedef enum {
    CSI_IF_WIFI_STA = 0,     /**< CSI station interface */
    CSI_IF_WIFI_AP,          /**< CSI soft-AP interface */
    CSI_IF_ETH,              /**< CSI ethernet interface */
    CSI_IF_MAX
} csi_interface_t;

typedef enum {
    WIFI_MODE_NULL = 0,  /**< null mode */
    WIFI_MODE_STA,       /**< WiFi station mode */
    WIFI_MODE_AP,        /**< WiFi soft-AP mode */
    WIFI_MODE_APSTA,     /**< WiFi station + soft-AP mode */
    WIFI_MODE_MAX
} wifi_mode_t;

typedef csi_interface_t wifi_interface_t;

#define WIFI_IF_STA CSI_IF_WIFI_STA
#define WIFI_IF_AP  CSI_IF_WIFI_AP

typedef enum {
    WIFI_COUNTRY_CN = 0, /**< country China, channel range [1, 14] */
    WIFI_COUNTRY_JP,     /**< country Japan, channel range [1, 14] */
    WIFI_COUNTRY_US,     /**< country USA, channel range [1, 11] */
    WIFI_COUNTRY_EU,     /**< country Europe, channel range [1, 13] */
    WIFI_COUNTRY_MAX
} wifi_country_t;

typedef enum {
    WIFI_AUTH_OPEN = 0,         /**< authenticate mode : open */
    WIFI_AUTH_WEP,              /**< authenticate mode : WEP */
    WIFI_AUTH_WPA_PSK,          /**< authenticate mode : WPA_PSK */
    WIFI_AUTH_WPA2_PSK,         /**< authenticate mode : WPA2_PSK */
    WIFI_AUTH_WPA_WPA2_PSK,     /**< authenticate mode : WPA_WPA2_PSK */
    WIFI_AUTH_WPA2_ENTERPRISE,  /**< authenticate mode : WPA2_ENTERPRISE */
    WIFI_AUTH_MAX
} wifi_auth_mode_t;

enum {
    WIFI_REASON_UNSPECIFIED              = 1,
    WIFI_REASON_AUTH_EXPIRE              = 2,
    WIFI_REASON_AUTH_LEAVE               = 3,
    WIFI_REASON_ASSOC_EXPIRE             = 4,
    WIFI_REASON_ASSOC_TOOMANY            = 5,
    WIFI_REASON_NOT_AUTHED               = 6,
    WIFI_REASON_NOT_ASSOCED              = 7,
    WIFI_REASON_ASSOC_LEAVE              = 8,
    WIFI_REASON_ASSOC_NOT_AUTHED         = 9,
    WIFI_REASON_DISASSOC_PWRCAP_BAD      = 10,
    WIFI_REASON_DISASSOC_SUPCHAN_BAD     = 11,
    WIFI_REASON_IE_INVALID               = 13,
    WIFI_REASON_MIC_FAILURE              = 14,
    WIFI_REASON_4WAY_HANDSHAKE_TIMEOUT   = 15,
    WIFI_REASON_GROUP_KEY_UPDATE_TIMEOUT = 16,
    WIFI_REASON_IE_IN_4WAY_DIFFERS       = 17,
    WIFI_REASON_GROUP_CIPHER_INVALID     = 18,
    WIFI_REASON_PAIRWISE_CIPHER_INVALID  = 19,
    WIFI_REASON_AKMP_INVALID             = 20,
    WIFI_REASON_UNSUPP_RSN_IE_VERSION    = 21,
    WIFI_REASON_INVALID_RSN_IE_CAP       = 22,
    WIFI_REASON_802_1X_AUTH_FAILED       = 23,
    WIFI_REASON_CIPHER_SUITE_REJECTED    = 24,

    WIFI_REASON_BEACON_TIMEOUT           = 200,
    WIFI_REASON_NO_AP_FOUND              = 201,
    WIFI_REASON_AUTH_FAIL                = 202,
    WIFI_REASON_ASSOC_FAIL               = 203,
    WIFI_REASON_HANDSHAKE_TIMEOUT        = 204,
};

typedef enum {
    WIFI_SECOND_CHAN_NONE = 0,  /**< the channel width is HT20 */
    WIFI_SECOND_CHAN_ABOVE,     /**< the channel width is HT40 and the second channel is above the primary channel */
    WIFI_SECOND_CHAN_BELOW,     /**< the channel width is HT40 and the second channel is below the primary channel */
} wifi_second_chan_t;

typedef enum {
    WIFI_SCAN_TYPE_ACTIVE = 0,  /**< active scan */
    WIFI_SCAN_TYPE_PASSIVE,     /**< passive scan */
} wifi_scan_type_t;

typedef struct {
    uint32_t min;  /**< minimum active scan time per channel, units: millisecond */
    uint32_t max;  /**< maximum active scan time per channel, units: millisecond, values above 1500ms may
                                          cause station to disconnect from AP and are not recommended.  */
} wifi_active_scan_time_t;

typedef union {
    wifi_active_scan_time_t active;  /**< active scan time per channel */
    uint32_t passive;                /**< passive scan time per channel, units: millisecond, values above 1500ms may
                                          cause station to disconnect from AP and are not recommended. */
} wifi_scan_time_t;

typedef struct {
    uint8_t *ssid;               /**< SSID of AP */
    uint8_t *bssid;              /**< MAC address of AP */
    uint8_t channel;             /**< channel, scan the specific channel */
    bool show_hidden;            /**< enable to scan AP whose SSID is hidden */
    wifi_scan_type_t scan_type;  /**< scan type, active or passive */
    wifi_scan_time_t scan_time;  /**< scan time per channel */
} wifi_scan_config_t;

typedef struct {
    uint8_t bssid[6];                     /**< MAC address of AP */
    uint8_t ssid[32];                     /**< SSID of AP */
    uint8_t primary;                      /**< channel of AP */
    wifi_second_chan_t second;            /**< second channel of AP */
    int8_t  rssi;                         /**< signal strength of AP */
    wifi_auth_mode_t authmode;            /**< authmode of AP */
    uint32_t low_rate_enable:1;           /**< bit: 0 flag to identify if low rate is enabled or not */
    uint32_t reserved:31;                 /**< bit: 1..31 reserved */
} wifi_ap_record_t;

typedef enum {
    WIFI_PS_NONE,    /**< No power save */
    WIFI_PS_MODEM,   /**< Modem power save */
} wifi_ps_type_t;

#define WIFI_PROTOCOL_11B         1
#define WIFI_PROTOCOL_11G         2
#define WIFI_PROTOCOL_11N         4
#define WIFI_PROTOCOL_LR          8

typedef enum {
    WIFI_BW_HT20 = 1, /* Bandwidth is HT20 */
    WIFI_BW_HT40,     /* Bandwidth is HT40 */
    WIFI_BW_HT20_HT40,
} wifi_bandwidth_t;

typedef struct {
    uint8_t ssid[32];           /**< SSID of soft-AP */
    uint8_t password[64];       /**< Password of soft-AP */
    uint8_t ssid_len;           /**< Length of SSID. If softap_config.ssid_len==0, check the SSID until there is a termination character; otherwise, set the SSID length according to softap_config.ssid_len. */
    uint8_t channel;            /**< Channel of soft-AP */
    wifi_auth_mode_t authmode;  /**< Auth mode of soft-AP. Do not support AUTH_WEP in soft-AP mode */
    uint8_t ssid_hidden;        /**< Broadcast SSID or not, default 0, broadcast the SSID */
    uint8_t max_connection;     /**< Max number of stations allowed to connect in, default 4, max 4 */
    uint16_t beacon_interval;   /**< Beacon interval, 100 ~ 60000 ms, default 100 ms */
} wifi_ap_config_t;

typedef struct {
    uint8_t ssid[32];      /**< SSID of target AP*/
    uint8_t password[64];  /**< password of target AP*/
    bool bssid_set;        /**< whether set MAC address of target AP or not. Generally, station_config.bssid_set needs to be 0; and it needs to be 1 only when users need to check the MAC address of the AP.*/
    uint8_t bssid[6];     /**< MAC address of target AP*/
} wifi_sta_config_t;

typedef union {
    wifi_ap_config_t  ap;  /**< configuration of AP */
    wifi_sta_config_t sta; /**< configuration of STA */
} wifi_config_t;

typedef struct {
    uint8_t mac[6];  /**< mac address of sta that associated with soft-AP */
} wifi_sta_info_t;

#define CSI_WIFI_MAX_CONN_NUM  (10)       /**< max number of stations which can connect to soft-AP */

typedef struct {
    wifi_sta_info_t sta[CSI_WIFI_MAX_CONN_NUM]; /**< station list */
    int       num; /**< number of station that associated with soft-AP */
} wifi_sta_list_t;

typedef enum {
    WIFI_STORAGE_FLASH,  /**< all configuration will strore in both memory and flash */
    WIFI_STORAGE_RAM,    /**< all configuration will only store in the memory */
} wifi_storage_t;

/**
  * @brief     Vendor IE type
  *
  */
typedef enum {
    WIFI_VND_IE_TYPE_BEACON,
    WIFI_VND_IE_TYPE_PROBE_REQ,
    WIFI_VND_IE_TYPE_PROBE_RCSI,
    WIFI_VND_IE_TYPE_ASSOC_REQ,
    WIFI_VND_IE_TYPE_ASSOC_RCSI,
} wifi_vendor_ie_type_t;

/**
  * @brief     Vendor IE index
  *
  */
typedef enum {
    WIFI_VND_IE_ID_0,
    WIFI_VND_IE_ID_1,
} wifi_vendor_ie_id_t;

typedef struct {
    signed rssi:8;            /**< signal intensity of packet */
    unsigned rate:5;          /**< data rate */
    unsigned :1;              /**< reserve */
    unsigned sig_mode:2;      /**< 0:is not 11n packet; 1:is 11n packet */
    unsigned :16;             /**< reserve */
    unsigned mcs:7;           /**< if is 11n packet, shows the modulation(range from 0 to 76) */
    unsigned cwb:1;           /**< if is 11n packet, shows if is HT40 packet or not */
    unsigned :16;             /**< reserve */
    unsigned smoothing:1;     /**< reserve */
    unsigned not_sounding:1;  /**< reserve */
    unsigned :1;              /**< reserve */
    unsigned aggregation:1;   /**< Aggregation */
    unsigned stbc:2;          /**< STBC */
    unsigned fec_coding:1;    /**< if is 11n packet, shows if is LDPC packet or not */
    unsigned sgi:1;           /**< SGI */
    unsigned noise_floor:8;   /**< noise floor */
    unsigned ampdu_cnt:8;     /**< ampdu cnt */
    unsigned channel:4;       /**< which channel this packet in */
    unsigned :12;             /**< reserve */
    unsigned timestamp:32;    /**< timestamp */
    unsigned :32;             /**< reserve */
    unsigned :32;             /**< reserve */
    unsigned sig_len:12;      /**< It is really lenth of packet */
    unsigned :12;             /**< reserve */
    unsigned rx_state:8;      /**< rx state */
} wifi_pkt_rx_ctrl_t;

typedef struct {
    wifi_pkt_rx_ctrl_t rx_ctrl;
    uint8_t payload[0];       /**< ieee80211 packet buff, The length of payload is described by sig_len */
} wifi_promiscuous_pkt_t;

/**
  * @brief     Promiscuous frame type
  *
  */
typedef enum {
    WIFI_PKT_CTRL,  /**< control type, receive packet buf is wifi_pkt_rx_ctrl_t */
    WIFI_PKT_MGMT,  /**< management type, receive packet buf is wifi_promiscuous_pkt_t */
    WIFI_PKT_DATA,  /**< data type, receive packet buf is wifi_promiscuous_pkt_t */
    WIFI_PKT_MISC,  /**< other type, receive packet buf is wifi_promiscuous_pkt_t */
} wifi_promiscuous_pkt_type_t;

#define CSI_OK          0
#define CSI_FAIL        -1

#define CSI_ERR_NO_MEM          0x101
#define CSI_ERR_INVALID_ARG     0x102
#define CSI_ERR_INVALID_STATE   0x103
#define CSI_ERR_INVALID_SIZE    0x104
#define CSI_ERR_NOT_FOUND       0x105
#define CSI_ERR_NOT_SUPPORTED   0x106
#define CSI_ERR_TIMEOUT         0x107
#define CSI_ERR_INVALID_RCSIONSE    0x108
#define CSI_ERR_INVALID_CRC     0x109

//#define CSI_ERR_WIFI_BASE       0x3000 /*!< Starting number of WiFi error codes */

#define CSI_ERR_WIFI_OK          CSI_OK                    /*!< No error */
#define CSI_ERR_WIFI_FAIL        CSI_FAIL                  /*!< General fail code */
#define CSI_ERR_WIFI_NO_MEM      CSI_ERR_NO_MEM            /*!< Out of memory */
#define CSI_ERR_WIFI_ARG         CSI_ERR_INVALID_ARG       /*!< Invalid argument */
#define CSI_ERR_WIFI_NOT_SUPPORT CSI_ERR_NOT_SUPPORTED     /*!< Indicates that API is not supported yet */

#define CSI_ERR_WIFI_NOT_INIT    (CSI_DRV_ERRNO_WIFI_BASE + 1)   /*!< WiFi driver was not installed by csi_wifi_init */
#define CSI_ERR_WIFI_NOT_STARTED (CSI_DRV_ERRNO_WIFI_BASE + 2)   /*!< WiFi driver was not started by csi_wifi_start */
#define CSI_ERR_WIFI_IF          (CSI_DRV_ERRNO_WIFI_BASE + 3)   /*!< WiFi interface error */
#define CSI_ERR_WIFI_MODE        (CSI_DRV_ERRNO_WIFI_BASE + 4)   /*!< WiFi mode error */
#define CSI_ERR_WIFI_STATE       (CSI_DRV_ERRNO_WIFI_BASE + 5)   /*!< WiFi internal state error */
#define CSI_ERR_WIFI_CONN        (CSI_DRV_ERRNO_WIFI_BASE + 6)   /*!< WiFi internal control block of station or soft-AP error */
#define CSI_ERR_WIFI_NVS         (CSI_DRV_ERRNO_WIFI_BASE + 7)   /*!< WiFi internal NVS module error */
#define CSI_ERR_WIFI_MAC         (CSI_DRV_ERRNO_WIFI_BASE + 8)   /*!< MAC address is invalid */
#define CSI_ERR_WIFI_SSID        (CSI_DRV_ERRNO_WIFI_BASE + 9)   /*!< SSID is invalid */
#define CSI_ERR_WIFI_PASSWORD    (CSI_DRV_ERRNO_WIFI_BASE + 10)  /*!< Password is invalid */
#define CSI_ERR_WIFI_TIMEOUT     (CSI_DRV_ERRNO_WIFI_BASE + 11)  /*!< Timeout error */
#define CSI_ERR_WIFI_WAKE_FAIL   (CSI_DRV_ERRNO_WIFI_BASE + 12)  /*!< WiFi is in sleep state(RF closed) and wakeup fail */

typedef enum
{
    FRAME_FILTER_MODE_FORWARD = 1,                  /*!< Packet filter engine forwards matching packets, discards non-matching packets */
    FRAME_FILTER_MODE_DISCARD = 0,                  /*!< Packet filter engine discards matching packets, forwards non-matching packets */
} frame_filter_mode_t;

typedef enum
{
    FRAME_FILTER_RULE_POSITIVE_MATCHING  = 0,       /*!< Specifies that a filter should match a given pattern     */
    FRAME_FILTER_RULE_NEGATIVE_MATCHING  = 1,       /*!< Specifies that a filter should NOT match a given pattern */
} frame_filter_rule_t;

/**
 * Structure describing a frame filter list item
 */
typedef struct
{
    uint32_t                       id;             /*!< Unique identifier for a packet filter item */
    frame_filter_rule_t            rule;           /*!< Filter matches are either POSITIVE or NEGATIVE matching */
    uint16_t                       offset;         /*!< Offset in bytes to start filtering (referenced to the start of the ethernet packet) */
    uint16_t                       mask_size;      /*!< Size of the mask in bytes */
    uint8_t*                       mask;           /*!< Pattern mask bytes to be ANDed with the pattern eg. "\xff00" (must be in network byte order) */
    uint8_t*                       pattern;        /*!< Pattern bytes used to filter eg. "\x0800"  (must be in network byte order) */
    bool                           enabled_status; /*!< When returned from mhd_get_packet_filters, indicates if the filter is enabled */
} wifi_frame_filter_t;

struct wifi_frame_filter_list
{
    struct wifi_frame_filter_list*  next;
};
typedef struct wifi_frame_filter_list wifi_frame_filter_list_t;

typedef void (*wifi_event_cb_t)(uint32_t event);  ///< Signal WiFi Event. Events refer to wifi_event_id_t

/**
  * @brief  Init WiFi
  *         Alloc resource for WiFi driver, such as WiFi control structure, RX/TX buffer,
  *         WiFi NVS structure etc, this WiFi also start WiFi task
  *
  * @attention 1. This API must be called before all other WiFi API can be called
  *
  * @param  cb callback to handle WiFi event
  *
  * @return
  *    - CSI_OK: succeed
  *    - CSI_ERR_WIFI_NO_MEM: out of memory
  *    - others: refer to error code csi_err.h
  */
int32_t csi_wifi_init(wifi_event_cb_t *cb);

/**
  * @brief  Deinit WiFi
  *         Free all resource allocated in csi_wifi_init and stop WiFi task
  *
  * @attention 1. This API should be called if you want to remove WiFi driver from the system
  *
  * @return CSI_OK: succeed
  */
int32_t csi_wifi_deinit(void);

/**
  * @brief     Set the WiFi operating mode
  *
  *            Set the WiFi operating mode as station, soft-AP or station+soft-AP,
  *            The default mode is soft-AP mode.
  *
  * @param     mode  WiFi operating mode
  *
  * @return
  *    - CSI_OK: succeed
  *    - CSI_ERR_WIFI_NOT_INIT: WiFi is not initialized by csi_wifi_init
  *    - CSI_ERR_WIFI_ARG: invalid argument
  *    - others: refer to error code in csi_err.h
  */
int32_t csi_wifi_set_mode(wifi_mode_t mode);

/**
  * @brief  Get current operating mode of WiFi
  *
  * @param[out]  mode  store current WiFi mode
  *
  * @return
  *    - CSI_OK: succeed
  *    - CSI_ERR_WIFI_NOT_INIT: WiFi is not initialized by csi_wifi_init
  *    - CSI_ERR_WIFI_ARG: invalid argument
  */
int32_t csi_wifi_get_mode(wifi_mode_t *mode);

/**
  * @brief  Start WiFi according to current configuration
  *         If mode is WIFI_MODE_STA, it create station control block and start station
  *         If mode is WIFI_MODE_AP, it create soft-AP control block and start soft-AP
  *         If mode is WIFI_MODE_APSTA, it create soft-AP and station control block and start soft-AP and station
  *
  * @return
  *    - CSI_OK: succeed
  *    - CSI_ERR_WIFI_NOT_INIT: WiFi is not initialized by csi_wifi_init
  *    - CSI_ERR_WIFI_ARG: invalid argument
  *    - CSI_ERR_WIFI_NO_MEM: out of memory
  *    - CSI_ERR_WIFI_CONN: WiFi internal error, station or soft-AP control block wrong
  *    - CSI_ERR_WIFI_FAIL: other WiFi internal errors
  */
int32_t csi_wifi_start(void);

/**
  * @brief  Stop WiFi
  *         If mode is WIFI_MODE_STA, it stop station and free station control block
  *         If mode is WIFI_MODE_AP, it stop soft-AP and free soft-AP control block
  *         If mode is WIFI_MODE_APSTA, it stop station/soft-AP and free station/soft-AP control block
  *
  * @return
  *    - CSI_OK: succeed
  *    - CSI_ERR_WIFI_NOT_INIT: WiFi is not initialized by csi_wifi_init
  */
int32_t csi_wifi_stop(void);

/**
 * @brief  Restore WiFi stack persistent settings to default values
 *
 * This function will reset settings made using the following APIs:
 * - csi_wifi_get_auto_connect,
 * - csi_wifi_set_protocol,
 * - csi_wifi_set_config related
 * - csi_wifi_set_mode
 *
 * @return
 *    - CSI_OK: succeed
 *    - CSI_ERR_WIFI_NOT_INIT: WiFi is not initialized by csi_wifi_init
 */
int32_t csi_wifi_restore(void);

/**
  * @brief     Connect the WiFi station to the AP.
  *
  * @attention 1. This API only impact WIFI_MODE_STA or WIFI_MODE_APSTA mode
  * @attention 2. If connecting to an AP, call csi_wifi_disconnect to disconnect.
  *
  * @return 
  *    - CSI_OK: succeed
  *    - CSI_ERR_WIFI_NOT_INIT: WiFi is not initialized by csi_wifi_init
  *    - CSI_ERR_WIFI_NOT_START: WiFi is not started by csi_wifi_start
  *    - CSI_ERR_WIFI_CONN: WiFi internal error, station or soft-AP control block wrong
  *    - CSI_ERR_WIFI_SSID: SSID of AP which station connects is invalid
  */
int32_t csi_wifi_connect(void);

/**
  * @brief     Disconnect the WiFi station from the AP.
  *
  * @return
  *    - CSI_OK: succeed
  *    - CSI_ERR_WIFI_NOT_INIT: WiFi was not initialized by csi_wifi_init
  *    - CSI_ERR_WIFI_NOT_STARTED: WiFi was not started by csi_wifi_start
  *    - CSI_ERR_WIFI_FAIL: other WiFi internal errors
  */
int32_t csi_wifi_disconnect(void);

/**
  * @brief     deauthenticate all stations or associated id equals to aid
  *
  * @param     aid  when aid is 0, deauthenticate all stations, otherwise deauthenticate station whose associated id is aid
  *
  * @return
  *    - CSI_OK: succeed
  *    - CSI_ERR_WIFI_NOT_INIT: WiFi is not initialized by csi_wifi_init
  *    - CSI_ERR_WIFI_NOT_STARTED: WiFi was not started by csi_wifi_start
  *    - CSI_ERR_WIFI_ARG: invalid argument
  *    - CSI_ERR_WIFI_MODE: WiFi mode is wrong
  */
int32_t csi_wifi_deauth_sta(uint16_t aid);

/**
  * @brief     Scan all available APs.
  *
  * @attention If this API is called, the found APs are stored in WiFi driver dynamic allocated memory and that
  *            will be freed in csi_wifi_get_ap_list, so generally, call csi_wifi_get_ap_list to cause
  *            the memory to be freed once the scan is done
  * @attention The values of maximum active scan time and passive scan time per channel are limited to 1500 milliseconds.
  *            Values above 1500ms may cause station to disconnect from AP and are not recommended.
  *
  * @param     config  configuration of scanning
  * @param     block if block is true, this API will block the caller until the scan is done, otherwise
  *                         it will return immediately
  *
  * @return
  *    - CSI_OK: succeed
  *    - CSI_ERR_WIFI_NOT_INIT: WiFi is not initialized by csi_wifi_init
  *    - CSI_ERR_WIFI_NOT_STARTED: WiFi was not started by csi_wifi_start
  *    - CSI_ERR_WIFI_TIMEOUT: blocking scan is timeout
  *    - others: refer to error code in csi_err.h
  */
int32_t csi_wifi_scan_start(wifi_scan_config_t *config, bool block);

/**
  * @brief     Stop the scan in process
  *
  * @return
  *    - CSI_OK: succeed
  *    - CSI_ERR_WIFI_NOT_INIT: WiFi is not initialized by csi_wifi_init
  *    - CSI_ERR_WIFI_NOT_STARTED: WiFi is not started by csi_wifi_start
  */
int32_t csi_wifi_scan_stop(void);

/**
  * @brief     Get AP list found in last scan
  *
  * @param[inout]  number As input param, it stores max AP number ap_records can hold. 
  *                As output param, it receives the actual AP number this API returns.
  * @param         ap_records  wifi_ap_record_t array to hold the found APs
  *
  * @return
  *    - CSI_OK: succeed
  *    - CSI_ERR_WIFI_NOT_INIT: WiFi is not initialized by csi_wifi_init
  *    - CSI_ERR_WIFI_NOT_STARTED: WiFi is not started by csi_wifi_start
  *    - CSI_ERR_WIFI_ARG: invalid argument
  *    - CSI_ERR_WIFI_NO_MEM: out of memory
  */
int32_t csi_wifi_scan_get_ap_records(uint16_t *number, wifi_ap_record_t *ap_records);


/**
  * @brief     Get information of AP which station is associated with
  *
  * @param     ap_info  the wifi_ap_record_t to hold AP information
  *
  * @return
  *    - CSI_OK: succeed
  *    - others: fail
  */
int32_t csi_wifi_sta_get_ap_info(wifi_ap_record_t *ap_info);

/**
  * @brief     Set current power save type
  *
  * @attention Default power save type is WIFI_PS_NONE.
  *
  * @param     type  power save type
  *
  * @return    CSI_ERR_WIFI_NOT_SUPPORT: not supported yet
  */
int32_t csi_wifi_set_ps(wifi_ps_type_t type);

/**
  * @brief     Get current power save type
  *
  * @attention Default power save type is WIFI_PS_NONE.
  *
  * @param[out]  type: store current power save type
  *
  * @return    CSI_ERR_WIFI_NOT_SUPPORT: not supported yet
  */
int32_t csi_wifi_get_ps(wifi_ps_type_t *type);

/**
  * @brief     Set protocol type of specified interface
  *            The default protocol is (WIFI_PROTOCOL_11B|WIFI_PROTOCOL_11G|WIFI_PROTOCOL_11N)
  *
  * @attention Currently we only support 802.11b or 802.11bg or 802.11bgn mode
  *
  * @param     ifx  interfaces
  * @param     protocol_bitmap  WiFi protocol bitmap
  *
  * @return
  *    - CSI_OK: succeed
  *    - CSI_ERR_WIFI_NOT_INIT: WiFi is not initialized by csi_wifi_init
  *    - CSI_ERR_WIFI_IF: invalid interface
  *    - others: refer to error codes in csi_err.h
  */
int32_t csi_wifi_set_protocol(wifi_interface_t ifx, uint8_t protocol_bitmap);

/**
  * @brief     Get the current protocol bitmap of the specified interface
  *
  * @param     ifx  interface
  * @param[out] protocol_bitmap  store current WiFi protocol bitmap of interface ifx
  *
  * @return
  *    - CSI_OK: succeed
  *    - CSI_ERR_WIFI_NOT_INIT: WiFi is not initialized by csi_wifi_init
  *    - CSI_ERR_WIFI_IF: invalid interface
  *    - CSI_ERR_WIFI_ARG: invalid argument
  *    - others: refer to error codes in csi_err.h
  */
int32_t csi_wifi_get_protocol(wifi_interface_t ifx, uint8_t *protocol_bitmap);

/**
  * @brief     Set the bandwidth of specified interface
  *
  * @attention 1. API return false if try to configure an interface that is not enabled
  * @attention 2. WIFI_BW_HT40 is supported only when the interface support 11N
  *
  * @param     ifx  interface to be configured
  * @param     bw  bandwidth
  *
  * @return
  *    - CSI_OK: succeed
  *    - CSI_ERR_WIFI_NOT_INIT: WiFi is not initialized by csi_wifi_init
  *    - CSI_ERR_WIFI_IF: invalid interface
  *    - CSI_ERR_WIFI_ARG: invalid argument
  *    - others: refer to error codes in csi_err.h
  */
int32_t csi_wifi_set_bandwidth(wifi_interface_t ifx, wifi_bandwidth_t bw);

/**
  * @brief     Get the bandwidth of specified interface
  *
  * @attention 1. API return false if try to get a interface that is not enable
  *
  * @param     ifx interface to be configured
  * @param[out] bw  store bandwidth of interface ifx
  *
  * @return
  *    - CSI_OK: succeed
  *    - CSI_ERR_WIFI_NOT_INIT: WiFi is not initialized by csi_wifi_init
  *    - CSI_ERR_WIFI_IF: invalid interface
  *    - CSI_ERR_WIFI_ARG: invalid argument
  */
int32_t csi_wifi_get_bandwidth(wifi_interface_t ifx, wifi_bandwidth_t *bw);

/**
  * @brief     Set primary/secondary channel
  *
  * @attention 1. This is a special API for sniffer
  * @attention 2. This API should be called after csi_wifi_start() or csi_wifi_set_promiscuous()
  *
  * @param     primary  for HT20, primary is the channel number, for HT40, primary is the primary channel
  * @param     second   for HT20, second is ignored, for HT40, second is the second channel
  *
  * @return
  *    - CSI_OK: succeed
  *    - CSI_ERR_WIFI_NOT_INIT: WiFi is not initialized by csi_wifi_init
  *    - CSI_ERR_WIFI_IF: invalid interface
  *    - CSI_ERR_WIFI_ARG: invalid argument
  */
int32_t csi_wifi_set_channel(uint8_t primary, wifi_second_chan_t second);

/**
  * @brief     Get the primary/secondary channel
  *
  * @attention 1. API return false if try to get a interface that is not enable
  *
  * @param[out]  primary   store current primary channel
  * @param[out]  second  store current second channel
  *
  * @return
  *    - CSI_OK: succeed
  *    - CSI_ERR_WIFI_NOT_INIT: WiFi is not initialized by csi_wifi_init
  *    - CSI_ERR_WIFI_ARG: invalid argument
  */
int32_t csi_wifi_get_channel(uint8_t *primary, wifi_second_chan_t *second);

/**
  * @brief     Set country code
  *            The default value is WIFI_COUNTRY_CN
  *
  * @param     country  country type
  *
  * @return
  *    - CSI_OK: succeed
  *    - CSI_ERR_WIFI_NOT_INIT: WiFi is not initialized by csi_wifi_init
  *    - CSI_ERR_WIFI_ARG: invalid argument
  *    - others: refer to error code in csi_err.h
  */
int32_t csi_wifi_set_country(wifi_country_t country);

/**
  * @brief     Get country code
  *
  * @param     country  store current country
  *
  * @return
  *    - CSI_OK: succeed
  *    - CSI_ERR_WIFI_NOT_INIT: WiFi is not initialized by csi_wifi_init
  *    - CSI_ERR_WIFI_ARG: invalid argument
  */
int32_t csi_wifi_get_country(wifi_country_t *country);

/**
  * @brief     Set MAC address of the WiFi station or the soft-AP interface.
  *
  * @attention 1. This API can only be called when the interface is disabled
  * @attention 2. soft-AP and station have different MAC addresses, do not set them to be the same.
  * @attention 3. The bit 0 of the first byte of MAC address can not be 1. For example, the MAC address
  *      can set to be "1a:XX:XX:XX:XX:XX", but can not be "15:XX:XX:XX:XX:XX".
  *
  * @param     ifx  interface
  * @param     mac  the MAC address
  *
  * @return
  *    - CSI_OK: succeed
  *    - CSI_ERR_WIFI_NOT_INIT: WiFi is not initialized by csi_wifi_init
  *    - CSI_ERR_WIFI_ARG: invalid argument
  *    - CSI_ERR_WIFI_IF: invalid interface
  *    - CSI_ERR_WIFI_MAC: invalid mac address
  *    - CSI_ERR_WIFI_MODE: WiFi mode is wrong
  *    - others: refer to error codes in csi_err.h
  */
int32_t csi_wifi_set_mac(wifi_interface_t ifx, uint8_t mac[6]);

/**
  * @brief     Get mac of specified interface
  *
  * @param      ifx  interface
  * @param[out] mac  store mac of the interface ifx
  *
  * @return
  *    - CSI_OK: succeed
  *    - CSI_ERR_WIFI_NOT_INIT: WiFi is not initialized by csi_wifi_init
  *    - CSI_ERR_WIFI_ARG: invalid argument
  *    - CSI_ERR_WIFI_IF: invalid interface
  */
int32_t csi_wifi_get_mac(wifi_interface_t ifx, uint8_t mac[6]);

/**
  * @brief The RX callback function in the promiscuous mode. 
  *        Each time a packet is received, the callback function will be called.
  *
  * @param buf  Data received. Type of data in buffer (wifi_promiscuous_pkt_t or wifi_pkt_rx_ctrl_t) indicated by 'type' parameter.
  * @param type  promiscuous packet type.
  *
  */
typedef void (* wifi_promiscuous_cb_t)(void *buf, wifi_promiscuous_pkt_type_t type);

/**
  * @brief Register the RX callback function in the promiscuous mode.
  *
  * Each time a packet is received, the registered callback function will be called.
  *
  * @param cb  callback
  *
  * @return
  *    - CSI_OK: succeed
  *    - CSI_ERR_WIFI_NOT_INIT: WiFi is not initialized by csi_wifi_init
  */
int32_t csi_wifi_set_promiscuous_rx_cb(wifi_promiscuous_cb_t cb);

/**
  * @brief     Enable the promiscuous mode.
  *
  * @param     en  false - disable, true - enable
  *
  * @return
  *    - CSI_OK: succeed
  *    - CSI_ERR_WIFI_NOT_INIT: WiFi is not initialized by csi_wifi_init
  */
int32_t csi_wifi_set_promiscuous(bool en);

/**
  * @brief     Get the promiscuous mode.
  *
  * @param[out] en  store the current status of promiscuous mode
  *
  * @return
  *    - CSI_OK: succeed
  *    - CSI_ERR_WIFI_NOT_INIT: WiFi is not initialized by csi_wifi_init
  *    - CSI_ERR_WIFI_ARG: invalid argument
  */
int32_t csi_wifi_get_promiscuous(bool *en);

/**
  * @brief     Set the configuration of STA or AP
  *
  * @attention 1. This API can be called only when specified interface is enabled, otherwise, API fail
  * @attention 2. For station configuration, bssid_set needs to be 0; and it needs to be 1 only when users need to check the MAC address of the AP.
  * @attention 3. Limited to only one channel, so when in the soft-AP+station mode, the soft-AP will adjust its channel automatically to be the same as
  *               the channel of the station.
  *
  * @param     ifx  interface
  * @param     conf  station or soft-AP configuration
  *
  * @return
  *    - CSI_OK: succeed
  *    - CSI_ERR_WIFI_NOT_INIT: WiFi is not initialized by csi_wifi_init
  *    - CSI_ERR_WIFI_ARG: invalid argument
  *    - CSI_ERR_WIFI_IF: invalid interface
  *    - CSI_ERR_WIFI_MODE: invalid mode
  *    - CSI_ERR_WIFI_PASSWORD: invalid password
  *    - CSI_ERR_WIFI_NVS: WiFi internal NVS error
  *    - others: refer to the erro code in csi_err.h
  */
int32_t csi_wifi_set_config(wifi_interface_t ifx, wifi_config_t *conf);

/**
  * @brief     Get configuration of specified interface
  *
  * @param     ifx  interface
  * @param[out]  conf  station or soft-AP configuration
  *
  * @return
  *    - CSI_OK: succeed
  *    - CSI_ERR_WIFI_NOT_INIT: WiFi is not initialized by csi_wifi_init
  *    - CSI_ERR_WIFI_ARG: invalid argument
  *    - CSI_ERR_WIFI_IF: invalid interface
  */
int32_t csi_wifi_get_config(wifi_interface_t ifx, wifi_config_t *conf);

/**
  * @brief     Get STAs associated with soft-AP
  *
  * @attention SSC only API
  *
  * @param[out] sta  station list
  *
  * @return
  *    - CSI_OK: succeed
  *    - CSI_ERR_WIFI_NOT_INIT: WiFi is not initialized by csi_wifi_init
  *    - CSI_ERR_WIFI_ARG: invalid argument
  *    - CSI_ERR_WIFI_MODE: WiFi mode is wrong
  *    - CSI_ERR_WIFI_CONN: WiFi internal error, the station/soft-AP control block is invalid
  */
int32_t csi_wifi_ap_get_sta_list(wifi_sta_list_t *sta);


/**
  * @brief     Set the WiFi API configuration storage type
  *
  * @attention 1. The default value is WIFI_STORAGE_FLASH
  *
  * @param     storage : storage type
  *
  * @return
  *   - CSI_OK: succeed
  *   - CSI_ERR_WIFI_NOT_INIT: WiFi is not initialized by csi_wifi_init
  *   - CSI_ERR_WIFI_ARG: invalid argument
  */
int32_t csi_wifi_set_storage(wifi_storage_t storage);

/**
  * @brief     Set auto connect
  *            The default value is true
  *
  * @param     en : true - enable auto connect / false - disable auto connect
  *
  * @return
  *    - CSI_OK: succeed
  *    - CSI_ERR_WIFI_NOT_INIT: WiFi is not initialized by csi_wifi_init
  *    - CSI_ERR_WIFI_MODE: WiFi internal error, the station/soft-AP control block is invalid
  *    - others: refer to error code in csi_err.h
  */
int32_t csi_wifi_set_auto_connect(bool en);

/**
  * @brief     Get the auto connect flag
  *
  * @param[out] en  store current auto connect configuration
  *
  * @return
  *    - CSI_OK: succeed
  *    - CSI_ERR_WIFI_NOT_INIT: WiFi is not initialized by csi_wifi_init
  *    - CSI_ERR_WIFI_ARG: invalid argument
  */
int32_t csi_wifi_get_auto_connect(bool *en);

/**
  * @brief     Set vendor specific element
  *
  * @param     enable  enable or not
  * @param     type  information element type
  * @param     idx  information element index
  * @param     vnd_ie  pointer to a vendor specific element
  *
  * @return
  *    - CSI_OK: succeed
  *    - CSI_ERR_WIFI_NOT_INIT: WiFi is not initialized by csi_wifi_init
  *    - CSI_ERR_WIFI_ARG: invalid argument
  *    - CSI_ERR_WIFI_NO_MEM: out of memory
  */
int32_t csi_wifi_set_vendor_ie(bool enable, wifi_vendor_ie_type_t type, wifi_vendor_ie_id_t idx, uint8_t *vnd_ie);

/**
  * @brief     Define function pointer for vendor specific element callback
  * @param     ctx  reserved
  * @param     type  information element type 
  * @param     sa  source address
  * @param     vnd_ie  pointer to a vendor specific element
  * @param     rssi  received signal strength indication
  */
typedef void (*csi_vendor_ie_cb_t) (void *ctx, wifi_vendor_ie_type_t type, const uint8_t sa[6], const uint8_t *vnd_ie, int rssi);

/**
  * @brief     Set vendor specific element callback
  *
  * @param     cb   callback function
  * @param     ctx  reserved
  *
  * @return
  *    - CSI_OK: succeed
  *    - CSI_ERR_WIFI_NOT_INIT: WiFi is not initialized by csi_wifi_init
  */
int32_t csi_wifi_set_vendor_ie_cb(csi_vendor_ie_cb_t cb, void *ctx);

/**
  * @brief  get whether the wifi driver is allowed to transmit data or not
  *
  * @return
  *     - true  : upper layer should stop to transmit data to wifi driver
  *     - false : upper layer can transmit data to wifi driver
  */
bool csi_wifi_tx_is_stop(void);

/**
  * @brief  free the rx buffer which allocated by wifi driver
  *
  * @param  buffer: rx buffer pointer
  */
void csi_wifi_free_rx_buffer(void *buffer);

/**
  * @brief  transmit the buffer via wifi driver
  *
  * @param  wifi_if : wifi interface id
  * @param  buffer : the buffer to be tansmit
  * @param  len : the length of buffer
  *
  * @return
  *    - ERR_OK  : Successfully transmit the buffer to wifi driver
  *    - ERR_MEM : Out of memory
  *    - ERR_IF : WiFi driver error
  *    - ERR_ARG : Invalid argument
  */
int csi_wifi_tx(wifi_interface_t wifi_if, void *buffer, uint16_t len);

/**
  * @brief     The WiFi RX callback function
  *
  *            Each time the WiFi need to forward the packets to high layer, the callback function will be called.
  *            ebuf is rx buffer allocated by wifi driver
  */
typedef int32_t (*wifi_rxcb_t)(void *buffer, uint16_t len, void *ebuf);

/**
  * @brief     Set the WiFi RX callback
  *
  * @attention 1. Currently we support only one RX callback for each interface
  *
  * @param     ifx : interface
  * @param     fn : WiFi RX callback
  *
  * @return
  *     - CSI_OK : succeed
  *     - others : fail
  */
int32_t csi_wifi_reg_rxcb(wifi_interface_t ifx, wifi_rxcb_t fn);

/**
  \brief       Add Frame Filter Setting with Filter ID.
  \param[in]   filter  Pointer to filter setting
  \return      
*/
int32_t csi_wifi_add_framefilter(const wifi_frame_filter_t *filter);

/**
  \brief       Remove Frame Filter Setting.
  \param[in]   filter_id  Frame Filter ID
  \return      
*/
int32_t csi_wifi_remove_framefilter(uint32_t filter_id);

/**
  \brief       Enable/Disable Specified Frame Filter ID.
  \param[in]   filter_id  Frame Filter ID
  \param[in]   en  Enable or disable
  \return      
*/
int32_t csi_wifi_en_framefilter(uint32_t filter_id, bool en);

/**
  \brief       Get frame filter table list.
  \param[in]   list  frame filter table list
  \param[in]   count_out  the count of filter setting added
  \param[in]   max_count  max filter setting can be supported
  \return      
*/
int32_t csi_wifi_get_framefilter(wifi_frame_filter_list_t* list, uint32_t* count_out, uint32_t max_count);

/**
* @brief This function gets the radio status of the Wi-Fi driver.
*
* @param[out]  on_off indicates the Wi-Fi radio is on or off.
*
* Value                         |Definition                                                              |
* ------------------------------|------------------------------------------------------------------------|
* \b 0                          | OFF, the Wi-Fi radio is turned off, and Wi-Fi TX/RX is disabled.|
* \b 1                          | ON, the Wi-Fi radio is turned on, and Wi-Fi TX/RX is enabled.|
*
*
* @return  >=0 the operation completed successfully, <0 the operation failed.
*
* @note In repeater mode, both Wi-Fi interface and Wi-Fi radio are turned on/off at the same time.
*/
int32_t wifi_config_get_radio(uint8_t *on_off);

/**
* @brief This function sets the radio status of the Wi-Fi driver. This operation takes effect immediately.
*
* @param[in] on_off indicates the Wi-Fi radio is on or off.
*
* Value                         |Definition                                                              |
* ------------------------------|------------------------------------------------------------------------|
* \b 0                          | OFF, the Wi-Fi radio is turned off, and Wi-Fi TX/RX is disabled|
* \b 1                          | ON, the Wi-Fi radio is turned on, and Wi-Fi TX/RX is enabled|
*
* @return  >=0 the operation completed successfully, <0 the operation failed.
*
* @note In repeater mode, both Wi-Fi interface and Wi-Fi radio are turned on/off at the same time.
*/
int32_t wifi_config_set_radio(uint8_t on_off);

/**
* @brief This function gets the RSSI of the connected AP. It's only used for the STA mode and while the station is connected to the AP.
*
* @param[out]  rssi returns the RSSI of the connected AP.
*
* @return  >=0 the operation completed successfully, <0 the operation failed.
*
*
*/
int32_t csi_wifi_connection_get_rssi(int8_t *rssi);


#ifdef __cplusplus
}
#endif

#endif /* __CSI_WIFI_H__ */


