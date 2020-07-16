# ChangeLog for FreeRTOS

## V200717_LTS_development_snapshot July 2020

### New Features

#### Over the Air Update

- Updated the over-the-air (OTA) agent with the ability to pause and resume an in-progress update.
- Updated the OTA demo to demonstrate how to suspend an in-progress OTA update should the MQTT connection disconnect, then resume the same update when the MQTT connection reconnects. In line with best practice, the reconnect logic uses an exponential backoff and jitter algorithm to prevent the MQTT server getting overwhelmed with connection requests if a fleet of devices get disconnected and then attempt to reconnect at the same time.
- For test purposes only, it is now possible to use OTA to downgrade the version number. That capability is disabled by default.
- Add doxygen comments to the OTA source files.

### Updates

#### Rename FreeRTOS-IoT-Libraries Directory

- The FreeRTOS-IoT-Libraries directories in the previous snapshot version (V2020218_LTS_development_snapshot) under `FreeRTOS-Plus/Source and FreeRTOS-Plus/Demo` has been renamed to *FreeRTOS-IoT-Libraries-Beta1* to make way for a parallel directory, *FreeRTOS-IoT-Libraries-Beta2*, that holds libraries for which the refactoring work is near completion (currently the MQTT library).

#### MQTT LTS rc1 Client Library (in FreeRTOS-IoT-Libraries-LTS-Beta2)

- The first release candidate for the refactored MQTT library is located in the `FreeRTOS-Plus/Source/FreeRTOS-IoT-Libraries-Beta2` directory. The library will be released in the main FreeRTOS download when the refactoring described on the [LTS roadmap](https://freertos.org/ltsroadmap.html) page is complete.
- Demos for the refactored MQTT library have been added to the `FreeRTOS-Plus/Demo/FreeRTOS-IoT-Libraries-Beta2 directory`.

#### Bugfixes in MQTT Client Library (in FreeRTOS-IoT-Libraries-LTS-Beta1)

* Improved the Keep-Alive mechanism: The MQTT library will not send PING requests when connection is not idle, which fixes a disconnect issue during OTA. In the prior version, MQTT would sometimes disconnect during OTA due to timeouts for server PING response.
* Bug fix for Keep-Alive interval: The MQTT library was incorrectly sending PING requests at intervals greater than the keep alive period sent in the CONNECT request. This has been fixed.
* Bugfix for synchronous Publish at QoS 0: The earlier implementation of IotMqtt_PublishSync  API always returned success even when network transmission of the PUBLISH packet failed. This bug has now been fixed such that the API function will return network error when network transmission fails.

#### PKCS #11

- Added doxygen to various PKCS #11 files.
- Added improved logging for mbed TLS  return codes in iot_pkcs11_mbedtls.c. 
- Added PKCS11_PAL_Initialize for initializing the PKCS #11 PAL layer.
- Addressed various MISRA violations.
- Refactored Sessions to use static memory instead of dynamic memory

#### FreeRTOS+TCP 

- Added ability to cache multiple IP addresses per DNS entry.
- Defensive security improvements: 
    - In compliance with the UDP protocol specification, prior versions of FreeRTOS+TCP accepted UDP packets that had their checksum set to 0. This release adds a new configuration parameter, `ipconfigUDP_PASS_ZERO_CHECKSUM_PACKETS`, that enables users to opt to drop UDP packets that have their checksum set to 0. Note this new setting defaults to 0, so it defaults to dropping UDP packets that have their checksum set to 0.
    - Prior versions of FreeRTOS+TCP accept IP packets that contain IP options, although those options are not processed. This release adds a new configuration parameter, `ipconfigIP_PASS_PACKETS_WITH_IP_OPTIONS`, that enables users to opt to drop IP packets that contain IP options. The default value of the configuration is set to 1, which means that IP packets that contain IP options are not dropped.
    - Setting `ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM` to 1 offloads IP checksum and length checking to the hardware. With this release, the length is checked in software even when it has already been checked in hardware.

#### Mbed TLS v2.16.7

- Upgraded the version of Mbed TLS to v2.16.7.
- Replaced copy of Mbed TLS with a submodule reference to the official [Mbed TLS GitHub repository](https://github.com/ARMmbed/mbedtls/tree/mbedtls-2.16.7).

#### Over the Air Update

- Fixed an issue for the scenario when an OTA job is force cancelled when its related download is in progress, caused due to the self-start timer starting after the OTA job document is received. The fix makes the self-start timer start when the OTA agent on the device starts, before receiving the OTA job.
