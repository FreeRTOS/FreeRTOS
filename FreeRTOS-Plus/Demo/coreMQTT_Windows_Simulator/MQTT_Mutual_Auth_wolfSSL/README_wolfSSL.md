#  MQTT Mutual Auth wolfSSL Demo

# Overview
This demo shows an MQTT subscriber / publisher establishing a TLS connection with an MQTT broker to send and receive topics in encrypted form. wolfSSL acts as a TLS library under the FreeRTOS MQTT library.
A single FreeRTOS task acts as both an MQTT subscriber and an MQTT publisher, sending and receiving topics through the MQTT broker endpoint you specified. The task holds a client certificate and authenticate each other with the MQTT broker.

# How to build and run the Demo application

By double-clicking the solution file named "**mqtt_mutual_auth_demo_wolfSSL.sln**" included in this folder, Visual Studio starts and shows you a project in its solution explorer. It is named "RTOSDemo" and provides a console application program which runs on windows. 

All required settings for wolfSSL have been set in the user_settings.h header file included in the RTOSDemo folder in the solution explorer pane. For this demo to work, you need to set the following information:

1. set broker endpoint
2. set root CA certificate
3. set client certificate
4. set private key
5. choose interface to use
 
If even one of the above 1 to 4 is not set, an error will occur at build time. You should open **demo_config.h** to set them.

<br>

# Set Broker endpoint

A broker endpoint is a url that represents where MQTT subscribers and publishers access. In case your device is going to access AWS IoT device data endpoints, the endpoint would be the following format: ***account-specific-prefix*.iot.*aws-region*. amazonaws.com**.

To set broker endpoint, find the statement '**#define democonfigMQTT_BROKER_ENDPOINT    "...insert here...**' in demo_config.h and activate it by copy & paste to the outside of the commented part. Replace "...insert here..." with your broker endpoint url.
```
#define democonfigMQTT_BROKER_ENDPOINT   "a****.iot.us-***.amazonaws.com"
```
You may find "democonfigMQTT_BROKER_PORT" just below of the democonfigMQTT_BROKER_ENDPOINT macro. If your MQTT broker port is "8883", no need to specifiy that value here, since the value is defined in MutualAuthMQTTExample.c by default.

<br>

# Set Credentials

Since this demo handles mutual authentication, you need to provide rootCA certificate, client certificate and client private key. Those credentials should be set by way of following macros in demo_config.h:
1. **democonfigROOT_CA_PEM**
2. **democonfigCLIENT_CERTIFICATE_PEM**
3. **democonfigCLIENT_PRIVATE_KEY_PEM**

For setting those credentials, you have a option to specify the source of them, using file or using buffer. If you want provide credentials using buffer,
activate **democonfigCREDENTIALS_IN_BUFFER** macro. Otherwise, let the macro commented out.
```
#define democonfigCREDENTIALS_IN_BUFFER
```
<br>

## Setting credentials using file

<br>

By default, above **democonfigCREDENTIALS_IN_BUFFER** macro definition is commented out, therefore each credential should be provided by PEM encoded file. In this case, each macro definition looks like:

```
#define democonfigROOT_CA_PEM  "rootCA-PEM-encoded-file-path"
```
Activate two other macro definitions and set a file path for each.

<br>

## Setting credential using buffer

<br>

First of all, activate **democonfigCREDENTIALS_IN_BUFFER** macro.
```
#define democonfigCREDENTIALS_IN_BUFFER
```

Second, activate following three macros:

```
#define democonfigROOT_CA_PEM               "...insert here..."
#define democonfigCLIENT_CERTIFICATE_PEM    "...insert here..."
#define democonfigCLIENT_PRIVATE_KEY_PEM    "...insert here..."
```
The "...insert here..." portion of each macro should be replaced with corrensponding credential file content data. 
For exsample, democonfigROOT_CA_PEM macro would be:

```
#define democonfigROOT_CA_PEM    \
"-----BEGIN CERTIFICATE-----\n"
"MIIE0zCCA7ugAwIBAgIQGNrRniZ96LtKIVjNzGs7SjANBgkqhkiG9w0BAQUFADCB\n" \
    ......
"-----END CERTIFICATE-----\n"
```

If you completes above settings, re-build demo to continue with the final setup.

# Choose an interface to use
At this point, assume that you have completed all the necessary settings other than this interface settings and the demo is runnable. Remember you should choose an interface to use to configure the demo. However you may not know how to choose it. The demo will give you  good guidance. Run the demo.

A console that pops up appears with output similar to the following:
```
The following network interfaces are available:

Interface 1 - rpcap://\Device\NPF_{F47******-2150-****-89***-*******8C8D8}
              (Network adapter 'Qualcomm Atheros Ar81xx series PCI-E Ethernet Controller' on local host)


The interface that will be opened is set by "configNETWORK_INTERFACE_TO_USE", which
should be defined in FreeRTOSConfig.h

ERROR:  configNETWORK_INTERFACE_TO_USE is set to 0, which is an invalid value.
Please set configNETWORK_INTERFACE_TO_USE to one of the interface numbers listed above,
then re-compile and re-start the application.  Only Ethernet (as opposed to WiFi)
interfaces are supported.

HALTING
```
<br>

This output provides guidance and a list of interfaces available on the system. Open the **FreeRTOSConfig.h** file in the same folder where this readme file located, and set the selected interface number to   ***configNETWORK_INTERFACE_TO_USE*** .
Then rebuild and run the demo. This time you can see that the interface is set up and working. 
<br><br>

```
The following network interfaces are available:

Interface 1 - rpcap://\Device\NPF_{F47******-2150-****-89***-*******8C8D8}
              (Network adapter 'Qualcomm Atheros Ar81xx series PCI-E Ethernet Controller' on local host)


The interface that will be opened is set by "configNETWORK_INTERFACE_TO_USE", which
should be defined in FreeRTOSConfig.h
Attempting to open interface number 1.
Successfully opened interface number 1.
0 560 [IP-task] vDHCPProcess: offer 192.168.1.6
vDHCPProcess: offer 192.168.1.6
1 600 [IP-task] [INFO] [MQTT-wolfSSL] [vApplicationIPNetworkEventHook:158] ---------STARTING DEMO---------
2 600 [IP-task] [INFO] [MQTT-wolfSSL] [vApplicationIPNetworkEventHook:167] IP Address: 192.168.1.6
3 600 [IP-task] [INFO] [MQTT-wolfSSL] [vApplicationIPNetworkEventHook:170] Subnet Mask: 255.255.255.0
4 600 [IP-task] [INFO] [MQTT-wolfSSL] [vApplicationIPNetworkEventHook:173] Gateway Address: 192.168.1.1
5 600 [IP-task] [INFO] [MQTT-wolfSSL] [vApplicationIPNetworkEventHook:176] DNS Server Address: 192.168.1.1
6 600 [MQTTDemo] [INFO] [MQTT-wolfSSL] [prvMQTTDemoTask:356] Creating a TLS connection to ...insert here...:8883.
vAssertCalled( ***\FreeRTOS\FreeRTOS-Plus\Demo\coreMQTT_Windows_Simulator\MQTT_Mutual_Auth_wolfSSL\DemoTasks\MutualAuthMQTTExample.c, 457
```

<br>

# Demo output
Below is the output digest when a Aws MQTT IoT endpoint and appropriate credentials are set. You can find "**Hello World!**" message was published and received as a topic repeatedly. 

```
...
1 8221 [IP-task] [INFO] [MQTT-wolfSSL] [vApplicationIPNetworkEventHook:158] ---------STARTING DEMO---------
2 8221 [IP-task] [INFO] [MQTT-wolfSSL] [vApplicationIPNetworkEventHook:167] IP Address: 192.168.1.14
...
6 8222 [MQTTDemo] [INFO] [MQTT-wolfSSL] [prvMQTTDemoTask:356] Creating a TLS connection to a**************************.amazonaws.com:8883.
...
8 10221 [MQTTDemo] A mutually authenticated TLS connection established with a**************************.amazonaws.com::8883.
...
9 10221 [MQTTDemo] [INFO] [MQTT-wolfSSL] [prvMQTTDemoTask:361] Creating an MQTT connection to a**************************.amazonaws.com:.
...
14 10381 [MQTTDemo] [INFO] [MQTT] [MQTT_Connect:1798] MQTT connection established with the broker.
15 10381 [MQTTDemo] [INFO] [MQTT-wolfSSL] [prvCreateMQTTConnectionWithBroker:514] An MQTT connection is established with a**************************.amazonaws.com:.
16 10381 [MQTTDemo] [INFO] [MQTT-wolfSSL] [prvMQTTDemoTask:375] Attempt to subscribe to the MQTT topic demoDevice/example/topic.
...
19 11481 [MQTTDemo] [INFO] [MQTT-wolfSSL] [prvMQTTDemoTask:394] Publish to the MQTT topic demoDevice/example/topic.
20 11481 [MQTTDemo] [INFO] [MQTT-wolfSSL] [prvMQTTDemoTask:399] Attempt to receive publish message from broker.
...
Incoming Publish Topic Name: demoDevice/example/topic matches subscribed topic.
Incoming Publish Message : Hello World!

30 12641 [MQTTDemo] [INFO] [MQTT-wolfSSL] [prvMQTTDemoTask:404] Keeping Connection Idle...
31 14641 [MQTTDemo] [INFO] [MQTT-wolfSSL] [prvMQTTDemoTask:394] Publish to the MQTT topic demoDevice/example/topic.
32 14641 [MQTTDemo] [INFO] [MQTT-wolfSSL] [prvMQTTDemoTask:399] Attempt to receive publish message from broker.
...
Incoming Publish Topic Name: demoDevice/example/topic matches subscribed topic.
Incoming Publish Message : Hello World!

42 15741 [MQTTDemo] [INFO] [MQTT-wolfSSL] [prvMQTTDemoTask:404] Keeping Connection Idle...
43 17741 [MQTTDemo] [INFO] [MQTT-wolfSSL] [prvMQTTDemoTask:394] Publish to the MQTT topic demoDevice/example/topic.
44 17741 [MQTTDemo] [INFO] [MQTT-wolfSSL] [prvMQTTDemoTask:399] Attempt to receive publish message from broker.
...
Incoming Publish Topic Name: demoDevice/example/topic matches subscribed topic.
Incoming Publish Message : Hello World!
...

```


