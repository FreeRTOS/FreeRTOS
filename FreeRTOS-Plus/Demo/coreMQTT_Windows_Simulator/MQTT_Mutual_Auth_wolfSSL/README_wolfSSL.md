#  MQTT Mutual Auth wolfSSL Demo

# Overview
This demo shows an MQTT subscriber / publisher establishing a TLS connection with an MQTT broker to send and receive topics in encrypted form. wolfSSL acts as a TLS library under the FreeRTOS MQTT library.
A single FreeRTOS task acts as both an MQTT subscriber and an MQTT publisher, sending and receiving topics through the MQTT broker endpoint you specified. The task holds a client certificate and authenticate each other with the MQTT broker.

# How to build and run the Demo application

By double-clicking the solution file named "**mqtt_mutual_auth_demo_wolfSSL.sln**" included in this folder, Visual Studio starts and shows you a project in its solution explorer. It is named "RTOSDemo" and provides a console application program which runs on windows. 

All required settings for wolfSSL have been set in the user_settings.h header file included in the RTOSDemo folder in the solution explorer pane. For this demo to work, you need to set the following information:

1. choose interface to use
2. set MQTT broker endpoint URL
2. set root CA certificate file(.pem) path
3. set private key file(.pem) path
 


# Choose an interface to use
You should choose an interface to use to configure the demo. However you may not know how to choose it. The demo will give you  good guidance. Follow the steps below.

1. Build the RTOSDemo project
2. Run the RTOSDemo.exe 

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

The demo stops by assertion. The log saying "Creating a TLS connection to **...insert here...**:8883" has a hint. 

<br>


# Set Credentials

Please remember you need to provide the remaining information to complete the demo configuration. This time, you should open **demo_config.h** and find following defininitions:

- **democonfigMQTT_BROKER_ENDPOINT**
- **democonfigROOT_CA_PEM**
- **democonfigCLIENT_CERTIFICATE_PEM**
- **democonfigCLIENT_PRIVATE_KEY_PEM**

All have **"...insert here..."** as their defined value. This is the casuse of the assertion that stopped the demo. In the file, "...insert here..." is used as a placeholder. Therefore, you need to specify the correct value for each. Immediately above them, there is information on how and what to set for each definitions. 

Please refer the [coreMQTT Demo(Mutual Authentication)](https://www.freertos.org/mqtt/mutual-authentication-mqtt-example.html) page to get more information. 
If you completes above settings, re-build demo and run it.

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


