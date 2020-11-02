#  MQTT Mutual Auth wolfSSL Demo

# Overview
This demo shows an MQTT subscriber / publisher establishing a TLS connection with an MQTT broker to send and receive topics in encrypted form. wolfSSL acts as a TLS library under the FreeRTOSMQTT library.
A single FreeRTOS task acts as both an MQTT subscriber and an MQTT publisher, sending and receiving topics through the AWS MQTT broker endpoint. The task holds a client certificate and authenticate each other with the MQTT broker.


# AWS IoT MQTT Broker Endpoint

wolfSSL provides an AWS IoT MQTT broker endpoint for this demo. The endpoint can be found in
demo_config.h. Certificates for the tasks and root CA are also provided in the DemoCerts folder. Please note that this endpoint and certificates are provided only for the demonstration or your evaluation purpose only. 

# MQTT Topic

In this demo, MQTT topic is defined as "demoDevice/example/topic" in DemoTasks/MutualAuthMQTTExample.c. 


# How to build and run the Demo application

By double-clicking the solution file named "mqtt_mutual_auth_demo_wolfSSL.sln" included in this folder, Visual Studio starts and shows you a project in its solution explorer. It is named "RTOSDemo" and provides a console application program which runs on windows. 

All required settings have been set in the user_settings.h header file included in the RTOSDemo folder in the solution explorer pane. The next step is to build the RTOSDemo application:

1. Build the RTOSDemo project
2. Run the RTOSDemo.exe 

You will see a console that pops up, and it shows output like the following:

```
The following network interfaces are available:
Interface 1 - rpcap://\Device\NPF_{F477128E-2150-1234-89DB-5B5983465C8D8}

The interface that will be opened is set by "configNETWORK_INTERFACE_TO_USE", which
should be defined in FreeRTOSConfig.h
Attempting to open interface number 1.
Successfully opened interface number 1.
 ...
4 440 [IP-task] [INFO] [MQTTDemo] [vApplicationIPNetworkEventHook:159] 
5 440 [IP-task] ---------STARTING DEMO---------
 ...
25 1260 [MQTTDemo] A mutually authenticated TLS connection established with a2dujmi05ideo2.iot.us-west-2.amazonaws.com:8883.
 ...
31 1360 [MQTTDemo] An MQTT connection is established with a2dujmi05ideo2.iot.us-west-2.amazonaws.com.
 ...
34 1360 [MQTTDemo] Attempt to subscribe to the MQTT topic demoDevice/example/topic.
 ...
37 1460 [MQTTDemo] Subscribed to the topic demoDevice/example/topic.
 ...
40 2260 [MQTTDemo] Publish to the MQTT topic demoDevice/example/topic.
 ...
43 2260 [MQTTDemo] Attempt to receive publish message from broker.
 ...
46 2380 [MQTTDemo] PUBACK received for packet Id 2.
 ...
Incoming Publish Topic Name: demoDevice/example/topic matches subscribed topic.
Incoming Publish Message : Hello World!

```

