# FreeRTOS+TCP IPv6 Multi-Endpoint Demo

The IPv6_Multi_WinSim Visual studio demo showcases the Multiple Interfaces (or
rather multiple endpoints) functionality of the FreeRTOS+TCP library.
The Windows Simulator environment doesn't actually have multiple
interfaces which can be used by FreeRTOS and thus, this demo shows
the use of different endpoints (IP-addresses).

## Setting up the workspace

Clone the repo along with submodules used:

```
git clone https://github.com/FreeRTOS/FreeRTOS.git --recurse-submodules
```

If you have cloned the repo without using the `--recurse-submodules`
argument, you need to run:

```
git submodule update --init --recursive
```

The FreeRTOS+TCP Multiple Interface Visual Studio project file is
[FreeRTOS_Plus_TCP_IPv6_Multi.sln](FreeRTOS_Plus_TCP_IPv6_Multi.sln).


## Prerequisites

1. The host PC needs to be connected to the network using an Ethernet cable.
2. Set `configNETWORK_INTERFACE_TYPE_TO_USE` in the [FreeRTOSConfig.h](FreeRTOSConfig.h)
   file to the name of the network interface to use , e.g. "Realtek". You can run the
   demo once to print all the available network interfaces.

## Running the demo

This demo provides 4 examples:
1. The TCP Echo Client Example
2. The TCP Echo Server Example
3. The UDP Echo Client Example
4. The CLI Example

### Running The TCP Echo Client Example

1. Set `mainCREATE_TCP_ECHO_TASKS_SINGLE` to 1 in the [main.c](main.c) file.
1. Clone the [FreeRTOS-Libraries-Integration-Tests](https://github.com/FreeRTOS/FreeRTOS-Libraries-Integration-Tests/tree/main)
   repo on the host where you want to run the echo server:
   ```
   git clone https://github.com/FreeRTOS/FreeRTOS-Libraries-Integration-Tests.git
   ```
1. Run the TCP echo server available at [tools/echo_server](https://github.com/FreeRTOS/FreeRTOS-Libraries-Integration-Tests/tree/main/tools/echo_server)
   by running the following command:
   ```
   go run echo_server.go
   ```
1. Set `configECHO_SERVER_ADDR_STRING` in the [FreeRTOSConfig.h](FreeRTOSConfig.h)
   file to the IP address of host on which you started echo server in the above
   step.
1. Set `configECHO_SERVER_PORT` in the [FreeRTOSConfig.h](FreeRTOSConfig.h)
   file to the echo server port. If you followed step 1 and 2 above to run the
   echo server, the port number is `9000` which can be changed in the
   [config.json](https://github.com/FreeRTOS/FreeRTOS-Libraries-Integration-Tests/blob/main/tools/echo_server/config.json#L5)
   file.
1. Build the project and run. You should see the output like the following:
   ```
   161 18.678 [echo_00        ] -------- Starting New Iteration --------
   162 18.916 [echo_00        ] FreeRTOS_connect returns 0
   163 19.136 [echo_00        ] FreeRTOS_send: 3289/3289
   164 19.376 [echo_00        ] Instance[0]: Good 27/27 shutdown 240
   165 19.376 [echo_00        ] 3 x 3480 = 10440 Exchange 3289/3289
   166 19.376 [echo_00        ] --------------------------------------
   ```

### Running The TCP Echo Server Example

1. Set `mainCREATE_TCP_ECHO_SERVER_TASK` to 1 in the [main.c](main.c) file.
1. Build the project and run.
   ```
   0 0.167 [IP-task        ] uxNetworkIsUp = 1
   1 0.167 [IP-task        ] uxNetworkIsUp = 2
   2 1.727 [IP-task        ] uxNetworkIsUp = 3
   3 1.727 [IP-task        ] IPv4 address = 192.168.1.83
   ```
1. Echo server should now be running and ready to accept incoming connections
   on port number 7. You can connect the echo server using any client. For example,
   you can use `nc` command to connect:
   ```
   nc 192.168.1.83 7
   Hello
   Hello
   World
   World
   ```
   Note that `192.168.1.83` is the IP address assigned to one of our endpoints as
   can be seen in the output of step 2. We send the string "Hello" and then "World"
   and we get the same strings back.

### Running The UDP Echo Client Example

1. Set `mainCREATE_UDP_ECHO_TASKS_SINGLE` to 1 in the [main.c](main.c) file.
1. Clone the [FreeRTOS-Libraries-Integration-Tests](https://github.com/FreeRTOS/FreeRTOS-Libraries-Integration-Tests/tree/main)
   repo on the host where you want to run the echo server:
   ```
   git clone https://github.com/FreeRTOS/FreeRTOS-Libraries-Integration-Tests.git
   ```
1. Set `use_udp` to `true` in the
   [tools/echo_server/config.json](https://github.com/FreeRTOS/FreeRTOS-Libraries-Integration-Tests/blob/main/tools/echo_server/config.json) file.
1. Run the UDP echo server available at [tools/echo_server](https://github.com/FreeRTOS/FreeRTOS-Libraries-Integration-Tests/tree/main/tools/echo_server)
   by running the following command:
   ```
   go run echo_server.go
   ```
1. Set `configECHO_SERVER_ADDR_STRING` in the [FreeRTOSConfig.h](FreeRTOSConfig.h)
   file to the IP address of host on which you started echo server in the above
   step.
1. Set `configECHO_SERVER_PORT` in the [FreeRTOSConfig.h](FreeRTOSConfig.h)
   file to the echo server port. If you followed step 1 and 2 above to run the
   echo server, the port number is `9000` which can be changed in the
   [config.json](https://github.com/FreeRTOS/FreeRTOS-Libraries-Integration-Tests/blob/main/tools/echo_server/config.json#L5)
   file.
1. Build the project and run. You should see the output like the following:
   ```
   12 15.722 [echo_00        ] -------- Starting New Iteration --------
   13 15.880 [echo_00        ] [Echo Client] Data was received correctly.
   14 17.880 [echo_00        ] [Echo Client] Data was received correctly.
   15 19.620 [echo_00        ] [Echo Client] Data was received correctly.
   16 21.380 [echo_00        ] [Echo Client] Data was received correctly.
   17 23.160 [echo_00        ] [Echo Client] Data was received correctly.
   18 24.840 [echo_00        ] Exchange (Sent/Received) : 100/99
   19 24.840 [echo_00        ] --------------------------------------
   ```

### Running The CLI Example

1. Set `mainCREATE_CLI_TASK` to 1 in the [main.c](main.c) file.
1. Uncomment the commands that you want to execute in the
   `pcCommandList` array in the [main.c](main.c) file. By default,
   only the `ifconfig` command is enabled.
1. Set `ipconfigHAS_PRINTF` to 1 in the [FreeRTOSIPConfig.h](FreeRTOSIPConfig.h)
   file.
1. Build the project and run. You should see the output like the following:
   ```
   44 3.742 [cli            ]
   45 3.742 [cli            ]
   46 3.742 [cli            ] /*==================== ifconfig (1/1) ====================*/
   47 3.742 [cli            ]
   48 3.742 [cli            ] Interface eth0
   49 3.742 [cli            ] IP-address : 192.168.1.83
   50 3.742 [cli            ] Default IP : 192.168.2.114
   51 3.742 [cli            ] End-point  : up = yes method DHCP
   52 3.742 [cli            ] Net mask   : 255.255.255.0
   53 3.742 [cli            ] GW         : 192.168.1.1
   54 3.742 [cli            ] DNS-0      : 192.168.1.1
   55 3.742 [cli            ] DNS-1      : 0.0.0.0
   56 3.742 [cli            ] Broadcast  : 192.168.1.255
   57 3.742 [cli            ] MAC address: 00-11-22-33-44-41
   58 3.742 [cli            ]
   59 3.742 [cli            ] IP-address : 2001:470:ed44::4d6d:0:3c15:0
   60 3.742 [cli            ] End-point  : up = yes method static
   61 3.742 [cli            ] Prefix     : 2001:470:ed44::/64
   62 3.742 [cli            ] GW         : fe80::ba27:ebff:fe5a:d751
   63 3.742 [cli            ] DNS-0      : 2001:4860:4860::8888
   64 3.742 [cli            ] DNS-1      : fe80::1
   65 3.742 [cli            ] MAC address: 00-11-22-33-44-41
   66 3.742 [cli            ]
   67 3.742 [cli            ] IP-address : fe80::7009
   68 3.742 [cli            ] End-point  : up = yes method static
   69 3.742 [cli            ] Prefix     : fe80::/10
   70 3.742 [cli            ] GW         : ::
   71 3.742 [cli            ] DNS-0      : ::
   72 3.742 [cli            ] DNS-1      : ::
   73 3.742 [cli            ] MAC address: 00-11-22-33-44-41
   74 3.742 [cli            ]
   ```

## Advanced Topics

### Using static IP configuration

Set `ipconfigUSE_DHCP` to 0 and set the following in the
[FreeRTOSConfig.h](FreeRTOSConfig.h) file:

* `configIP_ADDR0/3`         : Set to the IP address. It is used when DHCP is disabled.
* `configNET_MASK0/3`        : Set to the appropriate network mask.
* `configGATEWAY_ADDR0/3 `   : Set to the Default Gateway address.
* `configDNS_SERVER_ADDR0/3` : Set to the DNS Server address.

Note that we have only tested this demo with `ipconfigUSE_DHCPv6`
set to 0.

### Enabling debug logs

Set `ipconfigHAS_PRINTF` and `ipconfigHAS_DEBUG_PRINTF` to 1 in the
[FreeRTOSIPConfig.h](FreeRTOSIPConfig.h) file.

### Using Zero Copy

The UDP Echo Client demo also demonstrates the UDP zero copy which can be enabled
by setting `USE_ZERO_COPY` to 1 at the top of the
[UDPEchoClient_SingleTasks.c](UDPEchoClient_SingleTasks.c) file.

### Using the project in a different source tree

The following macros in the [FreeRTOS_Plus_TCP_IPv6_Multi.props](FreeRTOS_Plus_TCP_IPv6_Multi.props)
file can be updated to se this project in a different source tree:

* FREERTOS_SOURCE_DIR    : The location of the FreeRTOS Kernel source files.
* FREERTOS_INCLUDE_DIR   : The location of the FreeRTOS Kernel header files.
* DEMO_COMMON_SOURCE_DIR : The location of the "common" directory of the demos.
* PLUS_TCP_SOURCE_DIR    : The location of the FreeRTOS+TCP source files.
* PLUS_TCP_INCLUDE_DIR>  : The location of the FreeRTOS+TCP header files.
* UTILITIES_SOURCE_DIR   : The location of the tcp_utilities directory.
