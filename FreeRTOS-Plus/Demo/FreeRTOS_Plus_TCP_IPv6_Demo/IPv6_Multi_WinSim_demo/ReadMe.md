# FreeRTOS+TCP IPv6 Multi-Endpoint Demo

The IPv6_Multi_WinSim Visual studio demo showcases the Multiple Interfaces (or
rather the multiple endpoints) functionality of the FreeRTOS+TCP library.
The Windows Simulator environment doesn't actually have multiple
interfaces which can be used by FreeRTOS and thus, this demo shows
the use of different endpoints which will be resolved by the OS having multiple
interfaces. It shows that the library will use different endpoints (IP-addresses)
to connect to IP-addresses on different subnets (or using different netmasks).

## Setting up the workspace

Clone the submodules used in the FreeRTOS repo:

```
git submodule update --init --recursive
```

The FreeRTOS+TCP Multiple Interface Visual Studio project file is in the following
directory: `FreeRTOS-Plus\Demo\FreeRTOS_Plus_TCP_IPv6_Demo\IPv6_Multi_WinSim_demo`

In FreeRTOS_Plus_TCP_IPv6_Multi.props, you will find a couple of macros that indicate
the location of source files:

- FREERTOS_SOURCE_DIR    The kernel sources
- FREERTOS_INCLUDE_DIR   The kernel header files
- DEMO_COMMON_SOURCE_DIR The location of the "common" directory of the demos
- PLUS_TCP_SOURCE_DIR    The FreeRTOS+TCP source files
- PLUS_TCP_INCLUDE_DIR>  The FreeRTOS+TCP header files
- UTILITIES_SOURCE_DIR   The location of the tcp_utilities directory

You can changes these directory to let the project work with a different
source tree.

## Prerequisites

[Optional] Running IPv4 demo [FreeRTOS_Plus_TCP_Minimal_Windows_Simulator](https://github.com/FreeRTOS/FreeRTOS/tree/main/FreeRTOS-Plus/Demo/FreeRTOS_Plus_TCP_Minimal_Windows_Simulator)
The instructions are provided on the following URL, see the ["Hardware Setup" and "Software Setup"](http://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/examples_FreeRTOS_simulator.html).
This will give more hands on experience of running Echo server and client.

For this demo, FreeRTOS configuration file *FreeRTOSConfig.h* needs to be updated as shown below :

*Client Configuration* :
1. `configIP_ADDR0/3`         : Setup with client IP address, when DHCP is disabled.
2. `configNET_MASK0/3`        : Setup with the appropriate network mask.
3. `configGATEWAY_ADDR0/3 `   : Setup with Default Gateway address of Client IP.
4. `configDNS_SERVER_ADDR0/3` : Setup wit DNS Server address of Client IP.

*Server Configuration :*
1. `configECHO_SERVER_ADDR_STRING` as an IPv6 Server IP address for IPv6
    validation, it can be updated to IPv4 address for IPv4 validations.
2. `configECHO_SERVER_PORT` Needs to be setup for the Server port number.

Note that, as delivered, configUSE_DHCPv6 is set to 0, so a static IP address is used.

## Selecting the Examples to Run

### The TCP client example:

This example can be enabled by setting the `mainCREATE_TCP_ECHO_TASKS_SINGLE`
macro to 1 at the top of the project's main.c source file.

The example creates two RTOS tasks that send TCP echo requests to an external
echo server using the echo port set in FreeRTOSConfig.h, then wait to receive
the echo reply within the same RTOS task.

The IP address of the echo server must be configured by updating the `configECHO_SERVER_ADDR_STRING`
as IPv4 or IPv6 address and server port number must be updated as `configECHO_SERVER_PORT` in FreeRTOSConfig.h.
The echo server must be enabled and not blocked by a firewall.

### The TCP server example:

This example can be enabled by setting the `mainCREATE_TCP_ECHO_SERVER_TASK`
macro to 1 at the top of the project's main.c source file.

This example creates an echo server that listens for echo requests on
the standard echo protocol port number 7. It then echos back any data
received on that connection.

### The UDP Echo Client example

The demo also demonstrates a IPv4/IPv6 UDP echo client which can be enabled by
setting the `mainCREATE_UDP_ECHO_TASKS_SINGLE` macro to 1 in the main file.

The UDP Echo Client creates a task and sends messages to the IP address and port
defined as `configECHO_SERVER_ADDR_STRING` (either v4 or v6 address) 
and configECHO_SERVER_PORT respectively in the FreeRTOSConfig.h file and expect to
get echo of the messages back. There should be a UDP echo server running in the 
given IP and port.

These RTOS tasks are self checking and will trigger a configASSERT() failure if they
detect a difference in the data that is received from that which was sent. As these
RTOS tasks use UDP, which can legitimately loose packets, they can cause configASSERT()
failures when they are executed in a less than perfect networking environment.

#### *Note* Sample TCP and UDP echo server can be found at the last section of ReadME.
### The IPv6_Multi_WinSim_demo demo also performs some basic network activities:

- ARP address resolution for IPv4 addresses on the LAN
- Neighbour Discovery for IPv6 addresses on the LAN
- Looking up a IPv4 or IPv6  address using DNS, either asynchronous or synchronous.
- Looking up a local host ( IPv4/6 ) using LLMNR ( not considered safe anymore )
- Talk with an NTP server and fetch the time using UDP, with IPv4/6
- Download a file from any public server using TCP/HTTP
- Ping any server on the web or on the LAN, , with IPv4 or IPv6

The demo can be easily adapted to your own needs. It works like a command line
interface ( CLI ) that performs the above tasks. Although it is called a CLI,
the demo does not have a STDIN. The commands are hard-coded in main.c pcCommandList.

The pcCommandList options can be uncommented to run the commands. Here are some examples of
valid command lines, using the keywords “http”, “ping”, “dnsq”, and “ntp:

    "http4 google.co.uk /index.html",
    "http6 amazon.com /index.html",
    "ping4 10.0.1.10",
    "ping6 2001:470:ec54::",
    "dnsq4 yahoo.com",
    "ping6 aws.com",
    "ntp6a 2.europe.pool.ntp.org",

The last line will first lookup the mentioned NTP server, send a request, and wait
for a reply. The time will be printed in the logging.

The keywords can have some single-letter suffices: 4 or 6 ( for IPv4/6 ), “a” to do
an asynchronous DNS lookup, and “c” to clear all caches before starting the task.

## Sample Echo server
##### Prerequisites : [Install go](https://go.dev/doc/install)

#### Sample UDP server in Go:
``` go

// Filename: echo_server.go 
// Run: go run echo_server.go <ip_address>:<port>
// Example IPv4:  go run echo_server.go 192.168.1.2:9000
// Example IPv6:  go run echo_server.go [fe80::1b99:a6bd:a344:b09d]:9000

package main

import (
	"fmt"
	"net"
	"os"
)

func main() {

	if len(os.Args) == 1 {
		fmt.Println("Please provide host:port")
		os.Exit(1)
	}

	// Resolve the string address to a UDP address
	udpAddr, err := net.ResolveUDPAddr("udp", os.Args[1])

	if err != nil {
		fmt.Println(err)
		os.Exit(1)
	}

	// Start listening for UDP packages on the given address
	conn, err := net.ListenUDP("udp", udpAddr)

	if err != nil {
		fmt.Println(err)
		os.Exit(1)
	}

	// Read from UDP listener 
	for {
		var buf [1024]byte
		_, addr, err := conn.ReadFromUDP(buf[0:])
		if err != nil {
			fmt.Println(err)
			return
		}

		fmt.Print(string(buf[0:]))

		// Write back the message over UDP
		conn.WriteToUDP([]byte(buf[0:]), addr)
	}
}
```

The UDP Echo Client demo also demonstrates the UDP zero copy for both IPv4 and IPv6
(based on the IP type), it can be enabled by setting `USE_ZERO_COPY` macro of the
UDPEchoClient_SingleTasks.c file to 1.

#### Sample TCP server in Go:
[TCP Echo Server](https://github.com/aws/amazon-freertos/tree/main/tools/echo_server)
