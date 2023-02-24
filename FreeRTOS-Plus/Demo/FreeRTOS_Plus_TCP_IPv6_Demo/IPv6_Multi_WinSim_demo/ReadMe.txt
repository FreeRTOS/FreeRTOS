The FreeRTOS+TCP IPv6/multiple-interface source code and example projects are
currently provided in the FreeRTOS+TCP repository's "feature/ipv6_multi_beta"
branch. These demos only require the FreeRTOS+TCP IPv6/multiple Interface
source code and the FreeRTOS-Kernel.

The FreeRTOS+TCP Multiple Interface Visual Studio project file is in the following
directory: demos\IPv6_Multi_WinSim_demo

In FreeRTOS_Plus_TCP_IPv6_Multi.props, you will find a couple of macros that indicate
the location of source files:

- FREERTOS_SOURCE_DIR    The kernel sources
- FREERTOS_INCLUDE_DIR   The kernel header files
- DEMO_COMMON_SOURCE_DIR The location of the "common" directory of the demos
- PLUS_TCP_SOURCE_DIR    The FreeRTOS+TCP source files
- PLUS_TCP_INCLUDE_DIR>  The FreeRTOS+TCP header files
- UTILITIES_SOURCE_DIR   The location of the tcp_utilities directory

You can changes these directory to let the proyejct work with a different
source tree.

The Multiple Interface Visual studio demo showcases the Multiple Interfaces (or
rather the multiple endpoints) functionality of the FreeRTOS+TCP
IPv6/multi-interface library. The Windows Simulator environment doesn't actually
have multiple interfaces which can be used by FreeRTOS and thus, this demo shows
the use of different endpoints which will be resolved by the OS having multiple
interfaces. It shows that the library will use different endpoints (IP-addresses)
to connect to IP-addresses on different subnets (or using different netmasks).
The instructions for the full Windows demo are still relevant though as they
describe how to set up the WinPCap development environment, how to set the IP
address, and other such items. Note that, as delivered, configUSE_DHCP is set to 0,
so a static IP address is used. The instructions are provided on the following URL,
see the "Hardware Setup" section:
http://www.FreeRTOS.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/examples_FreeRTOS_simulator.html

The IPv6_Multi_WinSim_demo demo performs some basic network activities:

- ARP address resolution for IPv4 addresses on the LAN
- Neighbour Discovery for IPv6 addresses on the LAN
- Looking up a IPv4 or IPv6  address using DNS, either asynchronous or synchronous.
- Looking up a local host ( IPv4/6 ) using LLMNR ( not considered safe anymore )
- Talk with an NTP server and fetch the time using UDP, with IPv4/6
- Download a file from any public server using TCP/HTTP
- Ping any server on the web or on the LAN, , with IPv4 or IPv6

The demo can be easily adapted to your own needs. It works like a command line
interface ( CLI ) that performs the above tasks.

Here are some examples of valid command lines, using the keywords “http”, “ping”,
“dnsq”, and “ntp:

    "http4 google.co.uk /index.html",
    "http6 amazon.com /index.html",
    "ping4 10.0.1.10",
    "ping6 2001:470:ec54::",
    "dnsq4 yahoo.com",
    "ping6 aws.com",
    "ntp6a 2.europe.pool.ntp.org",

The last line will first lookup the mentioned NTP server, send a request, and wait
for a reply. The time will be printed in the logging.

Although it is called a CLI, the demo does not have a STDIN. The commands are
hard-coded in main.c

The keywords can have some single-letter suffices: 4 or 6 ( for IPv4/6 ), “a” to do
an asynchronous DNS lookup, and “c” to clear all caches before starting the task.
