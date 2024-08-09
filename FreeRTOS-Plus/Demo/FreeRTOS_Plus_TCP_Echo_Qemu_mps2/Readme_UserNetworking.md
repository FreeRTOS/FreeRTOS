# TCP Echo Client Demo for MPS2 Cortex-M3 AN385 emulated using QEMU with User Mode Networking

## Setup Description
The demo requires 2 components -
1. Echo Client - The demo in this repository.
1. Echo Server - An echo server.

```
+--------------------------------------------------------+
|  Host Machine                                          |
|  OS - Any                                              |
|  Runs - Echo Server                                    |
|                          +--------------------------+  |
|                          |                          |  |
|                          | QEMU                     |  |
|                          | Runs - Echo Client       |  |
|                          |                          |  |
|  +----------------+      |    +----------------+    |  |
|  |                |      |    |                |    |  |
|  |                |      |    |                |    |  |
|  |  Echo Server   | <-------> |   Echo Client  |    |  |
|  |                |      |    |                |    |  |
|  |                |      |    |                |    |  |
|  |                |      |    |                |    |  |
|  +----------------+      |    +----------------+    |  |
|                          |                          |  |
|                          +--------------------------+  |
+--------------------------------------------------------+
```

## Launch Echo Server
Launch Echo Server on the host machine.

### Host OS is Linux
* Install `netcat`:
   ```
   sudo apt install netcat
   ```
* Start an Echo Server on port 7:
   ```shell
   sudo nc -l 7
   ```

### Host OS is Windows
* Install [Npcap/Nmap](https://nmap.org/download.html#windows).
* Start an Echo Server on port 7:
    ```shell
    ncat -l 7
    ```

### Host OS is Mac
* Install `netcat`:
   ```shell
   brew install netcat
   ```
* Start an Echo Server on port 7:
    ```shell
    nc -l -p 7
    ```

## Enable User Mode Networking in QEMU

The User Mode Networking is implemented using *slirp*, which provides a full
TCP/IP stack within QEMU and uses it to implement a virtual NAT network. It does
not require Administrator privileges.

User Mode Networking has the following limitations:

 - The performance is not very good because of the overhead involved..
 - ICMP does not work out of the box i.e. you cannot use ping within the guest.
   Linux hosts require one time setup by root to make ICMP work within the
   guest.
 - The guest is not directly accessible from the host or the external network.

Do the following steps on the host machine:

1. Pick a MAC address for the QEMU. Define a shell variable `QEMU_MAC_ADDRESS`
and set its value to the picked MAC Address. For example, run the following
command if you picked `52:54:00:12:34:AD`:
```shell
export QEMU_MAC_ADDRESS=52:54:00:12:34:AD
```

2. Define a shell variable `ECHO_SERVER_IP_ADDRESS` and set its value to the
IP address of the Echo Server which is running on the host. For example,
run the following command if the IP address of the Echo Server is
`192.168.76.2`:
```shell
export ECHO_SERVER_IP_ADDRESS=192.168.76.2
```

## Build and Run
Do the following steps on the host machine:

1. Set `configMAC_ADDR0`-`configMAC_ADDR5` in `FreeRTOSConfig.h` to the value
of `QEMU_MAC_ADDRESS`:
```shell
echo $QEMU_MAC_ADDRESS
```
```c
#define configMAC_ADDR0         0x52
#define configMAC_ADDR1         0x54
#define configMAC_ADDR2         0x00
#define configMAC_ADDR3         0x12
#define configMAC_ADDR4         0x34
#define configMAC_ADDR5         0xAD
```

2. Set `configECHO_SERVER_ADDR0`-`configECHO_SERVER_ADDR3` in `FreeRTOSConfig.h`
to the value of `ECHO_SERVER_IP_ADDRESS`:
```shell
echo $ECHO_SERVER_IP_ADDRESS
```
```c
#define configECHO_SERVER_ADDR0 192
#define configECHO_SERVER_ADDR1 168
#define configECHO_SERVER_ADDR2 76
#define configECHO_SERVER_ADDR3 2
```

3. Build:
```shell
   make
```

4. Run:
```shell
   qemu-system-arm -machine mps2-an385 -cpu cortex-m3 —kernel
      build/freertos_tcp_mps2_demo.axf -monitor null -semihosting
      -semihosting-config enable=on,target=native -serial stdio -nographic
      -netdev user,id=mynet0,net=192.168.76.0/24,dhcpstart=192.168.76.9 -net
      nic,macaddr=$QEMU_MAC_ADDRESS,model=lan9118,netdev=mynet0
```
Adding `-netdev user,id=mynet0,net=192.168.76.0/24,dhcpstart=192.168.76.9` to
the qemu command line changes the network configuration to use 192.168.76.0/24
instead of the default (10.0.2.0/24) and starts guest DHCP allocation from
9 (instead of 15).

5. You should see that following output on the terminal of the Echo Server (which
is running `sudo nc -l 7` or `netcat -l 7` depending on your OS):
```
0FGHIJKLMNOPQRSTUVWXYZ[\]^_`abcdefghijklmnopqrstuvwxyz{|}~0123456789:;<=> ?
@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\]^_`abcdefghijklmnopqrstuvwxyz{|}~0123456789:;<=>?
@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\]^_`abcdefghijklmnopqrstuvwxyz{|}~0123456789:;<=>?
@ABCDEFGHIJKLM
```

## Debug
1. Build with debugging symbols:
```
make DEBUG=1
```

2. Start QEMU in the paused state waiting for GDB connection:
```shell
   qemu-system-arm -machine mps2-an385 -cpu cortex-m3 —kernel -s -S
      build/freertos_tcp_mps2_demo.axf -monitor null -semihosting
      -semihosting-config enable=on,target=native -serial stdio -nographic
      -netdev user,id=mynet0,net=192.168.76.0/24,dhcpstart=192.168.76.9 -net
      nic,macaddr=$QEMU_MAC_ADDRESS,model=lan9118,netdev=mynet0
```

3. Run GDB:
```shell
$ arm-none-eabi-gdb -q ./build/freertos_tcp_mps2_demo.axf

(gdb) target remote :1234
(gdb) break main
(gdb) c
```

4. The above QEMU command creates a network packet dump in the file
`/tmp/qemu_tap_dump` which you can examine using `tcpdump` or WireShark:
```shell
sudo tcpdump -r /tmp/qemu_tap_dump  | less
```
