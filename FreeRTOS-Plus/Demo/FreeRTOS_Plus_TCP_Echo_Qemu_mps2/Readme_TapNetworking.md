# TCP Echo Client Demo for MPS2 Cortex-M3 AN385 emulated using QEMU with TAP Networking

## Setup Description
The demo requires 2 components -
1. Echo Client - The demo in this repository.
1. Echo Server - An external echo server.

We need a Virtual Machine (VM) running Linux OS to run this demo. Echo Client
runs in the Virtual Machine (VM) and Echo Server runs on the host machine.
```
+--------------------------------------------------------+
|  Host Machine                                          |
|  OS - Any                                              |
|  Runs - Echo Server                                    |
|                          +--------------------------+  |
|                          | Virtual Machine (VM)     |  |
|                          | OS - Linux               |  |
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

## Setting up VM
1. Install a Virtual Machine software on your machine. On Windows you can use
[Oracle VirtualBox](https://www.virtualbox.org/) and on Mac you can use
[Parallels](https://www.parallels.com/products/desktop/).
2. Launch a Linux VM. We tested using Ubuntu 22.04.
3. Install the following tools in the VM:
   * [GNU Arm Embedded Toolchain](https://developer.arm.com/tools-and-software/open-source-software/developer-tools/gnu-toolchain/gnu-rm/downloads).
   * [qemu-arm-system](https://www.qemu.org/download).
   * Make (Version 4.3):
     ```
     sudo apt install make
     ```
   * ipcalc:
     ```
     sudo apt install ipcalc
     ```
   * brctl:
     ```
     sudo apt install bridge-utils
     ```
4. Clone the source code in the VM:
    ```shell
    git clone https://github.com/FreeRTOS/FreeRTOS.git --recurse-submodules --depth 1
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

## Enable Tap Networking in QEMU

The Tap Networking backend makes use of a tap networking device in the host. It offers very good performance and can be configured to create virtually any type of network topology.

The Echo Client in this demo runs in QEMU inside the VM. We need to enable
tap networking in QEMU to enable the Echo Client to be able to reach the Echo
Server. Do the following steps in the VM:


1. Run the `ifconfig` command to find the VM's network interface details:
```
enp0s3: flags=4163<UP,BROADCAST,RUNNING,MULTICAST>  mtu 9001
          inet 192.168.1.81  netmask 255.255.255.0  broadcast 192.168.15.255
          inet6 fe80::89c:55ff:fe3d:18ad  prefixlen 64  scopeid 0x20<link>
          ether 0a:9c:55:3d:18:ad  txqueuelen 1000  (Ethernet)
          RX packets 15001255  bytes 11443805826 (11.4 GB)
          RX errors 0  dropped 0  overruns 0  frame 0
          TX packets 9248218  bytes 2080385000 (2.0 GB)
          TX errors 0  dropped 0 overruns 0  carrier 0  collisions 0

```

2. Define a shell variable `VM_NETWORK_INTERFACE` and set its value to the
name of the network interface of the VM. For example, in the above output
of the `ifconfig` command, name of the the network interface is `enp0s3`:
```shell
export VM_NETWORK_INTERFACE=enp0s3
```

3. Define a shell variable `VM_IP_ADDRESS` and set its value to the IP address
of the VM. For example, in the above output of the `ifconfig` command, IP
address of the VM is `192.168.1.81`:
```shell
export VM_IP_ADDRESS=192.168.1.81
```

4. Define a shell variable `VM_NETMASK` and set its value to the netmask of
the VM. For example, in the above output of the `ifconfig` command, netmask
of the VM is `255.255.255.0`:
```shell
export VM_NETMASK=255.255.255.0
```

5. Calculate the CIDR of the VM from the netmask:
```shell
$ ipcalc -b 1.1.1.1 $VM_NETMASK | grep Netmask
Netmask:   255.255.255.0 = 24
```
CIDR is `24` in the above output.

6. Define a shell variable `VM_CIDR` and set its value to the CIDR of the VM
found in the above step.
```shell
export VM_CIDR=24
```

7. Find the Default Gateway for the VM:
```shell
$ ip route show
default via 192.168.1.254 dev enp0s3 proto dhcp src 192.168.1.81 metric 100
```
Default Gateway is `192.168.1.254` in the above output.

8. Define a shell variable `VM_DEFAULT_GATEWAY` and set its value to the
Default Gateway of the VM found in the above step.
```shell
export VM_DEFAULT_GATEWAY=192.168.1.254
```

9. Find the DNS Server of the VM:
```shell
$ grep "nameserver" /etc/resolv.conf
nameserver 192.168.1.254
```

10. Define a shell variable `VM_DNS_SERVER` and set its value to the
DNS Server of the host machine found in the above step.
```shell
export VM_DNS_SERVER=192.168.1.254
```

11. Pick an IP address for the QEMU which is in the same network as the VM.
This IP address must not be in-use by any other machine on the same network.
Define a shell variable `QEMU_IP_ADDRESS` and set its value to the
picked IP Address. For example, run the following command if you picked
`192.168.1.80`:
```shell
export QEMU_IP_ADDRESS=192.168.1.80
```

12. Pick a MAC address for the QEMU. Define a shell variable `QEMU_MAC_ADDRESS`
and set its value to the picked MAC Address. For example, run the following
command if you picked `52:54:00:12:34:AD`:
```shell
export QEMU_MAC_ADDRESS=52:54:00:12:34:AD
```

13. Define a shell variable `ECHO_SERVER_IP_ADDRESS` and set its value to the
IP address of the Echo Server which is running on the host. For example,
run the following command if the IP address of the Echo Server is
`192.168.1.204`:
```shell
export ECHO_SERVER_IP_ADDRESS=192.168.1.204
```

14. Turn off firewall on the VM.
On Ubuntu run:
```shell
sudo ufw disable
sudo ufw status
```
On RedHat/Fedora system run:
```shell
sudo systemctl status firewalld
sudo systemctl stop firewalld
```

15. Create virtual bridge (virbr0) and virtual NIC (virbr0-nic) to enable
networking in QEMU.
```shell
sudo ip link add virbr0 type bridge
sudo ip tuntap add dev virbr0-nic mode tap

sudo ip addr add $VM_IP_ADDRESS/$VM_CIDR dev virbr0

sudo brctl addif virbr0 $VM_NETWORK_INTERFACE
sudo brctl addif virbr0 virbr0-nic

sudo ip link set virbr0 up
sudo ip link set virbr0-nic up

sudo ip route add default via $VM_DEFAULT_GATEWAY dev virbr0
```

The following diagram shows the setup:
```
+-------------------------------------------------------------------------+
|   Virtual Machine (VM)                                                  |
|                                                                         |
|     +-------------------------+                                         | VM NIC (enp0s3)
|     |                         | Virtual NIC (virbr0-nic)                +--+
|     |  QEMU                   +--+                                      |  |
|     |                         |  |          +--------------+            |  |
|     |                         |  +--------->|    virbr0    | ---------->|  +--------> Internet
|     |                         |  |          +--------------+            |  |
|     |                         +--+           Virtual Bridge             |  |
|     |                         |                                         +--+
|     +-------------------------+                                         |
|                                                                         |
|                                                                         |
+-------------------------------------------------------------------------+
```

## Build and Run
Do the following steps in the VM where you cloned the code:

1. Set `configIP_ADDR0`-`configIP_ADDR3` in `FreeRTOSConfig.h` to the value
of `QEMU_IP_ADDRESS`:
```shell
echo $QEMU_IP_ADDRESS
```
```c
#define configIP_ADDR0          192
#define configIP_ADDR1          168
#define configIP_ADDR2          1
#define configIP_ADDR3          80
```

2. Set `configNET_MASK0`-`configNET_MASK3` in `FreeRTOSConfig.h` to the value
of `VM_NETMASK`:
```shell
echo $VM_NETMASK
```
```c
#define configNET_MASK0         255
#define configNET_MASK1         255
#define configNET_MASK2         255
#define configNET_MASK3         0
```

3. Set `configGATEWAY_ADDR0`-`configGATEWAY_ADDR3` in `FreeRTOSConfig.h` to
the value of `VM_DEFAULT_GATEWAY`:
```shell
echo $VM_DEFAULT_GATEWAY
```
```c
#define configGATEWAY_ADDR0     192
#define configGATEWAY_ADDR1     168
#define configGATEWAY_ADDR2     1
#define configGATEWAY_ADDR3     254
```

4. Set `configDNS_SERVER_ADDR0`-`configDNS_SERVER_ADDR3` in `FreeRTOSConfig.h`
to the value of `VM_DNS_SERVER`:
```shell
echo $VM_DNS_SERVER
```
```c
#define configDNS_SERVER_ADDR0  192
#define configDNS_SERVER_ADDR1  168
#define configDNS_SERVER_ADDR2  1
#define configDNS_SERVER_ADDR3  254
```

5. Set `configMAC_ADDR0`-`configMAC_ADDR5` in `FreeRTOSConfig.h` to the value
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

6. Set `configECHO_SERVER_ADDR0`-`configECHO_SERVER_ADDR3` in `FreeRTOSConfig.h`
to the value of `ECHO_SERVER_IP_ADDRESS`:
```shell
echo $ECHO_SERVER_IP_ADDRESS
```
```c
#define configECHO_SERVER_ADDR0 192
#define configECHO_SERVER_ADDR1 168
#define configECHO_SERVER_ADDR2 1
#define configECHO_SERVER_ADDR3 204
```

7. The echo server is assumed to be on port 7, which is the standard echo
protocol port. You can change the port to any other listening port (e.g. 3682 ).
Set `configECHO_PORT` to the value of this port.

```c
#define configECHO_PORT          ( 7 )
```

8. Build:
```shell
make
```

9. Run:
```shell
sudo qemu-system-arm -machine mps2-an385 -cpu cortex-m3 \
          -kernel ./build/freertos_tcp_mps2_demo.axf \
          -netdev tap,id=mynet0,ifname=virbr0-nic,script=no \
          -net nic,macaddr=$QEMU_MAC_ADDRESS,model=lan9118,netdev=mynet0 \
          -object filter-dump,id=tap_dump,netdev=mynet0,file=/tmp/qemu_tap_dump\
          -display gtk -m 16M  -nographic -serial stdio \
          -monitor null -semihosting -semihosting-config enable=on,target=native
```

10. You should see that following output on the terminal of the Echo Server (which
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
sudo qemu-system-arm -machine mps2-an385 -cpu cortex-m3 -s -S \
          -kernel ./build/freertos_tcp_mps2_demo.axf \
          -netdev tap,id=mynet0,ifname=virbr0-nic,script=no \
          -net nic,macaddr=$QEMU_MAC_ADDRESS,model=lan9118,netdev=mynet0 \
          -object filter-dump,id=tap_dump,netdev=mynet0,file=/tmp/qemu_tap_dump\
          -display gtk -m 16M  -nographic -serial stdio \
          -monitor null -semihosting -semihosting-config enable=on,target=native
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
