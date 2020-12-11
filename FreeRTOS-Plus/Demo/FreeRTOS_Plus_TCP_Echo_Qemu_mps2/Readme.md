# Emulating MPS2 Cortex M3 AN385 on QEMU

## Requirements
1. GNU Arm Embedded Toolchain download [here](https://developer.arm.com/tools-and-software/open-source-software/developer-tools/gnu-toolchain/gnu-rm/downloads)
3. qemu-arm-system download [here](https://www.qemu.org/download)
2. Make (tested on version 3.82)
4. Linux OS (tested on Ubuntu 18.04)

## How to download
Navigate to a parent directory of your choice and run the following command
```
$ git clone https://github.com/FreeRTOS/FreeRTOS.git --recurse-submodules --depth 1
```
The previous command should create a directory named **FreeRTOS**

## Networking Echo client Demo
To make networking support possible a few steps needs to be done on the machine
lets assume the following interfaces using ubuntu 18.04  or Fedora 30
(the interface names on your machine could be different)
```
l0:         loopback in terface
enp0s3:     ethernet interface
virbr0:     virtual bridge         (to be created)
virbr0-nic: veth virtual interface (to be created)
```
### A few assumptions (your numbers could vary)
```
Local Host IP address:          192.168.1.81
Local FreeRTOS IP address:      192.168.1.80
Local FreeRTOS Subnet mask:     255.255.255.0
Default Gateway IP address:     192.168.1.254
Default DNS IP address:         192.168.1.254
Echo Server IP address:         192.168.1.204
Echo Server Port:               7
Local FreeRTOS Mac address:     52:54:00:12:34:AD
```

### Building and Running

1. Fill the defines values in FreeRTOSConfig.h with what is equivalent to the
   above values on your system
```c
#define configIP_ADDR0          192
#define configIP_ADDR1          168
#define configIP_ADDR2          1
#define configIP_ADDR3          80

#define configNET_MASK0         255
#define configNET_MASK1         255
#define configNET_MASK2         255
#define configNET_MASK3         0

#define configGATEWAY_ADDR0     192
#define configGATEWAY_ADDR1     168
#define configGATEWAY_ADDR2     1
#define configGATEWAY_ADDR3     254

#define configDNS_SERVER_ADDR0  192
#define configDNS_SERVER_ADDR1  168
#define configDNS_SERVER_ADDR2  1
#define configDNS_SERVER_ADDR3  254

#define configMAC_ADDR0         0x52
#define configMAC_ADDR1         0x54
#define configMAC_ADDR2         0x00
#define configMAC_ADDR3         0x12
#define configMAC_ADDR4         0x34
#define configMAC_ADDR5         0xAD

#define configECHO_SERVER_ADDR0 192
#define configECHO_SERVER_ADDR1 168
#define configECHO_SERVER_ADDR2 1
#define configECHO_SERVER_ADDR3 204
```

2.  Build your software
```
$ make
```
options: DEBUG=1 to build with **-O0** and debugging symbols

3. On the remote machine  (ip 192.168.1.204)
```
$ sudo nc -l 7
```
4. Turn off the firewall if running
On RedHat/Fedora system (tested Fedora 30) run:
```
sudo systemctl status firewalld
sudo systemctl stop firewalld
```
On Ubuntu run:
```
$ sudo ufw disable
$ sudo ufw status
```
5. Setup the local machine
Run the following commands replacing the values  and interface names
that conform to your system
```
sudo ip link add virbr0 type bridge
sudo ip tuntap add dev virbr0-nic mode tap

sudo ip addr add 192.168.1.81/24 dev virbr0

sudo brctl addif virbr0 enp0s3
sudo brctl addif virbr0 virbr0-nic

sudo ip link set virbr0 up
sudo ip link set virbr0-nic up

sudo ip route add default via 192.168.1.254 dev virbr0
```

6. Run the demo
```
$ sudo qemu-system-arm -machine mps2-an385 -cpu cortex-m3 
          -kernel ./build/RTOSDemo.axf \
          -netdev tap,id=mynet0,ifname=virbr0-nic,script=no \
          -net nic,macaddr=52:54:00:12:34:AD,model=lan9118,netdev=mynet0 \
          -object filter-dump,id=tap_dump,netdev=mynet0,file=/tmp/qemu_tap_dump\
          -display gtk -m 16M  -nographic -serial stdio \
          -monitor null -semihosting -semihosting-config enable=on,target=native 
```
Replace the value of macaddr=52:54:00:12:34:AD with your own value from
```
configMAC_ADDR0 through  configMAC_ADDR5
```

7. Expectations
On the remote machine you should expect to see something similar to the
following:
```
$ sudo nc -l 7
Password:
TxRx message number
0FGHIJKLMNOPQRSTUVWXYZ[\]^_`abcdefghijklmnopqrstuvwxyz{|}~0123456789:;<=> ?
@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\]^_`abcdefghijklmnopqrstuvwxyz{|}~0123456789:;<=>?
@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\]^_`abcdefghijklmnopqrstuvwxyz{|}~0123456789:;<=>?
@ABCDEFGHIJKLM
```

## How to start debugging
1. gdb
<P>
Append the -s and -S switches to the previous command (qemu-system-arm)<br>
-s: allow gdb to be attached to the process remotely at port 1234 <br>
-S: start the program in the paused state <br>

run: (make sure you build the debug version)
```
$ arm-none-eabi-gdb -q ./build/RTOSDemo.axf

(gdb) target remote :1234
(gdb) break main
(gdb) c
```

2. tcpdump
To monitor packets received to qemu running the qemu command (qemu-system-arm)
    shown above will create a network packet dump that you could inspect with

```
$ sudo tcpdump -r /tmp/qemu_tap_dump  | less
```

