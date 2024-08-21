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

## PreRequisites

1. Install the following tools in the Host Machine:
   * [GNU Arm Embedded Toolchain](https://developer.arm.com/tools-and-software/open-source-software/developer-tools/gnu-toolchain/gnu-rm/downloads).
   * [qemu-arm-system](https://www.qemu.org/download).
   * Make (Version 4.3):
     ```
     sudo apt install make
     ```
2.  Clone the source code:
     ```
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


## Build and Run
Do the following steps on the host machine:

1. The echo server is assumed to be on port 7, which is the standard echo
protocol port. You can change the port to any other listening port (e.g. 3682 ).
Set `configECHO_PORT` to the value of this port.

```c
#define configECHO_PORT          ( 7 )
```

2. Build:
```shell
   make
```

3. Run:
```shell
   sudo qemu-system-arm -machine mps2-an385 -cpu cortex-m3 \
   -kernel ./build/freertos_tcp_mps2_demo.axf \
   -monitor null -semihosting -semihosting-config enable=on,target=native -serial stdio -nographic \
   -netdev user,id=mynet0, -net nic,model=lan9118,netdev=mynet0

```

6. You should see that following output on the terminal of the Echo Server (which
is running `sudo nc -l 7` or `netcat -l 7` or `nc -l -p 7` depending on your OS):
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
   sudo qemu-system-arm -machine mps2-an385 -cpu cortex-m3 \
   -kernel ./build/freertos_tcp_mps2_demo.axf \
   -monitor null -semihosting -semihosting-config enable=on,target=native -serial stdio -nographic \
   -netdev user,id=mynet0, -net nic,model=lan9118,netdev=mynet0 \
   -object filter-dump,id=tap_dump,netdev=mynet0,file=/tmp/qemu_tap_dump
```

3. Run GDB:
```shell
sudo arm-none-eabi-gdb -q ./build/freertos_tcp_mps2_demo.axf

(gdb) target remote :1234
(gdb) break main
(gdb) c
```

4. The above QEMU command creates a network packet dump in the file
`/tmp/qemu_tap_dump` which you can examine using `tcpdump` or WireShark:
```shell
sudo tcpdump -r /tmp/qemu_tap_dump  | less
```
