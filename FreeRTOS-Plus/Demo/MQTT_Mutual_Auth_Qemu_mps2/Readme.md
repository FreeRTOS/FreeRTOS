# Emulating MPS2 Cortex M3 AN385 on QEMU

## Requirements
1. GNU Arm Embedded Toolchain download [here](https://developer.arm.com/tools-and-software/open-source-software/developer-tools/gnu-toolchain/gnu-rm/downloads)
2. qemu-system-arm download [here](https://www.qemu.org/download)
3. Make (tested on version 3.82)

## How to download
Navigate to a parent directory of your choice and run the following command
```
$ git clone https://github.com/FreeRTOS/FreeRTOS.git --recurse-submodules --depth 1
```
The previous command should create a directory named **FreeRTOS**

## Mutual Auth MQTT Demo
To connect to the AWS IoT Core, a few steps are necessary. See the steps <br>
below in building and running.

### Building and Running

1.  Create a Thing in the AWS IoT Core 
<P>
Go to aws.amazon.com and login or create an account <br>
Navigate to AWS IoT Core and in the left menu, click on manage>All devices>Things <br>
Click "Create things" and then create a single thing.<br>
Give the thing a name, and select 'no device shadow'<br>
Save the Endpoint, Root CA, Client Cert. and Client Private key<br>

2. Fill defines values in demo_config.h 

Ensure to include the headers and footers and to format as shown in the comments for each macro.<br>
For client identifier, insert the name of the thing you created in the last step.<br>
```c
#define democonfigCLIENT_IDENTIFIER
#define democonfigMQTT_BROKER_ENDPOINT
#define democonfigROOT_CA_PEM
#define democonfigCLIENT_CERTIFICATE_PEM
#define democonfigCLIENT_PRIVATE_KEY_PEM
```

3.  Build your software
```
$ make
```
options: DEBUG=1 to build with **-O0** and debugging symbols

4. Run the demo
```
$ qemu-system-arm -machine mps2-an385 -cpu cortex-m3 \
          -kernel ./build/RTOSDemo.axf \
          -netdev user,id=mynet0 \
          -net nic,macaddr=52:54:00:12:34:AD,model=lan9118,netdev=mynet0 \
          -display none -m 16M  -nographic -serial stdio \
          -monitor null -semihosting -semihosting-config enable=on,target=native
 
```

5. Expectations

Navigate to the AWS IoT Core and click on "MQTT Test Client" <br>
In the topic section, enter "yourThingName/example/topic" <br>
With the demo running, you should see "Hello World" messages in the client <br>

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

# Note on the Entropy Source 
<P>
Within mbedtls_freertos_port.c, mbedtls_platform_entropy_poll utilizes a pseudo-random number<br>
generator. This allows MPS2-AN385 boards emulated via QEMU to establish a TLS connection, but should<br>
be updated if you plan to build a project off of this demo to improve security.<br> 
