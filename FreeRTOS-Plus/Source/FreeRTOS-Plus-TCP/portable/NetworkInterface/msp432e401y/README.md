# Networkinterface driver for texas instruments msp432e401y 

Networkinterface implemented as described in [Porting FreeRTOS+TCP to a Different Microcontroller ](https://www.freertos.org/FreeRTOS-Plus/FreeRTOS_Plus_TCP/Embedded_Ethernet_Porting.html). 
The driver is a modified version of the  `EMACMSP432E.c` found in [SIMPLELINK-MSP432E4-SDK](https://www.ti.com/tool/download/SIMPLELINK-MSP432E4-SDK).
It is a zero copy driver, where  rx, tx and phy  events are handled directly in the interrupt routine.
The Hardware is able to do IP checksum offloading.

## Usage

This driver require the following defines in `FreeRTOSIPConfig.h`

```c
/*in FreeRTOSIPConfig.h */
#define ipconfigUSE_LINKED_RX_MESSAGES 0
#define ipconfigZERO_COPY_TX_DRIVER 1
``` 

This driver can use the following defines in `FreeRTOSIPConfig.h`

```c
#define ipconfigDRIVER_INCLUDED_TX_IP_CHECKSUM 0
#define ipconfigDRIVER_INCLUDED_RX_IP_CHECKSUM 0
``` 

The user must provide a global structure called `g_EMAC_DriverAttrs` containing a pointer to the macaddress and other driver configutaions. The file `MSP432E4_Networkinterface.h` sould be included.
```c
/* array containing macaddress as needed in freeRTOS+TCP */
uint8_t ucMACAddress[ 6 ] = { 0xff,0xff,0xff, 0xff, 0xff, 0xff};
/* EMAC configuration structure */
const EMACMSP432E4_DriverAttrs g_EMAC_DriverAttrs = {
    .intNum = INT_EMAC0,
    .intPriority = (~0),
    .led0Pin = EMACMSP432E4_PF0_EN0LED0,
    .led1Pin = EMACMSP432E4_PF4_EN0LED1,
    .macAddress = ucMACAddress
};
``` 

### Example 
An example for the [SimpleLink™ Ethernet MSP432E401Y MCU Launchpad™](https://www.ti.com/tool/MSP-EXP432E401Y) can be found at []().


## Some notes on test checksum offloading
The main problem is that the pc does itself checksum offloading, thus is hard to send frames or ip packets with error checksums.
In Linux using `ethtools` it is possible to change some settings of eth devices.

To turn tx and rx offoload off for the devicename eth0
```bash 
sudo ethtool --offload  eth0 tx off rx off
```
To read the settings of the devicename eth0

```bash
sudo ethtool -k eth0  
```

Then unsig `nping` or `hping3` it is possible to ping with different protocol and bad checksum. Some examples
```
# tcp
sudo nping 192.168.0.10 --tcp  -c1 --badsum
sudo nping 192.168.0.10 --tcp  -c1 

# icmp
sudo hping3 192.168.0.10  -i -c 1 -b
sudo hping3 192.168.0.10  -i -c 1 

``` 
to sniff frames sent wireshark is a good option.
