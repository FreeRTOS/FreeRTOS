PLEASE REFER TO THE APPLICATION NOTE FOR THIS DRIVER FOR MORE INFORMATION

r_sci_rx
========

Overview
--------------------------------------------------------------------------------
The r_sci_rx module is a multi-channel, multi-mode, interrupt-driven driver which
supports Asynchronous, Master Synchronous, and Single Master Simple SPI (SSPI)
operation for the SCI peripherals. The API includes standard functions 
to initialize a channel and to send and receive data, as well as a special control 
function for taking actions such as issuing a break signal or enabling noise 
cancellation. The driver supports all channels available on the mcu. The driver 
can be reduced in size by removing code used for parameter checking, unused 
channels, or unused modes. These configuration options can be found in 
"r_config\r_sci_rx_config.h". An original copy of the configuration file 
is stored in "r_sci_rx\ref\r_sci_rx_config_reference.h".


Features
--------
* (RX110/111/113, RX65N/651) Simultaneous operation of up to 13 channels.
* (RX231/230) Simultaneous operation of up to 7 channels.
* (RX23T) Simultaneous operation of up to 2 channels.
* (RX23W) Simultaneous operation of up to 4 channels.
* (RX64M, RX71M) Simultaneous operation of up to 9 channels.
* (RX130) Simultaneous operation of up to 4 channels.
* (RX13T) Simultaneous operation of up to 3 channels.
* (RX24T) Simultaneous operation of up to 3 channels.
* (RX24U) Simultaneous operation of up to 6 channels.
* (RX66T) Simultaneous operation of up to 7 channels
* (RX72T) Simultaneous operation of up to 7 channels
* (RX72M) Simultaneous operation of up to 13 channels
* (RX72N) Simultaneous operation of up to 13 channels
* (RX66N) Simultaneous operation of up to 13 channels
* (RX23E-A) Simultaneous operation of up to 4 channels
* Simultaneous operation of Async, Sync, or SSPI modes on different channels.
* Queueing of incoming and outgoing data for Asynchronous channels.
* Interrupt driven.


File Structure
--------------
r_sci_rx
|   readme.txt
|   r_sci_rx_if.h
|
+---doc
|   +---ja
|   |    r01an1815jj{VERSION_NUMBER}-rx-serial.pdf
|   +---en
|        r01an1815ej{VERSION_NUMBER}-rx-serial.pdf
|
+---ref
|       r_sci_rx_config_reference.h
|
+---src
    |   r_sci_rx.c
    |   r_sci_rx_platform.h
    |   r_sci_rx_private.h
    |
    +---targets
        |   
        +---rx110
        |       r_sci_rx110.c
        |       r_sci_rx110_data.c
        |       r_sci_rx110_private.h
        +---rx111
        |       r_sci_rx111.c
        |       r_sci_rx111_data.c
        |       r_sci_rx111_private.h
        :

r_config
    r_sci_rx_config.h

r_sci_rx.ftl

