PLEASE REFER TO THE APPLICATION NOTE FOR THIS MODULE FOR MORE INFORMATION 

r_gpio_rx
=========

Overview
--------
This code implements a General Purpose Input/Output driver. Common features such as reading, writing, and setting the
direction of ports and pins are supported. Enabling features such as open-drain outputs and internal pull-ups are also
supported.

Features
--------
* Read ports and pins
* Write ports and pins
* Set ports and pins as inputs and outputs
* Enable features of pins such as internal pull-ups or open-drain outputs

File Structure
--------------
r_gpio_rx
|   readme.txt
|   r_gpio_rx_if.h
|   
+---doc
|   +---ja
|   |    r01an1721jj{VERSION_NUMBER}-rx-gpio.pdf
|   +---en
|        r01an1721ej{VERSION_NUMBER}-rx-gpio.pdf
|       
+---ref
|       r_gpio_rx_config_reference.h
|       
\---src
    |   r_gpio_rx.c
    |   
    \---targets
        +---rx110
        |       r_gpio_rx110.c
        |       r_gpio_rx110.h
        |       
        +---rx111
        |       r_gpio_rx111.c
        |       r_gpio_rx111.h
        |       
        :

r_config
    r_gpio_rx_config.h

