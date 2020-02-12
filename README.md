## Getting Started

The easiest way to use FreeRTOS is to start with one of the pre-configured demo 
application projects (found in the FreeRTOS/Demo directory).  That way you will
have the correct FreeRTOS source files included, and the correct include paths
configured.  Once a demo application is building and executing you can remove
the demo application file, and start to add in your own application source
files.

See also the [FreeRTOS Kernel Quick Start Guide](https://www.freertos.org/FreeRTOS-quick-start-guide.html) or the [FreeRTOS Kernel FAQ](http://www.freertos.org/FAQHelp.html)

For detailed documentation on the FreeRTOS Kernel API's, refer to the [FreeRTOS Kernel API Reference](https://www.freertos.org/a00106.html).

## Repository Structure
This repository contains the FreeRTOS Kernel and a number of supplementary libraries.

### Kernel Sources
The FreeRTOS Kernel Source is located under [FreeRTOS/Source](https://github.com/FreeRTOS/FreeRTOS/tree/master/FreeRTOS/Source)

Hardware specific ports can be found under [FreeRTOS/Source/portable](https://github.com/FreeRTOS/FreeRTOS/tree/master/FreeRTOS/Source/portable)

A number of Demo projects can be found under [FreeRTOS/Demo](https://github.com/FreeRTOS/FreeRTOS/tree/master/FreeRTOS/Demo)

### Supplementary Library Sources
[FreeRTOS-Labs](https://github.com/FreeRTOS/FreeRTOS/tree/master/FreeRTOS-Labs) contains libraries and demos that are fully functional, but
undergoing optimizations or refactoring to improve memory usage, modularity,
documentation, demo usability, or test coverage.  At this time the projects ARE
A WORK IN PROGRESS and will be released in the main FreeRTOS directories of the
download following full review and completion of the documentation.

The [FreeRTOS-Plus/Source](https://github.com/FreeRTOS/FreeRTOS/tree/master/FreeRTOS-Plus/Source) directory contains source code for some of the FreeRTOS+ components. These subdirectories contain further readme files and links to documentation.

## Cloning

To clone using HTTPS:
```
git clone https://github.com/FreeRTOS/FreeRTOS 
```
Using SSH:
```
git clone https://github.com/FreeRTOS/FreeRTOS.git
```




