## Getting Started

The easiest way to use FreeRTOS is to start with one of the pre-configured demo 
application projects (found in the FreeRTOS/Demo directory).  That way you will
have the correct FreeRTOS source files included, and the correct include paths
configured.  Once a demo application is building and executing you can remove
the demo application files, and start to add in your own application source
files.  See the [FreeRTOS Kernel Quick Start Guide](https://www.freertos.org/FreeRTOS-quick-start-guide.html) 
for detailed instructions and other useful links.

Additionally, for FreeRTOS kernel feature information refer to the [Developer Documentation](https://www.freertos.org/features.html), and [API Reference](https://www.freertos.org/a00106.html).

### Getting Help

If you have any questions or issues, then we provide our community responsive active assistance on [FreeRTOS support forum](https://forums.freertos.org).

## Repository Structure
This repository contains the FreeRTOS Kernel, a number of supplementary libraries, and a comprehensive set of example applications.

### Kernel Sources
The FreeRTOS Kernel Source is located under [FreeRTOS/Source](https://github.com/FreeRTOS/FreeRTOS/tree/master/FreeRTOS/Source)

Hardware specific ports can be found under [FreeRTOS/Source/portable](https://github.com/FreeRTOS/FreeRTOS/tree/master/FreeRTOS/Source/portable)

A number of Demo projects can be found under [FreeRTOS/Demo](https://github.com/FreeRTOS/FreeRTOS/tree/master/FreeRTOS/Demo)

### Supplementary Library Sources
The [FreeRTOS-Plus/Source](https://github.com/FreeRTOS/FreeRTOS/tree/master/FreeRTOS-Plus/Source) directory contains source code for some of the FreeRTOS+ components, as well as select partner provided libraries. These subdirectories contain further readme files and links to documentation.

[FreeRTOS-Labs](https://github.com/FreeRTOS/FreeRTOS/tree/master/FreeRTOS-Labs) contains libraries and demos that are fully functional, but undergoing optimizations or refactoring to improve memory usage, modularity,
documentation, demo usability, or test coverage.  At this time the projects ARE
A WORK IN PROGRESS and will be released in the main FreeRTOS directories of the
download following full review and completion of the documentation.

## Cloning

To clone using HTTPS:
```
git clone https://github.com/FreeRTOS/FreeRTOS 
```
Using SSH:
```
git clone git@github.com:FreeRTOS/FreeRTOS.git
```




