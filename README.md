## Getting started
The easiest way to use FreeRTOS is to start with one of the pre-configured demo application projects (found in the FreeRTOS/Demo directory).  That way you will have the correct FreeRTOS source files included, and the correct include paths configured.  Once a demo application is building and executing you can remove the demo application files, and start to add in your own application source files.  See the [FreeRTOS Kernel Quick Start Guide](https://www.freertos.org/FreeRTOS-quick-start-guide.html) for detailed instructions and other useful links.

Additionally, for FreeRTOS kernel feature information refer to the [Developer Documentation](https://www.freertos.org/features.html), and [API Reference](https://www.freertos.org/a00106.html).

### Getting help
If you have any questions or need assistance troubleshooting your FreeRTOS project, we have an active community that can help on the [FreeRTOS Community Support Forum](https://forums.freertos.org). Please also refer to [FAQ](http://www.freertos.org/FAQHelp.html) for frequently asked questions.

## Cloning this repository
This repo uses [Git Submodules](https://git-scm.com/book/en/v2/Git-Tools-Submodules) to bring in dependent components.

Note: If you download the ZIP file provided by GitHub UI, you will not get the contents of the submodules. (The ZIP file is also not a valid git repository)

To clone using HTTPS:
```
git clone https://github.com/FreeRTOS/FreeRTOS.git --recurse-submodules
```
Using SSH:
```
git clone git@github.com:FreeRTOS/FreeRTOS.git --recurse-submodules
```

If you have downloaded the repo without using the `--recurse-submodules` argument, you need to run:
```
git submodule update --init --recursive
```

## Repository structure
This repository contains the FreeRTOS Kernel, a number of supplementary libraries, and a comprehensive set of example applications.

### Kernel sources
The FreeRTOS Kernel Source is in [FreeRTOS/FreeRTOS-Kernel repository](https://github.com/FreeRTOS/FreeRTOS-Kernel), and it is consumed as a submodule in this repository.

The version of the FreeRTOS Kernel Source in use could be accessed at ```./FreeRTOS/Source``` directory.

A number of Demo projects can be found under ```./FreeRTOS/Demo``` directory.

### Supplementary library sources
The [FreeRTOS-Plus/Source](https://github.com/FreeRTOS/FreeRTOS/tree/master/FreeRTOS-Plus/Source) directory contains source code for some of the FreeRTOS+ components, as well as select partner provided libraries. These subdirectories contain further readme files and links to documentation.

[FreeRTOS-Labs](https://github.com/FreeRTOS/FreeRTOS/tree/master/FreeRTOS-Labs) contains libraries and demos that are fully functional, but undergoing optimizations or refactorization to improve memory usage, modularity,
documentation, demo usability, or test coverage.  At this time the projects ARE A WORK IN PROGRESS and will be released in the main FreeRTOS directories of the download following full review and completion of the documentation.

## Previous releases
Previous releases are available for download under [releases](https://github.com/FreeRTOS/FreeRTOS/releases).
