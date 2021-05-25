The [FreeRTOS 202104.00](https://github.com/FreeRTOS/FreeRTOS/tree/202104.00) release introduces the new [coreMQTT Agent library](https://github.com/FreeRTOS/coreMQTT-Agent), and includes all the Long-Term Support (LTS) libraries that are part of the [FreeRTOS-LTS 202012.01-LTS](https://github.com/FreeRTOS/FreeRTOS-LTS/tree/202012.01-LTS) release. Learn more about the FreeRTOS 202012.01 LTS libraries at [https://freertos.org/lts-libraries.html](https://freertos.org/lts-libraries.html).

## Getting started
The [FreeRTOS.org](https://www.freertos.org) website contains a [FreeRTOS Kernel Quick Start Guide](https://www.freertos.org/FreeRTOS-quick-start-guide.html), a [list of supported devices and compilers](https://www.freertos.org/RTOS_ports.html), the [API reference](https://www.freertos.org/a00106.html), and many other resources.

### Getting help
You can use your Github login to get support from both the FreeRTOS community and directly from the primary FreeRTOS developers on our [active support forum](https://forums.freertos.org).  The [FAQ](https://www.freertos.org/FAQ.html) provides another support resource.

## Cloning this repository
This repo uses [Git Submodules](https://git-scm.com/book/en/v2/Git-Tools-Submodules) to bring in dependent components.

**Note:** If you download the ZIP file provided by the GitHub UI, you will not get the contents of the submodules. (The ZIP file is also not a valid git repository)

If using Windows, set `core.symlinks` to true since copying a directory with symlinks may cause hangups:
```
git config --global core.symlinks true
```

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
This repository contains the FreeRTOS Kernel, a number of supplementary libraries including the LTS ones, and a comprehensive set of example projects.  Many libraries (including the FreeRTOS kernel) are included as Git submodules from their own Git repositories.

### Kernel source code and example projects
```FreeRTOS/Source``` contains the FreeRTOS kernel source code (submoduled from https://github.com/FreeRTOS/FreeRTOS-Kernel).

```FreeRTOS/Demo``` contains pre-configured example projects that demonstrate the FreeRTOS kernel executing on different hardware platforms and using different compilers.

### Supplementary library source code and example projects
```FreeRTOS-Plus/Source``` contains source code for additional FreeRTOS component libraries, as well as select partner provided libraries. These subdirectories contain further readme files and links to documentation.

```FreeRTOS-Plus/Demo``` contains pre-configured example projects that demonstrate the FreeRTOS kernel used with the additional FreeRTOS component libraries.

## Previous releases
[Releases](https://github.com/FreeRTOS/FreeRTOS/releases) contains older FreeRTOS releases.


## FreeRTOS Lab Projects
FreeRTOS Lab projects are libraries and demos that are fully functional, but may be experimental or undergoing optimizations and refactorization to improve memory usage, modularity, documentation, demo usability, or test coverage.

Most FreeRTOS Lab libraries can be found in the [FreeRTOS-Labs repository](https://github.com/FreeRTOS/FreeRTOS-Labs).

A number of FreeRTOS Lab Demos can be found in the [FreeRTOS Github Organization](https://github.com/FreeRTOS) by searching for "Lab" or following [this link](https://github.com/FreeRTOS?q=Lab&type=&language=) to the search results.

## coreMQTT Agent Demos
The [FreeRTOS/coreMQTT-Agent-Demos](https://github.com/FreeRTOS/coreMQTT-Agent-Demos) repository contains demos to showcase use of the [coreMQTT-Agent](https://github.com/FreeRTOS/coreMQTT-Agent) library to share an MQTT connection between multiple application tasks.

The demos show a single MQTT connection usage between multiple application tasks for interacting with AWS services (including [Over-the-air-Updates](https://docs.aws.amazon.com/freertos/latest/userguide/freertos-ota-dev.html), [Device Shadow](https://docs.aws.amazon.com/iot/latest/developerguide/iot-device-shadows.html), 
[Device Defender](https://docs.aws.amazon.com/iot/latest/developerguide/device-defender.html)) alongside performing simple Publish-Subscribe operations.
