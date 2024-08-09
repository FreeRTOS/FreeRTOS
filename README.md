The [FreeRTOS 202212.00](https://github.com/FreeRTOS/FreeRTOS/tree/202212.00) release updates FreeRTOS Kernel, FreeRTOS+TCP, coreMQTT, corePKCS11, coreHTTP, coreJSON, AWS IoT Over-the-air-Updates (OTA), AWS IoT Device Shadow, AWS IoT Jobs, AWS IoT Device Defender, Backoff Algorithm, AWS IoT Fleet Provisioning, coreSNTP, SigV4, and FreeRTOS Cellular Interface libraries to their [LTS 2.0](https://github.com/FreeRTOS/FreeRTOS-LTS/blob/202210-LTS/CHANGELOG.md) versions. It also updates coreMQTT Agent to v1.2.0 to be compatible with coreMQTT v2.X.X, and updates MbedTLS to v3.2.1. This release also adds Visual Studio static library projects for the FreeRTOS Kernel, FreeRTOS+TCP, Logging, MbedTLS, coreHTTP, and corePKCS11. With the addition of the static library projects, all Visual Studio projects have been updated to use them. Additionally, all demos dependent on coreMQTT have been updated to work with coreMQTT v2.X.X.

## Getting started
The [FreeRTOS.org](https://www.freertos.org) website contains a [FreeRTOS Kernel Quick Start Guide](https://www.freertos.org/Documentation/01-FreeRTOS-quick-start/01-Beginners-guide/02-Quick-start-guide), a [list of supported devices and compilers](https://www.freertos.org/RTOS_ports.html), the [API reference](https://www.freertos.org/Documentation/02-Kernel/04-API-references/01-Task-creation/00-TaskHandle), and many other resources.

### Getting help
You can use your Github login to get support from both the FreeRTOS community and directly from the primary FreeRTOS developers on our [active support forum](https://forums.freertos.org).  The [FAQ](https://www.freertos.org/Why-FreeRTOS/FAQs) provides another support resource.

## Cloning this repository
This repo uses [Git Submodules](https://git-scm.com/book/en/v2/Git-Tools-Submodules) to bring in dependent components.

**Note:** If you download the ZIP file provided by the GitHub UI, you will not get the contents of the submodules. (The ZIP file is also not a valid git repository)

If using Windows, because this repository and its submodules contain symbolic links, set `core.symlinks` to true with the following command:
```
git config --global core.symlinks true
```
In addition to this, either enable [Developer Mode](https://docs.microsoft.com/en-us/windows/apps/get-started/enable-your-device-for-development) or, whenever using a git command that writes to the system (e.g. `git pull`, `git clone`, and `git submodule update --init --recursive`), use a console elevated as administrator so that git can properly create symbolic links for this repository. Otherwise, symbolic links will be written as normal files with the symbolic links' paths in them as text. [This](https://blogs.windows.com/windowsdeveloper/2016/12/02/symlinks-windows-10/) gives more explanation.

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
## CBMC

The `FreeRTOS/Test/CBMC/proofs` directory contains CBMC proofs.

To learn more about CBMC and proofs specifically, review the training material [here](https://model-checking.github.io/cbmc-training).

In order to run these proofs you will need to install CBMC and other tools by following the instructions [here](https://model-checking.github.io/cbmc-training/installation.html).
