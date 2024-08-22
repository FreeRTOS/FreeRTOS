## Testing in FreeRTOS
FreeRTOS kernel consists of common code and porting layer. Extensive [static analysis](https://en.wikipedia.org/wiki/Static_program_analysis) and [dynamic analysis](https://en.wikipedia.org/wiki/Dynamic_program_analysis) are done on both to ensure functional correctness of FreeRTOS kernel.

For more information on FreeRTOS testing please refer to https://www.freertos.org/FreeRTOS-Coding-Standard-and-Style-Guide.html.

## Directory structure
This directory is in working progress -- we are migrating scattered test cases to this directory. Here only lists what's currently under this directory.

- ```./CBMC```: This directory contains automated proofs of the memory safety of various parts of the FreeRTOS code base.
- ```./CMock```: This directory contains unit tests for verification of functional correctness of FreeRTOS Kernel APIs.
- ```./Target```:  This directory contains integration tests which run on target devices to verify functional correctness of FreeRTOS Kernel APIs.
- ```./VeriFast```: This directory contains automated proofs of the functional correctness of various parts of the FreeRTOS code base.
