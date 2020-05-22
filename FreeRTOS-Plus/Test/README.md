## Testing in FreeRTOS
FreeRTOS (kernel and libraries) consists of common code and porting layer. Extensive [static analysis](https://en.wikipedia.org/wiki/Static_program_analysis) and [dynamic analysis](https://en.wikipedia.org/wiki/Dynamic_program_analysis) are done on both to ensure functional correctness of FreeRTOS.

Additional bounded-ness checks are done using [CBMC](https://www.cprover.org/cbmc/). Although these checks do not cover all functions, they cover considerable chunk of code base. Missing CBMC tests will be added later.

For more information on FreeRTOS testing please refer to https://www.freertos.org/FreeRTOS-Coding-Standard-and-Style-Guide.html.

## Directory structure
This directory is in working progress -- we are migrating scattered test cases to this directory. Here only lists what's currently under this directory. 

- ```./CBMC```: This directory contains automated proofs of the memory safety of various parts of the FreeRTOS code base.
- ```./CMock```: This directory has the submoduled version of CMock for providing basis Unit testing
- ```./Unit-Tests```: This directory has the Unit tests for FreeRTOS-Plus libraries. As of now, just Unit tests for +TCP (testing these).
