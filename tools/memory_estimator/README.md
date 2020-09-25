# MemoryEstimator

This utility helps in determining the memory estimates for FreeRTOS libraries.

# Usage

```
python memory_estimator.py -p <path_to_freertos_lts_directory> -o <optimization> -l <library_name>
```

Where:

* `<path_to_freertos_lts_directory>` is the path to the directory containing FreeRTOS LTS source code.
* `<optimization>` is the compiler optimization level (O0, Os etc).
* `<library_name>` is the library to calculate the memory estimates for.


# Options
| Short Name | Long Name | Default |Description |
| ---------- | --------- | ------- | ---------- |
| -p | --lts-path | | Path to the directory containing FreeRTOS LTS code. |
| -o | --optimization | O0 | Compiler optimization level (O0, Os etc). |
| -l | --lib | `mqtt-beta1` | The library to calculate the memory estimates for. Currently supported libraries are: `mqtt-beta1`, `light-mqtt-beta1`, `mqtt-beta2`, `https`, `shadow`, `jobs`, `ota-mqtt`, `ota-http`, `pkcs11`, `kernel`|
| -c | --compiler | arm-none-eabi-gcc | Compiler to use. |
| -s | --sizetool | arm-none-eabi-size | Size tool to use. |
| -d | --dontclean | | The generated artifacts, which include the generated Makefile and built object files, are deleted by default. Pass `-d` to ensure that the generated artifacts are not deleted. |
| -g | --generate-report | | Pass `-g` to generate a JSON report containing sizes for all libraries. If this option is used, values for `--optimization`, `--lib` and `--dontclean` are ignored. |
