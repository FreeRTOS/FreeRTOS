# MemoryEstimator

This utility helps in determining the memory estimates for FreeRTOS libraries.

# Usage

```
python memory_estimator.py --path <path_to_freertos_library> --lib <library_name> --optimization <optimization>
```

Where:

* `<path_to_freertos_library>` is the path to the directory containing FreeRTOS library source code.
* `<optimization>` is the compiler optimization level (O0, O1, Os etc).
* `<library_name>` is the library to calculate the memory estimates for.


# Options
| Short Name | Long Name | Default |Description |
| ---------- | --------- | ------- | ---------- |
| -p | --path | | Path to the directory containing FreeRTOS library code. |
| -l | --lib | | The library to calculate the memory estimates for. |
| -o | --optimization | O0 | Compiler optimization level (O0, O1, Os etc). |
| -a | --disableasserts | | Disable asserts. It is done by adding `-DNDEBUG` compiler flag. |
| -d | --dontclean | | The generated artifacts, which include the generated Makefile and built object files, are deleted by default. Pass `-d` to ensure that the generated artifacts are not deleted. |
| -g | --generate-report | | Pass `-g` to generate a JSON report containing sizes for all libraries. If this option is used, values for `--optimization`, `--disableasserts` and `--dontclean` are ignored. |
