# Running with VSCode Launch Configurations

## Prerequisites
* Install [C/C++ extension](https://marketplace.visualstudio.com/items?itemName=ms-vscode.cpptools) in VSCode.
* Install [arm-none-eabi-gcc](https://developer.arm.com/tools-and-software/open-source-software/developer-tools/gnu-toolchain/gnu-rm/downloads).
* Install GNU make utility.
* Ensure the required binaries are in PATH with ```arm-none-eabi-gcc --version```, ```arm-none-eabi-gdb --version```, and ```make --version```.

## Building and Running
1. Open VSCode to the folder ```FreeRTOS/Demo/CORTEX_MPS2_QEMU_IAR_GCC```.
2. Open ```.vscode/launch.json```, and ensure the ```miDebuggerPath``` variable is set to the path where arm-none-eabi-gdb is on your machine.
3. Open ```main.c```, and set ```mainCREATE_SIMPLE_BLINKY_DEMO_ONLY``` to ```1``` to generate just the [simply blinky demo](https://www.freertos.org/a00102.html#simple_blinky_demo).
4. On the VSCode left side panel, select the “Run and Debug” button. Then select “Launch QEMU RTOSDemo” from the dropdown on the top right and press the play button. This will build, run, and attach a debugger to the demo program.

## Tracing with Percepio View
This demo project includes Percepio TraceRecorder, configured for snapshot tracing with Percepio View or Tracealyzer.
Percepio View is a free tracing tool from Percepio, providing the core features of Percepio Tracealyzer but limited to snapshot tracing.
No license or registration is required. More information and download is found at [Percepio's product page for Percepio View](https://traceviewer.io/get-view?target=freertos).

### TraceRecorder Integration
If you like to study how TraceRecorder is integrated, the steps for adding TraceRecorder are tagged with "TODO TraceRecorder" comments in the demo source code.
This way, if using an Eclipse-based IDE, you can find a summary in the Tasks window by selecting Window -> Show View -> Tasks (or Other, if not listed).
See also [the official getting-started guide](https://traceviewer.io/getting-started-freertos-view).

### Usage with GDB
To save the TraceRecorder trace, start a debug session with GDB.
Halt the execution and the run the command below. 
This saves the trace as trace.bin in the build/gcc folder.
Open the trace file in Percepio View or Tracealyzer.

If using an Eclipse-based IDE, run the following command in the "Debugger Console":
```
dump binary value trace.bin *RecorderDataPtr
```

If using VS Code, use the "Debug Console" and add "-exec" before the command:
```
-exec dump binary value trace.bin *RecorderDataPtr
```

Note that you can typically copy/paste this command into the debug console.


### Usage with IAR Embedded Workbench for Arm
Launch the IAR debugger. With the default project configuration, this should connect to the QEMU GDB server.
To save the trace, please refer to the "Snapshot Mode" guide at [https://percepio.com/iar](https://percepio.com/iar).
In summary:
- Download the IAR macro file [save_trace_buffer.mac](https://percepio.com/downloads/save_trace_buffer.mac) (click "save as")
- Add the macro file in the project options -> Debugger -> Use Macro File(s). 
- Start debugging and open View -> Macros -> Debugger Macros.
- Locate and run "save_trace_buffer". Open the resulting "trace.hex" in Percepio View or Tracealyzer.


