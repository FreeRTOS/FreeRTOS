
# Setup your Development Environment
This demo requires the following packages to build and debug:
* Shell: A posix-like shell environmnet. (e.g., sh, bash, or zsh
* Posix Compatible Environment: (e.g., linux, macos, MSYS2, or Cygwin)
* Compiler: gcc or clang (with gcc frontend)
* Debugger: gdb or lldb
* Build Tool: make
* IDE (optional): Microsoft Visual Studio Code (VS Code)

## Microsoft Windows with MSYS2
### Install the MSYS2 Runtime
*Option A*: Download the gui installer from [msys2.org](https://www.msys2.org/) or

*Option B*: Instally msys2 using the [Microsoft winget](https://github.com/microsoft/winget-cli/releases) package manager:
>```powershell
>winget install msys2
>```

### Install the GCC MinGW Toolchain with pacman
Open the MSYS2 terminal ( *MSYS2 MSYS* in the start menu ).

Using the MSYS2 terminal, install the required packages with the pacman command:
>*MSYS2: bash*
>```bash
>pacman -S --needed --noconfirm base-devel mingw-w64-x86_64-toolchain
>```

Optionally, install the llvm / clang toolchain
>*MSYS2: bash*
>```bash
>pacman -S --needed mingw-w64-x86_64-lldb mingw-w64-x86_64-llvm mingw-w64-x86_64-clang
>```

Finally, determine the windows path for your MinGW bin directory with the following command:
>*MSYS2: bash*
>```bash
>cygpath -w $(dirname $(which gcc))
>```

### Add MinGW to your windows PATH
Add the Mingw-w64 bin folder to the Windows PATH with the following steps:

1. In the Windows search bar, search for and select ```Edit environment variables for your account```.
3. Under the *User Variables for YourUserName* header, Select the **Path** entry and select the **Edit** button.
4. Select the **New** button and add the MinGW bin directory path determined in the previous step (usually ```C:\msys64\mingw64\bin```) to the list.
5. Select the **OK** to save the updated PATH environment variable.
6. Select the **OK** to close the *Environment Variables* editor.

> Note: You will need to reopen any apps for the new PATH settings to take effect.

## Install Windows Subsystem for Linux (WSL)
Windows Subsystem for Linux provides a more or less complete linux distribution tightly integrated into Microsoft Windows.

Open an elevated Windows Powershell session:
1. Click the start button
2. Search for ```PowerShell```
3. Select ```Run as Administator```

In the elevated PowerShell console run the following command to install [Windows Subsystem for Linux (WSL)](https://docs.microsoft.com/en-us/windows/wsl/install):

>*PowerShell*
> ```powershell
>wsl --install
>```

Open a terminal in your WSL linux environment and follow the instructions below for setting up the toolchain for your chosen Windows Subsystem for Linux Distibution.

## Debian / Ubuntu Linux and derivatives
From a terminal, install the required pakages wth apt-get:
>```
>sudo apt-get install -y build-essential gcc gdb make
>```

Optionally, install the LLVM toolchain with the following command:
>```
>sudo apt-get install -y llvm clang lldb
>```

## Redhat Linux and derivatives
From a terminal, install the required pakages with dnf:
>```
>sudo dnf install gcc gdb make
>```

Optionally, install the LLVM toolchain with the following command:
>```
>sudo dnf install -y llvm clang lldb
>```

## MacOS
Install the Apple commandline developer tools including the AppleClang toolchain with lldb using the following command in Terminal:
>```
>xcode-select --install
>```
Due to code signing requirments in MacOS, running gdb is challenging. For this reason, we suggest using the included clang compiler and lldb debugger.

Note: Apple's command line developer tools installer adds a clang wrapper in ```/usr/bin/gcc``` for compatibility.

## Install and Configure Visual Studio Code
Download the [Visual Studio Code package for your platform](https://code.visualstudio.com/Download) from the Visual Studio Code website and install it in the normal way for your platform.

> Note: For the Windows Subsystem for Linux platform, ensure that you install the native windows VS Code package.
> For more information, you may refernce the [Visual Studio Code WSL documentation](https://code.visualstudio.com/docs/remote/wsl).

### Install VS Code Extensions
Next, Install the following Visual Studio Code extensions by selecting the "install" button on the extension web page linked below or by searching for the relevant extension in the Visual Studio Code **Extensions** tab in the left-hand sidebar.

* [C/C++](https://marketplace.visualstudio.com/items?itemName=ms-vscode.cpptools) Extension, used to enable code syntax hilighting and debugging
* [Remote Development](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.vscode-remote-extensionpack) Extension Pack, paritcularly useful for WSL

### Add the VS Code launcher to your PATH
Launch Visual Studio Code and open the **Command Palette* with ```CTRL+SHIFT+P``` (windows, linux) or ```CMD+SHIFT+P``` (MacOS).

Search for "Shell Command: Install ‘code’ command in Path" and select the command with the ```ENTER``` or ```RETURN``` key.

This allows you to launch VS Code from your system's commandline with the ```code``` commnd.

## Validate your installation:

Check that the necessary binaries are available in your terminal PATH by running the following commands:
>*bash*
>```bash
>gcc --version
>make --version
>lldb --version
>gdb --version
>```

# Build on the command line
Navigate to the Posix_GCC directory in your FreeRTOS download and build
>*bash*
>```bash
> cd /path/to/FreeRTOS/Demo/Posix_GCC
>```
## Building with GCC
>*bash*
>```bash
> make clean
> make CC=gcc
>```
## Building with Clang
>*bash*
>```bash
> make clean
> make CC=clang
>```

# Debugging with Visual Studio Code
## Open the Project in VS Code on Linux, MacOS, or Windows with MSYS2
Ooen the project directory in Visual Studio Code using one of the
>*bash*
>```
> code /path/to/FreeRTOS/Demo/Posix_GCC
>```

Alternatively, open VSCode from your system launcher, select **File**->**Open Folder** and navigate to the ```FreeRTOS/Demo/Posix_GCC``` directory.

## Open the Project in VS Code with Windows Subsystem for Linux
From your WSL Terminal, run the following command:

>*WSL Terminal*
>```bash
> code /path/in/wsl/to/FreeRTOS/Demo/Posix_GCC
>```

To open the project without using the command line:
1. Open VSCode from the start menu
2. Press the ```F1``` key or ```CTRL+SHIFT+P``` to open the VS Code command palette
3. Select **WSL: New WSL Window** for the default distro or **WSL: New WSL Window using Distro** for a specific distro.
4. Finally, select the **File**->**Open Folder** menu item and navigate to the ```FreeRTOS/Demo/Posix_GCC``` directory.

## Build the demo and run it in the debugger

1. On the VSCode left side panel, select **Run and Debug**
2. Select the relevant launch configuration for your preferred debugger:
    - Linux: select either **Launch lldb** or **Launch gdb** depending on your preferred debugger
    - Windows with MSYS2: select **Launch GDB MSYS2**
    - Window Subsystem for Linux: select **Launch GDB Ubuntu WSL**

Finally, select the green triangle button to begin debugging.

## On Windows using Ubuntu WSL
On the VSCode left side panel, select the **Run and Debug** button, then select  and press the green triangle button. This will build, run, and attach a debugger to the demo program.

For additional information, you may refer to the [Visual Studio Code mingw documentation](https://code.visualstudio.com/docs/cpp/config-mingw) page.

## On Windows using MSYS2
2. Open VSCode to the folder ```FreeRTOS/Demo/Posix_GCC```.
3. In ```.vscode/settings.json```, ensure the ```path``` variable under ```MSYS2``` is set to the ```bash.exe``` under your msys64 installation directory. The path should resemble ```${path to msys2 installation}\\msys64\\usr\\bin\\bash.exe```.
4. On the VSCode left side panel, select the “Run and Debug” button. Then select the “Launch GDB MSYS2” and press the play button to begin debugging.
    1. If the demo was previously built by Ubuntu WSL, make sure to ```make clean``` before building on MSYS2.

# Profiling your application

## Introduction [(from the official gprof doc)](https://sourceware.org/binutils/docs/gprof/Introduction.html#Introduction)
Profiling allows you to learn where your program spent its time and which
functions called which other functions while it was executing.  This information
can show you which pieces of your program are slower than you expected, and
might be candidates for rewriting to make your program execute faster.  It can
also tell you which functions are being called more or less often than you
expected.  This may help you spot bugs that had otherwise been unnoticed.

## Requirements
### gprof
Version as tested: GNU gprof (GNU Binutils) 2.36
### make
Version as tested: GNU Make 3.82
### gcc
Version as tested: gcc (GCC) 11.0.0

## Generating Profiles
```
$ make PROFILE=1
```
Run your application
```
$ ./build/posix_demo
```
Since FreeRTOS and its application never come to an end and typically run
forever.  The user has to kill the application with **Ctrl_C**  when they feel
satisfied that the application achieved its intented task.  Killing the
application will force the profiling file *gmon.out* to be generated
automatically.
In order to make sense of this file, the user has to convert the file with:
```
$ make profile
```
After running the previous command, two (2) profiling files
*prof_call_graph.txt* and *prof_flat.txt* will be generated and placed in
the build directory.
* *prof_call_graph.txt*: The call graph shows which functions called which
others, and how much time each function used when its subroutine calls are
included.
* *prof_flat.txt*: The flat profile shows how much time was spent
executing directly in each function.
In order to understand the outputs generated, the best way is to read the
official documentation of gprof
[here](https://sourceware.org/binutils/docs/gprof/Output.html#Output)


# Run your application with Sanitizers
## Introduction
* AddressSanitizer, a fast memory error detector.  Memory
access instructions are instrumented to detect out-of-bounds and use-after-free
bugs
* LeakSanitizer, a memory leak detector.  This option only matters for linking of
executables and the executable is linked against a library that overrides malloc
and other allocator functions

## Building and Running the Application
```
$ make SANITIZE_ADDRESS=1
or
$ make SANITIZE_LEAK=1
```
Then run your program normally.
```
$ ./build/posix_demo
```
If an error is detected by the sanitizer, a report showing the error will be printed to stdout.
