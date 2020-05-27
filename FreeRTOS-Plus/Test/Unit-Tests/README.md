# Unit Tests for FreeRTOS-Plus libraries
This directory is made for the purpose of Unit testing and tries to provide the tools for developing unit tests along with a simple example. To that end, this directory submodules the [CMock](https://github.com/ThrowTheSwitch/CMock) framework (which submodules [Unity](https://github.com/throwtheswitch/unity/tree/cf949f45ca6d172a177b00da21310607b97bc7a7)).

## Getting Started
### Prerequisites
You can run this on any GNU Make compatible systems. But in case of DOS based systems some tweaking is required with the makefile.
To compile and run this project successfully, you must have the following:
1. Make (You can check whether you have this by typing `make --version`)
    - Not found? Try `apt-get install make`.
2. Ruby (You can check whether you have this by typing `ruby --version`)
    - Not found? Try `apt-get install ruby`.
3. Downloaded the repo with --recurse-submodules option to include CMock (and by extension Unity) in the cloned repo.
    - `git clone https://github.com/FreeRTOS/FreeRTOS.git --recurse-submodules ./FreeRTOS_Dir`

### To run the Unit tests:
Go to `FreeRTOS/FreeRTOS-Plus/Test/Unit-Tests`. Most probably you are in the mentioned directory already.
Run:
- `make clean`
- `make coverage`

You should see an output similar to this:
```
-----------------------
3 Tests 0 Failures 0 Ignored 
OK
Capturing coverage data from .
... <Skipped some lines here for the sake of brevity>
Overall coverage rate:
  lines......: 84.8% (56 of 66 lines)
  functions..: 85.7% (12 of 14 functions)
  branches...: 50.0% (2 of 4 branches)

```

NOTE: after this point all directories mentioned in the README will be relative to this path: `FreeRTOS/FreeRTOS-Plus/Test/Unit-Tests`

## Examples:
The examples are present in `/tests/example` directory. The examples are in the form of a few small '.c' and '.h' files. Open those files and have a look at all of them. These files try to show all scenarios which you might find in actual libraries (e.g. One module calling functions defined in other modules by including corresponding header files etc.).
The file that tests the functions in `hello_world.c` file is aptly named `hello_world_test.c`. It includes a header file `mock_some_value.h`. This header is present there since we will be mocking the functions declared in the file `some_value.h`.

### The Makefile
The makefile is used to make the development easier by doing all the backend work required to make CMock and Unity work. The Makefile has a special section which is bound by commented headings directing what is to be added in which section. Else everything should be self explanatory.
