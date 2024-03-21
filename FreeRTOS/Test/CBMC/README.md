CBMC Proof Infrastructure
=========================

This directory contains automated proofs of the memory safety of various parts
of the FreeRTOS codebase. A continuous integration system validates every
pull request posted to the repository against these proofs, and developers can
also run the proofs on their local machines.

The proofs are checked using the
[C Bounded Model Checker](http://www.cprover.org/cbmc/), an open-source static
analysis tool
([GitHub repository](https://github.com/diffblue/cbmc)). This README describes
how to run the proofs on your local clone of FreeRTOS.


Building and running proofs
--------------------------

Currently, only python based builds are supported for the CBMC proofs. The proofs
can be run on Linux and MacOS. Windows users can use [WSL](https://docs.microsoft.com/en-us/windows/wsl).
The below section outlines the instructions for the Python based build.

### Prerequisites

On Windows, you can install WSL using these simple [instructions](https://docs.microsoft.com/en-us/windows/wsl/install).

You will need Python version >= 3.7.
And you will need Make to build and run the proofs.

If you are running on a 64-bit machine, please install the 32-bit version of gcc
libraires. For example, on linux, one would run the following command to install
the libraries: `sudo apt-get install gcc-multilib`

### Installing CBMC

- The latest installation instructions can be found on the
  [releases](https://github.com/diffblue/cbmc/releases) page of the CBMC repository.

- Please follow all the installation instructions given for your platform.

- Ensure that you can run the programs `cbmc`, `goto-cc` (or `goto-cl`
  on Windows), and `goto-instrument` from the command line. If you cannot run these
  commands, please refer to the above instructions to install CBMC.

### Installing CBMC-viewer (to generate the report)

- The latest installation instructions can be found on the
  [releases](https://github.com/awslabs/aws-viewer-for-cbmc/releases) page of the CBMC-viewer repository.

- Please follow all the installation instructions given for your platform.

- Ensure that you can run the programs `cbmc-viewer`. If not, please verify
  that all instructions above have been followed.

### Setting up the proofs

Make sure that all the submodules of the FreeRTOS repository have been cloned. To
clone all the submodules, go to the root of the FreeRTOS repository and run this
command: `git submodule update --init --recursive --checkout`.

Change into the `proofs` directory and run
```
python3 prepare.py
```
If you are on a Windows machine but want to generate Linux Makefiles (or vice
versa), you can pass the `--system linux` or `--system windows` options to those
programs.

### Running the proofs

Each of the leaf directories under `proofs` is a proof of the memory
safety of a single entry point in FreeRTOS. The scripts that you ran in the
previous step will have left a Makefile in each of those directories. To
run a proof, change into the directory for that proof and run `make`.
The proofs may take some time to run; they eventually write their output to
`cbmc.txt`, which should have the text `VERIFICATION SUCCESSFUL` at the end.

The make command will also generate a report in html and json format which makes
understanding the failures easier.

#### CBMC results

As a result, a CBMC report will be generated for every test case. Taking [TaskCreate](./proofs/Task/TaskCreate) as an example, an html folder is generated, such as `./proofs/Task/TaskCreate/html`. Within this folder, both HTML and JSON formats are available to indicate the CBMC result for better readability. The `html/index.html` file in TaskCreate, generated after running the proofs, is provided below. Note that it is expected to see `None` under the `Errors` section.

<div style="padding: 10px;">
  <h4>CBMC report</h4>
  <div class="coverage">
      <h5>Coverage</h5>
      <p>
        Coverage: 0.99 (reached 140 of 141 reachable lines)
      </p>
      <table class="coverage">
        <tr>
          <th class="coverage">Coverage</th>
          <th class="function">Function</th>
          <th class="file">File</th>
        </tr>
        <tr>
          <td class="coverage">1.00 (6/6)</td>
          <td class="function">vListInitialise</td>
          <td class="file">Source/list.c</td>
        </tr>
        <tr>
          <td class="coverage">1.00 (2/2)</td>
          <td class="function">vListInitialiseItem</td>
          <td class="file">Source/list.c</td>
        </tr>
        <tr>
          <td class="coverage">1.00 (20/20)</td>
          <td class="function">prvAddNewTaskToReadyList</td>
          <td class="file">Source/tasks.c</td>
        </tr>
        <tr>
          <td class="coverage">1.00 (17/17)</td>
          <td class="function">prvCreateTask</td>
          <td class="file">Source/tasks.c</td>
        </tr>
        <tr>
          <td class="coverage">1.00 (11/11)</td>
          <td class="function">prvInitialiseTaskLists</td>
          <td class="file">Source/tasks.c</td>
        </tr>
        <tr>
          <td class="coverage">1.00 (9/9)</td>
          <td class="function">xTaskCreate</td>
          <td class="file">Source/tasks.c</td>
        </tr>
        <tr>
          <td class="coverage">1.00 (4/4)</td>
          <td class="function">pvPortMalloc</td>
          <td class="file">Test/CBMC/include/cbmc.h</td>
        </tr>
        <tr>
          <td class="coverage">1.00 (3/3)</td>
          <td class="function">vPortFree</td>
          <td class="file">Test/CBMC/include/cbmc.h</td>
        </tr>
        <tr>
          <td class="coverage">1.00 (19/19)</td>
          <td class="function">harness</td>
          <td class="file">Test/CBMC/proofs/Task/TaskCreate/TaskCreate_harness.c</td>
        </tr>
        <tr>
          <td class="coverage">1.00 (8/8)</td>
          <td class="function">pcNondetSetString</td>
          <td class="file">Test/CBMC/proofs/Task/TaskCreate/tasks_test_access_functions.h</td>
        </tr>
        <tr>
          <td class="coverage">1.00 (3/3)</td>
          <td class="function">pxNondetSetTaskHandle</td>
          <td class="file">Test/CBMC/proofs/Task/TaskCreate/tasks_test_access_functions.h</td>
        </tr>
        <tr>
          <td class="coverage">1.00 (2/2)</td>
          <td class="function">vNondetSetCurrentTCB</td>
          <td class="file">Test/CBMC/proofs/Task/TaskCreate/tasks_test_access_functions.h</td>
        </tr>
        <tr>
          <td class="coverage">1.00 (3/3)</td>
          <td class="function">vPrepareTaskLists</td>
          <td class="file">Test/CBMC/proofs/Task/TaskCreate/tasks_test_access_functions.h</td>
        </tr>
        <tr>
          <td class="coverage">1.00 (3/3)</td>
          <td class="function">vSetGlobalVariables</td>
          <td class="file">Test/CBMC/proofs/Task/TaskCreate/tasks_test_access_functions.h</td>
        </tr>
        <tr>
          <td class="coverage">0.97 (30/31)</td>
          <td class="function">prvInitialiseNewTask</td>
          <td class="file">Source/tasks.c</td>
        </tr>
      </table>
    </div>
    <div class="warnings">
      <h5> Warnings</h5>
      <p>
      Functions omitted from test (expected):
      </p>
      <ul>
        <li> pxPortInitialiseStack </li>
        <li> vPortEnterCritical </li>
        <li> vPortExitCritical </li>
        <li> vPortGenerateSimulatedInterrupt </li>
      </ul>
      <p>
      Other warnings:
      </p>
      <ul>
        <li> loop identifier prvInitialiseNewTask.1 provided with unwindset does not match any loop </li>
      </ul>
    <div class="errors">
      <h5>Errors</h5>
      None
    </div>
</div>

### Proof directory structure

This directory contains the following subdirectories:

- `proofs` contains the proofs run against each pull request
- `patches` contains a set of patches that get applied to the codebase prior to
  running the proofs. The patches are used to remove static and volatile qualifiers
  from the source.
- `include` and `windows` contain header files used by the proofs.
