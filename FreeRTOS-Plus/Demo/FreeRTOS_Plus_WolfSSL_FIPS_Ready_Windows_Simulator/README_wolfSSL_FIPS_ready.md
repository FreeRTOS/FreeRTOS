#  wolfSSL FIPS-Ready

# Overview
Federal Information Processing Standards(FIPS) 140-2 specifies the security requirements that will be satisfied by a cryptographic module. It specifies that a cryptographic module should set a cryptographic boundary and it should contain cryptgraphic functions, algorithmsa and key generation inside.

wolfSSL FIPS Ready is FIPS enabled cryptography layer code and is compliant to FIPS 140-2 specs. If your project need to get a FIPS certificate in the future, try using a FIPS-Ready version wolfSSL now. It makes your project FIPS-Ready.  

Next to this folder you will see another demo folder named "FreeRTOS_Plus_WolfSSL_Windows_Simulator". The demo uses regular(not-FIPS-Ready) wolfSSL. If you compare both demos, you will notice that there are no changes to the client code, and will also notice some tests run prior to your main program in this FIPS-Ready demo.

This fact indicates that wolfSSL FIPS Ready provides a FIPS compliant cryptographic module with minimal impact on client code. 

# What does FIPS 140-2 specify?

FIPS 140-2 enforces cryptographic module to follow belows:

1. Remove unsecure algorithms such as MD5 and DES.
1. Have default entry point
1. Perform Power On Self Test(POST)


wolfSSL FIPS Ready fulfils those requirements. The third requirement means, the POST should run automatically whenever the application using the FIPS code starts up. For wolfSSL FIPS Ready, the POST consits of two tests: 

- In-Core Memory Test
- Known Answer Test(KAT)

In-Core Memory Test perfoms hashing the "Core" part of the program with HMAC-SHA-256 algorithm. The "Core" means a cryptographic boundary, in other words, FIPS code and its related static data in the memory of the program. In this test, calculated hash value is to be compare with the expexted pre-calculated value in the memory. Failure of the test means that core part was modified after its build.

KAT's other algorithms in the FIPS boundary are tested with canned data and the output is compared to pre-computed known answers. The test values are all inside the boundary and are checked with the in-core memory test.

# How to build and run the Demo application

By double-clicking the solution file named "FreeRTOS_Plus_WolfSSL_FIPS_Ready.sln" included in this folder, Visual Studio starts and shows you two projects in its solution explorer pane. One is "RTOSDemo" and another is "wolfSSL_FIPS_Ready" project. RTOSDemo provides a console application program runs on windows and wolfSSL_FIPS_Ready provides static-link library to be linked by the RTOSDemo. 

All the required settings has been set in user_settings.h included in the wolfSSL_FIPS_Ready project. It's ready to build the RTOSDemo project.

1. Build the DTROSDemo project (wolfSSL_FIPS_Ready will be build automatically)
1. Run the RTOSDemo.exe 


You will see a console pops up, and it shows like as follows:


```
Starting Power On Self Test
In core integrity check error: hash = C66491A040D5B9686BAA7A75A280290D91B49...
ERROR: -203
Power On Self Test(Known-Answer-Test) FAILURE
```

Do not warry about this result. It is predicted. Error number "-203" means In-Core-integrity-check failed. The check is identical to the "In Core Memory Test" listed in the previous section. And the subsequent KAT also failed due to the first error. Once FIPS Ready faild POST, it falls an error state and never allows subsequent cryptographic operations. 

"In Core Memory Test" requires pre-calclated hash value to be stored in the memory. Remember that you did not set this pre-calculated value durling your build. That is the reason why your first run failed.

# Update Pre-calculated hash value

1. Let us go back to the messages in the console shown in the previous section. You may see "hash = C66491A040..." in the message. **The charactor sequence is the value for the pre-calculated hash value.** Please copy this charactor sequece and store it in any file.

1. Find and open the file named "**fips_test.c**" under the wolfSSL_FIPS_Ready/wolfSSL/wolfcrypt folder in the Visual Studio solution explorer pane. Or you can reach the file by traversing   "../../Source/WolfSSL-FIPS-Ready/wolfcrypt/src/fips_test.c" starting from the folder this README included.

1. In the fips_test.c, find the following statement: 


    ```
    static const char verifyCore[] =
        "903B291C50C8F0BAB8D2C632853C6D827A9022A4B12260C3A14F4BEBD101228";
    ```

    Replace "903b291C..." with the character sequecece(C66491A040... ) you have storeaed in a file. Save the fips_test.c and buil the application.

1. Run the application.

    This time, you will see:

    ```
    Starting Power On Self Test
    Power On Self Test SUCCESS
    Waiting for new connection
    Connection established
    Received by the secure server: Message number 0

    Received by the secure server: Message number 1
    
        ...
    
    Received by the secure server: Message number 9

    Connection closed, back to start
    Waiting for new connection

    ```

    This time, in-core memory test and KAT finished successfully, then Demo application performs its own tasks.

    # When is the hash value update needed? 

    Whenever the FIPS Core get any change in its configuration such as options, location in the application, hash value may change. Even you just add or remove your code in your application, it may give FIPS Core location shift in the memory. 

    It may be a workaround to avoid this tiresome hash-value update, to use ordinary wolfSSL until your application get mature or fix cryptographic specs. Replacing ordinary wolfSSL with FIPS Ready version gives no harm to your coding.