#  wolfSSL FIPS-Ready

# Overview
Federal Information Processing Standards (FIPS) 140-2 specifies the security requirements that will be satisfied by a cryptographic module. It specifies that a cryptographic module should set a cryptographic boundary and mandates certain power-on selftest requirements such as an integrity check and cryptographic known answer tests.

wolfSSL FIPS Ready includes FIPS-enabled cryptography layer code along with the wolfSSL source code. It is not associated with a FIPS certificate, but allows applications to include the same FIPS-specific code (default entry point, power on self test) and best practices used by and required in FIPS-validated modules. If your project may need to get a FIPS certificate in the future, using the wolfSSL FIPS-Ready version now will accelerate future validation times. It makes your project FIPS-Ready and helps ensure best practices.

Next to this folder you will see another demo folder named "FreeRTOS_Plus_WolfSSL_Windows_Simulator". The demo uses regular (non-FIPS-Ready) wolfSSL. If you compare both demos, you will notice that there are no changes to the client code, and will also notice that some additional tests run prior to your main program in this FIPS-Ready demo.

This demo shows that wolfSSL FIPS Ready provides a FIPS compliant cryptographic module with minimal impact on client code. 

# What does FIPS 140-2 specify?

FIPS 140-2 enforces cryptographic modules to follow best practices, including:

1. Removal of insecure algorithms (such as MD5 and DES)
2. Include a default entry point
3. Perform a Power On Self Test (POST)

wolfSSL FIPS Ready fulfils these requirements. The third requirement means that the POST should run automatically whenever the application using the FIPS code starts up. For wolfSSL FIPS Ready, the POST consits of two tests: 

- In-Core Integrity Check (HMAC-SHA256 over cryptographic algorithm object files)
- Known Answer Tests (KATs)

The in-core integrity check performs an HMAC-SHA256 operation over the object files included in the FIPS-compliant algorithm boundary. The cryptographic boundary is the FIPS-specific code and its related static data in the memory of the program. In the integrity check process, the calculated hash value is compared with the expexted pre-calculated value in the memory. Failure of this check means that compiled boundary code was modified after it was compiled. If either the integrity check or KAT fails, the module enters an error state.

The KAT (Known Answer Tests) run algorithm test cases using pre-computed NIST test vectors, thus verifying that the algorithms are working successfully. The KAT code and test vectors are inside the cryptographic boundary and are also checked as part of the in-core integrity check.

# How to build and run the Demo application

By double-clicking the solution file named "FreeRTOS_Plus_WolfSSL_FIPS_Ready.sln" included in this folder, Visual Studio starts and shows you a project in its solution explorer. It is named "RTOSDemo" and provides a console application program which runs on windows. 

All required settings have been set in the user_settings.h header file included in the RTOSDemo/FreeRTOS+/wolfSSL folder in the solution explorer pane. The next step is to build the RTOSDemo application:

1. Build the RTOSDemo project
2. Run the RTOSDemo.exe 

You will see a console that pops up, and it shows output like the following:
# Self Test Explanation
```
Starting Power On Self Test
In core integrity check error: hash = C66491A040D5B9686BAA7A75A280290D91B49...
```

Do not worry about this result, an error is expected at this point. Error number "-203" means In-Core-integrity-check failed. The check is identical to the "In Core Integrity Test" listed in the previous section. And the subsequent KAT also failed due to the first error. Once FIPS Ready has failed POST, it enters an error state and never allows subsequent cryptographic operations until the device is restarted and the tests can complete successfully. 

The in-core integrity check requires a pre-calculated hash value to be stored in the fips_test.c source file. Remember that you did not yet set this pre-calculated value during the build process. Because the hash does not match the stored value is the reason why this first run will fail.

# Update Pre-calculated hash value

1. Let us go back to the messages in the console shown in the previous section. You may see "hash = C66491A040..." in the message. **The charactor sequence is the value for the pre-calculated hash value.** Please copy this charactor sequece and store it in a temporary location for reference in the next step.

2. Find and open the file named "**fips_test.c**" under the RTOSDemo/FreeRTOS+/wolfSSL/wolfcrypt folder in the Visual Studio solution explorer pane. Or you can reach the file by traversing "../../ThirdParty/WolfSSL-FIPS-Ready/wolfcrypt/src/fips_test.c" starting from the folder where this README is included.

3. In the fips_test.c, find the following statement: 

    ```
    static const char verifyCore[] =
        "903B291C50C8F0BAB8D2C632853C6D827A9022A4B12260C3A14F4BEBD101228";
    ```

    Replace "903b291C..." with the character sequecece(C66491A040... ) you have stored in your temporary location from above. Save fips_test.c and build the application.

4. Run the application.

    This time, you should see:

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

    This time, the in-core integrity check and KAT finished successfully, and Demo application was allowed to continue and perform its own tasks.

    # When is the hash value update needed? 

Whenever the FIPS boundary files have had changes made to them, such as options, location in the application, hash value, code, etc. the verifyHash value in fips_test.c will need to be updated. Even you just add or remove your code in your application, it may shift the FIPS boundary code in the memory, thus requiring a new hash value to be computed and updated.
