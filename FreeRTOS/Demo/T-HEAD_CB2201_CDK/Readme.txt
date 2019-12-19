# T-HEAD CB2201 Demo Project

The demo show a two task commmunication with Queue structio provided by FreeRTOS. The Send task keeps
sending a Queue with const value(100) to other task, the Receive Task will dump some message once it 
receives expected value.

## CDK software
The demo project is build with CDK, you can download the latst version at 
https://occ.t-head.cn/community/download_detail?spm=a2oza.cdk.0.0.413b180fZ5hVxQ&id=575997419775328256

## Build

1. Install CDK correctly
2. Open RTOSDemo.cdkproj and rebuild it by pressing F7
3. Connect to T-HEAD Cb2201 board and make sure serial cable is plugged correctly.
4. Run it by Press CTRL+F5
5. Check serial windows message