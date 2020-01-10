# T-HEAD CB2201 Demo Project

The demo shows inter-task communication using a queue. 
The sender periodically sends a constant value to the queue. The receiver blocks until 
the next value is received and validates it. Receiver prints evaluation result to output. 


## References
CB2201 development board: https://occ.t-head.cn/#/vendor_product_detail?id=635878225301471232&vendorId=3706716635429273600&module=4
The latest version of CDK: https://occ.t-head.cn/community/download_detail?spm=a2oza.cdk.0.0.413b180fZ5hVxQ&id=575997419775328256


## Getting started
1. Download the latest version of CDK and follow CDK installation wizard to intall. 
2. Open RTOSDemo.cdkproj under ./RTOSDemo_CDK/RTOSDemo/
3. Build project.
4. Connect to T-HEAD Cb2201 board. (Make sure serial cable is connected correctly.)
5. Run. 
6. Check messages in serial window. 