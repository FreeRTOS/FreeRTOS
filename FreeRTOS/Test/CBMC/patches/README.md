This directory includes patches to FreeRTOS required to run the CBMC proofs.

The patches fall into three classes:
* First is a refactoring of prvCheckOptions
* Second is the removal of static attributes from some functions
* Third is two patches dealing with shortcomings of CBMC that should be removed soon.