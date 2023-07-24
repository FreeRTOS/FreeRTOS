// Copyright (c) 2020, XMOS Ltd, All rights reserved

#ifndef REGTEST_H_
#define REGTEST_H_

void vStartRegTestTasks( UBaseType_t uxPriority );
BaseType_t xAreRegTestTasksStillRunning( void );

/* These functions load known values into all general purpose registers
and verify that their integrity remains intact.
If this function ever returns, register values were unexpectedly changed */
void prvRegisterCheck_asm1( void );
void prvRegisterCheck_asm2( void );

#endif /* REGTEST_H_ */
