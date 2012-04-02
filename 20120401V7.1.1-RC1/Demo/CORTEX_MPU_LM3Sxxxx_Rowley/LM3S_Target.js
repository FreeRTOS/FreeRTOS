/******************************************************************************
  Target Script for LM3S.

  Copyright (c) 2006 Rowley Associates Limited.

  This file may be distributed under the terms of the License Agreement
  provided with this software.

  THIS FILE IS PROVIDED AS IS WITH NO WARRANTY OF ANY KIND, INCLUDING THE
  WARRANTY OF DESIGN, MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE.
 ******************************************************************************/

function Reset()
{
  TargetInterface.resetAndStop(1000);
}

function RAMReset()
{
  Reset();
}

function FLASHReset()
{
  Reset();
}


