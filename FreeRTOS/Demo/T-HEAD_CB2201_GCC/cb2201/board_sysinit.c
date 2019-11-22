/*
 * Copyright (C) 2017 C-SKY Microsystems Co., Ltd. All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

 #include "board.h"

extern void hobbit_ioreuse_initial(void);

/*****************************************************************************
 * Private types/enumerations/variables
 ****************************************************************************/

/* Set up and initialize hardware prior to call to main */
void Board_SystemInit(void)
{
    hobbit_ioreuse_initial();
}
