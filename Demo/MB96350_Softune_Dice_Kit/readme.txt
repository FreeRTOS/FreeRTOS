==========================================================================
             DICE2 Project for DICE-KIT-16FX Evaluation Board
==========================================================================
                   Fujitsu Microelectronics Europe GmbH                       
   
 The following  software  is for  demonstration  purposes only.  It is not
 fully  tested, nor validated  in order  to fullfill  its task  under  all
 circumstances.  Therefore,  this software or  any part of it must only be
 used in an evaluation laboratory environment.                        
 This software is subject to the rules of our standard DISCLAIMER, that is
 delivered with our SW-tools on the Fujitsu Microcontrollers DVD 
 (V5.0 or higher "\START.HTM").
==========================================================================
               
History
Date        Ver     Author  Softune     Description
2008-04-28  1.0     AVo/HWe V30L34R06   original version
==========================================================================

This is Demoproject for the DICE-KIT-16FX Evaluation-Board. 
It includes some basic settings for e.g. Linker, C-Compiler 
which must be checked and modified in detail, 
corresponding to the user application.

Description:
This projects simulates two dices.
SEG1 is dice1 and can be started by pressing key SW2 (INT8)
SEG2 is dice2 and can be started by pressing key SW3 (INT9)
After a while the started dice will stop displaying a value from 1..6.

Note:
Remove jumper JP2 (External watchdog is not supported by this project)

Clock settings:
---------------
Crystal:  4 MHz
CLKB:    56 MHz
CLKP1:   56 MHz
CLKP2:   14 MHz
