# THIS SAMPLE CODE IS PROVIDED AS IS AND IS SUBJECT TO ALTERATIONS. FUJITSU */
# MICROELECTRONICS ACCEPTS NO RESPONSIBILITY OR LIABILITY FOR ANY ERRORS OR */
# ELIGIBILITY FOR ANY PURPOSES.                                             */
#                 (C) Fujitsu Microelectronics Europe GmbH                  */

# Environment and memory manioulation after program upload




print "patch reset vector to \"__start\"\n";
SET MEMORY/WORD 0xFFFFC=__start
  
