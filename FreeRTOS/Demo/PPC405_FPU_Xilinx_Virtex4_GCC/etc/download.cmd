setMode -bscan
setCable -p auto
identify
assignfile -p 3 -file implementation/download.bit
program -p 3
quit
