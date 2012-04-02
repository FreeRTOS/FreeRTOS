setMode -bscan
setCable -p auto
identify
assignfile -p 2 -file implementation/download.bit
program -p 2
quit
