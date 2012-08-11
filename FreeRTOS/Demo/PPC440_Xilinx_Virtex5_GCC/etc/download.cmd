setMode -bscan
setCable -p auto
identify
assignfile -p 5 -file implementation/download.bit
program -p 5
quit
