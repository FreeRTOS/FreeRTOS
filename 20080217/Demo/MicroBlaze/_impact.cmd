setMode -bs
setCable -port auto
identify
identifyMPM
setAttribute -position 3 -attr configFileName -value "implementation/download.bit"
program -p 3 
quit
