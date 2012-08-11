set $IPSBAR = 0x40000000

set $DCR    = $IPSBAR + 0x000040
set $DACR0  = $IPSBAR + 0x000048
set $DMR0   = $IPSBAR + 0x00004C

set $CSAR0  = $IPSBAR + 0x000080
set $CSMR0  = $IPSBAR + 0x000084
set $CSCR0  = $IPSBAR + 0x00008A

set $PAR_SDRAM = $IPSBAR + 0x100046
set $PAR_AD    = $IPSBAR + 0x100040

set $WCR    = $IPSBAR + 0x140000

define delay
  set $delay = 0
  while ($delay < 20000)
    set $delay += 1
  end  
end

define delay_memsync
  set $delay = 0
  while ($delay < 10000)
    set $delay += 1
  end  
end

define setup-cs
  # 2MB FLASH on CS0 at 0x80000000
  set *(unsigned short *)$CSAR0 = 0x00008000
  set *(unsigned long  *)$CSMR0 = 0x001F0101
  set *(unsigned short *)$CSCR0 = 0x00001980
end

define setup-sdram
  # Set PAR_SDRAM to allow SDRAM signals to be enable
  set *(unsigned char *)$PAR_SDRAM = 0x3F
  # Set PAR_AD to allow 32-bit SDRAM if the external boot device is 16-bit
  set *(unsigned char *)$PAR_AD = 0xE1

  # SDRAM
  set *(unsigned short *)$DCR   = 0x0446
  set *(unsigned long *)$DACR0  = 0x00001300
  set *(unsigned long *)$DMR0   = 0x00FC0001

  # Set IP in DACR and init precharge.
  set *(unsigned long *)$DACR0 |= 0x00000008
  set *(0x00000000)             = 0xAA55AA55
  delay

  # Set RE in DACR
  set *(unsigned long *)$DACR0 |= 0x00008000
  # Issue IMRS
  set *(unsigned long *)$DACR0 |= 0x00000040
  set *(0x00000400)             = 0xAA55AA55
  delay
end

define setup-other
  # Turn Off WCR
  set *(unsigned char *)$WCR = 0x00
end

define setup-and-load
  bdm-reset

  # Set VBR to the vector table.
  set $vbr = 0x00000000
  # Set internal SRAM to start at 0x20000000
  set $rambar = 0x20000001

  setup-other
  setup-cs
  setup-sdram
end

define debug-sramtest
  set $srambase = 0x20000000
  set $sramsize = 0x00010000
  set $j = 0
  printf "Testing SRAM : 0x%08X - 0x%08X\n", $srambase, ($srambase + $sramsize)
  set $i = $srambase
  while $i < ($srambase + $sramsize)
    set *(unsigned long *)($i) = 0xAA55AA55
    delay_memsync
    if 0xAA55AA55 != *(unsigned long *)$i
      printf "  0x%08X = FAIL\n", $i
    else
      printf "  0x%08X = OK", $i
      if $j % 4 == 3
        printf "\n"
      end
      set $j = $j + 1
    end
    set $i = $i + 0x400
  end
en

define debug-ramtest
  set $sdrambase = 0x00000000
  set $sdramsize = 0x01000000
  set $j = 0
  printf "Testing SDRAM : 0x%08X - 0x%08X\n", $sdrambase, ($sdrambase + $sdramsize)
  set $i = $sdrambase 
  while $i < ($sdrambase + $sdramsize)
    set *(unsigned long *)($i) = 0xAA55AA55
    delay_memsync
    if 0xAA55AA55 != *(unsigned long *)$i
      printf "  0x%08X = FAIL\n", $i
    else
      printf "  0x%08X = OK", $i
      if $j % 4 == 3
        printf "\n"
      end
      set $j = $j + 1
    end
    set $i = $i + 0x10000
  end
  printf "\n"
end

define execute
  set $pc = *(long *)0x00000004
  tbreak main
  tk gdbtk_update
end

define debug-printexception
  printf "vector: %d", *(unsigned short *)$sp >> 2 &0x1F
  printf "old pc: 0x%08x", *(unsigned long *)($sp + 4)
  printf "old sr: 0x%02x", *(unsigned short *)($sp + 2)
end
