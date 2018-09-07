
SECTIONS
{
    _sdram_lma = .;
    sdram_region :
    AT ( _sdram_lma )
    {
        *(sdram_region)
    } >sdram
}
