    /* in progress */

    Name (Z160, 0xA0)
    Method (M600, 0, Serialized)
    {
        Name (I000, 0xABCD0000)
        Method (M000, 1, NotSerialized)
        {
            I000 = 0x11223344
            If ((Arg0 != 0xABCD0000))
            {
                ERR (__METHOD__, Z160, __LINE__, 0x00, 0x00, Arg0, 0xABCD0000)
            }
        }

        M000 (I000)
        If ((I000 != 0x11223344))
        {
            ERR (__METHOD__, Z160, __LINE__, 0x00, 0x00, I000, 0x11223344)
        }
    }

    /*
     do these
     Method(m003)
     {
     Name(i000, 0x00000001)
     Method(m001, 1)
     {
     Store(0x00000020, i000)
     Return (arg0)
     }
     Store(Add(i000, m001(i000)), Local0)
     if (LNotEqual(Local0, 0x00000002)) {
     Store("Error 2", Debug)
     Store(Local0, Debug)
     } else {
     Store("Ok 2", Debug)
     }
     if (LNotEqual(i000, 0x00000020)) {
     Store("Error 3", Debug)
     } else {
     Store("Ok 3", Debug)
     }
     }
     */
    Method (N006, 0, NotSerialized)
    {
        If (0x01)
        {
            SRMT ("m600")
            M600 ()
        }
        Else
        {
            SRMT ("m600")
            M600 ()
        }
    }
