DefinitionBlock(
	"ssdt.aml",   // Output filename
	"SSDT",     // Signature
	0x02,       // DSDT Revision
	"Intel",    // OEMID
	"Many",     // TABLE ID
	0x00000001  // OEM Revision
	) {

	Device (AUXD) {

		OperationRegion (OPR0, 0x80, 0x00, 0x4)

		Field (OPR0, DWordAcc, NoLock, Preserve) {
			RF00,   32}

		Name (REGC, Ones)
		Name (REGP, 0)

		Method(_REG, 2)
		{
			Store("\\AUXD._REG:", Debug)
			Store(arg0, Debug)
			Store(arg1, Debug)

			if (LEqual(arg0, 0x80)) {
				Store(REGC, REGP)
				Store(arg1, REGC)
			}
		}

		Method(ACC0)
		{
			Store("\\AUXD.ACC0:", Debug)
			Store(RF00, Debug)
			Store(REGP, Debug)
			if (LNotEqual(REGC, 1)) {
				Store("Error: REGC != 1", Debug)
				Store(REGC, Debug)
			}
		}
	}
}
