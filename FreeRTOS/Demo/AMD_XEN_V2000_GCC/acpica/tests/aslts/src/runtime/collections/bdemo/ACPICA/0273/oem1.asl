/*
 * Intel ACPI Component Architecture
 * AML Disassembler version 20061109
 *
 * Disassembly of oem1.aml, Thu Nov 16 18:41:26 2006
 *
 *
 * Original Table Header:
 *     Signature        "OEM1"
 *     Length           0x00000038 (56)
 *     Revision         0x01
 *     OEM ID           "Intel"
 *     OEM Table ID     "Many"
 *     OEM Revision     0x00000001 (1)
 *     Creator ID       "INTL"
 *     Creator Revision 0x20030918 (537069848)
 */
DefinitionBlock ("oem1.aml", "OEM1", 1, "Intel", "Many", 0x00000001)
{
    Name (_XT2, 0x04)
    Method (_XT1, 0, NotSerialized)
    {
        Store (One, _XT2)
    }
}
