/********************************************************************************/
/*      FILENAME  RegisterFile.h   												*/
/* The current release of the documentation and header files does not include
 * the system register file or the VBAT register file. This header file
 * adds support for accessing both register files. 
 * 
 * Once the manual is updated to include the register files, this file
 * will become obsolete. 
 */
/********************************************************************************/

/* Register File - Peripheral instance base addresses */
/* Peripheral System Register File base pointer */
#define RFSYS_DATA_BASE_PTR                        ((RFDATA_MemMapPtr)0x40041000u)
/* Peripheral VBAT Register File  base pointer */
#define RFVBAT_DATA_BASE_PTR                       ((RFDATA_MemMapPtr)0x4003E000u)

  typedef struct RFDATA_MemMap {
  uint32_t RFDATA [32];            /*!< Register file  n, array offset: 0x0, array step: 0x4 */
 
  
} volatile *RFDATA_MemMapPtr;

/* ----------------------------------------------------------------------------
   -- Register file - Register accessor macros
   ---------------------------------------------------------------------------- */

/* Register file - Register accessors */
#define RFSYS_DATA_REG(base,index)              ((base)->RFDATA[index])
#define RFVBAT_DATA_REG(base,index)             ((base)->RFDATA[index])

#define RFSYS_DATA0                             RFSYS_DATA_REG(RFSYS_DATA_BASE_PTR,0 )
#define RFSYS_DATA1                             RFSYS_DATA_REG(RFSYS_DATA_BASE_PTR,1 )
#define RFSYS_DATA2                             RFSYS_DATA_REG(RFSYS_DATA_BASE_PTR,2 )
#define RFSYS_DATA3                             RFSYS_DATA_REG(RFSYS_DATA_BASE_PTR,3 )
#define RFSYS_DATA4                             RFSYS_DATA_REG(RFSYS_DATA_BASE_PTR,4 )
#define RFSYS_DATA5                             RFSYS_DATA_REG(RFSYS_DATA_BASE_PTR,5 )
#define RFSYS_DATA6                             RFSYS_DATA_REG(RFSYS_DATA_BASE_PTR,6 )
#define RFSYS_DATA7                             RFSYS_DATA_REG(RFSYS_DATA_BASE_PTR,7 )

#define RFVBAT_DATA0                            RFVBAT_DATA_REG(RFVBAT_DATA_BASE_PTR,0 )
#define RFVBAT_DATA1                            RFVBAT_DATA_REG(RFVBAT_DATA_BASE_PTR,1 )
#define RFVBAT_DATA2                            RFVBAT_DATA_REG(RFVBAT_DATA_BASE_PTR,2 )
#define RFVBAT_DATA3                            RFVBAT_DATA_REG(RFVBAT_DATA_BASE_PTR,3 )
#define RFVBAT_DATA4                            RFVBAT_DATA_REG(RFVBAT_DATA_BASE_PTR,4 )
#define RFVBAT_DATA5                            RFVBAT_DATA_REG(RFVBAT_DATA_BASE_PTR,5 )
#define RFVBAT_DATA6                            RFVBAT_DATA_REG(RFVBAT_DATA_BASE_PTR,6 )
#define RFVBAT_DATA7                            RFVBAT_DATA_REG(RFVBAT_DATA_BASE_PTR,7 )
                                                                                     

/* LL Bit Fields */
#define RF_DATA_LL_MASK                           0x000000FFu
#define RF_DATA_LL_SHIFT                          0
#define RF_DATA_LL(x)                            (((x)<<RF_DATA_LL_SHIFT)&RF_DATA_LL_MASK)
/* LH Bit Fields */                        
#define RF_DATA_LH_MASK                           0x0000FF00u
#define RF_DATA_LH_SHIFT                          8
#define RF_DATA_LH(x)                             (((x)<<RF_DATA_LH_SHIFT)&RF_DATA_LH_MASK)
/* HL Bit Fields */
#define RF_DATA_HL_MASK                           0x00FF0000u
#define RF_DATA_HL_SHIFT                          16
#define RF_DATA_HL(x)                             (((x)<<RF_DATA_HL_SHIFT)&RF_DATA_HL_MASK)
/* HH Bit Fields */
#define RF_DATA_HH_MASK                           0xFF000000u
#define RF_DATA_HH_SHIFT                          24
#define RF_DATA_HH(x)                             (((x)<<RF_DATA_HH_SHIFT)&RF_DATA_HH_MASK)


/*! \} */ /* end of group Register_File_Register_Accessor_Macros */
