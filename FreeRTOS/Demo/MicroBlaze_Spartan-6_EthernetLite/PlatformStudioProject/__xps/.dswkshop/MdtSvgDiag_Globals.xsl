<?xml version="1.0" standalone="no"?>
<!DOCTYPE stylesheet [
	<!ENTITY UPPERCASE "ABCDEFGHIJKLMNOPQRSTUVWXYZ">
	<!ENTITY LOWERCASE "abcdefghijklmnopqrstuvwxyz">
	
	<!ENTITY UPPER2LOWER " '&UPPERCASE;' , '&LOWERCASE;' ">
	<!ENTITY LOWER2UPPER " '&LOWERCASE;' , '&UPPERCASE;' ">
	
	<!ENTITY ALPHALOWER "ABCDEFxX0123456789">
	<!ENTITY HEXUPPER   "ABCDEFxX0123456789">
	<!ENTITY HEXLOWER   "abcdefxX0123456789">
	<!ENTITY HEXU2L     " '&HEXLOWER;' , '&HEXUPPER;' ">
	
	<!ENTITY ALLMODS "MODULE[(@INSTANCE)]">
	<!ENTITY BUSMODS "MODULE[(@MODCLASS ='BUS')]">
	<!ENTITY CPUMODS "MODULE[(@MODCLASS ='PROCESSOR')]">
	
	<!ENTITY MODIOFS "MODULE/IOINTERFACES/IOINTERFACE">
	<!ENTITY ALLIOFS "&MODIOFS;[(not(@IS_VALID) or (@IS_VALID = 'TRUE'))]">
	
	<!ENTITY V11MODBIFS "MODULE/BUSINTERFACE">
	<!ENTITY V12MODBIFS "MODULE/BUSINTERFACES/BUSINTERFACE">
	<!ENTITY V11ALLBIFS "&V11MODBIFS;[(not(@IS_VALID) or (@IS_VALID = 'TRUE')) and  @TYPE and @BUSSTD]">
	<!ENTITY V12ALLBIFS "&V12MODBIFS;[(not(@IS_VALID) or (@IS_VALID = 'TRUE')) and  @TYPE and @BUSSTD]">
	
	<!ENTITY V11MODPORTS "MODULE/PORT">
	<!ENTITY V12MODPORTS "MODULE/PORTS/PORT">
	<!ENTITY V11ALLPORTS "&V11MODPORTS;[ (not(@IS_VALID) or (@IS_VALID = 'TRUE'))]">
	<!ENTITY V12ALLPORTS "&V12MODPORTS;[ (not(@IS_VALID) or (@IS_VALID = 'TRUE'))]">
	<!ENTITY V11NDFPORTS "&V11MODPORTS;[((not(@IS_VALID) or (@IS_VALID = 'TRUE')) and (not(@BUS) and not(@IOS)))]">
	<!ENTITY V12NDFPORTS "&V12MODPORTS;[((not(@IS_VALID) or (@IS_VALID = 'TRUE')) and (not(@BUS) and not(@IOS)))]">
	<!ENTITY V11DEFPORTS "&V11MODPORTS;[((not(@IS_VALID) or (@IS_VALID = 'TRUE')) and ((@BUS) or (@IOS)))]">
	<!ENTITY V12DEFPORTS "&V12MODPORTS;[((not(@IS_VALID) or (@IS_VALID = 'TRUE')) and ((@BUS) or (@IOS)))]">
]>

<!-- 
	<!ENTITY MSTBIFS "&MODBIFS;[(not(@IS_VALID) or (@IS_VALID = 'TRUE')) and (@TYPE = 'MASTER')]">
	<!ENTITY SLVBIFS "&MODBIFS;[(not(@IS_VALID) or (@IS_VALID = 'TRUE')) and (@TYPE = 'SLAVE')]">
	<!ENTITY MOSBIFS "&MODBIFS;[(not(@IS_VALID) or (@IS_VALID = 'TRUE')) and ((@TYPE = 'MASTER') or (@TYPE = 'SLAVE'))]">
	<!ENTITY P2PBIFS "&MODBIFS;[(not(@IS_VALID) or (@IS_VALID = 'TRUE')) and ((@TYPE = 'TARGET') or (@TYPE = 'INITIATOR'))]">	
-->
<xsl:stylesheet version="1.0"
	  xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
      xmlns:exsl="http://exslt.org/common"
      xmlns:dyn="http://exslt.org/dynamic"
      xmlns:math="http://exslt.org/math"
      xmlns:xlink="http://www.w3.org/1999/xlink"
      extension-element-prefixes="math exsl dyn xlink">
<!--	
	======================================================
			EDK SYSTEM (EDWARD) Globals.	
	======================================================
-->	

<xsl:variable name="G_SYS_ROOT" 	  select="/"/>
<!-- 
<xsl:variable name="G_SYS_DOC"   	  select="dyn:evaluate($G_SYS_ROOT)"/>
<xsl:variable name="G_SYS_DOC"   	  select="dyn:evaluate($G_SYS_ROOT)"/>
 -->
<xsl:variable name="G_SYS"   		  select="$G_SYS_ROOT/EDKSYSTEM"/>
<xsl:variable name="G_SYS_TIMESTAMP"  select="$G_SYS/@TIMESTAMP"/>
<xsl:variable name="G_SYS_EDKVERSION" select="$G_SYS/@EDKVERSION"/>

<xsl:variable name="G_SYS_INFO"   	  select="$G_SYS/SYSTEMINFO"/>
<xsl:variable name="G_SYS_INFO_PKG"   select="$G_SYS_INFO/@PACKAGE"/>
<xsl:variable name="G_SYS_INFO_DEV"   select="$G_SYS_INFO/@DEVICE"/>
<xsl:variable name="G_SYS_INFO_ARCH"  select="$G_SYS_INFO/@ARCH"/>
<xsl:variable name="G_SYS_INFO_SPEED" select="$G_SYS_INFO/@SPEEDGRADE"/>

<xsl:variable name="G_SYS_MODS" 	  select="$G_SYS/MODULES"/>
<xsl:variable name="G_SYS_EXPS" 	  select="$G_SYS/EXTERNALPORTS"/>

<!--  INDEX KEYS FOR FAST ACCESS  -->
<xsl:key name="G_MAP_MODULES"   	  match="&ALLMODS;" use="@INSTANCE"/>
<xsl:key name="G_MAP_PROCESSORS"   	  match="&CPUMODS;" use="@INSTANCE"/>

<xsl:key name="G_MAP_BUSSES"   		  match="&BUSMODS;" use="@INSTANCE"/>
<xsl:key name="G_MAP_BUSSES"   		  match="&BUSMODS;" use="@BUSSTD"/>
<xsl:key name="G_MAP_BUSSES" 	  	  match="&BUSMODS;" use="@BUSSTD_PSF"/>

<xsl:key name="G_MAP_ALL_IOFS"   	  match="&ALLIOFS;" use="../../@INSTANCE"/>

<xsl:key name="G_MAP_ALL_BIFS"   	  match="&V11ALLBIFS;" use="@TYPE"/>
<xsl:key name="G_MAP_ALL_BIFS"   	  match="&V12ALLBIFS;" use="@TYPE"/>
<xsl:key name="G_MAP_ALL_BIFS"   	  match="&V11ALLBIFS;" use="@BUSSTD"/>
<xsl:key name="G_MAP_ALL_BIFS"   	  match="&V12ALLBIFS;" use="@BUSSTD"/>
<xsl:key name="G_MAP_ALL_BIFS"   	  match="&V11ALLBIFS;" use="@BUSSTD_PSF"/>
<xsl:key name="G_MAP_ALL_BIFS"   	  match="&V12ALLBIFS;" use="@BUSSTD_PSF"/>
<xsl:key name="G_MAP_ALL_BIFS"   	  match="&V11ALLBIFS;" use="../@INSTANCE"/>
<xsl:key name="G_MAP_ALL_BIFS"   	  match="&V12ALLBIFS;" use="../../@INSTANCE"/>

<!-- 
<xsl:key name="G_MAP_ALL_BIFS_BY_BUS" match="&ALLBIFS;" use="@BUSNAME"/>
<xsl:key name="G_MAP_ALL_BIFS_BY_STD" match="&ALLBIFS;" use="@BUSSTD"/>
<xsl:key name="G_MAP_ALL_BIFS_BY_STD" match="&ALLBIFS;" use="@BUSSTD_PSF"/>


<xsl:key name="G_MAP_MST_BIFS"   	  match="&MSTBIFS;" use="@BUSNAME"/>
<xsl:key name="G_MAP_SLV_BIFS"   	  match="&SLVBIFS;" use="@BUSNAME"/>
<xsl:key name="G_MAP_MOS_BIFS"   	  match="&MOSBIFS;" use="@BUSNAME"/>

<xsl:key name="G_MAP_P2P_BIFS"   	  match="&P2PBIFS;" use="@BUSNAME"/>
<xsl:key name="G_MAP_P2P_BIFS"   	  match="&P2PBIFS;" use="@BUSSTD"/>
<xsl:key name="G_MAP_P2P_BIFS"   	  match="&P2PBIFS;" use="@BUSSTD_PSF"/>
-->

<xsl:key name="G_MAP_ALL_PORTS"   	  match="&V11ALLPORTS;" use="../@INSTANCE"/>
<xsl:key name="G_MAP_ALL_PORTS"   	  match="&V12ALLPORTS;" use="../../@INSTANCE"/>
<xsl:key name="G_MAP_DEF_PORTS"   	  match="&V11DEFPORTS;" use="../@INSTANCE"/> <!-- Default ports -->
<xsl:key name="G_MAP_DEF_PORTS"   	  match="&V12DEFPORTS;" use="../../@INSTANCE"/> <!-- Default ports -->
<xsl:key name="G_MAP_NDF_PORTS"   	  match="&V11NDFPORTS;" use="../@INSTANCE"/> <!-- Non Default ports -->
<xsl:key name="G_MAP_NDF_PORTS"   	  match="&V12NDFPORTS;" use="../../@INSTANCE"/> <!-- Non Default ports -->

<xsl:variable name="G_BIFTYPES">

	<BIFTYPE TYPE="SLAVE"/>
	<BIFTYPE TYPE="MASTER"/>
	<BIFTYPE TYPE="MASTER_SLAVE"/>
	
	<BIFTYPE TYPE="TARGET"/>
	<BIFTYPE TYPE="INITIATOR"/>
	
	<BIFTYPE TYPE="MONITOR"/>
	
	<BIFTYPE TYPE="USER"/>
	<BIFTYPE TYPE="TRANSPARENT"/>
	
</xsl:variable>	
<xsl:variable name="G_BIFTYPES_NUMOF" select="count(exsl:node-set($G_BIFTYPES)/BIFTYPE)"/>

<xsl:variable name="G_IFTYPES">
    <IFTYPE TYPE="SLAVE"/>
    <IFTYPE TYPE="MASTER"/>
    <IFTYPE TYPE="MASTER_SLAVE"/>
    
    <IFTYPE TYPE="TARGET"/>
    <IFTYPE TYPE="INITIATOR"/>
    
    <IFTYPE TYPE="MONITOR"/>
    
    <IFTYPE TYPE="USER"/>
<!-- 
     <IFTYPE TYPE="TRANSPARENT"/>
--> 
</xsl:variable> 
<xsl:variable name="G_IFTYPES_NUMOF" select="count(exsl:node-set($G_IFTYPES)/IFTYPE)"/>

<xsl:variable name="G_BUSSTDS">
	
	<BUSSTD NAME="AXI"/>
	<BUSSTD NAME="XIL"/>
	<BUSSTD NAME="OCM"/>
	<BUSSTD NAME="OPB"/>
	<BUSSTD NAME="LMB"/>
	<BUSSTD NAME="FSL"/>
	<BUSSTD NAME="DCR"/>
	<BUSSTD NAME="FCB"/>
	<BUSSTD NAME="PLB"/>
	<BUSSTD NAME="PLB34"/>
	<BUSSTD NAME="PLBV46"/>
	<BUSSTD NAME="PLBV46_P2P"/>
	
	<BUSSTD NAME="USER"/>
	<BUSSTD NAME="KEY"/>
</xsl:variable>
<xsl:variable name="G_BUSSTDS_NUMOF" select="count(exsl:node-set($G_BUSSTDS)/BUSSTD)"/>

</xsl:stylesheet>
