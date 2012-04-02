<?xml version="1.0" standalone="no"?>

<!DOCTYPE stylesheet [
	<!ENTITY UPPERCASE "ABCDEFGHIJKLMNOPQRSTUVWXYZ">
	<!ENTITY LOWERCASE "abcdefghijklmnopqrstuvwxyz">
	
	<!ENTITY UPPER2LOWER " '&UPPERCASE;' , '&LOWERCASE;' ">
	<!ENTITY LOWER2UPPER " '&LOWERCASE;' , '&UPPERCASE;' ">
	
	<!ENTITY ALPHALOWER "ABCDEFxX0123456789">
	<!ENTITY HEXUPPER "ABCDEFxX0123456789">
	<!ENTITY HEXLOWER "abcdefxX0123456789">
	<!ENTITY HEXU2L " '&HEXLOWER;' , '&HEXUPPER;' ">
	
	<!ENTITY ALLMODS "MODULE[(@INSTANCE)]">
	<!ENTITY BUSMODS "MODULE[(@MODCLASS ='BUS')]">
	<!ENTITY CPUMODS "MODULE[(@MODCLASS ='PROCESSOR')]">
	
	<!ENTITY MODIOFS "MODULE/IOINTERFACES/IOINTERFACE">
	<!ENTITY ALLIOFS "&MODIOFS;[(not(@IS_VALID) or (@IS_VALID = 'TRUE'))]">
	
	<!ENTITY MODBIFS "MODULE/BUSINTERFACES/BUSINTERFACE">
	<!ENTITY ALLBIFS "&MODBIFS;[(not(@IS_VALID) or (@IS_VALID = 'TRUE'))]">
	<!ENTITY MSTBIFS "&MODBIFS;[(not(@IS_VALID) or (@IS_VALID = 'TRUE')) and  (@TYPE = 'MASTER')]">
	<!ENTITY SLVBIFS "&MODBIFS;[(not(@IS_VALID) or (@IS_VALID = 'TRUE')) and  (@TYPE = 'SLAVE')]">
	<!ENTITY MOSBIFS "&MODBIFS;[(not(@IS_VALID) or (@IS_VALID = 'TRUE')) and ((@TYPE = 'MASTER') or (@TYPE = 'SLAVE'))]">
	<!ENTITY P2PBIFS "&MODBIFS;[(not(@IS_VALID) or (@IS_VALID = 'TRUE')) and ((@TYPE = 'TARGET') or (@TYPE = 'INITIATOR'))]">	
	
	<!ENTITY MODPORTS "MODULE/PORTS/PORT">
	<!ENTITY ALLPORTS "&MODPORTS;[ (not(@IS_VALID) or (@IS_VALID = 'TRUE'))]">
	<!ENTITY NDFPORTS "&MODPORTS;[((not(@IS_VALID) or (@IS_VALID = 'TRUE')) and (not(@BUS) and not(@IOS)))]">
	<!ENTITY DEFPORTS "&MODPORTS;[((not(@IS_VALID) or (@IS_VALID = 'TRUE')) and ((@BUS) or (@IOS)))]">
]>

<xsl:stylesheet version="1.0"
	   xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
       xmlns:exsl="http://exslt.org/common"
       xmlns:dyn="http://exslt.org/dynamic"
       xmlns:math="http://exslt.org/math"
       xmlns:xlink="http://www.w3.org/1999/xlink"
       extension-element-prefixes="math dyn exsl xlink">
           
<xsl:variable name="G_ROOT"     select="/"/>



<!--	
	======================================================
			EDK SYSTEM (EDWARD) Globals.	
	======================================================
-->	
<xsl:variable name="G_SYS_EVAL">
	<xsl:choose>
          <xsl:when test="not($P_SYSTEM_XML = '__UNDEF__')"><xsl:text>document($P_SYSTEM_XML)</xsl:text></xsl:when>
           <xsl:otherwise><xsl:text>/</xsl:text></xsl:otherwise>
 	</xsl:choose>
</xsl:variable>

<xsl:variable name="G_SYS_DOC"   	  select="dyn:evaluate($G_SYS_EVAL)"/>
<xsl:variable name="G_SYS"   		  select="$G_SYS_DOC/EDKSYSTEM"/>
<xsl:variable name="G_SYS_TIMESTAMP"  select="$G_SYS/@TIMESTAMP"/>
<xsl:variable name="G_SYS_EDKVERSION" select="$G_SYS/@EDKVERSION"/>

<xsl:variable name="G_SYS_INFO"   	  select="$G_SYS/SYSTEMINFO"/>
<xsl:variable name="G_SYS_INFO_PKG"   select="$G_SYS_INFO/@PACKAGE"/>
<xsl:variable name="G_SYS_INFO_DEV"   select="$G_SYS_INFO/@DEVICE"/>
<xsl:variable name="G_SYS_INFO_ARCH"  select="$G_SYS_INFO/@ARCH"/>
<xsl:variable name="G_SYS_INFO_SPEED" select="$G_SYS_INFO/@SPEEDGRADE"/>

<xsl:variable name="G_SYS_MODS" 	  select="$G_SYS/MODULES"/>
<xsl:variable name="G_SYS_EXPS" 	  select="$G_SYS/EXTERNALPORTS"/>

<xsl:variable name="COL_FOCUSED_MASTER" 			select="'AAAAFF'"/>
<xsl:variable name="COL_BG_OUTOF_FOCUS_CONNECTIONS" select="'AA7711'"/>

<!--  INDEX KEYS FOR FAST ACCESS  -->
<xsl:key name="G_MAP_MODULES"   	match="&ALLMODS;" use="@INSTANCE"/>
<xsl:key name="G_MAP_PROCESSORS"   	match="&CPUMODS;" use="@INSTANCE"/>

<xsl:key name="G_MAP_BUSSES"   		match="&BUSMODS;" use="@INSTANCE"/>
<xsl:key name="G_MAP_BUSSES"   		match="&BUSMODS;" use="@BUSSTD"/>
<xsl:key name="G_MAP_BUSSES" 	  	match="&BUSMODS;" use="@BUSSTD_PSF"/>

<xsl:key name="G_MAP_ALL_IOFS"   	match="&ALLIOFS;" use="../../@INSTANCE"/>
<xsl:key name="G_MAP_ALL_BIFS"   	match="&ALLBIFS;" use="../../@INSTANCE"/>

<xsl:key name="G_MAP_ALL_BIFS_BY_BUS" match="&ALLBIFS;" use="@BUSNAME"/>
<!-- 
 -->

<xsl:key name="G_MAP_MST_BIFS"   	match="&MSTBIFS;" use="@BUSNAME"/>
<xsl:key name="G_MAP_SLV_BIFS"   	match="&SLVBIFS;" use="@BUSNAME"/>
<xsl:key name="G_MAP_MOS_BIFS"   	match="&MOSBIFS;" use="@BUSNAME"/>

<xsl:key name="G_MAP_P2P_BIFS"   	match="&P2PBIFS;" use="@BUSNAME"/>
<xsl:key name="G_MAP_P2P_BIFS"   	match="&P2PBIFS;" use="@BUSSTD"/>
<xsl:key name="G_MAP_P2P_BIFS"   	match="&P2PBIFS;" use="@BUSSTD_PSF"/>

<xsl:key name="G_MAP_ALL_PORTS"   	match="&ALLPORTS;" use="../../@INSTANCE"/>
<xsl:key name="G_MAP_DEF_PORTS"   	match="&DEFPORTS;" use="../../@INSTANCE"/> <!-- Default ports -->
<xsl:key name="G_MAP_NDF_PORTS"   	match="&NDFPORTS;" use="../../@INSTANCE"/> <!-- Non Default ports -->

<!--
<xsl:key name="G_MAP_MASTER_BIFS"        match="&MSTBIFS;" use="@BUSNAME"/>
<xsl:key name="G_MAP_MASTER_BIFS"        match="MODULE[not(@MODCLASS ='BUS')]/BUSINTERFACES/BUSINTERFACE[(not(@IS_VALID) or (@IS_VALID = 'TRUE')) and (@TYPE = 'MASTER')]" use="../../@INSTANCE.@NAME"/>
<xsl:key name="G_MAP_BUSSES_BY_INSTANCE" match="MODULE[(@MODCLASS ='BUS')]" use="@INSTANCE"/>
<xsl:key name="G_MAP_XB_BUSSES" match="MODULE[(@MODCASS ='BUS')and (@IS_CROSSBAR)]" use="@INSTANCE"/>
 -->
<!--	
	======================================================
		 Groups.xml (BLOCKS) Globals	
	======================================================
-->	
<xsl:variable name="G_GRP_EVAL">
	<xsl:choose>
          <xsl:when test="not($P_GROUPS_XML = '__UNDEF__')"><xsl:text>document($P_GROUPS_XML)</xsl:text></xsl:when>
           <xsl:otherwise><xsl:text>/</xsl:text></xsl:otherwise>
 	</xsl:choose>
</xsl:variable>

<xsl:variable name="G_GRPS_DOC" select="dyn:evaluate($G_GRP_EVAL)"/>
<xsl:variable name="G_GROUPS" 	select="$G_GRPS_DOC/BLOCKS"/>

<xsl:variable name="G_NUM_OF_PROCS" 		select="count($G_SYS/MODULES/MODULE[(@MODCLASS = 'PROCESSOR')])"/>
<xsl:variable name="G_NUM_OF_PROCS_W_ADDRS" select="count($G_SYS/MODULES/MODULE[(@MODCLASS = 'PROCESSOR') and MEMORYMAP/MEMRANGE[(not(@IS_VALID) or (@IS_VALID = 'TRUE'))]])"/>

<xsl:variable name="G_FOCUSED_SCOPE">
    <xsl:choose>
    
        <!--  FOCUSING ON SPECIFIC SELECTIONS-->
        <xsl:when test="$G_ROOT/SAV/SELECTION">
        </xsl:when>
        
        <!--  FOCUSING ON PROCESSOR -->
        <xsl:when test="$G_ROOT/SAV/MASTER">
       		<xsl:if test="$G_DEBUG = 'TRUE'"><xsl:message>FOCUSED MASTERS SPECIFIED</xsl:message></xsl:if>
        	<xsl:for-each select="$G_ROOT/SAV/MASTER">
        		<xsl:variable name="m_inst_"  select="@INSTANCE"/>
   				<xsl:variable name="m_mod_"   select="$G_SYS_MODS/MODULE[(@INSTANCE = $m_inst_)]"/>
     			<xsl:for-each select="$m_mod_/BUSINTERFACES/BUSINTERFACE[(not(@IS_VALID) or (@IS_VALID = 'TRUE')) and not(@BUSNAME = '__NOC__') and ((@TYPE = 'MASTER') or (@TYPE = 'SLAVE') or (@TYPE = 'INITIATOR') or (@TYPE = 'TARGET'))]">
 				 	<xsl:if test="$G_DEBUG = 'TRUE'"><xsl:message>  FOCUSED MASTER BIF <xsl:value-of select="$m_inst_"/>.<xsl:value-of select="@NAME"/> = <xsl:value-of select="@BUSNAME"/></xsl:message></xsl:if>
   					<xsl:variable name="b_bus_"   select="@BUSNAME"/>
     				<BUS NAME="{@BUSNAME}" BUSSTD="{@BUSSTD}"/>
     				<xsl:for-each select="$G_SYS_MODS/MODULE[(not(@INSTANCE = $m_inst_) and (@MODCLASS = 'BUS_BRIDGE'))]/BUSINTERFACES/BUSINTERFACE[(not(@IS_VALID) or (@IS_VALID = 'TRUE')) and (@TYPE = 'SLAVE') and (@BUSNAME = $b_bus_)]">
 				 		<xsl:variable name="b_inst_" select="../../@INSTANCE"/>
     					<xsl:choose>
     						<xsl:when test="MASTERS/MASTER">
								<xsl:for-each select="MASTERS/MASTER">
									<xsl:variable name="sm_inst_" select="@INSTANCE"/>
									<xsl:if test="count($G_ROOT/SAV/MASTER[(@INSTANCE = $sm_inst_)]) &gt; 0">
 				 						<xsl:if test="$G_DEBUG = 'TRUE'"><xsl:message>  FOCUSED PERIPHERAL BRIDGE <xsl:value-of select="$b_inst_"/></xsl:message></xsl:if>
										<PERIPHERAL NAME="{$b_inst_}"/>
									</xsl:if>
								</xsl:for-each>
							</xsl:when>	
     						<xsl:otherwise>
 				 				<xsl:if test="$G_DEBUG = 'TRUE'"><xsl:message>  FOCUSED PERIPHERAL BRIDGE <xsl:value-of select="$b_inst_"/></xsl:message></xsl:if>
    			    			<PERIPHERAL NAME="{$b_inst_}"/>
     						</xsl:otherwise>
     					</xsl:choose>
     				</xsl:for-each>	
     			</xsl:for-each>
     			<xsl:for-each select="$m_mod_/PERIPHERALS/PERIPHERAL">
     				<xsl:variable name="p_id_"  select="@INSTANCE"/>
     				<xsl:variable name="p_mod_" select="$G_SYS_MODS/MODULE[@INSTANCE = $p_id_]"/>
    			    <PERIPHERAL NAME="{@INSTANCE}"/>
     				<xsl:variable name="p_mr_cnt_"  select="count($m_mod_/MEMORYMAP/MEMRANGE[(@INSTANCE = $p_id_)])"/>
 				 	<xsl:if test="$G_DEBUG = 'TRUE'"><xsl:message>  FOCUSED PERIPHERAL <xsl:value-of select="$p_id_"/> has <xsl:value-of select="$p_mr_cnt_"/> memory ranges</xsl:message></xsl:if>
 				 	<xsl:for-each select="$m_mod_/MEMORYMAP/MEMRANGE[(@INSTANCE = $p_id_)]/ACCESSROUTE/ROUTEPNT">
     					<xsl:variable name="b_id_"  select="@INSTANCE"/>
						<xsl:for-each select="$G_SYS_MODS/MODULE[((@INSTANCE = $b_id_) and (@MODCLASS = 'BUS'))]">
 				 			<xsl:if test="$G_DEBUG = 'TRUE'"><xsl:message>  FOCUSED PERIPHERAL BUS <xsl:value-of select="@INSTANCE"/></xsl:message></xsl:if>
     						<BUS NAME="{@INSTANCE}" BUSSTD="{@BUSSTD}"/> 
     					</xsl:for-each>
     				</xsl:for-each>
     			</xsl:for-each>
        	</xsl:for-each>
        </xsl:when>
        
        <!--  FOCUSING ON BUS -->
       <xsl:when test="$G_ROOT/SAV/BUS">
			<xsl:if test="$G_DEBUG = 'TRUE'"><xsl:message>FOCUSED BUSSES SPECIFIED</xsl:message></xsl:if>
        	<xsl:for-each select="$G_ROOT/SAV/BUS">
        		<xsl:variable name="m_inst_"  select="@INSTANCE"/>
   				<xsl:variable name="m_mod_"   select="$G_SYS_MODS/MODULE[(@INSTANCE = $m_inst_)]"/>
				<xsl:variable name="m_bstd_"  select="$m_mod_/@BUSSTD"/>
   				<BUS NAME="{$m_inst_}" BUSSTD="{$m_bstd_}"/> 
 			 	<xsl:if test="$G_DEBUG = 'TRUE'"><xsl:message>  FOCUSED BUS <xsl:value-of select="$m_inst_"/> <xsl:value-of select="$m_bstd_"/></xsl:message></xsl:if>
   			</xsl:for-each>	
       </xsl:when>
    </xsl:choose>
</xsl:variable>

<xsl:variable name="G_HAVE_XB_BUSSES">
	<xsl:choose>
		<xsl:when test="(count($G_SYS_MODS/MODULE[((@MODCLASS = 'BUS') and (@IS_CROSSBAR = 'TRUE'))]) &gt; 0)">TRUE</xsl:when>
		<xsl:otherwise>FALSE</xsl:otherwise>
	</xsl:choose>
</xsl:variable>			
			
<xsl:template name="F_ModClass_To_IpClassification">
	<xsl:param name="iModClass" select="'NONE'"/>
	<xsl:param name="iBusStd"   select="'NONE'"/>
	<xsl:choose>
		<xsl:when test="$iModClass = 'BUS'"><xsl:value-of select="$iBusStd"/> Bus</xsl:when>
		<xsl:when test="$iModClass = 'DEBUG'">Debug</xsl:when>
		<xsl:when test="$iModClass = 'MEMORY'">Memory</xsl:when>
		<xsl:when test="$iModClass = 'MEMORY_CNTLR'">Memory Controller</xsl:when>
		<xsl:when test="$iModClass = 'INTERRUPT_CNTLR'">Interrupt Controller</xsl:when>
		<xsl:when test="$iModClass = 'PERIPHERAL'">Peripheral</xsl:when>
		<xsl:when test="$iModClass = 'PROCESSOR'">Processor</xsl:when>
		<xsl:when test="$iModClass = 'BUS_BRIDGE'">Bus Bridge</xsl:when>
		<xsl:otherwise><xsl:value-of select="$iModClass"/></xsl:otherwise>
	</xsl:choose>	
</xsl:template>	

<xsl:template name="F_Connection_To_AXI_SLAVE">
  <xsl:param name="iNameParam" select="''"/>
  <xsl:param name="iModuleRefParam" select="''"/>

  <xsl:variable name="FilName" select="$iModuleRefParam/PARAMETERS/PARAMETER[@NAME=concat('C_', $iNameParam, '_MASTERS')]/@VALUE"/>
  <!-- <xsl:message>FIL NAME WAS <xsl:value-of select="$FilName"/></xsl:message>  -->
  <xsl:value-of select="$FilName"/>
</xsl:template>	

<xsl:template name="F_IS_Interface_External">
    <xsl:param name="iInstRef"/> <!--  Instance reference -->
    <xsl:param name="iIntfRef"/> <!--  Interface reference -->
    <xsl:variable name="intfName_" select="$iIntfRef/@NAME"/>
    <xsl:variable name="instName_" select="$iInstRef/@INSTANCE"/>
    
	<!-- <xsl:message>NAME 1 <xsl:value-of select="$expName1_"/></xsl:message>-->
    <!-- <xsl:message>NAME 2 <xsl:value-of select="$expName2_"/></xsl:message>-->
<!--
    <xsl:variable name="expName1_" select="concat($instName_,'_',$intfName_,'_',@PHYSICAL,'_pin')"/>
    <xsl:variable name="expName2_" select="concat($instName_,'_',@PHYSICAL,'_pin')"/>
  -->    
    
	<!-- Store the number of physical ports connected externals in a variable -->	
	
	<xsl:variable name="connected_externals_">
		<xsl:for-each select="$iIntfRef/PORTMAPS/PORTMAP">
			<xsl:variable name="portName_" select="@PHYSICAL"/>
    		<xsl:if test="$iInstRef/PORTS/PORT[(@NAME = $portName_)]">
    			<xsl:variable name="portNet_" select="$iInstRef/PORTS/PORT[(@NAME = $portName_)]/@SIGNAME"/>
  				<xsl:if test="$G_SYS_EXPS/PORT[(@SIGNAME = $portNet_)]">
  					<EXTP NAME="{@PHYSICAL}"/>
  				</xsl:if>
    		</xsl:if>
		</xsl:for-each>
	</xsl:variable>
	
	<!-- 
	<xsl:message><xsl:value-of select="$instName_"/>.<xsl:value-of select="$intfName_"/> has <xsl:value-of select="count(exsl:node-set($connected_externals_)/EXTP)"/> connected externals.</xsl:message> 
    -->
	<xsl:choose>
		<xsl:when test="(count(exsl:node-set($connected_externals_)/EXTP) &gt; 0)">TRUE</xsl:when>
		<xsl:otherwise>FALSE</xsl:otherwise>
	</xsl:choose>	
</xsl:template>

</xsl:stylesheet>

