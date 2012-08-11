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
]>	        

<xsl:stylesheet version="1.0"
	   xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
       xmlns:exsl="http://exslt.org/common"
       xmlns:dyn="http://exslt.org/dynamic"
       xmlns:math="http://exslt.org/math"
       xmlns:xlink="http://www.w3.org/1999/xlink"
       extension-element-prefixes="exsl dyn math xlink">
           
<xsl:output method="xml" version="1.0" encoding="UTF-8" indent="yes"/>

<!--
    ================================================================================
                            Generate XTeller for ADDRESSES
    ================================================================================ 
-->

<xsl:template name="WRITE_VIEW_ADDRESS">
              
    <xsl:for-each select="$G_SYS_MODS/MODULE[((@MODCLASS = 'PROCESSOR') and (MEMORYMAP/MEMRANGE[((not(@IS_VALID) or (@IS_VALID = 'TRUE')) and ACCESSROUTE)]))]">
        <xsl:sort data-type="number" select="@ROW_INDEX" order="ascending"/>
            
        <xsl:variable name="procInst_"     select="@INSTANCE"/>
        <xsl:variable name="procMod_"      select="self::node()"/>
        <xsl:variable name="procModType"   select="@MODTYPE"/>
        <xsl:variable name="procModClass_" select="@MODCLASS"/>
        <xsl:variable name="procInstHdrVal_"><xsl:value-of select="$procInst_"/>'s Address Map</xsl:variable>
        <xsl:variable name="procInstRowIdx_" select="position() - 1"/>
        
        <!-- <SET ID="{$procInst_}" CLASS="MODULE" ROW_INDEX="{$procInstRowIdx_}"> -->
        
        <xsl:element name="SET">
			<xsl:attribute name="ID"><xsl:value-of select="$procInst_"/></xsl:attribute>
			<xsl:attribute name="CLASS">MODULE</xsl:attribute>
			<xsl:attribute name="ROW_INDEX"><xsl:value-of select="$procInstRowIdx_"/></xsl:attribute>

            <!-- <VARIABLE VIEWTYPE="STATIC" VIEWDISP="Instance" NAME="INSTANCE"  VALUE="{$procInstHdrVal_}"/> -->
            
            <xsl:element name="VARIABLE">
				<xsl:attribute name="NAME">INSTANCE</xsl:attribute>
				<xsl:attribute name="VALUE"><xsl:value-of select="$procInstHdrVal_"/></xsl:attribute>
				<xsl:attribute name="VIEWDISP">Instance</xsl:attribute>
				<xsl:attribute name="VIEWTYPE">STATIC</xsl:attribute>
			</xsl:element>
            
            <xsl:for-each select="$procMod_/MEMORYMAP/MEMRANGE[((not(@IS_VALID) or (@IS_VALID = 'TRUE')) and (ACCESSROUTE or (@MEMTYPE = 'BRIDGE')))]">
                <xsl:sort data-type="number" select="@BASEDECIMAL" order="ascending"/>
                
                <xsl:variable name="addr_id_"><xsl:value-of select="@BASENAME"/>:<xsl:value-of select="@HIGHNAME"/></xsl:variable>
                <xsl:variable name="baseName_" select="@BASENAME"/>
                <xsl:variable name="highName_" select="@HIGHNAME"/>
                
                <!-- 
                <xsl:if test="$G_DEBUG='TRUE'">
                	<xsl:message>ADDRESS ID <xsl:value-of select="$addr_id_"/></xsl:message>
                </xsl:if>
                -->
                
                <xsl:variable name="set_id_">
                    <xsl:if test="(@INSTANCE)">
                        <xsl:value-of select="$procInst_"/>.<xsl:value-of select="@INSTANCE"/>:<xsl:value-of select="$addr_id_"/>
                    </xsl:if>
                    <xsl:if test="not(@INSTANCE)">
                        <xsl:value-of select="$procInst_"/>:<xsl:value-of select="$addr_id_"/>
                    </xsl:if>
                </xsl:variable>
                
                <xsl:variable name="procAddrRowIdx_" select="position() - 1"/>
                <SET ID="{$set_id_}" CLASS="ADDRESS" ROW_INDEX="{$procAddrRowIdx_}">
                    
                    <xsl:if test="(@INSTANCE)">
                        <xsl:variable name="periInst_"   select="@INSTANCE"/>
	                	<xsl:variable name="periMod_"    select="key('G_MAP_MODULES', $periInst_)"/>
                        <!-- 
                         <xsl:variable name="subInstance_"     select="$G_SYS_MODS/MODULE[(@INSTANCE = $instance_)]"/>
	                	<xsl:message>Count memrange slaves <xsl:value-of select="count($modMemMapSlvs_)"/> </xsl:message>
	                	<xsl:message>Count mod valid bifs  <xsl:value-of select="count($modValidBifs_)"/> </xsl:message>
                         -->
  
	                                      
                        <xsl:variable name="periModType_"   select="$periMod_/@MODTYPE"/>
                        <xsl:variable name="periViewIcon_"  select="$periMod_/LICENSEINFO/@ICON_NAME"/>
                        <xsl:variable name="periHwVersion_" select="$periMod_/@HWVERSION"/>
                        
                        <VARIABLE VIEWTYPE="STATIC" VIEWDISP="Instance"   NAME="INSTANCE"  VALUE="{$periInst_}"/>
                        <VARIABLE VIEWTYPE="STATIC" VIEWDISP="IP Type"    NAME="MODTYPE"   VALUE="{$periModType_}" VIEWICON="{$periViewIcon_}"/>
                        <VARIABLE VIEWTYPE="STATIC" VIEWDISP="IP Version" NAME="HWVERSION" VALUE="{$periHwVersion_}"/>
                    </xsl:if>
                    
                    <xsl:if test="not(@INSTANCE)">
                        <VARIABLE VIEWTYPE="STATIC" VIEWDISP="Instance"   NAME="INSTANCE"  VALUE="{$procInst_}"/>
                        <VARIABLE VIEWTYPE="STATIC" VIEWDISP="IP Type"    NAME="MODTYPE"   VALUE="{$procModType}" VIEWICON="{$procMod_/LICENSEINFO/@ICON_NAME}"/>
                        <VARIABLE VIEWTYPE="STATIC" VIEWDISP="IP Version" NAME="HWVERSION" VALUE="{$procHwVersion_}"/>
                    </xsl:if>

                    <VARIABLE VIEWTYPE="STATIC" VIEWDISP="Address Type" NAME="MEMTYPE" VALUE="{@MEMTYPE}"/>
                    
                    <xsl:variable name="instName_">
                        <xsl:choose>
                            <xsl:when test="@INSTANCE"><xsl:value-of select="@INSTANCE"/></xsl:when>
                            <xsl:otherwise>Connected<xsl:value-of select="$procInst_"/></xsl:otherwise>
                        </xsl:choose>
                    </xsl:variable>
                    <!-- 
                    <xsl:message>INST : <xsl:value-of select="$set_id_"/></xsl:message>
                     -->

                   <xsl:variable name="is_locked_">
                       <xsl:if test="@IS_LOCKED = 'TRUE'">TRUE</xsl:if>
                       <xsl:if test="not(@IS_LOCKED) or not(@IS_LOCKED = 'TRUE')">FALSE</xsl:if>
                   </xsl:variable>

                   <xsl:variable name="baseAddrViewType_">
						<xsl:choose>
							<xsl:when test="$is_locked_='TRUE'">STATIC</xsl:when>
							<xsl:otherwise>TEXTBOX</xsl:otherwise>
						</xsl:choose>
				   </xsl:variable>

                   <xsl:if test="(@SIZEABRV and not(@SIZEABRV = 'U'))">
						<xsl:variable name="baseAddr_"><xsl:value-of select="translate(@BASEVALUE,&HEXU2L;)"/></xsl:variable>
                     	<xsl:variable name="highAddr_"><xsl:value-of select="translate(@HIGHVALUE,&HEXU2L;)"/></xsl:variable>
                     	<VARIABLE VIEWTYPE="{$baseAddrViewType_}"  VIEWDISP="Base Address" NAME="BASEVALUE" VALUE="{$baseAddr_}"/>
                     	<VARIABLE VIEWTYPE="STATIC"   VIEWDISP="High Address" NAME="HIGHVALUE" VALUE="{$highAddr_}"/>

                     	<xsl:if test="not(@MEMTYPE) or not(@MEMTYPE = 'BRIDGE')">
                       		<VARIABLE VIEWTYPE="CHECKBOX" VIEWDISP="Lock" NAME="IS_LOCKED" VALUE="{$is_locked_}"/>
                     	</xsl:if>

                     	<xsl:if test="@MEMTYPE and (@MEMTYPE = 'BRIDGE') and not(@BRIDGE_TO)">
                       		<VARIABLE VIEWTYPE="CHECKBOX" VIEWDISP="Lock" NAME="IS_LOCKED" VALUE="{$is_locked_}"/>
                   		</xsl:if>
					</xsl:if>
                    
                    <xsl:if test="(@SIZEABRV and (@SIZEABRV = 'U'))">
                      <VARIABLE VIEWTYPE="TEXTBOX" VIEWDISP="Base Address" NAME="BASEVALUE" VALUE=""/>
                    </xsl:if>
                   
                    <VARIABLE VIEWTYPE="STATIC"   VIEWDISP="Base Name"  NAME="BASENAME" VALUE="{@BASENAME}"/>

					<xsl:variable name="sizeViewType_">
						<xsl:choose>
							<xsl:when test="(@SIZEABRV and (@SIZEABRV = 'U'))">DROPDOWN</xsl:when>
							<xsl:when test="$is_locked_='TRUE'">STATIC</xsl:when>
							<xsl:otherwise>DROPDOWN</xsl:otherwise>
						</xsl:choose>
					</xsl:variable>

                   <VARIABLE VIEWTYPE="{$sizeViewType_}" VIEWDISP="Size" NAME="SIZEABRV" VALUE="{@SIZEABRV}"/>
                   
                   <xsl:variable name="periInst_"       select="@INSTANCE"/>
	               <xsl:variable name="periMod_"        select="key('G_MAP_MODULES',  $periInst_)"/>
	               <xsl:variable name="periModClass_"   select="$periMod_/@MODCLASS"/>
	      		   <xsl:variable name="periValidBifs_"  select="key('G_MAP_ALL_BIFS', $periInst_)[not(@BUSNAME = '__NOC__')]"/>	
	               <xsl:variable name="periMemMapSlvs_" select="$periMod_/MEMORYMAP/MEMRANGE[(@BASENAME = $baseName_) and (@HIGHNAME = $highName_)]/SLAVES/SLAVE"/>
	               <xsl:variable name="periMemMapBifs_">
						<xsl:for-each select="$periMemMapSlvs_">
                            <xsl:variable name="periSlvBifName_"  select="@BUSINTERFACE"/>
                            <xsl:if test="$periValidBifs_[(@NAME = $periSlvBifName_)]">
                                <xsl:variable name="periBif_"     select="$periValidBifs_[(@NAME = $periSlvBifName_)]"/>
                                <xsl:variable name="periBifName_" select="$periBif_/@NAME"/>
                                <xsl:variable name="periBifBus_"  select="$periBif_/@BUSNAME"/>
                                	<!-- 
                                  	<xsl:message>  Slv Bif  <xsl:value-of select="$periBifName_"/> = <xsl:value-of select="$periBifBus_"/></xsl:message> 
                                	 -->
                                	<MMBIF NAME="{$periBifName_}" BUS="{$periBifBus_}"/>
                            </xsl:if>
						</xsl:for-each>
	               </xsl:variable>
	               
	               <xsl:variable name="num_of_periMemMapBifs_" select="count(exsl:node-set($periMemMapBifs_)/MMBIF)"/>
	               
	               <!-- 
				   <xsl:message>  Total num of slv bifs <xsl:value-of select="$num_of_periMemMapBifs_"/>  </xsl:message>
				   <xsl:message>  </xsl:message>
	                -->

					<xsl:variable name="valid_bifNames_">
				   		<xsl:for-each select="exsl:node-set($periMemMapBifs_)/MMBIF">
	                    	<xsl:variable name="bifName_"  select="@NAME"/>
                        	<xsl:if test="position() &gt; 1">:</xsl:if><xsl:value-of select="$bifName_"/>
						</xsl:for-each>
                    </xsl:variable>
                    
 					<xsl:variable name="valid_busNames_">
				   		<xsl:for-each select="exsl:node-set($periMemMapBifs_)/MMBIF">
	                        <xsl:variable name="busName_"  select="@BUS"/>
                        	<xsl:if test="position() &gt; 1">:</xsl:if><xsl:value-of select="$busName_"/>
						</xsl:for-each>
                    </xsl:variable>                   
                    
	                <!--
                             <xsl:message>  Mod Bif  <xsl:value-of select="$bifName_"/>  : <xsl:value-of select="position()"/></xsl:message> 
                             <xsl:message>  Mod Bif  <xsl:value-of select="$bifName_"/>  : <xsl:value-of select="position()"/></xsl:message> 
	                             <xsl:message>Slv Bif <xsl:value-of select="$bifName_"/>  : <xsl:value-of select="position()"/></xsl:message> 
	                               	<xsl:variable name="modBifs_"  select="$modInst_/BUSINTERFACES"/>
	                            <xsl:if test="$periValidBifs_[(@NAME = $bifName_)]">
	                                <xsl:variable name="busName_" select="$periValidBifs_[(@NAME = $bifName_)]/@BUSNAME"/>
	                                  	<xsl:message>Mod Bif  <xsl:value-of select="$bifName_"/>  : <xsl:value-of select="position()"/></xsl:message> 
	                                <xsl:if test="position() &gt; 1">:</xsl:if><xsl:value-of select="$bifName_"/>
	                            </xsl:if>             
	                -->
                    <!-- 
	                <xsl:message>Module Instances <xsl:value-of select="$instName_"/> </xsl:message>
	                <xsl:message>Base Name <xsl:value-of select="$baseName_"/> </xsl:message>
	                <xsl:message>High Name <xsl:value-of select="$highName_"/> </xsl:message>
	                <xsl:message>Valid bif names <xsl:value-of select="$valid_bifNames_"/> </xsl:message>
	                <xsl:message>Valid bif names <xsl:value-of select="$valid_bifNames_"/> </xsl:message>
	                <xsl:message>Valid bus names <xsl:value-of select="$valid_busNames_"/> </xsl:message>
	                -->
	                
                    
	                <xsl:variable name="var_bifNames_">
	                    <xsl:choose>
		                    <xsl:when test="string-length($valid_bifNames_) &lt; 1">
		                        <xsl:choose>
		                            <xsl:when test="$periModClass_ = 'BUS'">Not Applicable</xsl:when>
		                            <xsl:otherwise>Not Connected</xsl:otherwise>
		                        </xsl:choose>
		                    </xsl:when>
		                    <xsl:otherwise><xsl:value-of select="$valid_bifNames_"/></xsl:otherwise>
	                    </xsl:choose> 
	                </xsl:variable>
	                
					<VARIABLE VIEWTYPE="STATIC" VIEWDISP="Bus Interface(s)"  NAME="BIFNAMES" VALUE="{$var_bifNames_}"/>
					<xsl:if test="(($num_of_periMemMapBifs_ &gt; 0) and (string-length($valid_busNames_) &gt; 0))">
                    	<VARIABLE VIEWTYPE="STATIC" VIEWDISP="Bus Name"      NAME="BUSNAME"  VALUE="{$valid_busNames_}"/>
					</xsl:if>
            	</SET>  <!--  End of one processor memory range row -->
            </xsl:for-each> <!-- end of processor memory ranges loop -->
        </xsl:element><!--  End of Processor memory map set -->
    </xsl:for-each> <!-- end of processor module address space loop -->
    
    <!-- 
        Add branch for valid address that are not part of a processor's 
        memory map. Usually modules that have just been added, but have 
        not been connected to a bus yet.
     -->
     
    <xsl:variable name="nonProcAddresses_">
    
        <!-- Add a dummy non proc as a place holder. Otherwise the exsl:node-set test
             Below complains if the variable is completely empty
        -->
        <NONPROCADDRESS INSTANCE="__DUMMY__" BASENAME="__DUMMY__" HIGHNAME="__DUMMY__" BASEDECIMAL="__DUMMY__"/>
         
        <xsl:for-each select="$G_SYS_MODS/MODULE[(not(@MODCLASS = 'PROCESSOR') and (MEMORYMAP/MEMRANGE[((not(@IS_VALID) or (@IS_VALID = 'TRUE')) and ACCESSROUTE)]))]">
            <xsl:variable name="nonProcInst_" select="@INSTANCE"/>
        
            <xsl:for-each select="MEMORYMAP/MEMRANGE[(not(@IS_VALID) or (@IS_VALID = 'TRUE'))]">
        
                <xsl:variable name="highName_"    select="@HIGHNAME"/>
                <xsl:variable name="baseName_"    select="@BASENAME"/>
                <xsl:variable name="baseDecimal_" select="@BASEDECIMAL"/>
            
                <xsl:if test="not($G_SYS_MODS/MODULE[(@MODCLASS = 'PROCESSOR')]/MEMORYMAP/MEMRANGE[((@INSTANCE = $nonProcInst_) and (@BASENAME = $baseName_) and (@HIGHNAME = $highName_))])">
                     <NONPROCADDRESS INSTANCE="{$nonProcInst_}" BASENAME="{$baseName_}" HIGHNAME="{$highName_}" BASEDECIMAL="{$baseDecimal_}"/>
                </xsl:if>
            </xsl:for-each>
        </xsl:for-each>
        
    </xsl:variable>

    <!--  Add unmapped addresses -->
    <xsl:variable name="hasUnMappedAddress">
        <xsl:for-each select="$G_SYS_MODS/MODULE[(not(@MODCLASS = 'PROCESSOR') and (MEMORYMAP/MEMRANGE[(not(@IS_VALID) or (@IS_VALID = 'TRUE'))]))]">
            <xsl:variable name="nonProcInst_" select="@INSTANCE"/>
            <xsl:for-each select="MEMORYMAP/MEMRANGE[(not(@IS_VALID) or (@IS_VALID = 'TRUE'))]">
                <xsl:variable name="highName_"    select="@HIGHNAME"/>
                <xsl:variable name="baseName_"    select="@BASENAME"/>
                <xsl:variable name="baseDecimal_" select="@BASEDECIMAL"/>
                <xsl:if test="not($G_SYS_MODS/MODULE[(@MODCLASS = 'PROCESSOR')]/MEMORYMAP/MEMRANGE[((@INSTANCE = $nonProcInst_) and (@BASENAME = $baseName_) and (@HIGHNAME = $highName_))])"><xsl:value-of select="$nonProcInst_"/></xsl:if>
            </xsl:for-each>
        </xsl:for-each>
    </xsl:variable>

    <xsl:if test="string-length($hasUnMappedAddress) &gt; 1">
    
        <SET ID="Unmapped Addresses" CLASS="MODULE" ROW_INDEX="{$G_NUM_OF_PROCS_W_ADDRS}">
            
            <VARIABLE VIEWTYPE="STATIC" VIEWDISP="Instance" NAME="INSTANCE"  VALUE="Unmapped Addresses"/>
            
            <xsl:for-each select="$G_SYS_MODS/MODULE[(not(@MODCLASS = 'PROCESSOR') and (MEMORYMAP/MEMRANGE[(not(@IS_VALID) or (@IS_VALID = 'TRUE'))]))]/MEMORYMAP/MEMRANGE[(not(@IS_VALID) or (@IS_VALID = 'TRUE'))]"> 
            
                <xsl:variable name="nonProcMod_"  select="../.."/>
                <xsl:variable name="nonProcMMap_" select="$nonProcMod_/MEMORYMAP"/>
                <xsl:variable name="instance_"    select="$nonProcMod_/@INSTANCE"/>
                
                <xsl:variable name="row_index_"    select="position()"/>
                <xsl:variable name="instName_"     select="$nonProcMod_/@INSTANCE"/>
                <xsl:variable name="highName_"     select="@HIGHNAME"/>
                <xsl:variable name="baseName_"     select="@BASENAME"/>
                <xsl:variable name="baseDecimal_"  select="@BASEDECIMAL"/>
                
                <xsl:for-each select="$nonProcMMap_/MEMRANGE[((@BASENAME = $baseName_) and (@HIGHNAME = $highName_))]">
                    
                    <xsl:if test="not($G_SYS_MODS/MODULE[(@MODCLASS = 'PROCESSOR')]/MEMORYMAP/MEMRANGE[((@INSTANCE = $instName_) and (@BASENAME = $baseName_) and (@HIGHNAME = $highName_))])">
                    
                        <xsl:variable name="addr_id_"><xsl:value-of select="$baseName_"/>:<xsl:value-of select="$highName_"/></xsl:variable>
                        <xsl:variable name="set_id_"><xsl:value-of select="$instName_"/>:<xsl:value-of select="$addr_id_"/></xsl:variable>
                            
                        <xsl:variable name="inst_modtype_"    select="$nonProcMod_/@MODTYPE"/>
                        <xsl:variable name="inst_viewicon_"   select="$nonProcMod_/LICENSEINFO/@ICON_NAME"/>
                        <xsl:variable name="inst_modclass_"   select="$nonProcMod_/@MODCLASS"/>
                        <xsl:variable name="inst_hwversion_"  select="$nonProcMod_/@HWVERSION"/>
                            
                        <SET ID="{$set_id_}" CLASS="ADDRESS">
                                
                            <VARIABLE VIEWTYPE="STATIC" VIEWDISP="Instance"   NAME="INSTANCE"  VALUE="{$instance_}"/>
                            <VARIABLE VIEWTYPE="STATIC" VIEWDISP="IP Type"    NAME="MODTYPE"   VALUE="{$inst_modtype_}" VIEWICON="{$inst_viewicon_}"/>
                            <VARIABLE VIEWTYPE="STATIC" VIEWDISP="IP Version" NAME="HWVERSION" VALUE="{$inst_hwversion_}"/>
                            <VARIABLE VIEWTYPE="STATIC" VIEWDISP="Address Type" NAME="MEMTYPE" VALUE="{@MEMTYPE}"/>

                            <xsl:variable name="is_locked_">
                              <xsl:if test="@IS_LOCKED = 'TRUE'">TRUE</xsl:if>
                              <xsl:if test="not(@IS_LOCKED) or not(@IS_LOCKED = 'TRUE')">FALSE</xsl:if>
                            </xsl:variable>

                            <xsl:variable name="baseAddrViewType_">
                              <xsl:choose>
                                <xsl:when test="$is_locked_='TRUE'">STATIC</xsl:when>
                                <xsl:otherwise>TEXTBOX</xsl:otherwise>
                              </xsl:choose>
                            </xsl:variable>

                            <xsl:if test="(@SIZEABRV and not(@SIZEABRV = 'U'))">
                            
                                <xsl:variable name="baseAddr_"><xsl:value-of select="translate(@BASEVALUE,&HEXU2L;)"/></xsl:variable>
                                <xsl:variable name="highAddr_"><xsl:value-of select="translate(@HIGHVALUE,&HEXU2L;)"/></xsl:variable>
                                
                                <VARIABLE VIEWTYPE="{$baseAddrViewType_}"  VIEWDISP="Base Address" NAME="BASEVALUE" VALUE="{$baseAddr_}"/>
                                <VARIABLE VIEWTYPE="STATIC"   VIEWDISP="High Address" NAME="HIGHVALUE" VALUE="{$highAddr_}"/>

                                <xsl:if test="not(@MEMTYPE) or not(@MEMTYPE = 'BRIDGE')">
                                  <VARIABLE VIEWTYPE="CHECKBOX" VIEWDISP="Lock" NAME="IS_LOCKED" VALUE="{$is_locked_}"/>
                                </xsl:if>

                                <xsl:if test="@MEMTYPE and (@MEMTYPE = 'BRIDGE') and not(@BRIDGE_TO)">
                                  <VARIABLE VIEWTYPE="CHECKBOX" VIEWDISP="Lock" NAME="IS_LOCKED" VALUE="{$is_locked_}"/>
                                </xsl:if>

                            </xsl:if>
                                
                            <xsl:if test="(@SIZEABRV and (@SIZEABRV = 'U'))">
                                <VARIABLE VIEWTYPE="TEXTBOX" VIEWDISP="Base Address" NAME="BASEVALUE" VALUE=""/>
                            </xsl:if>

                                
            <!--
                                Lock, DCache and ICache removed in 11.1
                                
                                <xsl:if test="(@IS_CACHEABLE = 'TRUE')">
                                    
                                    <xsl:variable name="is_dcached_">
                                        <xsl:if test="(@IS_DCACHED = 'TRUE')">TRUE</xsl:if>
                                        <xsl:if test="(not(@IS_DCACHED) or not(@IS_DCACHED = 'TRUE'))">FALSE</xsl:if>
                                    </xsl:variable>
                                    
                                    <xsl:variable name="is_icached_">
                                        <xsl:if test="(@IS_ICACHED = 'TRUE')">TRUE</xsl:if>
                                        <xsl:if test="(not(@IS_ICACHED) or not(@IS_ICACHED = 'TRUE'))">FALSE</xsl:if>
                                    </xsl:variable>
                                    
                                    <VARIABLE VIEWTYPE="CHECKBOX" VIEWDISP="DCache" NAME="IS_DCACHED" VALUE="{$is_dcached_}"/>
                                    <VARIABLE VIEWTYPE="CHECKBOX" VIEWDISP="ICache" NAME="IS_ICACHED" VALUE="{$is_icached_}"/>
                                </xsl:if>
             -->                    
                                
		                    <VARIABLE VIEWTYPE="STATIC"   VIEWDISP="Base Name"  NAME="BASENAME" VALUE="{@BASENAME}"/>

                        <xsl:variable name="sizeViewType_">
                          <xsl:choose>
                            <xsl:when test="(@SIZEABRV and (@SIZEABRV = 'U'))">DROPDOWN</xsl:when>
                            <xsl:when test="$is_locked_='TRUE'">STATIC</xsl:when>
                            <xsl:otherwise>DROPDOWN</xsl:otherwise>
                          </xsl:choose>
                        </xsl:variable>

                        <VARIABLE VIEWTYPE="{$sizeViewType_}" VIEWDISP="Size" NAME="SIZEABRV" VALUE="{@SIZEABRV}"/>
	                    
	                    <xsl:variable name="valid_bifNames_">
	                        <xsl:choose>
	                            <xsl:when test="$nonProcMMap_/MEMRANGE[(@BASENAME = $baseName_) and (@HIGHNAME = $highName_)]/SLAVES">
	                                <xsl:for-each select="$nonProcMMap_/MEMRANGE[(@BASENAME = $baseName_) and (@HIGHNAME = $highName_)]/SLAVES/SLAVE">
	                                    <xsl:variable name="bifName_"  select="@BUSINTERFACE"/>
	                                     <!-- <xsl:message>Bif Name <xsl:value-of select="$bifName_"/> </xsl:message> -->
	                                    <xsl:variable name="modBifs_"  select="$nonProcMod_/BUSINTERFACES"/>
	                                    <xsl:if test="$modBifs_/BUSINTERFACE[((@NAME = $bifName_) and not(@IS_VALID = 'FALSE') and not(@BUSNAME = '__NOC__'))]">
	                                        <xsl:variable name="busName_" select="$modBifs_/BUSINTERFACE[((@NAME = $bifName_) and not(@IS_VALID = 'FALSE') and not(@BUSNAME = '__NOC__'))]/@BUSNAME"/>
	                                        <xsl:if test="position() &gt; 1">:</xsl:if><xsl:value-of select="@BUSINTERFACE"/>
	                                    </xsl:if>    
	                                </xsl:for-each>
	                            </xsl:when>
	                            <xsl:otherwise>
	                                <xsl:for-each select="$nonProcMMap_/MEMRANGE[(@BASENAME = $baseName_) and (@HIGHNAME = $highName_)]/SLVINTERFACES/BUSINTERFACE">
	                                    <xsl:variable name="bifName_"  select="@NAME"/>
	                                    <xsl:variable name="modBifs_"  select="$nonProcMod_"/>
	                                    <xsl:if test="$modBifs_/BUSINTERFACE[((@NAME = $bifName_) and not(@IS_VALID = 'FALSE') and not(@BUSNAME = '__NOC__'))]">
	                                        <xsl:variable name="busName_" select="$modBifs_/BUSINTERFACE[((@NAME = $bifName_) and not(@IS_VALID = 'FALSE') and not(@BUSNAME = '__NOC__'))]/@BUSNAME"/>
	                                        <xsl:if test="position() &gt; 1">:</xsl:if><xsl:value-of select="@NAME"/>
	                                    </xsl:if>    
	                                </xsl:for-each>                       
	                            </xsl:otherwise>
	                        </xsl:choose>
	                    </xsl:variable>		                    
                    
                     <xsl:variable name="def_bifNames_">
                        <xsl:choose>
                         <xsl:when test="(string-length($valid_bifNames_) &lt; 1) or ((string-length($valid_bifNames_) = 1) and ($valid_bifNames_ = ':'))">Not Connected</xsl:when>
	                    <xsl:when test="starts-with($valid_bifNames_,':')"><xsl:value-of select="substring-after($valid_bifNames_,':')"/></xsl:when>
	                    <xsl:otherwise><xsl:value-of select="$valid_bifNames_"/></xsl:otherwise>
                        </xsl:choose>
                     </xsl:variable>
                     
                     
                    <VARIABLE VIEWTYPE="STATIC" VIEWDISP="Bus Interface(s)"  NAME="BIFNAMES" VALUE="{$def_bifNames_}"/>
                            
	                <xsl:choose>
	                    <xsl:when test="$nonProcMMap_/MEMRANGE[(@BASENAME = $baseName_) and (@HIGHNAME = $highName_)]/SLAVES">
	                       <xsl:for-each select="$nonProcMMap_/MEMRANGE[(@BASENAME = $baseName_) and (@HIGHNAME = $highName_)]/SLAVES/SLAVE">
	                            <xsl:variable name="slvBifName_" select="@BUSINTERFACE"/>
	                            <xsl:variable name="modBifs_"    select="$nonProcMod_/BUSINTERFACES"/>
	                            <xsl:if test="count($modBifs_/BUSINTERFACE[((@NAME = $slvBifName_) and not(@IS_VALID = 'FALSE') and not(@BUSNAME = '__NOC__'))]) = 1">
	                                <xsl:variable name="slvBusName_" select="$modBifs_/BUSINTERFACE[((@NAME = $slvBifName_) and not(@IS_VALID = 'FALSE') and not(@BUSNAME = '__NOC__'))]/@BUSNAME"/>
	                                <VARIABLE VIEWTYPE="STATIC" VIEWDISP="Bus Name" NAME="BUSNAME" VALUE="{$slvBusName_}"/>
	                            </xsl:if>    
	                        </xsl:for-each>
	                    </xsl:when>
	                    <xsl:otherwise>
	                        <xsl:for-each select="$nonProcMMap_/MEMRANGE[(@BASENAME = $baseName_) and (@HIGHNAME = $highName_)]/SLVINTERFACES/BUSINTERFACE">
	                            <xsl:variable name="slvBifName_" select="@NAME"/>
	                            <xsl:variable name="modBifs_"    select="$nonProcMod_"/>
	                            <xsl:if test="count($modBifs_/BUSINTERFACE[((@NAME = $slvBifName_) and not(@IS_VALID = 'FALSE') and not(@BUSNAME = '__NOC__'))]) = 1">
	                                <xsl:variable name="slvBusName_" select="$modBifs_/BUSINTERFACE[((@NAME = $slvBifName_) and not(@IS_VALID = 'FALSE') and not(@BUSNAME = '__NOC__'))]/@BUSNAME"/>
	                                <VARIABLE VIEWTYPE="STATIC" VIEWDISP="Bus Name" NAME="BUSNAME" VALUE="{$slvBusName_}"/>
	                            </xsl:if>    
	                        </xsl:for-each>
	                    </xsl:otherwise>
	                </xsl:choose>
                            
                            
                </SET>  <!--  End of one non processor memory range row -->
            </xsl:if>   
                        
        </xsl:for-each> <!-- end of non processor memory ranges loop -->
            
      </xsl:for-each> <!--  end of NONPROCADDRESS loop -->
        
      </SET> <!--  End of non processor tree branch -->
        
    </xsl:if> <!--  End of test to see if we have and non processor mapped address -->

</xsl:template> 


<xsl:template name="__WRITE_VIEW_ADDRESS__">

<!--
-->                
    <xsl:for-each select="$G_SYS_MODS/MODULE[((@MODCLASS = 'PROCESSOR') and (MEMORYMAP/MEMRANGE[((not(@IS_VALID) or (@IS_VALID = 'TRUE')) and ACCESSROUTE)]))]">
        <xsl:sort data-type="number" select="@ROW_INDEX" order="ascending"/>
            
        <xsl:variable name="procInst_" select="@INSTANCE"/>
        <xsl:variable name="modClass_" select="@MODCLASS"/>
        
        <xsl:variable name="procInstHdrVal_"><xsl:value-of select="$procInst_"/>'s Address Map</xsl:variable>
        <xsl:variable name="procInstRowIdx_" select="position() - 1"/>
        <xsl:variable name="modInstance_" select="self::node()"/>
        
        <SET ID="{$procInst_}" CLASS="MODULE" ROW_INDEX="{$procInstRowIdx_}">
        
            <VARIABLE VIEWTYPE="STATIC" VIEWDISP="Instance" NAME="INSTANCE"  VALUE="{$procInstHdrVal_}"/>
            
            <xsl:for-each select="$modInstance_/MEMORYMAP/MEMRANGE[((not(@IS_VALID) or (@IS_VALID = 'TRUE')) and (ACCESSROUTE or (@MEMTYPE = 'BRIDGE')))]">
                <xsl:sort data-type="number" select="@BASEDECIMAL" order="ascending"/>
                
                <xsl:variable name="addr_id_"><xsl:value-of select="@BASENAME"/>:<xsl:value-of select="@HIGHNAME"/></xsl:variable>
                <xsl:variable name="baseName_" select="@BASENAME"/>
                <xsl:variable name="highName_" select="@HIGHNAME"/>
                
                <xsl:if test="$G_DEBUG='TRUE'">
                	<xsl:message>ADDRESS ID <xsl:value-of select="$addr_id_"/></xsl:message>
                </xsl:if>
                
                <xsl:variable name="set_id_">
                    <xsl:if test="(@INSTANCE)">
                        <xsl:value-of select="$procInst_"/>.<xsl:value-of select="@INSTANCE"/>:<xsl:value-of select="$addr_id_"/>
                    </xsl:if>
                    <xsl:if test="not(@INSTANCE)">
                        <xsl:value-of select="$procInst_"/>:<xsl:value-of select="$addr_id_"/>
                    </xsl:if>
                </xsl:variable>
                
                <xsl:variable name="procAddrRowIdx_" select="position() - 1"/>
                <SET ID="{$set_id_}" CLASS="ADDRESS" ROW_INDEX="{$procAddrRowIdx_}">
                    
                    <xsl:if test="(@INSTANCE)">
                        <xsl:variable name="instance_"        select="@INSTANCE"/>
                        <xsl:variable name="subInstance_"     select="$G_SYS_MODS/MODULE[(@INSTANCE = $instance_)]"/>
                        
                        <xsl:variable name="inst_modtype_"    select="$subInstance_/@MODTYPE"/>
                        <xsl:variable name="inst_viewicon_"   select="$subInstance_/LICENSEINFO/@ICON_NAME"/>
                        <xsl:variable name="inst_hwversion_"  select="$subInstance_/@HWVERSION"/>
                        
                        <VARIABLE VIEWTYPE="STATIC" VIEWDISP="Instance"   NAME="INSTANCE"  VALUE="{$instance_}"/>
                        <VARIABLE VIEWTYPE="STATIC" VIEWDISP="IP Type"    NAME="MODTYPE"   VALUE="{$inst_modtype_}" VIEWICON="{$inst_viewicon_}"/>
                        <VARIABLE VIEWTYPE="STATIC" VIEWDISP="IP Version" NAME="HWVERSION" VALUE="{$inst_hwversion_}"/>
                    </xsl:if>
                    
                    <xsl:if test="not(@INSTANCE)">
                        <VARIABLE VIEWTYPE="STATIC" VIEWDISP="Instance"   NAME="INSTANCE"  VALUE="{$modInstance_/@INSTANCE}"/>
                        <VARIABLE VIEWTYPE="STATIC" VIEWDISP="IP Type"    NAME="MODTYPE"   VALUE="{$modInstance_/@MODTYPE}" VIEWICON="{$modInstance_/LICENSEINFO/@ICON_NAME}"/>
                        <VARIABLE VIEWTYPE="STATIC" VIEWDISP="IP Version" NAME="HWVERSION" VALUE="{$modInstance_/@HWVERSION}"/>
                    </xsl:if>

                    <VARIABLE VIEWTYPE="STATIC" VIEWDISP="Address Type" NAME="MEMTYPE" VALUE="{@MEMTYPE}"/>
                    
                    <xsl:variable name="instName_">
                        <xsl:choose>
                            <xsl:when test="@INSTANCE"><xsl:value-of select="@INSTANCE"/></xsl:when>
                            <xsl:otherwise>Connected<xsl:value-of select="$modInstance_/@INSTANCE"/></xsl:otherwise>
                        </xsl:choose>
                    </xsl:variable>
                    <!-- 
                    <xsl:message>INST : <xsl:value-of select="$set_id_"/></xsl:message>
                     -->    

                   <xsl:variable name="is_locked_">
                       <xsl:if test="@IS_LOCKED = 'TRUE'">TRUE</xsl:if>
                       <xsl:if test="not(@IS_LOCKED) or not(@IS_LOCKED = 'TRUE')">FALSE</xsl:if>
                   </xsl:variable>

                   <xsl:variable name="baseAddrViewType_">
                     <xsl:choose>
                       <xsl:when test="$is_locked_='TRUE'">STATIC</xsl:when>
                       <xsl:otherwise>TEXTBOX</xsl:otherwise>
                     </xsl:choose>
                   </xsl:variable>

                   <xsl:if test="(@SIZEABRV and not(@SIZEABRV = 'U'))">
                     <xsl:variable name="baseAddr_"><xsl:value-of select="translate(@BASEVALUE,&HEXU2L;)"/></xsl:variable>
                     <xsl:variable name="highAddr_"><xsl:value-of select="translate(@HIGHVALUE,&HEXU2L;)"/></xsl:variable>
                     <VARIABLE VIEWTYPE="{$baseAddrViewType_}"  VIEWDISP="Base Address" NAME="BASEVALUE" VALUE="{$baseAddr_}"/>
                     <VARIABLE VIEWTYPE="STATIC"   VIEWDISP="High Address" NAME="HIGHVALUE" VALUE="{$highAddr_}"/>

                     <xsl:if test="not(@MEMTYPE) or not(@MEMTYPE = 'BRIDGE')">
                       <VARIABLE VIEWTYPE="CHECKBOX" VIEWDISP="Lock" NAME="IS_LOCKED" VALUE="{$is_locked_}"/>
                     </xsl:if>

                     <xsl:if test="@MEMTYPE and (@MEMTYPE = 'BRIDGE') and not(@BRIDGE_TO)">
                       <VARIABLE VIEWTYPE="CHECKBOX" VIEWDISP="Lock" NAME="IS_LOCKED" VALUE="{$is_locked_}"/>
                     </xsl:if>

                   </xsl:if>
                    
                    <xsl:if test="(@SIZEABRV and (@SIZEABRV = 'U'))">
                      <VARIABLE VIEWTYPE="TEXTBOX" VIEWDISP="Base Address" NAME="BASEVALUE" VALUE=""/>
                    </xsl:if>
                   
                    <VARIABLE VIEWTYPE="STATIC"   VIEWDISP="Base Name"  NAME="BASENAME" VALUE="{@BASENAME}"/>

                   <xsl:variable name="sizeViewType_">
                     <xsl:choose>
                       <xsl:when test="(@SIZEABRV and (@SIZEABRV = 'U'))">DROPDOWN</xsl:when>
                       <xsl:when test="$is_locked_='TRUE'">STATIC</xsl:when>
                       <xsl:otherwise>DROPDOWN</xsl:otherwise>
                     </xsl:choose>
                   </xsl:variable>

                   <VARIABLE VIEWTYPE="{$sizeViewType_}" VIEWDISP="Size" NAME="SIZEABRV" VALUE="{@SIZEABRV}"/>

	                <xsl:variable name="modInst_"    select="$G_SYS_MODS/MODULE[(@INSTANCE = $instName_)]"/>
	                <xsl:variable name="modMemMap_"  select="$modInst_/MEMORYMAP"/>
	                
                    <xsl:variable name="valid_bifNames_">
                        <xsl:choose>
                            <xsl:when test="$modMemMap_/MEMRANGE[(@BASENAME = $baseName_) and (@HIGHNAME = $highName_)]/SLAVES">
		                        <xsl:for-each select="$modMemMap_/MEMRANGE[(@BASENAME = $baseName_) and (@HIGHNAME = $highName_)]/SLAVES/SLAVE">
		                            <xsl:variable name="bifName_"  select="@BUSINTERFACE"/>
                                     <!-- <xsl:message>Bif Name <xsl:value-of select="$bifName_"/> </xsl:message> -->
		                            <xsl:variable name="modBifs_"  select="$modInst_/BUSINTERFACES"/>
		                            <xsl:if test="$modBifs_/BUSINTERFACE[((@NAME = $bifName_) and not(@IS_VALID = 'FALSE') and not(@BUSNAME = '__NOC__'))]">
		                                <xsl:variable name="busName_" select="$modBifs_/BUSINTERFACE[((@NAME = $bifName_) and not(@IS_VALID = 'FALSE') and not(@BUSNAME = '__NOC__'))]/@BUSNAME"/>
		                                <xsl:if test="position() &gt; 1">:</xsl:if><xsl:value-of select="@BUSINTERFACE"/>
		                            </xsl:if>    
		                        </xsl:for-each>
                            </xsl:when>
                            <xsl:otherwise>
	                            <xsl:for-each select="$modMemMap_/MEMRANGE[(@BASENAME = $baseName_) and (@HIGHNAME = $highName_)]/SLVINTERFACES/BUSINTERFACE">
	                                <xsl:variable name="bifName_"  select="@NAME"/>
		                            <xsl:variable name="modBifs_"  select="$modInst_"/>
	                                <xsl:if test="$modBifs_/BUSINTERFACE[((@NAME = $bifName_) and not(@IS_VALID = 'FALSE') and not(@BUSNAME = '__NOC__'))]">
	                                    <xsl:variable name="busName_" select="$modBifs_/BUSINTERFACE[((@NAME = $bifName_) and not(@IS_VALID = 'FALSE') and not(@BUSNAME = '__NOC__'))]/@BUSNAME"/>
	                                    <xsl:if test="position() &gt; 1">:</xsl:if><xsl:value-of select="@NAME"/>
	                                </xsl:if>    
	                            </xsl:for-each>                       
                            </xsl:otherwise>
                        </xsl:choose>
                    </xsl:variable>
                    
                    <!-- 
	                <xsl:message>Module Instances <xsl:value-of select="$instName_"/> </xsl:message>
	                <xsl:message>Base Name <xsl:value-of select="$baseName_"/> </xsl:message>
	                <xsl:message>High Name <xsl:value-of select="$highName_"/> </xsl:message>
	                <xsl:message>Valid bif names <xsl:value-of select="$valid_bifNames_"/> </xsl:message>
	                -->
                    
                    
                <xsl:variable name="def_bifNames_">
                    <xsl:choose>
	                    <xsl:when test="string-length($valid_bifNames_) &lt; 1">
	                        <xsl:choose>
	                            <xsl:when test="$modClass_ = 'BUS'">Not Applicable</xsl:when>
	                            <xsl:otherwise>Not Connected</xsl:otherwise>
	                        </xsl:choose>
	                    </xsl:when>
	                    <xsl:when test="starts-with($valid_bifNames_,':')"><xsl:value-of select="substring-after($valid_bifNames_,':')"/></xsl:when>
	                    <xsl:otherwise><xsl:value-of select="$valid_bifNames_"/></xsl:otherwise>
                    </xsl:choose> 
                </xsl:variable>
                <VARIABLE VIEWTYPE="STATIC" VIEWDISP="Bus Interface(s)"  NAME="BIFNAMES" VALUE="{$def_bifNames_}"/>
                
                <xsl:choose>
                 <xsl:when test="$modMemMap_/MEMRANGE[(@BASENAME = $baseName_) and (@HIGHNAME = $highName_)]/SLAVES">
                     <xsl:for-each select="$modMemMap_/MEMRANGE[(@BASENAME = $baseName_) and (@HIGHNAME = $highName_)]/SLAVES/SLAVE">
                      <xsl:variable name="bifName_"  select="@BUSINTERFACE"/>
                         <xsl:variable name="modBifs_"  select="$modInst_/BUSINTERFACES"/>
                      <xsl:if test="$modBifs_/BUSINTERFACE[((@NAME = $bifName_) and not(@IS_VALID = 'FALSE') and not(@BUSNAME = '__NOC__'))]">
                          <xsl:variable name="busName_" select="$modBifs_/BUSINTERFACE[((@NAME = $bifName_) and not(@IS_VALID = 'FALSE') and not(@BUSNAME = '__NOC__'))]/@BUSNAME"/>
                          <xsl:variable name="numBifs_" select="count($modBifs_/BUSINTERFACE[((@NAME = $bifName_) and not(@IS_VALID = 'FALSE') and not(@BUSNAME = '__NOC__'))])"/>
                          <xsl:if test="((position() = 1) or ($numBifs_ = 1))">
                              <VARIABLE VIEWTYPE="STATIC" VIEWDISP="Bus Name" NAME="BUSNAME" VALUE="{$busName_}"/>
                          </xsl:if>
                      </xsl:if>    
                  </xsl:for-each>
                 </xsl:when>
                 <xsl:otherwise>
                        <xsl:for-each select="$modMemMap_/MEMRANGE[(@BASENAME = $baseName_) and (@HIGHNAME = $highName_)]/SLVINTERFACES/BUSINTERFACE">
                        <xsl:variable name="bifName_" select="@NAME"/>
                        <xsl:variable name="modBifs_" select="$modInst_"/>
                        <xsl:if test="$modBifs_/BUSINTERFACE[((@NAME = $bifName_) and not(@IS_VALID = 'FALSE') and not(@BUSNAME = '__NOC__'))]">
                            <xsl:variable name="busName_" select="$modBifs_/BUSINTERFACE[((@NAME = $bifName_) and not(@IS_VALID = 'FALSE') and not(@BUSNAME = '__NOC__'))]/@BUSNAME"/>
                            <xsl:variable name="numBifs_" select="count($modBifs_/BUSINTERFACE[((@NAME = $bifName_) and not(@IS_VALID = 'FALSE') and not(@BUSNAME = '__NOC__'))])"/>
                            <xsl:if test="((position() = 1) or ($numBifs_ = 1))">
                                <VARIABLE VIEWTYPE="STATIC" VIEWDISP="Bus Name" NAME="BUSNAME" VALUE="{$busName_}"/>
                            </xsl:if>
                        </xsl:if>    
                    </xsl:for-each>                   
                </xsl:otherwise>
            </xsl:choose>
<!-- 
 -->
            </SET>  <!--  End of one processor memory range row -->
            </xsl:for-each> <!-- end of processor memory ranges loop -->
        </SET>  
    </xsl:for-each> <!-- end of processor module address space loop -->
    
    <!-- 
        Add branch for valid address that are not part of a processor's 
        memory map. Usually modules that have just been added, but have 
        not been connected to a bus yet.
     -->
     
    <xsl:variable name="nonProcAddresses_">
    
        <!-- Add a dummy non proc as a place holder. Otherwise the exsl:node-set test
             Below complains if the variable is completely empty
        -->
        <NONPROCADDRESS INSTANCE="__DUMMY__" BASENAME="__DUMMY__" HIGHNAME="__DUMMY__" BASEDECIMAL="__DUMMY__"/>
         
        <xsl:for-each select="$G_SYS_MODS/MODULE[(not(@MODCLASS = 'PROCESSOR') and (MEMORYMAP/MEMRANGE[((not(@IS_VALID) or (@IS_VALID = 'TRUE')) and ACCESSROUTE)]))]">
            <xsl:variable name="nonProcInst_" select="@INSTANCE"/>
        
            <xsl:for-each select="MEMORYMAP/MEMRANGE[(not(@IS_VALID) or (@IS_VALID = 'TRUE'))]">
        
                <xsl:variable name="highName_"    select="@HIGHNAME"/>
                <xsl:variable name="baseName_"    select="@BASENAME"/>
                <xsl:variable name="baseDecimal_" select="@BASEDECIMAL"/>
            
                <xsl:if test="not($G_SYS_MODS/MODULE[(@MODCLASS = 'PROCESSOR')]/MEMORYMAP/MEMRANGE[((@INSTANCE = $nonProcInst_) and (@BASENAME = $baseName_) and (@HIGHNAME = $highName_))])">
                     <NONPROCADDRESS INSTANCE="{$nonProcInst_}" BASENAME="{$baseName_}" HIGHNAME="{$highName_}" BASEDECIMAL="{$baseDecimal_}"/>
                </xsl:if>
            </xsl:for-each>
        </xsl:for-each>
        
    </xsl:variable>

    <!--  Add unmapped addresses -->
    <xsl:variable name="hasUnMappedAddress">
        <xsl:for-each select="$G_SYS_MODS/MODULE[(not(@MODCLASS = 'PROCESSOR') and (MEMORYMAP/MEMRANGE[(not(@IS_VALID) or (@IS_VALID = 'TRUE'))]))]">
            <xsl:variable name="nonProcInst_" select="@INSTANCE"/>
            <xsl:for-each select="MEMORYMAP/MEMRANGE[(not(@IS_VALID) or (@IS_VALID = 'TRUE'))]">
                <xsl:variable name="highName_"    select="@HIGHNAME"/>
                <xsl:variable name="baseName_"    select="@BASENAME"/>
                <xsl:variable name="baseDecimal_" select="@BASEDECIMAL"/>
                <xsl:if test="not($G_SYS_MODS/MODULE[(@MODCLASS = 'PROCESSOR')]/MEMORYMAP/MEMRANGE[((@INSTANCE = $nonProcInst_) and (@BASENAME = $baseName_) and (@HIGHNAME = $highName_))])"><xsl:value-of select="$nonProcInst_"/></xsl:if>
            </xsl:for-each>
        </xsl:for-each>
    </xsl:variable>

    <xsl:if test="string-length($hasUnMappedAddress) &gt; 1">
    
        <SET ID="Unmapped Addresses" CLASS="MODULE" ROW_INDEX="{$G_NUM_OF_PROCS_W_ADDRS}">
            
            <VARIABLE VIEWTYPE="STATIC" VIEWDISP="Instance" NAME="INSTANCE"  VALUE="Unmapped Addresses"/>
            
            <xsl:for-each select="$G_SYS_MODS/MODULE[(not(@MODCLASS = 'PROCESSOR') and (MEMORYMAP/MEMRANGE[(not(@IS_VALID) or (@IS_VALID = 'TRUE'))]))]/MEMORYMAP/MEMRANGE[(not(@IS_VALID) or (@IS_VALID = 'TRUE'))]"> 
            
                <xsl:variable name="nonProcMod_"  select="../.."/>
                <xsl:variable name="nonProcMMap_" select="$nonProcMod_/MEMORYMAP"/>
                <xsl:variable name="instance_"    select="$nonProcMod_/@INSTANCE"/>
                
                <xsl:variable name="row_index_"    select="position()"/>
                <xsl:variable name="instName_"     select="$nonProcMod_/@INSTANCE"/>
                <xsl:variable name="highName_"     select="@HIGHNAME"/>
                <xsl:variable name="baseName_"     select="@BASENAME"/>
                <xsl:variable name="baseDecimal_"  select="@BASEDECIMAL"/>
                
                <xsl:for-each select="$nonProcMMap_/MEMRANGE[((@BASENAME = $baseName_) and (@HIGHNAME = $highName_))]">
                    
                    <xsl:if test="not($G_SYS_MODS/MODULE[(@MODCLASS = 'PROCESSOR')]/MEMORYMAP/MEMRANGE[((@INSTANCE = $instName_) and (@BASENAME = $baseName_) and (@HIGHNAME = $highName_))])">
                    
                        <xsl:variable name="addr_id_"><xsl:value-of select="$baseName_"/>:<xsl:value-of select="$highName_"/></xsl:variable>
                        <xsl:variable name="set_id_"><xsl:value-of select="$instName_"/>:<xsl:value-of select="$addr_id_"/></xsl:variable>
                            
                        <xsl:variable name="inst_modtype_"    select="$nonProcMod_/@MODTYPE"/>
                        <xsl:variable name="inst_viewicon_"   select="$nonProcMod_/LICENSEINFO/@ICON_NAME"/>
                        <xsl:variable name="inst_modclass_"   select="$nonProcMod_/@MODCLASS"/>
                        <xsl:variable name="inst_hwversion_"  select="$nonProcMod_/@HWVERSION"/>
                            
                        <SET ID="{$set_id_}" CLASS="ADDRESS">
                                
                            <VARIABLE VIEWTYPE="STATIC" VIEWDISP="Instance"   NAME="INSTANCE"  VALUE="{$instance_}"/>
                            <VARIABLE VIEWTYPE="STATIC" VIEWDISP="IP Type"    NAME="MODTYPE"   VALUE="{$inst_modtype_}" VIEWICON="{$inst_viewicon_}"/>
                            <VARIABLE VIEWTYPE="STATIC" VIEWDISP="IP Version" NAME="HWVERSION" VALUE="{$inst_hwversion_}"/>
                            <VARIABLE VIEWTYPE="STATIC" VIEWDISP="Address Type" NAME="MEMTYPE" VALUE="{@MEMTYPE}"/>

                            <xsl:variable name="is_locked_">
                              <xsl:if test="@IS_LOCKED = 'TRUE'">TRUE</xsl:if>
                              <xsl:if test="not(@IS_LOCKED) or not(@IS_LOCKED = 'TRUE')">FALSE</xsl:if>
                            </xsl:variable>

                            <xsl:variable name="baseAddrViewType_">
                              <xsl:choose>
                                <xsl:when test="$is_locked_='TRUE'">STATIC</xsl:when>
                                <xsl:otherwise>TEXTBOX</xsl:otherwise>
                              </xsl:choose>
                            </xsl:variable>

                            <xsl:if test="(@SIZEABRV and not(@SIZEABRV = 'U'))">
                            
                                <xsl:variable name="baseAddr_"><xsl:value-of select="translate(@BASEVALUE,&HEXU2L;)"/></xsl:variable>
                                <xsl:variable name="highAddr_"><xsl:value-of select="translate(@HIGHVALUE,&HEXU2L;)"/></xsl:variable>
                                
                                <VARIABLE VIEWTYPE="{$baseAddrViewType_}"  VIEWDISP="Base Address" NAME="BASEVALUE" VALUE="{$baseAddr_}"/>
                                <VARIABLE VIEWTYPE="STATIC"   VIEWDISP="High Address" NAME="HIGHVALUE" VALUE="{$highAddr_}"/>

                                <xsl:if test="not(@MEMTYPE) or not(@MEMTYPE = 'BRIDGE')">
                                  <VARIABLE VIEWTYPE="CHECKBOX" VIEWDISP="Lock" NAME="IS_LOCKED" VALUE="{$is_locked_}"/>
                                </xsl:if>

                                <xsl:if test="@MEMTYPE and (@MEMTYPE = 'BRIDGE') and not(@BRIDGE_TO)">
                                  <VARIABLE VIEWTYPE="CHECKBOX" VIEWDISP="Lock" NAME="IS_LOCKED" VALUE="{$is_locked_}"/>
                                </xsl:if>

                            </xsl:if>
                                
                            <xsl:if test="(@SIZEABRV and (@SIZEABRV = 'U'))">
                                <VARIABLE VIEWTYPE="TEXTBOX" VIEWDISP="Base Address" NAME="BASEVALUE" VALUE=""/>
                            </xsl:if>

                                
            <!--
                                Lock, DCache and ICache removed in 11.1
                                
                                <xsl:if test="(@IS_CACHEABLE = 'TRUE')">
                                    
                                    <xsl:variable name="is_dcached_">
                                        <xsl:if test="(@IS_DCACHED = 'TRUE')">TRUE</xsl:if>
                                        <xsl:if test="(not(@IS_DCACHED) or not(@IS_DCACHED = 'TRUE'))">FALSE</xsl:if>
                                    </xsl:variable>
                                    
                                    <xsl:variable name="is_icached_">
                                        <xsl:if test="(@IS_ICACHED = 'TRUE')">TRUE</xsl:if>
                                        <xsl:if test="(not(@IS_ICACHED) or not(@IS_ICACHED = 'TRUE'))">FALSE</xsl:if>
                                    </xsl:variable>
                                    
                                    <VARIABLE VIEWTYPE="CHECKBOX" VIEWDISP="DCache" NAME="IS_DCACHED" VALUE="{$is_dcached_}"/>
                                    <VARIABLE VIEWTYPE="CHECKBOX" VIEWDISP="ICache" NAME="IS_ICACHED" VALUE="{$is_icached_}"/>
                                </xsl:if>
             -->                    
                                
		                    <VARIABLE VIEWTYPE="STATIC"   VIEWDISP="Base Name"  NAME="BASENAME" VALUE="{@BASENAME}"/>

                        <xsl:variable name="sizeViewType_">
                          <xsl:choose>
                            <xsl:when test="(@SIZEABRV and (@SIZEABRV = 'U'))">DROPDOWN</xsl:when>
                            <xsl:when test="$is_locked_='TRUE'">STATIC</xsl:when>
                            <xsl:otherwise>DROPDOWN</xsl:otherwise>
                          </xsl:choose>
                        </xsl:variable>

                        <VARIABLE VIEWTYPE="{$sizeViewType_}" VIEWDISP="Size" NAME="SIZEABRV" VALUE="{@SIZEABRV}"/>
	                    
                    <xsl:variable name="valid_bifNames_">
                        <xsl:choose>
                            <xsl:when test="$nonProcMMap_/MEMRANGE[(@BASENAME = $baseName_) and (@HIGHNAME = $highName_)]/SLAVES">
                                <xsl:for-each select="$nonProcMMap_/MEMRANGE[(@BASENAME = $baseName_) and (@HIGHNAME = $highName_)]/SLAVES/SLAVE">
                                    <xsl:variable name="bifName_"  select="@BUSINTERFACE"/>
                                     <!-- <xsl:message>Bif Name <xsl:value-of select="$bifName_"/> </xsl:message> -->
                                    <xsl:variable name="modBifs_"  select="$nonProcMod_/BUSINTERFACES"/>
                                    <xsl:if test="$modBifs_/BUSINTERFACE[((@NAME = $bifName_) and not(@IS_VALID = 'FALSE') and not(@BUSNAME = '__NOC__'))]">
                                        <xsl:variable name="busName_" select="$modBifs_/BUSINTERFACE[((@NAME = $bifName_) and not(@IS_VALID = 'FALSE') and not(@BUSNAME = '__NOC__'))]/@BUSNAME"/>
                                        <xsl:if test="position() &gt; 1">:</xsl:if><xsl:value-of select="@BUSINTERFACE"/>
                                    </xsl:if>    
                                </xsl:for-each>
                            </xsl:when>
                            <xsl:otherwise>
                                <xsl:for-each select="$nonProcMMap_/MEMRANGE[(@BASENAME = $baseName_) and (@HIGHNAME = $highName_)]/SLVINTERFACES/BUSINTERFACE">
                                    <xsl:variable name="bifName_"  select="@NAME"/>
                                    <xsl:variable name="modBifs_"  select="$nonProcMod_"/>
                                    <xsl:if test="$modBifs_/BUSINTERFACE[((@NAME = $bifName_) and not(@IS_VALID = 'FALSE') and not(@BUSNAME = '__NOC__'))]">
                                        <xsl:variable name="busName_" select="$modBifs_/BUSINTERFACE[((@NAME = $bifName_) and not(@IS_VALID = 'FALSE') and not(@BUSNAME = '__NOC__'))]/@BUSNAME"/>
                                        <xsl:if test="position() &gt; 1">:</xsl:if><xsl:value-of select="@NAME"/>
                                    </xsl:if>    
                                </xsl:for-each>                       
                            </xsl:otherwise>
                        </xsl:choose>
                    </xsl:variable>		                    
                    
                     <xsl:variable name="def_bifNames_">
                        <xsl:choose>
                         <xsl:when test="(string-length($valid_bifNames_) &lt; 1) or ((string-length($valid_bifNames_) = 1) and ($valid_bifNames_ = ':'))">Not Connected</xsl:when>
	                    <xsl:when test="starts-with($valid_bifNames_,':')"><xsl:value-of select="substring-after($valid_bifNames_,':')"/></xsl:when>
	                    <xsl:otherwise><xsl:value-of select="$valid_bifNames_"/></xsl:otherwise>
                        </xsl:choose>
                     </xsl:variable>
                     
                     
                    <VARIABLE VIEWTYPE="STATIC" VIEWDISP="Bus Interface(s)"  NAME="BIFNAMES" VALUE="{$def_bifNames_}"/>
                            
	                <xsl:choose>
	                    <xsl:when test="$nonProcMMap_/MEMRANGE[(@BASENAME = $baseName_) and (@HIGHNAME = $highName_)]/SLAVES">
	                       <xsl:for-each select="$nonProcMMap_/MEMRANGE[(@BASENAME = $baseName_) and (@HIGHNAME = $highName_)]/SLAVES/SLAVE">
	                            <xsl:variable name="slvBifName_" select="@BUSINTERFACE"/>
	                            <xsl:variable name="modBifs_"    select="$nonProcMod_/BUSINTERFACES"/>
	                            <xsl:if test="count($modBifs_/BUSINTERFACE[((@NAME = $slvBifName_) and not(@IS_VALID = 'FALSE') and not(@BUSNAME = '__NOC__'))]) = 1">
	                                <xsl:variable name="slvBusName_" select="$modBifs_/BUSINTERFACE[((@NAME = $slvBifName_) and not(@IS_VALID = 'FALSE') and not(@BUSNAME = '__NOC__'))]/@BUSNAME"/>
	                                <VARIABLE VIEWTYPE="STATIC" VIEWDISP="Bus Name" NAME="BUSNAME" VALUE="{$slvBusName_}"/>
	                            </xsl:if>    
	                        </xsl:for-each>
	                    </xsl:when>
	                    <xsl:otherwise>
	                        <xsl:for-each select="$nonProcMMap_/MEMRANGE[(@BASENAME = $baseName_) and (@HIGHNAME = $highName_)]/SLVINTERFACES/BUSINTERFACE">
	                            <xsl:variable name="slvBifName_" select="@NAME"/>
	                            <xsl:variable name="modBifs_"    select="$nonProcMod_"/>
	                            <xsl:if test="count($modBifs_/BUSINTERFACE[((@NAME = $slvBifName_) and not(@IS_VALID = 'FALSE') and not(@BUSNAME = '__NOC__'))]) = 1">
	                                <xsl:variable name="slvBusName_" select="$modBifs_/BUSINTERFACE[((@NAME = $slvBifName_) and not(@IS_VALID = 'FALSE') and not(@BUSNAME = '__NOC__'))]/@BUSNAME"/>
	                                <VARIABLE VIEWTYPE="STATIC" VIEWDISP="Bus Name" NAME="BUSNAME" VALUE="{$slvBusName_}"/>
	                            </xsl:if>    
	                        </xsl:for-each>
	                    </xsl:otherwise>
	                </xsl:choose>
                            
                            
                </SET>  <!--  End of one non processor memory range row -->
            </xsl:if>   
                        
                </xsl:for-each> <!-- end of non processor memory ranges loop -->
            
            </xsl:for-each> <!--  end of NONPROCADDRESS loop -->
        
        </SET> <!--  End of non processor tree branch -->
        
    </xsl:if> <!--  End of test to see if we have and non processor mapped address -->

</xsl:template> 

</xsl:stylesheet>

