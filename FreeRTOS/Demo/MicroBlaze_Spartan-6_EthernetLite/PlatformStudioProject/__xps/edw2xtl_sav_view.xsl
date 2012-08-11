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
      extension-element-prefixes="math exsl dyn xlink">
           
<xsl:include href="edw2xtl_sav_globals.xsl"/>

<xsl:include href="edw2xtl_sav_view_addr.xsl"/>
<xsl:include href="edw2xtl_sav_view_busif.xsl"/>
<xsl:include href="edw2xtl_sav_view_port.xsl"/>
<xsl:include href="edw2xtl_sav_view_groups.xsl"/>

<xsl:output method="xml" version="1.0" encoding="UTF-8" indent="yes"/>

<xsl:param name="P_SYSTEM_XML" select= "'__UNDEF__'"/>
<xsl:param name="P_GROUPS_XML" select= "'__UNDEF__'"/>

<xsl:param name="G_DEBUG"       select="'FALSE'"/>
<xsl:param name="G_ADD_CHOICES" select="'TRUE'"/>

<!-- 
<xsl:param name="P_VIEW"  	   select="'__UNDEF__'"/>
<xsl:param name="P_MODE"  	   select="'__UNDEF__'"/>
<xsl:param name="P_SCOPE"  	   select="'__UNDEF__'"/>
-->



<!--  MAIN TEMPLATE -->
 
<xsl:template match="SAV[@VIEW]">
    <xsl:if test="$G_DEBUG='TRUE'">
        <xsl:message>SAV VIEW <xsl:value-of select="@VIEW"/></xsl:message>
        <xsl:message>SAV MODE <xsl:value-of select="@MODE"/></xsl:message>
        <xsl:message>SAV SCOPE <xsl:value-of select="@SCOPE"/></xsl:message>
    </xsl:if>
    
    <xsl:choose>
    	<xsl:when test="not(@VIEW = 'PORT') and not(@VIEW = 'BUSINTERFACE') and not(@VIEW = 'ADDRESS')">
    	   <xsl:message>EDW2SAV XTELLER ERROR: UNDEFINED VIEW <xsl:value-of select="@VIEW"/></xsl:message>	
    	</xsl:when>
    	
    	<xsl:when test="(@MODE and not(@MODE = 'FLAT') and not(@MODE = 'TREE') and not(@MODE = 'GROUPS'))">
    	   <xsl:message>EDW2SAV XTELLER ERROR: UNDEFINED MODE <xsl:value-of select="@MODE"/></xsl:message>	
    	</xsl:when>    	
    	
    	<xsl:when test="(@SCOPE and not(@SCOPE = 'FULL') and not(@SCOPE= 'FOCUS'))">
    	   <xsl:message>EDW2SAV XTELLER ERROR: UNDEFINED SCOPE <xsl:value-of select="@SCOPE"/></xsl:message>	
    	</xsl:when>      	
    	
    	<xsl:when test="$P_SYSTEM_XML ='__UNDEF__'">
    	   <xsl:message>EDW2SAV XTELLER ERROR: SYSTEM XML UNDEFINED</xsl:message>	
    	</xsl:when>
    	
      	<xsl:when test="not($G_SYS)" >
    	   <xsl:message>EDW2SAV XTELLER ERROR: EDKSYSTEM MISSING in SYSTEM XML <xsl:value-of select="$P_SYSTEM_XML"/></xsl:message>	
       	</xsl:when>
    	    	
       	<xsl:when test="($P_GROUPS_XML ='__UNDEF__') and (@MODE = 'GROUPS')" >
    	   <xsl:message>EDW2SAV XTELLER ERROR: GROUP XML UNDEFINED for FOCUS</xsl:message>	
    	</xsl:when>
    	
       	<xsl:when test="($P_GROUPS_XML ='__UNDEF__') and (@SCOPE = 'FOCUS') and (@VIEW = 'BUSINTERFACE')" >
    	   <xsl:message>EDW2SAV XTELLER ERROR: GROUP XML UNDEFINED for SCOPE</xsl:message>	
    	</xsl:when>
    	
    	<xsl:otherwise>
    	
	    	<xsl:if test="$G_DEBUG='TRUE'">
	   			<xsl:message>SYSTEM XML <xsl:value-of select="$P_SYSTEM_XML"/></xsl:message>
	   			<xsl:message>GROUPS XML <xsl:value-of select="$P_GROUPS_XML"/></xsl:message>
	   		</xsl:if>
	   		
	   		<xsl:variable name="use_mode_">
				<xsl:choose>
				<xsl:when test="@MODE = 'GROUPS'">TREE</xsl:when>
				<xsl:otherwise><xsl:value-of select="@MODE"/></xsl:otherwise>
				</xsl:choose>
	   		</xsl:variable>
	   		
	   		<xsl:variable name="num_procs_focused_on_" select="count(MASTER)"/>
	   		<xsl:variable name="num_buses_focused_on_" select="count(BUS)"/>
	   		
	   		<xsl:element name="SET">
		        <xsl:attribute name="CLASS">PROJECT</xsl:attribute>
		        <xsl:attribute name="VIEW_ID"><xsl:value-of select="@VIEW"/></xsl:attribute>
		        <xsl:attribute name="DISPLAYMODE"><xsl:value-of select="$use_mode_"/></xsl:attribute>
		        
				<xsl:choose>
				
					<!-- ADDRESS TAB VIEW -->
					<xsl:when test="(@VIEW = 'ADDRESS')">
						<xsl:call-template name="WRITE_VIEW_ADDRESS"/>
					</xsl:when>	
				
					<!-- BIF TAB VIEWS -->
					<xsl:when test="((@VIEW ='BUSINTERFACE') and (@SCOPE = 'FOCUS') and ($num_procs_focused_on_ &gt; 0))">
						<xsl:call-template name="WRITE_VIEW_BIF_FOCUS_ON_PROCS"/>
					</xsl:when>
					
					<!-- BIF TAB VIEWS -->
					<xsl:when test="((@VIEW ='BUSINTERFACE') and (@SCOPE = 'FOCUS') and ($num_buses_focused_on_ &gt; 0))">
						<xsl:call-template name="WRITE_VIEW_BIF_FOCUS_ON_BUSES"/>
					</xsl:when>					
					
					<xsl:when test="((@VIEW ='BUSINTERFACE') and (@MODE = 'TREE') and not(@SCOPE))">
						<xsl:call-template name="WRITE_VIEW_BIF_TREE"/>
					</xsl:when>
					
					<xsl:when test="((@VIEW = 'BUSINTERFACE') and (@MODE = 'FLAT') and not(@SCOPE))">
						<xsl:call-template name="WRITE_VIEW_BIF_FLAT"/>
					</xsl:when>
					
					<xsl:when test="((@VIEW = 'BUSINTERFACE') and (@MODE = 'GROUPS'))">
						<xsl:call-template name="WRITE_VIEW_BIF_GROUPS">
							<xsl:with-param name="iModules" select="$G_BLOCKS"/>
						</xsl:call-template>
					</xsl:when>
					
					
					<!-- PORT TAB VIEWS -->
					<xsl:when test="((@VIEW ='PORT') and (@SCOPE = 'FOCUS'))">
						<xsl:call-template name="WRITE_VIEW_PORT_FOCUSED"/>
					</xsl:when>					
										
					<!-- Generate XTeller panel data for Ports using hierarchy -->
					<xsl:when test="((@VIEW = 'PORT') and (@MODE = 'TREE'))">
						<xsl:call-template name="WRITE_VIEW_PORT_TREE"/>
					</xsl:when>
					
					<!-- Generate XTeller panel data for Ports without hierarchy, (flat view) -->
					<xsl:when test="((@VIEW='PORT') and (@MODE = 'FLAT'))">
						<xsl:call-template name="WRITE_VIEW_PORT_FLAT"/>
					</xsl:when>
					
					
					<xsl:otherwise>
						<xsl:message>ERROR during SAV XTeller generation with panel <xsl:value-of select="@VIEW"/> and display mode <xsl:value-of select="@MODE"/></xsl:message>
					</xsl:otherwise>		        
				
				</xsl:choose>
			</xsl:element>
    	</xsl:otherwise>
    </xsl:choose>
</xsl:template>
 
<xsl:template match="EDKSYSTEM">

<!-- 
    <xsl:message>EDW VERSION <xsl:value-of select="$G_EDWVER"/></xsl:message>
    <xsl:message>VIEW     <xsl:value-of select="$VIEW"/></xsl:message>
    <xsl:message>MODE <xsl:value-of select="$MODE"/></xsl:message>
-->    

	<xsl:variable name="by_interface_">
		<xsl:choose>
		<!--  
			Show interfaces or not
		-->	
			<xsl:when test="(($SHOW_BUSIF ='TRUE') or ($SHOW_IOIF ='TRUE'))">TRUE</xsl:when>
			<xsl:otherwise>FALSE</xsl:otherwise>
		</xsl:choose>
	</xsl:variable>
	
    <!--  
    <xsl:message>VIEW <xsl:value-of select="$VIEW"/></xsl:message>
    <xsl:message>MODE <xsl:value-of select="$MODE"/></xsl:message>
    <xsl:message>BY INTERFACE <xsl:value-of select="$by_interface_"/></xsl:message>
    -->
	<xsl:variable name="displayMode_">
		<xsl:choose>
		<!--  
			  Hard code view to view for address panel, 
			  always show view in what was formerly 
			  multiprocessor view. See below.
			  
			<xsl:when test="(($G_NUM_OF_PROCS &gt;  1) and ($VIEW='ADDRESS'))">TREE</xsl:when>
			<xsl:when test="(($G_NUM_OF_PROCS &lt;= 1) and ($VIEW='ADDRESS'))">FLAT</xsl:when>
		-->	
			<xsl:when test="($VIEW='ADDRESS')">TREE</xsl:when>
			<xsl:otherwise><xsl:value-of select="$MODE"/></xsl:otherwise>
		</xsl:choose>	
	</xsl:variable>	
	
	<SET CLASS="PROJECT" VIEW= "{$VIEW}" MODE="{$displayMode_}">
		<xsl:choose>
		
			<!-- Generate XTeller panel data for Bus Interfaces using hierarchy -->
			<xsl:when test="(($VIEW='BUSINTERFACE') and (not($MODE) or ($MODE = 'TREE')))">
				<xsl:call-template name="WRITE_VIEW_BIF_TREE"/>
			</xsl:when>
		
			<!-- Generate XTeller panel data for Bus Interfaces without hierarchy, (flat view) -->
			<xsl:when test="(($VIEW='BUSINTERFACE') and ($MODE = 'FLAT'))">
				<xsl:call-template name="WRITE_VIEW_BIF_FLAT"/>
			</xsl:when>
			
			<!-- Generate XTeller panel data for Ports using hierarchy -->
			<xsl:when test="(($VIEW='PORT') and (not($MODE) or ($MODE = 'TREE')))">
				<xsl:call-template name="WRITE_VIEW_PORT_TREE"/>
			</xsl:when>
			
			<!-- Generate XTeller panel data for Ports without hierarchy, (flat view) -->
			<xsl:when test="(($VIEW='PORT') and ($MODE = 'FLAT'))">
				<xsl:call-template name="WRITE_VIEW_PORT_FLAT"/>
			</xsl:when>
			
			<!--
				Hard code display of the address panel to always the the same.
				No more tree or flat mode, always show address panel 
				in what was formerly the multiprocessor view.  
			-->
			<xsl:when test="($VIEW='ADDRESS')">
				<xsl:call-template name="WRITE_VIEW_ADDRESS"/>
			</xsl:when>	
			
			<xsl:otherwise>
				<xsl:message>ERROR during SAV XTeller generation with panel <xsl:value-of select="$VIEW"/> and display mode <xsl:value-of select="$MODE"/></xsl:message>
			</xsl:otherwise>
			
		</xsl:choose>
	</SET>
	
</xsl:template>	

</xsl:stylesheet>

