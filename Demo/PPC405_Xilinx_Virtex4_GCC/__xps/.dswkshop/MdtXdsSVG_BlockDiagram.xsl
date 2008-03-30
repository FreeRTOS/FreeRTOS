<?xml version="1.0" standalone="no"?>
<xsl:stylesheet version="1.0"
           xmlns:svg="http://www.w3.org/2000/svg"
           xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
           xmlns:exsl="http://exslt.org/common"
           xmlns:math="http://exslt.org/math"
 	       xmlns:xlink="http://www.w3.org/1999/xlink"
           extension-element-prefixes="math">
		   
<xsl:include href="MdtXdsSVG_Colors.xsl"/>

<xsl:include href="MdtXdsSVG_BlkDBifDefs.xsl"/>
<xsl:include href="MdtXdsSVG_BlkdBusses.xsl"/>
<xsl:include href="MdtXdsSVG_BlkdIOPorts.xsl"/>
<xsl:include href="MdtXdsSVG_BlkdProcessors.xsl"/>
<xsl:include href="MdtXdsSVG_BlkDDimensions.xsl"/>
<xsl:include href="MdtXdsSVG_BlkDModuleDefs.xsl"/>
<xsl:include href="MdtXdsSVG_BlkDPeripherals.xsl"/>
<xsl:include href="MdtXdsSVG_BlkDCalculations.xsl"/>
<xsl:include href="MdtXdsSVG_BlkDBusLaneSpaces.xsl"/>
	
<xsl:output method="xml" version="1.0" encoding="UTF-8" indent="yes"
	       doctype-public="-//W3C//DTD SVG 1.0//EN"
		   doctype-system="svg10.dtd"/>
	
<xsl:param    name="ADD_VIEWBOX"        select="'FALSE'"/>		   
<xsl:param    name="CSS_RENDER"         select="'MdtXdsSVG_Render.css'"/>
<xsl:param    name="IN_TESTMODE"        select="'FALSE'"/>
		
	
<!-- ======================= MAIN SVG BLOCK =============================== -->
<xsl:template match="EDKSYSTEM">

<!-- ===========================================================================
    Calculate the width of the Block Diagram based on the total number of      
    buslanes and modules in the design. If there are no buslanes or modules,
	a default width, just wide enough to display the KEY and SPECS is used
   =========================================================================== -->
	
<xsl:variable name="totalStacksW_">
	<xsl:call-template name="_calc_Stack_X">
		<xsl:with-param name="stackIdx"     select="(BLKDSHAPES/@STACK_HORIZ_WIDTH)"/>
	</xsl:call-template>
</xsl:variable>
	
<xsl:variable name="numBridges_"        select="count(BLKDSHAPES/BRIDGESHAPES/MODULE)"/>
<xsl:variable name="totalBridgesW_"     select="(($numBridges_ * ($periMOD_W + ($BUS_LANE_W * 2))) + $BRIDGE_GAP)"/>
<xsl:variable name="BLKD_DRAWAREA_CLC"  select="$totalStacksW_ + $totalBridgesW_ + ($BLKD_INNER_GAP * 2)"/>
	

<xsl:variable name="BLKD_DRAWAREA_W">
	<xsl:if test="$BLKD_DRAWAREA_CLC &gt; ($BLKD_KEY_W + $BLKD_SPECS_W + $SPECS2KEY_GAP)">
		<xsl:value-of select="$BLKD_DRAWAREA_CLC"/>
	</xsl:if>
	<xsl:if test="not($BLKD_DRAWAREA_CLC &gt; ($BLKD_KEY_W + $BLKD_SPECS_W + $SPECS2KEY_GAP))">
		<xsl:value-of select="($BLKD_KEY_W + $BLKD_SPECS_W + $SPECS2KEY_GAP)"/>
	</xsl:if>
</xsl:variable>
<xsl:variable name="BLKD_W"             select="($BLKD_DRAWAREA_W + (($BLKD_PRTCHAN_W  + $BLKD_IORCHAN_W)* 2))"/>

<!-- =========================================================================== -->
<!-- Calculate the height of the Block Diagram based on the total number of      -->
<!-- buslanes and modules in the design. Take into account special shapes such   -->
<!-- as MultiProc shapes.													     -->
<!-- =========================================================================== -->
	
<xsl:variable name="max_Stack_BlwSbs_H_">
	<xsl:call-template name="_calc_Max_Stack_BlwSbs_Height"/>
</xsl:variable>

<xsl:variable name="max_Stack_AbvSbs_H_">
	<xsl:call-template name="_calc_Max_Stack_AbvSbs_Height"/>
</xsl:variable>
	

<xsl:variable name="numSbs_"            select="count(BLKDSHAPES/SBSSHAPES/MODULE)"/>
<xsl:variable name="totalSbs_H_"        select="($numSbs_ * $SBS_LANE_H)"/>

<xsl:variable name="IpBktMods_H_">
	<xsl:if test="BLKDSHAPES/IPBUCKET/@MODS_H"><xsl:value-of select="BLKDSHAPES/IPBUCKET/@MODS_H"/></xsl:if>
	<xsl:if test="not(BLKDSHAPES/IPBUCKET/@MODS_H)">0</xsl:if>
</xsl:variable>
<xsl:variable name="totalIpBkt_H_"       select="($IpBktMods_H_ * ($periMOD_H + $BIF_H))"/>

	
<xsl:variable name="totalUnkBkt_H_">
	<xsl:if test="BLKDSHAPES/UNKBUCKET">
	
		<xsl:variable name="UnkBktModsH_">
			<xsl:if test="BLKDSHAPES/UNKBUCKET/@MODS_H"><xsl:value-of select="BLKDSHAPES/UNKBUCKET/@MODS_H"/></xsl:if>
			<xsl:if test="not(BLKDSHAPES/UNKBUCKET/@MODS_H)">0</xsl:if>
		</xsl:variable>
		<xsl:variable name="totalUnkModH_"       select="($UnkBktModsH_ * ($periMOD_H + $BIF_H))"/>
		
		<xsl:variable name="UnkBktBifsH_">
			<xsl:if test="BLKDSHAPES/UNKBUCKET/@BIFS_H"><xsl:value-of select="BLKDSHAPES/UNKBUCKET/@BIFS_H"/></xsl:if>
			<xsl:if test="not(BLKDSHAPES/UNKBUCKET/@BIFS_H)">0</xsl:if>
		</xsl:variable>
		<xsl:variable name="totalUnkBifH_"       select="($UnkBktBifsH_ * ($periMOD_H + $BIF_H))"/>
		
		<xsl:value-of select="($totalUnkBifH_ + $totalUnkModH_)"/>	
	</xsl:if>
	
	<xsl:if test="not(BLKDSHAPES/UNKBUCKET)">0</xsl:if>
</xsl:variable>

<xsl:variable name="BLKD_DRAWAREA_H"    select="($max_Stack_AbvSbs_H_ + $PROC2SBS_GAP + $totalSbs_H_ + $max_Stack_BlwSbs_H_ + $SBS2IP_GAP + $totalIpBkt_H_ + $IP2UNK_GAP + $totalUnkBkt_H_ + ($BLKD_INNER_GAP * 2))"/>
<xsl:variable name="BLKD_H"             select="($BLKD_DRAWAREA_H + (($BLKD_PRTCHAN_H  + $BLKD_IORCHAN_H)* 2))"/>
	
<!--	
<xsl:variable name="BLKD_TOTAL_H"       select="($BLKD_H + $BLKD2KEY_GAP + $BLKD_KEY_H)"/>
-->	
<xsl:variable name="BLKD_TOTAL_H">
	<xsl:if test="($IN_TESTMODE = 'TRUE')">
		<xsl:message>Generating Blkdiagram in TestMode </xsl:message>
       <xsl:value-of select="$BLKD_H"/>
	</xsl:if>
	<xsl:if test="(not($IN_TESTMODE) or ($IN_TESTMODE = 'FALSE'))">
       <xsl:value-of select="($BLKD_H + $BLKD2KEY_GAP + $BLKD_KEY_H)"/>
	</xsl:if>
</xsl:variable>
	
	
	
<!--
<xsl:message>Found Blkd Total as <xsl:value-of select="$BLKD_TOTAL_H"/></xsl:message>
<xsl:message>Found max abv as <xsl:value-of select="$max_Stack_AbvSbs_H_"/></xsl:message>
<xsl:message>Found max blw as <xsl:value-of select="$max_Stack_BlwSbs_H_"/></xsl:message>
<xsl:message>Found Blkd DrawArea height as <xsl:value-of select="$BLKD_DRAWAREA_H"/></xsl:message>
<xsl:message>Found Ip Bkt as <xsl:value-of select="$totalIpBkt_H_"/></xsl:message>
<xsl:message>Found Sbs as <xsl:value-of select="$totalSbs_H_"/></xsl:message>
<xsl:message>Found Unk Bkt as <xsl:value-of select="$totalUnkBkt_H_"/></xsl:message>
-->


<!--specify a css for the file -->
<xsl:processing-instruction name="xml-stylesheet">href="<xsl:value-of select="$CSS_RENDER"/>" type="text/css"</xsl:processing-instruction>
	
<xsl:variable name="BLKD_ZOOM_Y">
	<xsl:choose>
		<xsl:when test="($ADD_VIEWBOX = 'TRUE')">
				<xsl:value-of select="($BLKD_TOTAL_H * 2)"/>
		</xsl:when>
		<xsl:otherwise>0</xsl:otherwise>		
	</xsl:choose>
</xsl:variable>
	
<xsl:text>&#10;</xsl:text>
<svg width="{$BLKD_W}" height="{$BLKD_TOTAL_H}" viewBox="0 0 0 {$BLKD_ZOOM_Y}">	
<!-- =============================================== -->
<!--        Layout All the various definitions       -->
<!-- =============================================== -->
	<defs>
		<!-- Diagram Key Definition -->
		<xsl:call-template name="Define_BlkDiagram_Key"/>		
		
		<!-- Diagram Specs Definition -->
		<xsl:call-template name="Define_BlkDiagram_Specs">		
			<xsl:with-param name="blkd_arch"     select="@ARCH"/>
			<xsl:with-param name="blkd_part"     select="@PART"/>
			<xsl:with-param name="blkd_edkver"   select="@EDKVERSION"/>
			<xsl:with-param name="blkd_gentime"  select="@TIMESTAMP"/>
		</xsl:call-template>		
		
		<!-- IO Port Defs -->
		<xsl:call-template name="Define_IOPorts">		
			<xsl:with-param name="drawarea_w" select="$BLKD_DRAWAREA_W"/>
			<xsl:with-param name="drawarea_h" select="$BLKD_DRAWAREA_H"/>
		</xsl:call-template>	
		
		<!-- BIF Defs -->
		<xsl:call-template name="Define_BifTypes"/>		
		
		<!-- Bus Defs -->
		<xsl:call-template name="Define_Busses">		
			<xsl:with-param name="drawarea_w" select="$BLKD_DRAWAREA_W"/>
			<xsl:with-param name="drawarea_h" select="$BLKD_DRAWAREA_H"/>
		</xsl:call-template>	
		
		<!-- Shared Bus Buckets Defs -->
		<xsl:call-template name="Define_SBSBuckets"/>		
		
		<!-- IP Bucket Defs -->
		<xsl:call-template name="Define_IPBucket"/>		
		
		<!-- Stack Defs -->
		<xsl:call-template name="Define_AllStacks"/>		
		
		<!-- Space Defs -->
		<xsl:call-template name="Define_BusLaneSpaces"/>		
		
		<!-- Ext port Defs -->
<!--		
		<xsl:call-template name="Define_ExtPortsTable"/>		
-->	
			
			
	</defs>
	
<!-- =============================================== -->
<!--             Draw Outlines                       -->
<!-- =============================================== -->
	
	 <!-- The surrounding black liner -->
     <rect x="0"  
		   y="0" 
		   width ="{$BLKD_W}"
		   height="{$BLKD_TOTAL_H}" style="fill:{$COL_WHITE}; stroke:{$COL_BLACK};stroke-width:4"/>
		   
	 <!-- The outer IO channel -->
     <rect x="{$BLKD_PRTCHAN_W}"  
		   y="{$BLKD_PRTCHAN_H}" 
		   width= "{$BLKD_W - ($BLKD_PRTCHAN_W * 2)}" 
		   height="{$BLKD_H - ($BLKD_PRTCHAN_H * 2)}" style="fill:{$COL_IORING}"/>
		   
	 <!-- The Diagram's drawing area -->
     <rect x="{$BLKD_PRTCHAN_W + $BLKD_IORCHAN_W}"  
		   y="{$BLKD_PRTCHAN_H + $BLKD_IORCHAN_H}" 
		   width= "{$BLKD_DRAWAREA_W}"
		   height="{$BLKD_DRAWAREA_H}" rx="8" ry="8" style="fill:{$COL_BG}"/>
		   
<!-- =============================================== -->
<!--        Draw All the various components          -->
<!-- =============================================== -->
	
	<!--   Layout the IO Ports    -->	
	<xsl:if test="(not($IN_TESTMODE) or ($IN_TESTMODE = 'FALSE'))">
		<xsl:call-template name="Draw_IOPorts">		
			<xsl:with-param name="drawarea_w" select="$BLKD_DRAWAREA_W"/>
			<xsl:with-param name="drawarea_h" select="$BLKD_DRAWAREA_H"/>
		</xsl:call-template>	
	</xsl:if>
	
	<!--   Layout the Shapes      -->	
	<xsl:call-template name="Draw_BlkDiagram_Shapes">		
		<xsl:with-param name="blkd_w"     select="$BLKD_W"/>
		<xsl:with-param name="blkd_h"     select="$BLKD_H"/>
		<xsl:with-param name="drawarea_w" select="$BLKD_DRAWAREA_W"/>
		<xsl:with-param name="drawarea_h" select="$BLKD_DRAWAREA_H"/>
	</xsl:call-template>	
	
	
</svg>

<!-- ======================= END MAIN SVG BLOCK =============================== -->
</xsl:template>
	
<xsl:template name="Draw_BlkDiagram_Shapes">
	<xsl:param name="blkd_w"     select="820"/>
	<xsl:param name="blkd_h"     select="520"/>
	<xsl:param name="drawarea_w" select="800"/>
	<xsl:param name="drawarea_h" select="500"/>
	
	
	<xsl:variable name="max_Stack_AbvSbs_H_">
		<xsl:call-template name="_calc_Max_Stack_AbvSbs_Height"/>
	</xsl:variable>
	
	<xsl:variable name="max_Stack_BlwSbs_H_">
		<xsl:call-template name="_calc_Max_Stack_BlwSbs_Height"/>
	</xsl:variable>
	
	<xsl:variable name="numSbs_"    select="count(/EDKSYSTEM/BLKDSHAPES/SBSSHAPES/MODULE)"/>
	<xsl:variable name="sbs_h_"     select="($numSbs_  * $SBS_LANE_H)"/>
	<xsl:variable name="sbs_y_"     select="($BLKD_INNER_Y + $max_Stack_AbvSbs_H_ + $PROC2SBS_GAP)"/>
	
	<!-- 
		 ===========================================================
	 					Draw the shared busses 
		 ===========================================================
	-->
	<use   x="{$BLKD_INNER_Y}"    y="{$sbs_y_ + $PROC2SBS_GAP}"  xlink:href="#group_sharedBusses"/> 
	
	
	<!-- 
		 ===========================================================
	 					Draw the Bus Lane Spaces 
		 ===========================================================
	-->
	<xsl:call-template name="Draw_BlkDiagram_BusLaneSpaces">
		<xsl:with-param name="sbs_Y"  select="$sbs_y_"/>
	</xsl:call-template>	
	
	<!-- 
		 ===========================================================
	 					Draw the Bridges
		 ===========================================================
	-->
	<xsl:call-template name="Draw_BlkDiagram_Bridges">
		<xsl:with-param name="sbs_Y"    select="$sbs_y_"/>
		<xsl:with-param name="inner_X"  select="$BLKD_INNER_Y"/>
	</xsl:call-template>	
	
	
	<!-- 
		 ===========================================================
	 					Draw the Stacks
		 ===========================================================
	-->
	<xsl:call-template name="Draw_BlkDiagram_Stacks">
		<xsl:with-param name="sbs_Y"  select="$sbs_y_"/>
	</xsl:call-template>	
	
	
	<!-- 
		 ===========================================================
	 					Draw the Ip Bucket
		 ===========================================================
	-->
	
	<xsl:call-template name="Draw_BlkDiagram_IPBucket">
		<xsl:with-param name="blkd_W"               select="$blkd_w"/>
		<xsl:with-param name="sbs_Y"  		   		select="$sbs_y_"/>
		<xsl:with-param name="sbs_H"  		   		select="$sbs_h_"/>
	    <xsl:with-param name="max_Stack_AbvSbs_H"   select="$max_Stack_AbvSbs_H_"/>
	    <xsl:with-param name="max_Stack_BlwSbs_H"  	select="$max_Stack_BlwSbs_H_"/>
	</xsl:call-template>	
	
	<!-- 
		 ===========================================================
	 					Draw the shared busses 
		 ===========================================================
	<use   x="{$BLKD_INNER_Y}"    y="{$sbs_y_ + $PROC2SBS_GAP}"  xlink:href="#group_sharedBusses"/> 
	-->
	
	<!-- 
		 ===========================================================
	 					Draw the Key
		 ===========================================================
	-->
	<xsl:if test="(not($IN_TESTMODE) or ($IN_TESTMODE = 'FALSE'))">
		<use   x="{$blkd_w - $BLKD_KEY_W - $BLKD_PRTCHAN_W}"   y="{$blkd_h + $BLKD2KEY_GAP - 8}"  xlink:href="#BlkDiagram_Key"/> 
	</xsl:if>
	
	<!-- 
		 ===========================================================
	 					Draw the Specs
		 ===========================================================
	-->
	<xsl:if test="(not($IN_TESTMODE) or ($IN_TESTMODE = 'FALSE'))">
		<use   x="{$BLKD_PRTCHAN_W}"                           y="{$blkd_h + $BLKD2KEY_GAP - 8}"  xlink:href="#BlkDiagram_Specs"/> 
	</xsl:if>
	
	<!-- 
		************************************************************ 
		***************  DONE DRAWING BLOCK DIAGRAM   ************** 
		************************************************************ 
	-->	
	
</xsl:template>	
	
	
<!-- ======================================================================= -->
<!--                         FUNCTION TEMPLATE                               -->
<!--																		 -->
<!--  Draw Stacks on the Block Diagram										 -->
<!-- ======================================================================= -->
<xsl:template name="Draw_BlkDiagram_Stacks">
	
	<xsl:param name="sbs_Y"     select="$BLKD_INNER_Y"/>
	
	<xsl:variable name="max_stack_AbvSbs_H_">
		<xsl:call-template name="_calc_Max_Stack_AbvSbs_Height"/>
	</xsl:variable>
	
<!--	
	<xsl:variable name="inner_X_"   select="($BLKD_PRTCHAN_W  + $BLKD_IORCHAN_W + $BLKD_INNER_GAP)"/>
	<xsl:variable name="inner_Y_"   select="($BLKD_PRTCHAN_H  + $BLKD_IORCHAN_H + $BLKD_INNER_GAP)"/>
	<xsl:variable name="numSbs_"    select="count(BLKDSHAPES/SBSSHAPES/MODULE)"/>
	<xsl:variable name="sbs_h_"     select="($numSbs_  * $SBS_LANE_H)"/>
	<xsl:variable name="sbs_y_"     select="($inner_Y_ + $max_stack_AbvSbs_H_ + $PROC2SBS_GAP)"/>
	
	<xsl:variable name="numSbs_"    select="count(/BLKDSHAPES/SBSSHAPES/MODULE)"/>
	<xsl:variable name="sbs_h_"     select="($numSbs_  * $SBS_LANE_H)"/>
	<xsl:variable name="sbs_y_"     select="($BLKD_INNER_Y + $max_stack_AbvSbs_H_ + $PROC2SBS_GAP)"/>
-->	
	
	<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/BCLANESPACES/BCLANESPACE[(@EAST &lt; /EDKSYSTEM/BLKDSHAPES/@STACK_HORIZ_WIDTH)]">
			
		<xsl:variable name="stack_line_x_">
			<xsl:call-template name="_calc_Stack_X">
				<xsl:with-param name="stackIdx"  select="@EAST"/>
			</xsl:call-template>
		</xsl:variable>
		
		<xsl:variable name="stack_abv_sbs_">
			<xsl:call-template name="_calc_Stack_AbvSbs_Height">
				<xsl:with-param name="stackIdx"  select="@EAST"/>
			</xsl:call-template>
		</xsl:variable>
		
		<xsl:variable name="numBridges_"   select="count(/EDKSYSTEM/BLKDSHAPES/BRIDGESHAPES/MODULE)"/>
		<xsl:variable name="bridges_w_"    select="(($numBridges_ * ($periMOD_W + ($BUS_LANE_W * 2))) + $BRIDGE_GAP)"/>
		
		<xsl:variable name="stack_y_" select="($sbs_Y - $stack_abv_sbs_)"/>
		<xsl:variable name="stack_x_" select="($BLKD_INNER_X + $stack_line_x_ + $bridges_w_)"/>
		
		<xsl:variable name="stack_name_">
			<xsl:call-template name="_gen_Stack_Name"> 
				<xsl:with-param name="horizIdx" select="@EAST"/>
			</xsl:call-template>		
		</xsl:variable>	
		
		<use   x="{$stack_x_}"    y="{$stack_y_}"  xlink:href="#{$stack_name_}"/> 
	
<!--		
		<xsl:message>Stack Idx <xsl:value-of select="@EAST"/></xsl:message>	
		<xsl:message>Stack X <xsl:value-of select="$stack_x_"/></xsl:message>	
		<xsl:message>Stack Y <xsl:value-of select="$stack_y_"/></xsl:message>	
-->	
		
	</xsl:for-each>	
			
</xsl:template>
	
<!-- ======================================================================= -->
<!--                         FUNCTION TEMPLATE                               -->
<!--																		 -->
<!--  Draw Stacks on the Block Diagram										 -->
<!-- ======================================================================= -->
<xsl:template name="Draw_BlkDiagram_BusLaneSpaces">
	
	<xsl:param name="sbs_Y"     select="$BLKD_INNER_Y"/>
	
	<xsl:variable name="lastStack_" select="(/EDKSYSTEM/BLKDSHAPES/@STACK_HORIZ_WIDTH) - 1"/>
	
	<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/BCLANESPACES/BCLANESPACE[@EAST]">
		<xsl:sort select="@EAST" data-type="number"/>
			
		<xsl:call-template name="Draw_BlkDiagram_BusLaneSpace">
			<xsl:with-param name="sbs_Y"        select="$sbs_Y"/>
			<xsl:with-param name="stackToEast"  select="@EAST"/>
		</xsl:call-template>
	</xsl:for-each>	
	
	<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/BCLANESPACES/BCLANESPACE[(@WEST = $lastStack_)]">
		<xsl:call-template name="Draw_BlkDiagram_BusLaneSpace">
			<xsl:with-param name="sbs_Y"        select="$sbs_Y"/>
			<xsl:with-param name="stackToWest"  select="$lastStack_"/>
		</xsl:call-template>
	</xsl:for-each>	
			
</xsl:template>
	
<xsl:template name="Draw_BlkDiagram_BusLaneSpace">
	
	<xsl:param name="sbs_Y"       select="0"/>
	<xsl:param name="stackToEast" select="'NONE'"/>
	<xsl:param name="stackToWest" select="'NONE'"/>
	
	<xsl:variable name="spaceAbvSbs_H_">
		<xsl:call-template name="_calc_Space_AbvSbs_Height">
			<xsl:with-param name="stackToEast"  select="$stackToEast"/>
			<xsl:with-param name="stackToWest"  select="$stackToWest"/>
		</xsl:call-template>
	</xsl:variable>	
	
	<xsl:variable name="spaceBlwSbs_H_">
		<xsl:call-template name="_calc_Space_BlwSbs_Height">
			<xsl:with-param name="stackToEast"  select="$stackToEast"/>
			<xsl:with-param name="stackToWest"  select="$stackToWest"/>
		</xsl:call-template>
	</xsl:variable>	
	
<!--	
	<xsl:message>Abv Sbs  is <xsl:value-of select="$spaceAbvSbs_H_"/></xsl:message>
	<xsl:message>Abv Blw  is <xsl:value-of select="$spaceBlwSbs_H_"/></xsl:message>
	<xsl:variable name="inner_X_"   select="($BLKD_PRTCHAN_W  + $BLKD_IORCHAN_W + $BLKD_INNER_GAP)"/>
	<xsl:variable name="inner_Y_"   select="($BLKD_PRTCHAN_H  + $BLKD_IORCHAN_H + $BLKD_INNER_GAP)"/>
	<xsl:variable name="numSbs_"    select="count(BLKDSHAPES/SBSSHAPES/MODULE)"/>
	<xsl:variable name="sbs_h_"     select="($numSbs_  * $SBS_LANE_H)"/>
	<xsl:variable name="sbs_y_"     select="($inner_Y_ + $max_stack_AbvSbs_H_ + $PROC2SBS_GAP)"/>
	
	<xsl:variable name="numSbs_"    select="count(/BLKDSHAPES/SBSSHAPES/MODULE)"/>
	<xsl:variable name="sbs_h_"     select="($numSbs_  * $SBS_LANE_H)"/>
	<xsl:variable name="sbs_y_"     select="($BLKD_INNER_Y + $max_stack_AbvSbs_H_ + $PROC2SBS_GAP)"/>
-->	
			
	<xsl:variable name="space_line_x_">
		<xsl:call-template name="_calc_Space_X">
			<xsl:with-param name="stackToEast"  select="$stackToEast"/>
			<xsl:with-param name="stackToWest"  select="$stackToWest"/>
		</xsl:call-template>
	</xsl:variable>
	
	<xsl:variable name="numBridges_"   select="count(/EDKSYSTEM/BLKDSHAPES/BRIDGESHAPES/MODULE)"/>
	<xsl:variable name="bridges_w_"    select="(($numBridges_ * ($periMOD_W + ($BUS_LANE_W * 2))) + $BRIDGE_GAP)"/>
		
	<xsl:variable name="space_y_" select="($sbs_Y - $spaceAbvSbs_H_)"/>
	<xsl:variable name="space_x_" select="($BLKD_INNER_X + $space_line_x_ + $bridges_w_)"/>
		
	<xsl:variable name="space_Name_">
		<xsl:call-template name="_gen_Space_Name"> 
			<xsl:with-param name="stackToEast" select="$stackToEast"/>
			<xsl:with-param name="stackToWest" select="$stackToWest"/>
		</xsl:call-template>		
	</xsl:variable>	
		
	<use   x="{$space_x_}"    y="{$space_y_}"  xlink:href="#{$space_Name_}"/> 
	
</xsl:template>
	
	
	
<!-- =========================================================================== -->
<!--                          FUNCTION TEMPLATE                                  -->
<!--																			 -->
<!--  Draw Bridges on the Block Diagram											 -->
<!-- =========================================================================== -->
<xsl:template name="Draw_BlkDiagram_Bridges">
	
	<xsl:param name="sbs_Y"     select="0"/>
	<xsl:param name="inner_X"   select="0"/>
	
	<!-- First save all the bridge indexs in a variable	 -->
	<xsl:variable name="bridgeShapes_">
		
		<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/BRIDGESHAPES/MODULE/BUSCONNS[(@ORIENTED = 'WEST')]/BUSCONN">	
			<BRIDGE BUSINDEX="{@BUSINDEX}" INSTANCE="{../../@INSTANCE}" POSITION="{(position() -1)}"/>
			<BRIDGECONN BUSINDEX="{@BUSINDEX}" INSTANCE="{../../@INSTANCE}" ORIENTED="{../@ORIENTED}" POSITION="{(position()  - 1)}" BUSSTD="{@BUSSTD}" BIFRANK="{@BIFRANK}"/>
			<!-- So both bus conns have same position.... -->
			<xsl:if test="../../BUSCONNS[(@ORIENTED = 'EAST')]">
				<BRIDGECONN BUSINDEX="{../../BUSCONNS[(@ORIENTED ='EAST')]/BUSCONN/@BUSINDEX}" INSTANCE="{../../@INSTANCE}" ORIENTED="EAST" POSITION="{(position()  - 1)}"   BUSSTD="{../../BUSCONNS[(@ORIENTED = 'EAST')]/BUSCONN/@BUSSTD}" BIFRANK="{../../BUSCONNS[(@ORIENTED = 'EAST')]/BUSCONN/@BIFRANK}"/>
			</xsl:if>
		</xsl:for-each>
		
	</xsl:variable>
	
<!--				
			<xsl:message>Found an east connection on <xsl:value-of select="../../@INSTANCE"/></xsl:message>
-->				
	

	<!-- Now layout the bridge shapes between the shared busses	 -->
	<xsl:for-each select="exsl:node-set($bridgeShapes_)/BRIDGE">
		<xsl:sort select="@POSITION" data-type="number"/>
		
		<xsl:variable name="brdgPosition_"  select="@POSITION"/>
		<xsl:variable name="brdgInstance_"  select="@INSTANCE"/>
		
		<xsl:variable name="min_bus_idx_" select="math:min(exsl:node-set($bridgeShapes_)/BRIDGECONN[(@POSITION = $brdgPosition_)]/@BUSINDEX)"/>
<!--		
		<xsl:variable name="max_bus_idx_" select="math:max(exsl:node-set($bridgeShapes_)/BRIDGECONN[(@POSITION = $brdgPosition_)]/@BUSINDEX)"/>
		
     	<xsl:message>Maximum index <xsl:value-of select="$max_bus_idx_"/></xsl:message>
     	<xsl:message>Minimum index <xsl:value-of select="$min_bus_idx_"/></xsl:message>
-->
		
		
		<xsl:variable name="brdg_X_"  select="($inner_X + $BRIDGE_GAP + $BUS_LANE_W + (@POSITION * ($periMOD_W + ($BUS_LANE_W * 2))))"/>	
		<xsl:variable name="brdg_Y_"  select="($sbs_Y   + $PROC2SBS_GAP + ($min_bus_idx_ * $SBS_LANE_H) + ceiling($SBS_LANE_H div 2) - ceiling($periMOD_H div 2))"/>
		
		<use  x="{$brdg_X_}"  y="{$brdg_Y_}"  xlink:href="#symbol_{$brdgInstance_}"/>	
	</xsl:for-each>	
	
		
	
<!--	
	<xsl:message>Found <xsl:value-of select="count(exsl:node-set($bridgeShapes_)/BRIDGECONN)"/> busconns </xsl:message>
		<xsl:message>Drawing connection for bridge <xsl:value-of select="$brdgInstance_"/> at <xsl:value-of select="@POSITION"/> </xsl:message>
-->	
	
	<xsl:for-each select="exsl:node-set($bridgeShapes_)/BRIDGECONN">
		<xsl:sort select="@POSITION" data-type="number"/>
		
		<xsl:variable name="brdgInstance_"  select="@INSTANCE"/>
		<xsl:variable name="brdgPosition_"  select="@POSITION"/>
		
		<xsl:variable name="bus_col_">
			<xsl:call-template name="BusType2Color">
				<xsl:with-param name="busType" select="@BUSSTD"/>
			</xsl:call-template>	
		</xsl:variable>
		
		<xsl:variable name="min_bus_idx_" select="math:min(exsl:node-set($bridgeShapes_)/BRIDGECONN[(@POSITION = $brdgPosition_)]/@BUSINDEX)"/>
		<xsl:variable name="brdg_Y1_"     select="($sbs_Y   + $PROC2SBS_GAP + ($min_bus_idx_ * $SBS_LANE_H) + ceiling($SBS_LANE_H div 2) - ceiling($periMOD_H div 2))"/>
		<xsl:variable name="brdg_X_"      select="($inner_X + $BRIDGE_GAP + $BUS_LANE_W + (@POSITION * ($periMOD_W + ($BUS_LANE_W * 2))))"/>	
<!--		
		<xsl:variable name="bc_Y_"        select="($sbs_Y + $PROC2SBS_GAP  + (@BUSINDEX * $SBS_LANE_H)) - ceiling($BIFC_H div 4)"/>
-->	
		<xsl:variable name="bc_Y_"        select="$brdg_Y1_ + $MOD_LANE_H + $MOD_LABEL_H + $MOD_BIF_GAP_V + ceiling($BIF_H div 2) - ceiling($BIFC_H div 2)"/>	
		<xsl:variable name="bc_X_">
			<xsl:choose>
				<xsl:when test="@ORIENTED='WEST'">
					<xsl:value-of select="($brdg_X_ - $BIFC_W)"/>
				</xsl:when>
				<xsl:when test="@ORIENTED='EAST'">
					<xsl:value-of select="($brdg_X_ + $periMOD_W)"/>
				</xsl:when>
			</xsl:choose>
		</xsl:variable>	
		
		<!-- Layout the bus conn -->
		<use   x="{$bc_X_}"   y="{$bc_Y_}"  xlink:href="#{@BUSSTD}_busconn_{@BIFRANK}"/>
		
		<!-- Figure out the positions of the lines -->
		
<!--		
		<xsl:variable name="vert_line_x_"  select="$bc_X_    + ceiling($BIFC_W div 2)"/>
		<xsl:message>vert line x <xsl:value-of select="$vert_line_x_"/></xsl:message>
		<xsl:message>bus index <xsl:value-of select="@BUSINDEX"/></xsl:message>
-->		
		
		<xsl:variable name="vert_line_x_">
			<xsl:choose>
				<xsl:when test="@ORIENTED='WEST'">
					<xsl:value-of select="($bc_X_ - ($BUS_LANE_W - $BIFC_W))"/>
				</xsl:when>
				<xsl:when test="@ORIENTED='EAST'">
					<xsl:value-of select="($bc_X_ + ($BUS_LANE_W - $P2P_BUS_W))"/>
				</xsl:when>
			</xsl:choose>
		</xsl:variable>	
		
		<!-- At least one of the points is going to be the bus -->
		<xsl:variable name="vert_line_y1_" select="($sbs_Y  + $PROC2SBS_GAP + (@BUSINDEX * $SBS_LANE_H))"/>
		<xsl:variable name="vert_line_y2_" select="$bc_Y_ + ceiling($BIFC_H div 2)"/>
		
		<xsl:variable name="v_bus_ul_y_">
			<xsl:choose>
				<xsl:when test="$vert_line_y1_ &gt; $vert_line_y2_">
					<xsl:value-of select="$vert_line_y2_"/>
				</xsl:when>
				<xsl:when test="$vert_line_y2_ &gt; $vert_line_y1_">
					<xsl:value-of select="$vert_line_y1_"/>
				</xsl:when>
			</xsl:choose>
		</xsl:variable>	
<!--		
		<xsl:variable name="v_bus_ul_x_" select="$vert_line_x_"/>
-->	
		<xsl:variable name="v_bus_ul_x_">
			<xsl:choose>
				<xsl:when test="@ORIENTED='WEST'">
					<xsl:value-of select="($vert_line_x_ + $MOD_BIF_GAP_H)"/>
				</xsl:when>
				<xsl:when test="@ORIENTED='EAST'">
					<xsl:value-of select="($vert_line_x_ - $MOD_BIF_GAP_H)"/>
				</xsl:when>
			</xsl:choose>
		</xsl:variable>	
		
		
		<xsl:variable name="v_bus_width_" select="$P2P_BUS_W"/>
		<xsl:variable name="v_bus_height_">
			<xsl:choose>
				<xsl:when test="$vert_line_y1_ &gt; $vert_line_y2_">
					<xsl:value-of select="($vert_line_y1_ - $vert_line_y2_)"/>
				</xsl:when>
				<xsl:when test="$vert_line_y2_ &gt; $vert_line_y1_">
					<xsl:value-of select="($vert_line_y2_ - $vert_line_y1_)"/>
				</xsl:when>
			</xsl:choose>
		</xsl:variable>	
		
		<xsl:variable name="h_bus_ul_x_">
			<xsl:choose>
				<xsl:when test="@ORIENTED='WEST'">
					<xsl:value-of select="($bc_X_ - ($BUS_LANE_W - $BIFC_W) + $MOD_BIF_GAP_H)"/>
				</xsl:when>
				<xsl:when test="@ORIENTED='EAST'">
					<xsl:value-of select="($bc_X_ + $BIFC_W - ceiling(($BIFC_W - $BIFC_Wi) div 2))"/>
				</xsl:when>
			</xsl:choose>
		</xsl:variable>	
		
		<xsl:variable name="h_bus_ul_y_" select="$bc_Y_ + ceiling($BIFC_H div 2) - ceiling($P2P_BUS_W div 2)"/>
		<xsl:variable name="h_bus_height_" select="$P2P_BUS_W"/>
		
		<xsl:variable name="h_bus_width_">
			<xsl:choose>
				<xsl:when test="@ORIENTED='WEST'">
					<xsl:value-of select="(($bc_X_ + ceiling(($BIFC_W - $BIFC_Wi) div 2)) - $h_bus_ul_x_ + 1)"/>
				</xsl:when>
				<xsl:when test="@ORIENTED='EAST'">
					<xsl:value-of select="(($v_bus_ul_x_ + $P2P_BUS_W) - $h_bus_ul_x_)"/>
				</xsl:when>
			</xsl:choose>
		</xsl:variable>	
		
		
<!--		
		<xsl:message>vert line y1 <xsl:value-of select="$vert_line_y1_"/></xsl:message>
-->		
		
		<rect x="{$v_bus_ul_x_}" 
		  	  y="{$v_bus_ul_y_ + 2}"  
		 	  width= "{$v_bus_width_}" 
		 	  height="{$v_bus_height_}" 
		 	  style="stroke:none; fill:{$bus_col_}"/>
		
		<rect x="{$h_bus_ul_x_}" 
		  	  y="{$h_bus_ul_y_}"  
		 	  width= "{$h_bus_width_}" 
		 	  height="{$h_bus_height_}" 
		 	  style="stroke:none; fill:{$bus_col_}"/>
		
	</xsl:for-each>	
	
</xsl:template>
	
	
<!-- =========================================================================== -->
<!--                          FUNCTION TEMPLATE                                  -->
<!--																			 -->
<!--  Draw Processors on the Block Diagram										 -->
<!-- =========================================================================== -->
<xsl:template name="Draw_BlkDiagram_Processors">
	
	<xsl:param name="Inner_X"                select="0"/>
	<xsl:param name="SharedBus_Y"            select="0"/>
	<xsl:param name="Max_Proc_H"             select="0"/>
	<xsl:param name="Max_Proc_PerisAbvSbs_H" select="0"/>
	<xsl:param name="Max_Proc_PerisBlwSbs_H" select="0"/>
	
	
	<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE">			
		
		<xsl:variable name="procInst_"    select="@INSTANCE"/>
		<xsl:variable name="proc_bifs_h_" select="@BIFS_H"/>
<!--		
		<xsl:message>Shared Bus Y <xsl:value-of select="$SharedBus_Y"/></xsl:message>
		<xsl:variable name="numMemUs_"    select="count(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[((@PROCESSOR = $procInst_) and (@MODCLASS = 'MEMORY_UNIT'))])"/>	
		<xsl:variable name="numPerisBlw_" select="count(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[((@PROCESSOR = $procInst_) and (@MODCLASS = 'PERIPHERAL') and    (@IS_BLWSBS))])"/>	
		<xsl:variable name="numPerisAbv_" select="count(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[((@PROCESSOR = $procInst_) and (@MODCLASS = 'PERIPHERAL') and not(@IS_BLWSBS))])"/>	
		<xsl:variable name="gapsAbv_h_"   select="(($numMemUs_ + $numPerisAbv_) * $BIF_H)"/>
-->		
		
		<xsl:variable name="proc_h_">
			<xsl:call-template name="_calc_Proc_Height">
				<xsl:with-param name="procInst"  select="$procInst_"/>
			</xsl:call-template>	
		</xsl:variable>
		
<!--		
		<xsl:variable name="max_Proc_h_">
			<xsl:call-template name="_calc_Max_Proc_Height"/>
		</xsl:variable>
-->	
		
		<xsl:variable name="perisAbv_h_">
			<xsl:call-template name="_calc_Proc_PerisAbvSbs_Height">
				<xsl:with-param name="procInst"  select="$procInst_"/>
			</xsl:call-template>	
		</xsl:variable>
		
		<xsl:variable name="perisBlw_h_">
			<xsl:call-template name="_calc_Proc_PerisBlwSbs_Height">
				<xsl:with-param name="procInst"  select="$procInst_"/>
			</xsl:call-template>	
		</xsl:variable>
		
		<xsl:variable name="memUs_h_">
			<xsl:call-template name="_calc_Proc_MemoryUnits_Height">
				<xsl:with-param name="procInst" select="$procInst_"/>
			</xsl:call-template>	
		</xsl:variable>
		
		<xsl:variable name="proc_y_"          select="($SharedBus_Y  - ($PROC2SBS_GAP   + $proc_h_ + $perisAbv_h_ + $memUs_h_))"/>
		<xsl:variable name="gaps_right_"      select="(@GAPS_X      * $MOD_SHAPES_G)"/>
		<xsl:variable name="mods_right_"      select="(@MODS_X      * $periMOD_W)"/>
		<xsl:variable name="lanes_right_"     select="(@BUS_LANES_X * $BUS_LANE_W)"/>
		
		<xsl:variable name="bkt_lanes_right_" select="(@BKT_LANES_X * $MOD_BKTLANE_W)"/>
		<xsl:variable name="bkt_gaps_right_"  select="(@BKT_GAPS_X  * $MOD_BUCKET_G)"/>
		
		<xsl:variable name="proc_x_"          select="($Inner_X + $gaps_right_ +  $mods_right_ + $bkt_lanes_right_ + $bkt_gaps_right_ + $lanes_right_)"/>
		
		<xsl:variable name="procGroupName_">
			<xsl:call-template name="_gen_Proc_GroupName"> 
				<xsl:with-param name="procInst"  select="$procInst_"/>
			</xsl:call-template>		
		</xsl:variable>
	
		<use   x="{$proc_x_}"  
		       y="{$proc_y_}" 
		       xlink:href="#{$procGroupName_}"/> 
		
		<xsl:variable name="numProcMods_" select="($perisAbv_h_ + $perisBlw_h_ + $memUs_h_)"/>
		
		<xsl:if test="$numProcMods_ = 0">
			
			<xsl:variable name="pbktW_"       select="@PSTACK_BKT_W"/>
			<xsl:variable name="pmodW_"       select="@PSTACK_MOD_W"/>
			<xsl:variable name="numSbsBkts_"  select="count(/EDKSYSTEM/BLKDSHAPES/SBSBUCKETS/SBSBUCKET[(@PROCESSOR = $procInst_)])"/>		
			
			<xsl:variable name="bktModsW_">
				<xsl:if test="($numSbsBkts_ &gt; 0)">
					<xsl:value-of select="(($MOD_BKTLANE_W * 2) + ($periMOD_W * $pbktW_) + ($MOD_BUCKET_G * ($pbktW_ - 1)))"/>	
				</xsl:if>
				<xsl:if test="not($numSbsBkts_ &gt; 0)">0</xsl:if>
			</xsl:variable> 
		
			<xsl:variable name="pstkModsW_" select="$periMOD_W"/>	
			
			<xsl:variable name="pstackW_">
				<xsl:if test="$bktModsW_ &gt; $pstkModsW_">
					<xsl:value-of select="$bktModsW_"/>
				</xsl:if>
				<xsl:if test="not($bktModsW_ &gt; $pstkModsW_)">
					<xsl:value-of select="$pstkModsW_"/>
				</xsl:if>
			</xsl:variable>
			
			<xsl:variable name="busLaneWestW_">
				<xsl:if test="(BUSCONNS[(@ORIENTED = 'WEST' and @BUSLANE_W)])">
					<xsl:value-of select="((BUSCONNS[(@ORIENTED ='WEST')]/@BUSLANE_W) * $BUS_LANE_W)"/>
				</xsl:if>
				<xsl:if test="not(BUSCONNS[(@ORIENTED = 'WEST') and @BUSLANE_W])">0</xsl:if>
			</xsl:variable>
			
		
			<xsl:if test="not(@IS_LIKEPROC = 'TRUE')">	  
				<text class="procclass"
						x="{($proc_x_  + $busLaneWestW_ + ceiling($pstackW_ div 2))}" 
						y="{$proc_y_ - 4}">PROCESSOR</text>			
			</xsl:if>
		
			<xsl:if test="@IS_LIKEPROC = 'TRUE'">	  
				<text class="procclass"
						x="{($proc_x_  + $busLaneWestW_ + ceiling($pstackW_ div 2))}" 
						y="{$proc_y_ - 4}">USER</text>			
			</xsl:if>
		</xsl:if>		
		
			
		<!-- Draw the multiproc stacks for this processor, if any-->	
		<xsl:if test="@PSTACK_BLKD_X">
			<xsl:variable name="stackBlkd_X_" select="(@PSTACK_BLKD_X + 1)"/>	
			
			<xsl:variable name="numPerisInStack_" select="count(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[((@PSTACK_BLKD_X = $stackBlkd_X_) and (@MODCLASS = 'PERIPHERAL'))])"/>	
			<xsl:variable name="numMemusInStack_" select="count(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[((@PSTACK_BLKD_X = $stackBlkd_X_) and (@MODCLASS = 'MEMORY_UNIT'))])"/>	
			
			<xsl:if test="(($numPerisInStack_ + $numMemusInStack_) &gt; 0)">
<!--				
				<xsl:message>Peris are <xsl:value-of select="$numPerisInStack_"/></xsl:message>
				<xsl:message>Memus are <xsl:value-of select="$numMemusInStack_"/></xsl:message>
-->				
				
<!--				
				<xsl:variable name="mp_peris_h_"         select="($numPerisInStack_  * ($periMOD_H + $BIF_H))"/>
				<xsl:variable name="mp_memus_h_"         select="($numMemusInStack_  * (($periMOD_H * 2) + $BIF_H))"/>
				<xsl:variable name="mp_stack_h_"         select="($mp_peris_h_ + $mp_memus_h_)"/>
-->				
				<xsl:variable name="mp_stack_h_">
					<xsl:call-template name="_calc_MultiProc_Stack_Height">
						<xsl:with-param name="mpstack_blkd_x" select="(@PSTACK_BLKD_X + 1)"/>
					</xsl:call-template>
				</xsl:variable>
				
				<xsl:variable name="mp_StackName_">
					<xsl:call-template name="_gen_CStack_StackName"> 
						<xsl:with-param name="cstkIndex" select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@PSTACK_BLKD_X = $stackBlkd_X_)]/@CSTACK_INDEX"/>
					</xsl:call-template>		
				</xsl:variable>
				
<!--				
				<xsl:message>Multi Stack Name is <xsl:value-of select="$mp_StackName_"/></xsl:message>
-->				
	
				
				<xsl:variable name="mp_gaps_right_"      select="(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@PSTACK_BLKD_X = $stackBlkd_X_)]/@GAPS_X 	   * $MOD_SHAPES_G)"/>
				<xsl:variable name="mp_mods_right_"      select="(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@PSTACK_BLKD_X = $stackBlkd_X_)]/@MODS_X      * $periMOD_W)"/>
				<xsl:variable name="mp_lanes_right_"     select="(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@PSTACK_BLKD_X = $stackBlkd_X_)]/@BUS_LANES_X * $BUS_LANE_W)"/>
				<xsl:variable name="mp_bkt_lanes_right_" select="(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@PSTACK_BLKD_X = $stackBlkd_X_)]/@BKT_LANES_X * $MOD_BKTLANE_W)"/>
				<xsl:variable name="mp_bkt_gaps_right_"  select="(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@PSTACK_BLKD_X = $stackBlkd_X_)]/@BKT_GAPS_X  * $MOD_BUCKET_G)"/>
				
				<xsl:variable name="mpstack_x_"  select="($Inner_X + $mp_gaps_right_ +  $mp_mods_right_ + $mp_bkt_lanes_right_ + $mp_bkt_gaps_right_ + $mp_lanes_right_)"/>
				<xsl:variable name="mpstack_y_"  select="($SharedBus_Y - ($PROC2SBS_GAP + $Max_Proc_H + $Max_Proc_PerisAbvSbs_H + $mp_stack_h_))"/>
				
				<use   x="{$mpstack_x_}"  y="{$mpstack_y_}" xlink:href="#{$mp_StackName_}"/> 
				
				
			</xsl:if>
		</xsl:if>	
		
	</xsl:for-each>		

</xsl:template>
	
<!-- =========================================================================== -->
<!--                          FUNCTION TEMPLATE                                  -->
<!--																			 -->
<!-- Draw the Complex stacks, (collections of more than one module that 	     -->
<!-- are not memory and not connected to a processor) 							 -->	
<!-- =========================================================================== -->
<xsl:template name="Draw_BlkDiagram_ComplexStacks">
	
	<xsl:param name="Inner_X"                select="0"/>
	<xsl:param name="SharedBus_Y"            select="0"/>
	
	<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@IS_PROMOTED and not(@IS_PENALIZED) and @CSTACK_INDEX and @BUS_LANES_X and @BKT_LANES_X  and @GAPS_X and @MODS_X and @BKT_GAPS_X)]">
		
	
		<xsl:variable name="gaps_right_"      select="(@GAPS_X      * $MOD_SHAPES_G)"/>
		<xsl:variable name="mods_right_"      select="(@MODS_X      * $periMOD_W)"/>
		<xsl:variable name="lanes_right_"     select="(@BUS_LANES_X * $BUS_LANE_W)"/>
		
		<xsl:variable name="bkt_lanes_right_" select="(@BKT_LANES_X * $MOD_BKTLANE_W)"/>
		<xsl:variable name="bkt_gaps_right_"  select="(@BKT_GAPS_X  * $MOD_BUCKET_G)"/>
		
		<xsl:variable name="cstack_x_"          select="($Inner_X + $gaps_right_ +  $mods_right_ + $bkt_lanes_right_ + $bkt_gaps_right_ + $lanes_right_)"/>
		<xsl:variable name="cstack_y_"          select="($SharedBus_Y)"/>
	
		<use   x="{$cstack_x_}"  
		       y="{$cstack_y_}" 
		       xlink:href="#cgroup_{@CSTACK_INDEX}"/> 
		       
	</xsl:for-each>		
		
</xsl:template>
	
<!-- =========================================================================== -->
<!--                          FUNCTION TEMPLATE                                  -->
<!--																			 -->
<!-- Draw the Complex Modules, (Modules that are not memory and not  	         -->
<!--	connected to a processor)                                                -->	
<!-- =========================================================================== -->
<xsl:template name="Draw_BlkDiagram_ComplexModules">
	
	<xsl:param name="Inner_X"                select="0"/>
	<xsl:param name="SharedBus_Y"            select="0"/>
	<xsl:param name="SharedBus_H"            select="0"/>
	
	<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@IS_PROMOTED and not(@IS_PENALIZED) and not(@CSTACK_INDEX) and @GAPS_X and @MODS_X and @BUS_LANES_X and @BKT_LANES_X and @BKT_GAPS_X)]">
		
		<xsl:variable name="gaps_right_"      select="(@GAPS_X      * $MOD_SHAPES_G)"/>
		<xsl:variable name="mods_right_"      select="(@MODS_X      * $periMOD_W)"/>
		<xsl:variable name="lanes_right_"     select="(@BUS_LANES_X * $BUS_LANE_W)"/>
		<xsl:variable name="bkt_lanes_right_" select="(@BKT_LANES_X * $MOD_BKTLANE_W)"/>
		<xsl:variable name="bkt_gaps_right_"  select="(@BKT_GAPS_X  * $MOD_BUCKET_G)"/>
	
		<xsl:variable name="cmplxBusLaneWest_w_">
			<xsl:if test="BUSCONNS[(@ORIENTED = 'WEST') and @BUSLANE_W]">
				 <xsl:value-of select="((BUSCONNS[@ORIENTED = 'WEST']/@BUSLANE_W) * $BUS_LANE_W)"/>
			</xsl:if>
			<xsl:if test="not(BUSCONNS[@ORIENTED = 'WEST'])">0</xsl:if>
		</xsl:variable>
		
		<xsl:variable name="cmplxBusLaneEast_w_">
			<xsl:if test="BUSCONNS[(@ORIENTED = 'EAST')and @BUSLANE_W]">
				 <xsl:value-of select="((BUSCONNS[@ORIENTED = 'EAST']/@BUSLANE_W) * $BUS_LANE_W)"/>
			</xsl:if>
			<xsl:if test="not(BUSCONNS[@ORIENTED = 'EAST'])">0</xsl:if>
		</xsl:variable>
		
		<xsl:variable name="cmplx_x_"  select="($Inner_X + $gaps_right_ + $mods_right_ + $lanes_right_ + $bkt_lanes_right_ + $bkt_gaps_right_)"/>
		
		<xsl:variable name="cmplx_y_">
			<xsl:choose>
				<xsl:when test="((@MODCLASS = 'MASTER_SLAVE') or (@MODCLASS = 'MONITOR'))">
					<xsl:value-of select="($SharedBus_Y - ($PROC2SBS_GAP + $periMOD_H))"/>
				</xsl:when>
				<xsl:otherwise>
					<xsl:value-of select="($SharedBus_Y + $SharedBus_H)"/>
				</xsl:otherwise>		
			</xsl:choose>
		</xsl:variable>  
		
	    <xsl:if test="(@MODCLASS)">
			<text class="ipclass"
				x="{$cmplx_x_ + $cmplxBusLaneWest_w_}" 
				y="{$cmplx_y_ - 4}">
					<xsl:value-of select="@MODCLASS"/>
			</text>	
	    </xsl:if>
		
		<xsl:choose>
			<xsl:when test="((@MODCLASS = 'MASTER_SLAVE') or (@MODCLASS = 'MONITOR'))">
				<use   x="{$cmplx_x_ + $cmplxBusLaneWest_w_}"  y="{$cmplx_y_}" xlink:href="#symbol_{MODULE/@INSTANCE}"/> 
			</xsl:when>	
			<xsl:otherwise>	
				<use   x="{$cmplx_x_ + $cmplxBusLaneWest_w_}"  y="{$cmplx_y_}" xlink:href="#symbol_peripheral_{position()}"/> 
			</xsl:otherwise>
		</xsl:choose>		
		
		<xsl:variable name="cmplx_Dy_"      select="$MOD_LANE_H + $MOD_LABEL_H + $MOD_BIF_GAP_V + ceiling($BIF_H div 2)"/>	
		
		<xsl:for-each select="BUSCONNS[@ORIENTED = 'WEST']/BUSCONN[@IS_SBSBIF and @BUSLANE_X and @BUSINDEX]">
			
			<xsl:variable name="westSbsCX_"    select="($cmplx_x_ + $cmplxBusLaneWest_w_) - ((@BUSLANE_X + 1) * $BUS_LANE_W)"/>
			<xsl:variable name="westSbsBusY_"  select="($SharedBus_Y    + (@BUSINDEX * $SBS_LANE_H))"/>
			<xsl:variable name="westSbsBifY_"  select="($cmplx_y_ + $cmplx_Dy_)"/>
			
			<xsl:variable name="cmplxBif_Dx_">
				<xsl:choose>
					<xsl:when test="(@IS_CENTERED = 'TRUE')">
						<xsl:value-of select="(ceiling($periMOD_W div 2) - ceiling($BIF_W div 2))"/>
					</xsl:when>	
					<xsl:otherwise>	
						<xsl:value-of select="$MOD_LANE_W"/>
					</xsl:otherwise>
				</xsl:choose>		
			</xsl:variable>
			
			
			<xsl:variable name="westSbsCColor_">
				<xsl:call-template name="BusType2Color">
					<xsl:with-param name="busType" select="@BUSSTD"/>
				</xsl:call-template>	
			</xsl:variable>
			
			<line x1="{$westSbsCX_   + ceiling($BIFC_W div 2)}" 
				  y1="{$westSbsBifY_}" 
				  x2="{$westSbsCX_   + ceiling($BIFC_W div 2)}" 
				  y2="{$westSbsBusY_}" 
				  style="stroke:{$westSbsCColor_};stroke-width:1"/>
				  
			<line x1="{$westSbsCX_   + ceiling($BIFC_W div 2)}" 
				  y1="{$westSbsBifY_ }" 
				  x2="{$cmplx_x_     + $cmplxBusLaneWest_w_ + $cmplxBif_Dx_}" 
				  y2="{$westSbsBifY_}" 
				  style="stroke:{$westSbsCColor_};stroke-width:1"/>
				  
			<use   x="{$westSbsCX_}"   y="{$westSbsBusY_ - ceiling($BIFC_H div 2) + ($BUS_ARROW_G * 2)}"  xlink:href="#{@BUSSTD}_busconn_{@BIFRANK}"/>0
		</xsl:for-each>
		
		<xsl:for-each select="BUSCONNS[(@ORIENTED = 'EAST')]/BUSCONN[@IS_SBSBIF and @BUSLANE_X and @BUSINDEX]">
			
			<xsl:variable name="eastSbsCX_"    select="($cmplx_x_ + $cmplxBusLaneWest_w_ + $periMOD_W +  ((@BUSLANE_X + 1) * $BUS_LANE_W) - $BIFC_W)"/>
			<xsl:variable name="eastSbsBusY_"  select="($SharedBus_Y    + (@BUSINDEX * $SBS_LANE_H))"/>
			<xsl:variable name="eastSbsBifY_"  select="($cmplx_y_ + $cmplx_Dy_)"/>
			
			<xsl:variable name="eastSbsCColor_">
				<xsl:call-template name="BusType2Color">
					<xsl:with-param name="busType" select="@BUSSTD"/>
				</xsl:call-template>	
			</xsl:variable>
			
			<xsl:variable name="cmplxBif_Dx_">
				<xsl:choose>
					<xsl:when test="(@IS_CENTERED = 'TRUE')">
						<xsl:value-of select="(ceiling($periMOD_W div 2) - ceiling($BIF_W div 2))"/>
					</xsl:when>	
					<xsl:otherwise>	
						<xsl:value-of select="$MOD_LANE_W"/>
					</xsl:otherwise>
				</xsl:choose>		
			</xsl:variable>
			
			<line x1="{$eastSbsCX_   + ceiling($BIFC_W div 2)}" 
				  y1="{$eastSbsBifY_}" 
				  x2="{$eastSbsCX_   + ceiling($BIFC_W div 2)}" 
				  y2="{$eastSbsBusY_}" 
				  style="stroke:{$eastSbsCColor_};stroke-width:1"/>
				  
			<line x1="{$eastSbsCX_   + ceiling($BIFC_W div 2)}" 
				  y1="{$eastSbsBifY_ }" 
				  x2="{$cmplx_x_     + $cmplxBusLaneWest_w_ + $periMOD_W - $cmplxBif_Dx_}" 
				  y2="{$eastSbsBifY_}" 
				  style="stroke:{$eastSbsCColor_};stroke-width:1"/>
				  
			<use   x="{$eastSbsCX_}"   y="{$eastSbsBusY_ - ceiling($BIFC_H div 2) + ($BUS_ARROW_G * 2)}"  xlink:href="#{@BUSSTD}_busconn_{@BIFRANK}"/>
			
		</xsl:for-each>
		
	</xsl:for-each>		
	
</xsl:template>
	
<!-- =========================================================================== -->
<!--                          FUNCTION TEMPLATE                                  -->
<!--																			 -->
<!-- Draw the Shared Bus Buckets												 -->
<!-- =========================================================================== -->
<xsl:template name="Draw_BlkDiagram_SharedBusBuckets">
	
	<xsl:param name="Inner_X"                select="0"/>
	<xsl:param name="SharedBus_Y"            select="0"/>
	<xsl:param name="SharedBus_H"            select="0"/>
	
	<xsl:for-each select="/EDKSYSTSEM/BLKDSHAPES/SBSBUCKETS/SBSBUCKET[not(@PROCESSOR) and @BUS_LANES_X and @GAPS_X and @MODS_X ]">			
		
		<xsl:variable name="ownerBus_"   select="@BUSNAME"/>
	
		<xsl:variable name="bkt_y_"  select="($SharedBus_Y + $SharedBus_H)"/>
		
		<xsl:variable name="gaps_right_"  select="(@GAPS_X      * $MOD_SHAPES_G)"/>
		<xsl:variable name="mods_right_"  select="(@MODS_X      * $periMOD_W)"/>
		<xsl:variable name="lanes_right_" select="(@BUS_LANES_X * $BUS_LANE_W)"/>
	
		<xsl:variable name="bktBusLane_w_"  select="((BUSCONNS/@BUSLANE_W) * $BUS_LANE_W)"/>
		
		<xsl:variable name="bkt_x_"  select="($bktBusLane_w_ + $Inner_X + $gaps_right_ +  $mods_right_ + $lanes_right_)"/>
		
		<text class="ipclass"
			x="{$bkt_x_}" 
			y="{$bkt_y_ - 4}">
				SLAVES of <xsl:value-of select="ownerBus_"/>
		</text>	
		
		<use   x="{$bkt_x_}"  y="{$bkt_y_}" xlink:href="#sbsbucket_{$ownerBus_}"/> 
		
		<!-- next draw connections to the shared busses from the slave buckets-->		  
		<xsl:for-each select="BUSCONNS/BUSCONN[(@IS_BKTCONN and @BUSSTD and @BUSLANE_X and @BUSINDEX)]">	
			
			<xsl:variable name="bktSbsCColor_">
				<xsl:call-template name="BusType2Color">
					<xsl:with-param name="busType" select="@BUSSTD"/>
				</xsl:call-template>	
			</xsl:variable>
			
			<xsl:variable name="bktSbsCX_" >
				<xsl:value-of select="($bkt_x_ - ((@BUSLANE_X + 1) * $BUS_LANE_W))"/>
			</xsl:variable>
			
			<xsl:variable name="bktSbsCTop_"  select="($SharedBus_Y + (@BUSINDEX * $SBS_LANE_H) - ceiling($BIFC_H div 2) + ($BUS_ARROW_G * 2))"/>
			<xsl:variable name="bktSbsCBot_"  select="($bkt_y_ + $MOD_BKTLANE_H + ceiling($periMOD_H div 2))"/>
			
			<line x1="{$bktSbsCX_   + ceiling($BIFC_W div 2)}" 
				  y1="{$bktSbsCTop_ + ceiling($BIFC_H div 2)}" 
				  x2="{$bktSbsCX_   + ceiling($BIFC_W div 2)}" 
				  y2="{$bktSbsCBot_ + ceiling($BIFC_H div 2)}" 
				  style="stroke:{$bktSbsCColor_};stroke-width:1"/>
				  
			<line x1="{$bktSbsCX_   + ceiling($BIFC_W div 2)}" 
				  y1="{$bktSbsCBot_ + ceiling($BIFC_H div 2)}" 
				  x2="{$bkt_x_}" 
				  y2="{$bktSbsCBot_ + ceiling($BIFC_H div 2)}" 
				  style="stroke:{$bktSbsCColor_};stroke-width:1"/>
				  
				  
			<use   x="{$bktSbsCX_}"   y="{$bktSbsCTop_}"  xlink:href="#{@BUSSTD}_busconn_SLAVE"/>
			
		</xsl:for-each>		  
		
	</xsl:for-each>		
	
</xsl:template>
	
	
<!-- =========================================================================== -->
<!--                          FUNCTION TEMPLATE                                  -->
<!--																			 -->
<!-- Draw the IP Bucket          												 -->
<!-- =========================================================================== -->
<xsl:template name="Draw_BlkDiagram_IPBucket">
	
	<xsl:param name="blkd_W"               select="0"/>
	<xsl:param name="sbs_Y"  		   	   select="$BLKD_INNER_Y"/>
	<xsl:param name="sbs_H"  		   	   select="0"/>
    <xsl:param name="max_Stack_BlwSbs_H"   select="0"/>
    <xsl:param name="max_Stack_BlwSbs_H"   select="0"/>
	
<!--	
	<xsl:message>SBS Y <xsl:value-of select="$sbs_Y"/></xsl:message>
	<xsl:message>SBS H <xsl:value-of select="$sbs_H"/></xsl:message>
	<xsl:message>Max below Sbs  <xsl:value-of select="$max_Stack_BlwSbs_H"/></xsl:message>
    <xsl:with-param name="max_Stack_AbvSbs_H"   select="$max_Stack_AbvSbs_H_"/>
    <xsl:with-param name="max_Stack_BlwSbs_H"  	select="$max_Stack_BlwSbs_H_"/>
    <xsl:param name="max_SbsBuckets_H"     select="0"/>
-->	
	
	<!-- Draw IP Bucket -->	
	<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/IPBUCKET">
	
	
		<xsl:variable name="bucket_w_"  select="(($MOD_BKTLANE_W * 2) + (($periMOD_W * @MODS_W) + ($MOD_BUCKET_G * (@MODS_W - 1))))"/>
		<xsl:variable name="bucket_h_"  select="(($MOD_BKTLANE_H * 2) + (($periMOD_H * @MODS_H) + ($MOD_BUCKET_G * (@MODS_H - 1))))"/>
		
		<xsl:variable name="bucket_x_"  select="(ceiling($blkd_W div 2) - ceiling($bucket_w_ div 2))"/>
		<xsl:variable name="bucket_y_"  select="($sbs_Y + $sbs_H + $max_Stack_BlwSbs_H + $SBS2IP_GAP)"/>
		
		<text class="ipclass"
			x="{$bucket_x_}" 
			y="{$bucket_y_ - 4}">
				IP
		</text>
		
		<use   x="{$bucket_x_}"   y="{$bucket_y_}"  xlink:href="#ipbucket"/>
		
	</xsl:for-each>
	
</xsl:template>
	
<!--
	====================================================================================
	                          FUNCTION TEMPLATE                                 
	
		 Draw the Floating Modules Bucket      										
	====================================================================================
-->
<xsl:template name="Draw_BlkDiagram_FloatingModsBucket">
	<xsl:param name="Blkd_W"                 select="0"/>
	<xsl:param name="DrawArea_W"             select="0"/>
	<xsl:param name="Inner_X"                select="0"/>
	<xsl:param name="SharedBus_Y"            select="0"/>
	<xsl:param name="SharedBus_H"            select="0"/>
	<xsl:param name="Max_Proc_H"             select="0"/>
	<xsl:param name="Max_Proc_PerisAbvSbs_H" select="0"/>
	<xsl:param name="Max_Proc_PerisBlwSbs_H" select="0"/>
	<xsl:param name="Max_SbsBuckets_H"       select="0"/>
	
	<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/UNKBUCKET">
		
<!--		
		<xsl:variable name="sbsBktModsH_"    select="../@LIMIT_SBSBKTMODS_H"/>
		<xsl:variable name="sbsNumBktsH_"    select="../@LIMIT_SBSNUMBKTS_H"/>
		<xsl:variable name="modsBlwH_"       select="../@LIMIT_PMODS_BELOW_SBS_H"/>
		
		<xsl:variable name="totalSbsBktsH_">
			<xsl:if test="$sbsBktModsH_ &gt; 0">
				<xsl:value-of select="((($MOD_BKTLANE_H * 2) *  $sbsNumBktsH_) + ($periMOD_H * $sbsBktModsH_) + (($sbsNumBktsH_ - 1) * $BIF_H) + ($MOD_BUCKET_G * ($sbsBktModsH_ - 1)))"/>
			</xsl:if> 
			<xsl:if test="not($sbsBktModsH_ &gt; 0)">0</xsl:if> 
		</xsl:variable>  
-->		
		
		<xsl:variable name="totalIpBktsH_">
			<xsl:if test="/EDKSYSTEM/BLKDSHAPES/IPBUCKET">
				<xsl:value-of select="(($MOD_BKTLANE_H * 2) + (($periMOD_H * /EDKSYSTEM/BLKDSHAPES/IPBUCKET/@MODS_H) + ($MOD_BUCKET_G * (/EDKSYSTEM/BLKDSHAPES/IPBUCKET/@MODS_H - 1))) + $IP2UNK_GAP)"/>
			</xsl:if> 
			<xsl:if test="not(/EDKSYSTEM/BLKDSHAPES/IPBUCKET)"></xsl:if> 
		</xsl:variable>  
		
<!--		
		<xsl:variable name="totalModsBlwH_"        select="($modsBlwH_  * ($periMOD_H + $BIF_H))"/>
-->		
	
		<xsl:variable name="bucket_w_"  select="(($MOD_BKTLANE_W * 2) + (($periMOD_W * @MODS_W) + ($MOD_BUCKET_G * (@MODS_W - 1))))"/>
		<xsl:variable name="bucket_h_"  select="(($MOD_BKTLANE_H * 2) + (($periMOD_H * @MODS_H) + ($MOD_BUCKET_G * (@MODS_H - 1))))"/>
		
		<xsl:variable name="bucket_y_"  select="($SharedBus_Y + $SharedBus_H + $Max_SbsBuckets_H + $Max_Proc_PerisBlwSbs_H + $totalIpBktsH_ + $IP2UNK_GAP)"/>
		<xsl:variable name="bucket_x_"  select="(ceiling($DrawArea_W div 2) - ceiling($bucket_w_ div 2))"/>
		
		<text class="ipclass"
			x="{$bucket_x_}" 
			y="{$bucket_y_ - 4}">
				UNASSOCIATED
		</text>
		
		<use   x="{$bucket_x_}"   y="{$bucket_y_}"  xlink:href="#unkbucket"/>
		
	</xsl:for-each>
	
</xsl:template>
	
<!--
	====================================================================================
                           FUNCTION TEMPLATE      
																		 
	 Draw  Processor to Processor) BUS Connections between the modules.	
	====================================================================================
-->
<xsl:template name="Draw_BlkDiagram_Proc2ProcConnections">
	
	<xsl:param name="Inner_X"                select="0"/>
	<xsl:param name="SharedBus_Y"            select="0"/>
	<xsl:param name="SharedBus_H"            select="0"/>
	<xsl:param name="Max_Proc_H"             select="0"/>
	<xsl:param name="Max_Proc_PerisAbvSbs_H" select="0"/>
	<xsl:param name="Max_Proc_PerisBlwSbs_H" select="0"/>
	<xsl:param name="Max_SbsBuckets_H"       select="0"/>
	
	
	<!-- Draw the processor to processor connections with SPLIT connections -->	
	<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE/BUSCONNS/BUSCONN[(@IS_PROC2PROC = 'TRUE') and (@IS_SPLITCONN = 'TRUE')]">
			
		<xsl:variable name="oriented_"        select="../@ORIENTED"/>
		<xsl:variable name="procInst_"        select="../../@INSTANCE"/>
		
		<xsl:variable name="pbifsH_"          select="../../@BIFS_H"/>
		<xsl:variable name="pbifsW_"          select="../../@BIFS_W"/>
		<xsl:variable name="pbktW_"           select="../../@PSTACK_BKT_W"/>
		<xsl:variable name="pmodW_"           select="../../@PSTACK_MOD_W"/>
		
		<xsl:variable name="gaps_right_"      select="(../../@GAPS_X      * $MOD_SHAPES_G)"/>
		<xsl:variable name="mods_right_"      select="(../../@MODS_X      * $periMOD_W)"/>
		<xsl:variable name="lanes_right_"     select="(../../@BUS_LANES_X * $BUS_LANE_W)"/>
		<xsl:variable name="bkt_lanes_right_" select="(../../@BKT_LANES_X * $MOD_BKTLANE_W)"/>
		<xsl:variable name="bkt_gaps_right_"  select="(../../@BKT_GAPS_X  * $MOD_BUCKET_G)"/>
		
		<xsl:variable name="numSbsBkts_"      select="count(/EDKSYSTEM/BLKDSHAPES/SBSBUCKETS/SBSBUCKET[(@PROCESSOR = $procInst_)])"/>	
		
		<xsl:variable name="proc_h_"          select="(($MOD_LANE_H * 2) + (($BIF_H + $MOD_BIF_GAP_V) * $pbifsH_) + ($MOD_LABEL_H + $MOD_BIF_GAP_V))"/>	
		
		<xsl:variable name="proc_y_"          select="($SharedBus_Y - ($PROC2SBS_GAP + $proc_h_))"/>
		<xsl:variable name="proc_x_"          select="($Inner_X + $gaps_right_ +  $mods_right_ + $bkt_lanes_right_ + $bkt_gaps_right_ + $lanes_right_)"/>
		
		<xsl:variable name="busLaneWestW_">
			<xsl:if test="(../../BUSCONNS[(@ORIENTED = 'WEST')])">
				<xsl:value-of select="((../../BUSCONNS[(@ORIENTED ='WEST')]/@BUSLANE_W) * $BUS_LANE_W)"/>
			</xsl:if>
			<xsl:if test="not(../../BUSCONNS[(@ORIENTED = 'WEST')])">0</xsl:if>
		</xsl:variable>
		
			
		<xsl:variable name="busLaneEastW_">
			<xsl:if test="(../../BUSCONNS[(@ORIENTED = 'EAST')])">
				<xsl:value-of select="((../../BUSCONNS[(@ORIENTED ='EAST')]/@BUSLANE_W) * $BUS_LANE_W)"/>
			</xsl:if>
			<xsl:if test="not(../../BUSCONNS[(@ORIENTED = 'EAST')])">0</xsl:if>
		</xsl:variable>
		
<!--		
		<xsl:message>West width is <xsl:value-of select="$busLaneWestW_"/></xsl:message>
		<xsl:message>proc x <xsl:value-of select="$proc_x_"/></xsl:message>
		<xsl:message>Bus lane west <xsl:value-of select="$busLaneWestW_"/></xsl:message>
		<xsl:message>Bus lane east <xsl:value-of select="$busLaneEastW_"/></xsl:message>
		<xsl:message>Num shared buckets <xsl:value-of select="$numSbsBkts_"/></xsl:message>
-->		
		
		
		<xsl:variable name="bktModsW_">
			<xsl:if test="($numSbsBkts_ &gt; 0)">
				<xsl:value-of select="(($MOD_BKTLANE_W * 2) + ($periMOD_W * $pbktW_) + ($MOD_BUCKET_G * ($pbktW_ - 1)))"/>	
			</xsl:if>
			<xsl:if test="not($numSbsBkts_ &gt; 0)">0</xsl:if>
		</xsl:variable> 
		<xsl:variable name="pstkModsW_" select="($pmodW_ * $periMOD_W)"/>
		
		<xsl:variable name="pstackW_">
			<xsl:if test="$bktModsW_ &gt; $pstkModsW_">
				<xsl:value-of select="$bktModsW_"/>
			</xsl:if>
			<xsl:if test="not($bktModsW_ &gt; $pstkModsW_)">
				<xsl:value-of select="$pstkModsW_"/>
			</xsl:if>
		</xsl:variable>
		
		<xsl:variable name="splbus_w_" select="$BUS_ARROW_W + $BIFC_W + $BIFC_Wi"/>
		
		<xsl:variable name="proc2procX_" >
			<xsl:if test="$oriented_= 'WEST'"><xsl:value-of select="$proc_x_ + $busLaneWestW_  + ceiling($pstackW_ div 2) - (ceiling($periMOD_W div 2) + $BIFC_W + $splbus_w_)"/></xsl:if>	
			<xsl:if test="$oriented_= 'EAST'"><xsl:value-of select="$proc_x_ + $busLaneEastW_  + ceiling($pstackW_ div 2) + ceiling($periMOD_W div 2) + $BIFC_W"/></xsl:if>	
		</xsl:variable>  
		
		<xsl:variable name="pr2prNumX_" >
			<xsl:if test="$oriented_= 'WEST'"><xsl:value-of select="$proc2procX_ + ceiling($BIFC_W div 4)"/></xsl:if>	
			<xsl:if test="$oriented_= 'EAST'"><xsl:value-of select="$proc2procX_ + ($BUS_ARROW_W * 2) + ceiling($BIFC_W div 4)"/></xsl:if>	
<!--			
			<xsl:if test="$oriented_= 'EAST'"><xsl:value-of select="$proc2procX_ + ceiling($BIFC_W div 4)"/></xsl:if>	
			<xsl:if test="$oriented_= 'EAST'"><xsl:value-of select="$proc2procX_ + $BUS_ARROW_W + $BIFC_W + ceiling($BIFC_Wi div 2)"/></xsl:if>	
			<xsl:if test="$oriented_= 'EAST'"><xsl:value-of select="$proc2procX_ + $BUS_ARROW_W + $BIFC_W + ceiling($BIFC_Wi div 2) - 4"/></xsl:if>	
		<xsl:message>The Split count is <xsl:value-of select="@SPLITCNT"/></xsl:message>
-->	
		</xsl:variable>  
		
		
		<xsl:variable name="pr2prLabelX_" >
			<xsl:if test="$oriented_= 'WEST'"><xsl:value-of select="$proc2procX_ - (string-length(@BUSNAME) * 6)"/></xsl:if>	
			<xsl:if test="$oriented_= 'EAST'"><xsl:value-of select="$proc2procX_ + $splbus_w_"/></xsl:if>	
		</xsl:variable>  
		
		<xsl:variable name="proc2procY_"   select="(($proc_y_ + ($MOD_LANE_H + $MOD_LABEL_H + $MOD_BIF_GAP_V) + (($BIF_H + $BIF_GAP) * @PBIF_Y) + ceiling($BIF_H div 2)) - ceiling($BIFC_H div 2))"/>
		<xsl:variable name="proc2procDy_"  select="(ceiling($BIF_H div 2) - ceiling($BUS_ARROW_G div 2))"/>
		
		
		<!-- For unidirectional orientations, when its a master draw this end one way -->		
		<xsl:variable name="draw_oriented_">
			<xsl:choose>
				<xsl:when test="(@BIFRANK = 'MASTER')"><xsl:value-of select="$BIF_TYPE_ONEWAY"/></xsl:when>
				<xsl:otherwise><xsl:value-of select="$oriented_"/></xsl:otherwise>	
			</xsl:choose>		
		</xsl:variable>
		
		<use   x="{$proc2procX_}"   y="{$proc2procY_ + $proc2procDy_}"  xlink:href="#{@BUSSTD}_SplitBus_{$draw_oriented_}"/>
		
		
<!--		
		<text class="splitbustxt"
              x="{$pr2prNumX_} "
			  y="{$proc2procY_ + $proc2procDy_ + 8}">
			 <xsl:value-of select="@SPLITCNT"/> 
		</text>		  
-->		
		
		<text class="splitbustxt"
              x="{$pr2prNumX_} "
			  y="{$proc2procY_ + $proc2procDy_ + 7}">
			 <xsl:value-of select="@SPLITCNT"/> 
		</text>		  
		
		<text class="horizp2pbuslabel"
              x="{$pr2prLabelX_} "
			  y="{$proc2procY_ + $proc2procDy_ + 8}">
			 <xsl:value-of select="@BUSNAME"/> 
		</text>		  
	</xsl:for-each>		

		
	
	<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE/BUSCONNS/BUSCONN[(@IS_PROC2PROC = 'TRUE') and (@BIFRANK = 'MASTER') and not(@IS_SPLITCONN = 'TRUE')]">
			
<!--  MASTER VALUES -->		
		<xsl:variable name="mst_oriented_"        select="../@ORIENTED"/>
		<xsl:variable name="mst_procInst_"        select="../../@INSTANCE"/>
		<xsl:variable name="busName_"             select="@BUSNAME"/>
		
		<xsl:variable name="mst_numMemCs_"        select="count(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[((@PROCESSOR = $mst_procInst_) and (@MODCLASS='MEMORY_UNIT'))])"/>	
		<xsl:variable name="mst_numSbsBkts_"      select="count(/EDKSYSTEM/BLKDSHAPES/SBSBUCKETS/SBSBUCKET[   (@PROCESSOR = $mst_procInst_)])"/>	
		
		<xsl:variable name="mst_proc_bifs_h_"     select="../../@BIFS_H"/>
		<xsl:variable name="mst_numSlvsAbv_"      select="../../@PMODS_ABOVE_SBS_H"/>
		<xsl:variable name="mst_numSlvsBlw_"      select="../../@PMODS_BELOW_SBS_H"/>
		
		<xsl:variable name="mst_gaps_right_"      select="(../../@GAPS_X      * $MOD_SHAPES_G)"/>
		<xsl:variable name="mst_mods_right_"      select="(../../@MODS_X      * $periMOD_W)"/>
		<xsl:variable name="mst_lanes_right_"     select="(../../@BUS_LANES_X * $BUS_LANE_W)"/>
		<xsl:variable name="mst_bkt_lanes_right_" select="(../../@BKT_LANES_X * $MOD_BKTLANE_W)"/>
		<xsl:variable name="mst_bkt_gaps_right_"  select="(../../@BKT_GAPS_X  * $MOD_BUCKET_G)"/>
		
		<xsl:variable name="mst_pbifsW_"          select="../../@BIFS_W"/>
		<xsl:variable name="mst_pbktW_"           select="../../@PSTACK_BKT_W"/>
		<xsl:variable name="mst_pmodW_"           select="../../@PSTACK_MOD_W"/>
		
		<xsl:variable name="mst_pbifsH_"          select="../../@BIFS_H"/>
		<xsl:variable name="mst_pbktH_"           select="../../@PSTACK_BKT_H"/>
		<xsl:variable name="mst_pmodH_"           select="../../@PSTACK_MOD_H"/>
		
		<xsl:variable name="mst_memCH_"           select="($mst_numMemCs_   * (($periMOD_H * 2) + $BIF_H))"/>
		<xsl:variable name="mst_slavesH_"         select="($mst_numSlvsAbv_ * ( $periMOD_H      + $BIF_H))"/>
		<xsl:variable name="mst_proc_h_"          select="(($MOD_LANE_H * 2) + (($BIF_H + $MOD_BIF_GAP_V) * $mst_proc_bifs_h_) + ($MOD_LABEL_H + $MOD_BIF_GAP_V))"/>	
		<xsl:variable name="mst_pabv_h_"          select="($mst_proc_h_ + $mst_memCH_ + $mst_slavesH_)"/>
		
		<xsl:variable name="mst_proc_y_"          select="($SharedBus_Y - ($PROC2SBS_GAP + $mst_proc_h_))"/>
		<xsl:variable name="mst_proc_x_"          select="($Inner_X + $mst_gaps_right_ +  $mst_mods_right_ + $mst_bkt_lanes_right_ + $mst_bkt_gaps_right_ + $mst_lanes_right_)"/>
		
		<xsl:variable name="mst_busLaneWestW_">
			<xsl:if test="(../../BUSCONNS[@ORIENTED = 'WEST'])">
				<xsl:value-of select="((../../BUSCONNS[@ORIENTED ='WEST']/@BUSLANE_W) * $BUS_LANE_W)"/>
			</xsl:if>
			<xsl:if test="not(../../BUSCONNS[@ORIENTED = 'WEST'])">0</xsl:if>
		</xsl:variable>
			
		<xsl:variable name="mst_busLaneEastW_">
			<xsl:if test="(../../BUSCONNS[@ORIENTED = 'EAST'])">
				<xsl:value-of select="((../../BUSCONNS[@ORIENTED ='EAST']/@BUSLANE_W) * $BUS_LANE_W)"/>
			</xsl:if>
			<xsl:if test="not(../../BUSCONNS[@ORIENTED = 'EAST'])">0</xsl:if>
		</xsl:variable>
		
		<xsl:variable name="mst_bktModsW_">
			<xsl:if test="($mst_numSbsBkts_ &gt; 0)">
				<xsl:value-of select="(($MOD_BKTLANE_W * 2) + ($periMOD_W * $mst_pbktW_) + ($MOD_BUCKET_G * ($mst_pbktW_ - 1)))"/>	
			</xsl:if>
			<xsl:if test="not($mst_numSbsBkts_ &gt; 0)">0</xsl:if>
		</xsl:variable> 
		
		<xsl:variable name="mst_pstkModsW_" select="($mst_pmodW_ * $periMOD_W)"/>
		
		<xsl:variable name="mst_pstackW_">
			<xsl:if test="$mst_bktModsW_ &gt; $mst_pstkModsW_">
				<xsl:value-of select="$mst_bktModsW_"/>
			</xsl:if>
			<xsl:if test="not($mst_bktModsW_ &gt; $mst_pstkModsW_)">
				<xsl:value-of select="$mst_pstkModsW_"/>
			</xsl:if>
		</xsl:variable>
		
<!--  SLAVE VALUES -->		
		<xsl:variable name="slaveInst_"           select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[not(@INSTANCE = $mst_procInst_) and BUSCONNS/BUSCONN[@BUSNAME = $busName_]]/@INSTANCE"/>	
		<xsl:variable name="slv_numMemCs_"        select="count(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[((@PROCESSOR = $slaveInst_) and (@MODCLASS='MEMORY_UNIT'))])"/>
		<xsl:variable name="slv_numSbsBkts_"      select="count(/EDKSYSTEM/BLKDSHAPES/SBSBUCKETS/SBSBUCKET[   (@PROCESSOR = $slaveInst_)])"/>
		
		<xsl:variable name="slv_proc_bifs_h_"     select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[@INSTANCE = $slaveInst_]/@BIFS_H"/>
		<xsl:variable name="slv_numSlvsAbv_"      select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[@INSTANCE = $slaveInst_]/@PMODS_ABOVE_SBS_H"/>
		<xsl:variable name="slv_numSlvsBlw_"      select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[@INSTANCE = $slaveInst_]/@PMODS_BELOW_SBS_H"/>
		
		<xsl:variable name="slv_gaps_right_"      select="(/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[@INSTANCE = $slaveInst_]/@GAPS_X      * $MOD_SHAPES_G)"/>
		<xsl:variable name="slv_mods_right_"      select="(/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[@INSTANCE = $slaveInst_]/@MODS_X      * $periMOD_W)"/>
		<xsl:variable name="slv_lanes_right_"     select="(/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[@INSTANCE = $slaveInst_]/@BUS_LANES_X * $BUS_LANE_W)"/>
		<xsl:variable name="slv_bkt_lanes_right_" select="(/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[@INSTANCE = $slaveInst_]/@BKT_LANES_X * $MOD_BKTLANE_W)"/>
		<xsl:variable name="slv_bkt_gaps_right_"  select="(/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[@INSTANCE = $slaveInst_]/@BKT_GAPS_X  * $MOD_BUCKET_G)"/>
		
		<xsl:variable name="slv_pbifsW_"          select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[@INSTANCE = $slaveInst_]/@BIFS_W"/>
		<xsl:variable name="slv_pbktW_"           select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[@INSTANCE = $slaveInst_]/@PSTACK_BKT_W"/>
		<xsl:variable name="slv_pmodW_"           select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[@INSTANCE = $slaveInst_]/@PSTACK_MOD_W"/>
		
		<xsl:variable name="slv_pbifsH_"          select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[@INSTANCE = $slaveInst_]/@BIFS_H"/>
		<xsl:variable name="slv_pbktH_"           select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[@INSTANCE = $slaveInst_]/@PSTACK_BKT_H"/>
		<xsl:variable name="slv_pmodH_"           select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[@INSTANCE = $slaveInst_]/@PSTACK_MOD_H"/>
		
		<xsl:variable name="slv_memCH_"           select="($slv_numMemCs_   * (($periMOD_H * 2) + $BIF_H))"/>
		<xsl:variable name="slv_slavesH_"         select="($slv_numSlvsAbv_ * ( $periMOD_H      + $BIF_H))"/>
		<xsl:variable name="slv_proc_h_"          select="(($MOD_LANE_H * 2) + (($BIF_H + $MOD_BIF_GAP_V) * $slv_proc_bifs_h_) + ($MOD_LABEL_H + $MOD_BIF_GAP_V))"/>	
		<xsl:variable name="slv_pabv_h_"          select="($slv_proc_h_ + $slv_memCH_ + $slv_slavesH_)"/>
		
		<xsl:variable name="slv_proc_y_"          select="($SharedBus_Y - ($PROC2SBS_GAP + $slv_proc_h_))"/>
		<xsl:variable name="slv_proc_x_"          select="($Inner_X + $slv_gaps_right_ +  $slv_mods_right_ + $slv_bkt_lanes_right_ + $slv_bkt_gaps_right_ + $slv_lanes_right_)"/>
		
		<xsl:variable name="slv_busLaneWestW_">
			<xsl:if test="(/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[@INSTANCE = $slaveInst_]/BUSCONNS[@ORIENTED = 'WEST'])">
				<xsl:value-of select="((/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[@INSTANCE = $slaveInst_]/BUSCONNS[@ORIENTED ='WEST']/@BUSLANE_W) * $BUS_LANE_W)"/>
			</xsl:if>
			<xsl:if test="not(/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[@INSTANCE = $slaveInst_]/BUSCONNS[@ORIENTED = 'WEST'])">0</xsl:if>
		</xsl:variable>
		
		<xsl:variable name="mstArrow_">
			<xsl:choose>
				<xsl:when test="(@BUSSSTD = 'FSL')">BusArrowHInitiator</xsl:when>
				<xsl:otherwise>BusArrowWest</xsl:otherwise> 
			</xsl:choose>		
		</xsl:variable>
		
			
		<xsl:variable name="slv_busLaneEastW_">
			<xsl:if test="(/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[(@INSTANCE = $slaveInst_)]/BUSCONNS[(@ORIENTED = 'EAST')])">
				<xsl:value-of select="((/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[(@INSTANCE = $slaveInst_)]/BUSCONNS[(@ORIENTED ='EAST')]/@BUSLANE_W) * $BUS_LANE_W)"/>
			</xsl:if>
			<xsl:if test="not(/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE[(@INSTANCE = $slaveInst_)]/BUSCONNS[(@ORIENTED = 'EAST')])">0</xsl:if>
		</xsl:variable>
		
		<xsl:variable name="slv_bktModsW_">
			<xsl:if test="($slv_numSbsBkts_ &gt; 0)">
				<xsl:value-of select="(($MOD_BKTLANE_W * 2) + ($periMOD_W * $slv_pbktW_) + ($MOD_BUCKET_G * ($slv_pbktW_ - 1)))"/>	
			</xsl:if>
			<xsl:if test="not($slv_numSbsBkts_ &gt; 0)">0</xsl:if>
		</xsl:variable> 
		
		<xsl:variable name="slv_pstkModsW_" select="($slv_pmodW_ * $periMOD_W)"/>
		
		<xsl:variable name="slv_pstackW_">
			<xsl:if test="$slv_bktModsW_ &gt; $slv_pstkModsW_">
				<xsl:value-of select="$slv_bktModsW_"/>
			</xsl:if>
			<xsl:if test="not($slv_bktModsW_ &gt; $slv_pstkModsW_)">
				<xsl:value-of select="$slv_pstkModsW_"/>
			</xsl:if>
		</xsl:variable>
		
<!--		
		<xsl:message>Slave bus lane west <xsl:value-of select="$slv_busLaneWestW_"/></xsl:message>
		<xsl:message>Slave bus lane east <xsl:value-of select="$slv_busLaneEastW_"/></xsl:message>
-->		
		
		<xsl:variable name="proc2procBegX_" select="$mst_proc_x_ + $mst_busLaneWestW_  + ceiling($mst_pstackW_ div 2) + ceiling($periMOD_W div 2) + $BIFC_W"/>
		<xsl:variable name="proc2procEndX_" select="$slv_proc_x_ + $slv_busLaneWestW_  + ceiling($slv_pstackW_ div 2) - (ceiling($periMOD_W div 2) + $BIFC_W + $BUS_ARROW_W)"/>
		
		<xsl:variable name="proc2procBegY_" select="(($mst_proc_y_ + ($MOD_LANE_H + $MOD_LABEL_H + $MOD_BIF_GAP_V) + (($BIF_H + $MOD_BIF_GAP_V) * @PBIF_Y) + ceiling($BIF_H div 2)) - ceiling($BIFC_H div 2))"/>
		<xsl:variable name="proc2procDy_"   select="(ceiling($BIF_H div 2) - ceiling($BUS_ARROW_G div 2))"/>
		<xsl:variable name="proc2procY_"    select="($proc2procBegY_ + $proc2procDy_)"/>
		<xsl:variable name="bus_col_">
			<xsl:call-template name="BusType2Color">
				<xsl:with-param name="busType" select="@BUSSTD"/>
			</xsl:call-template>	
		</xsl:variable>
		
		<use  x="{$proc2procBegX_}" y="{$proc2procY_}"  xlink:href="#{@BUSSTD}_{$mstArrow_}"/>
		<use  x="{$proc2procEndX_}" y="{$proc2procY_}"  xlink:href="#{@BUSSTD}_BusArrowEast"/>	
		<rect x="{$proc2procBegX_ + $BUS_ARROW_W}" 
			  y="{$proc2procY_ + $BUS_ARROW_G}"  
			  width= "{($proc2procEndX_  - $proc2procBegX_ - $BUS_ARROW_W)}" 
			  height="{$BUS_ARROW_H - (2 * $BUS_ARROW_G)}" style="stroke:none; fill:{$bus_col_}"/>
			  
		<text class="horizp2pbuslabel"
              x="{$proc2procBegX_ + 8} "
			  y="{$proc2procY_    - 2}">
			 <xsl:value-of select="@BUSNAME"/> 
		</text>		  
		
		<text class="horizp2pbuslabel"
              x="{$proc2procEndX_ - (string-length(@BUSNAME) * 6)} "
			  y="{$proc2procY_    - 2}">
			 <xsl:value-of select="@BUSNAME"/> 
		</text>		  
		
<!--		
		<xsl:variable name="pr2prLabelX_" >
			<xsl:if test="$oriented_= 'WEST'"><xsl:value-of select="$proc2procX_ - (string-length(@BUSNAME) * 6)"/></xsl:if>	
			<xsl:if test="$oriented_= 'EAST'"><xsl:value-of select="$proc2procX_ + $splbus_w_"/></xsl:if>	
		</xsl:variable>  
		
		<use   x="{$proc2procX_}"   y="{$proc2procY_ + $proc2procDy_}"  xlink:href="#{@BUSSTD}_SplitBus_{$oriented_}"/>
		
		<text class="splitp2pbuslabel"
              x="{$pr2prLabelX_} "
			  y="{$proc2procY_ + $proc2procDy_ + 8}">
			 <xsl:value-of select="@BUSNAME"/> 
		</text>		  
-->		
	</xsl:for-each>		
	
</xsl:template>
	
<!--
	====================================================================================
                           FUNCTION TEMPLATE      
																		 
	 Draw Bus connections on modules that are connected to more than one module
	====================================================================================
-->
<xsl:template name="Draw_BlkDiagram_MultiProcConnections">
	
	<xsl:param name="Inner_X"                select="0"/>
	<xsl:param name="SharedBus_Y"            select="0"/>
	<xsl:param name="SharedBus_H"            select="0"/>
	<xsl:param name="Max_Proc_H"             select="0"/>
	<xsl:param name="Max_Proc_PerisAbvSbs_H" select="0"/>
	<xsl:param name="Max_Proc_PerisBlwSbs_H" select="0"/>
	<xsl:param name="Max_SbsBuckets_H"       select="0"/>
	
<!--	
	<xsl:message>Reached Multi Processor connections</xsl:message>
-->	
	
	<!--
		 ============================================================ 
	        Draw Multiproc Bus connection lanes, (two or more connections on the same bus lane)
		 ============================================================ 
	 -->	
	
	<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE/BUSCONNS/BUSCONNLANE[((@IS_MULTIPROC = 'TRUE') and not(@IS_SPLITCONN = 'TRUE') and @BUSNAME and @BUSSTD and @BUSLANE_X)]">
		
<!--		
		<xsl:message>Found a Multi Processor Busconn Group  </xsl:message>
-->		
		
		<xsl:variable name="oriented_"         select="../@ORIENTED"/>
		<xsl:variable name="busName_"          select="@BUSNAME"/>
		
		<xsl:variable name="busColor_">
			<xsl:call-template name="BusType2Color">
				<xsl:with-param name="busType" select="@BUSSTD"/>
			</xsl:call-template>	
		</xsl:variable>
		
		<xsl:variable name="mp_proc_inst_"    select="../../@INSTANCE"/>
		<xsl:variable name="mp_proc_bifs_h_"  select="../../@BIFS_H"/>
		<xsl:variable name="mp_proc_bifs_w_"  select="../../@BIFS_W"/>
		<xsl:variable name="mp_proc_pbktW_"   select="../../@PSTACK_BKT_W"/>
		<xsl:variable name="mp_proc_pbktH_"   select="../../@PSTACK_BKT_H"/>
		<xsl:variable name="mp_proc_pmodW_"   select="../../@PSTACK_MOD_W"/>
		<xsl:variable name="mp_proc_pmodH_"   select="../../@PSTACK_MOD_H"/>
		
		<xsl:variable name="mp_proc_gaps_right_"      select="(../../@GAPS_X      * $MOD_SHAPES_G)"/>
		<xsl:variable name="mp_proc_mods_right_"      select="(../../@MODS_X      * $periMOD_W)"/>
		<xsl:variable name="mp_proc_lanes_right_"     select="(../../@BUS_LANES_X * $BUS_LANE_W)"/>
		<xsl:variable name="mp_proc_bkt_lanes_right_" select="(../../@BKT_LANES_X * $MOD_BKTLANE_W)"/>
		<xsl:variable name="mp_proc_bkt_gaps_right_"  select="(../../@BKT_GAPS_X  * $MOD_BUCKET_G)"/>
		
		<xsl:variable name="mp_proc_h_"  select="(($MOD_LANE_H * 2) + (($BIF_H + $MOD_BIF_GAP_V) * $mp_proc_bifs_h_) + ($MOD_LABEL_H + $MOD_BIF_GAP_V))"/>	
		<xsl:variable name="mp_proc_y_"  select="($SharedBus_Y - ($PROC2SBS_GAP + $mp_proc_h_))"/>
		<xsl:variable name="mp_proc_x_"  select="($Inner_X + $mp_proc_gaps_right_ +  $mp_proc_mods_right_ + $mp_proc_bkt_lanes_right_ + $mp_proc_bkt_gaps_right_ + $mp_proc_lanes_right_)"/>
		
		<xsl:variable name="mp_proc_numSbsBkts_"  select="count(/EDKSYSTEM/BLKDSHAPES/SBSBUCKETS/SBSBUCKET[   (@PROCESSOR = $mp_proc_inst_)])"/>	
		
		<xsl:variable name="mp_proc_bktModsW_">
			<xsl:if test="($mp_proc_numSbsBkts_ &gt; 0)">
				<xsl:value-of select="(($MOD_BKTLANE_W * 2) + ($periMOD_W * $mp_proc_pbktW_) + ($MOD_BUCKET_G * ($mp_proc_pbktW_ - 1)))"/>	
			</xsl:if>
			<xsl:if test="not($mp_proc_numSbsBkts_ &gt; 0)">0</xsl:if>
		</xsl:variable> 
		
		<xsl:variable name="mp_proc_pstkModsW_" select="($mp_proc_pmodW_ * $periMOD_W)"/>
		
		<xsl:variable name="mp_proc_stack_w_">
			<xsl:if test="$mp_proc_bktModsW_ &gt; $mp_proc_pstkModsW_">
				<xsl:value-of select="$mp_proc_bktModsW_"/>
			</xsl:if>
			<xsl:if test="not($mp_proc_bktModsW_ &gt; $mp_proc_pstkModsW_)">
				<xsl:value-of select="$mp_proc_pstkModsW_"/>
			</xsl:if>
		</xsl:variable>
		
		<xsl:variable name="mp_stack_numMemus_"        select="count(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[((@PSTACK_BLKD_X = @PSTACK_BLKD_X) and (@MODCLASS = 'MEMORY_UNIT'))])"/>	
		
		<xsl:variable name="mp_stack_h_">
			<xsl:call-template name="_calc_MultiProc_Stack_Height">
				<xsl:with-param name="mpstack_blkd_x" select="(@PSTACK_BLKD_X)"/>
			</xsl:call-template>
		</xsl:variable>
		
		<xsl:variable name="mp_stack_y_"			   select="($SharedBus_Y - ($PROC2SBS_GAP + $Max_Proc_H + $Max_Proc_PerisAbvSbs_H + $mp_stack_h_))"/>

		<xsl:variable name="mp_stack_gaps_right_"      select="(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@PSTACK_BLKD_X = @PSTACK_BLKD_X)]/@GAPS_X 	  * $MOD_SHAPES_G)"/>
		<xsl:variable name="mp_stack_mods_right_"      select="(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@PSTACK_BLKD_X = @PSTACK_BLKD_X)]/@MODS_X      * $periMOD_W)"/>
		<xsl:variable name="mp_stack_lanes_right_"     select="(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@PSTACK_BLKD_X = @PSTACK_BLKD_X)]/@BUS_LANES_X * $BUS_LANE_W)"/>
		<xsl:variable name="mp_stack_bkt_lanes_right_" select="(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@PSTACK_BLKD_X = @PSTACK_BLKD_X)]/@BKT_LANES_X * $MOD_BKTLANE_W)"/>
		<xsl:variable name="mp_stack_bkt_gaps_right_"  select="(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@PSTACK_BLKD_X = @PSTACK_BLKD_X)]/@BKT_GAPS_X  * $MOD_BUCKET_G)"/>
		<xsl:variable name="mp_stack_x_"               select="($Inner_X + $mp_stack_gaps_right_ +  $mp_stack_mods_right_ + $mp_stack_bkt_lanes_right_ + $mp_stack_bkt_gaps_right_ + $mp_stack_lanes_right_)"/>
		
		<xsl:variable name="mp_stack_w_">
			<xsl:if test="($mp_stack_numMemus_ &gt; 0)">
				<xsl:value-of select="($periMOD_W * 2)"/>
			</xsl:if>
			<xsl:if test="not($mp_stack_numMemus_ &gt; 0)">
				<xsl:value-of select="$periMOD_W"/>
			</xsl:if>
		</xsl:variable>
		
		<xsl:variable name="mp_busLaneWestW_">
			<xsl:if test="(../../BUSCONNS[@ORIENTED = 'WEST'])">
				<xsl:value-of select="((../../BUSCONNS[@ORIENTED ='WEST']/@BUSLANE_W) * $BUS_LANE_W)"/>
			</xsl:if>
			<xsl:if test="not(../../BUSCONNS[@ORIENTED = 'WEST'])">0</xsl:if>
		</xsl:variable>
			
		<xsl:variable name="mp_busLaneEastW_">
			<xsl:if test="(../../BUSCONNS[@ORIENTED = 'EAST'])">
				<xsl:value-of select="((../../BUSCONNS[@ORIENTED ='EAST']/@BUSLANE_W) * $BUS_LANE_W)"/>
			</xsl:if>
			<xsl:if test="not(../../BUSCONNS[@ORIENTED = 'EAST'])">0</xsl:if>
		</xsl:variable>
		
		<!-- all the connections will be on the same line..	 -->	
		<xsl:variable name="mp_bc_x_" >
			<xsl:if test="$oriented_= 'EAST'">
				<xsl:value-of select="($mp_proc_x_ + $mp_busLaneWestW_ + $mp_proc_stack_w_ + ((@BUSLANE_X + 1) * $BUS_LANE_W))"/>
			</xsl:if>	
				
			<xsl:if test="$oriented_= 'WEST'">
				<xsl:value-of select="($mp_proc_x_ + $mp_busLaneWestW_ + - ((@BUSLANE_X + 1) * $BUS_LANE_W))"/>
			</xsl:if>	
		</xsl:variable>  
		
<!--		
		<rect 
              x="{$mp_bc_x_}"
			  y="{$mp_stack_y_}"
		      width= "4"
		      height="700"
			  style="fill:{$COL_WHITE}; stroke:none;"/>		
-->	
				
			
		<xsl:for-each select="BUSCONN">
			<xsl:choose>
				
				<!-- A processor connection -->		
				<xsl:when test="(@PBIF_Y and @BIFRANK)">
					
					<xsl:variable name="mp_proc_bif_dy_" select="((($BIF_H + $MOD_BIF_GAP_V) * @PBIF_Y) + ($MOD_LABEL_H + $MOD_BIF_GAP_V + $MOD_LANE_H))"/>	
					<xsl:variable name="mp_proc_bif_y_" select="$mp_proc_y_ + $mp_proc_bif_dy_"/>
<!--					
					<xsl:variable name="mp_proc_bif_y_" select="$mp_proc_y_ + $mp_proc_bif_dy_  - ceiling($BIFC_H div 2) + ($BUS_ARROW_G * 2)"/>
-->	
					
					<use   x="{$mp_bc_x_ - ceiling($BIFC_W div 2)}"
		       			   y="{$mp_proc_bif_y_}"
		       				xlink:href="#{../@BUSSTD}_busconn_{@BIFRANK}"/>
					
					<xsl:if test="$oriented_ = 'EAST'">
						<xsl:variable name="east_bif_x_" select="($mp_proc_x_ + $mp_busLaneWestW_ + ceiling($mp_proc_stack_w_ div 2) + ceiling($periMOD_W div 2) - $MOD_LANE_W)"/>
						<line x1="{$mp_bc_x_}" 
			          		  y1="{$mp_proc_bif_y_ + ceiling($BIFC_H div 2)}" 
			                  x2="{$east_bif_x_}" 
			          		  y2="{$mp_proc_bif_y_ + ceiling($BIFC_H div 2)}" 
			  		          style="stroke:{$busColor_};stroke-width:1"/>
					</xsl:if>
					
					<xsl:if test="$oriented_ = 'WEST'">
						<xsl:variable name="west_bif_x_" select="($mp_proc_x_ + $mp_busLaneWestW_ + ceiling($mp_proc_stack_w_ div 2) - ceiling($periMOD_W div 2) + $MOD_LANE_W)"/>
						<line x1="{$mp_bc_x_}" 
			          		  y1="{$mp_proc_bif_y_ + ceiling($BIFC_H div 2)}" 
			                  x2="{$west_bif_x_}" 
			          		  y2="{$mp_proc_bif_y_ + ceiling($BIFC_H div 2)}" 
			  		          style="stroke:{$busColor_};stroke-width:1"/>
					</xsl:if>
					
				</xsl:when>
				
				
				<!-- A non processor connection from some peripheral in the stack-->		
				<xsl:when test="(@BIF_Y and @CSTACK_MODS_Y and @CSTACK_INDEX and @BIFRANK)">
<!--					
					<xsl:variable name="mp_peri_bif_dy_" select="((($BIF_H + $BIF_GAP) * @PBIF_Y) + ($MOD_LABEL_H + $BIF_GAP + $MOD_LANE_H))"/>	
					<xsl:variable name="mp_peri_bif_y_" select="$mp_proc_y_ + $mp_proc_bif_dy_"/>
					<xsl:with-param name="cstackModY"  select="@CSTACK_MODS_Y"/>
-->	
					
					<xsl:variable name="mp_stack_mod_h_">
						<xsl:call-template name="_calc_CStackShapesAbv_Height">
							<xsl:with-param name="cstkIndex"  select="@CSTACK_INDEX"/>
							<xsl:with-param name="cstkMods_Y" select="@CSTACK_MODS_Y"/>
						</xsl:call-template>	
					</xsl:variable>
					
					<xsl:variable name="mp_stack_mod_y_" select="$mp_stack_y_ + $mp_stack_mod_h_"/>
					
					<xsl:variable name="mp_stack_mod_dy_" >
						<xsl:if test="not(@IS_MEMBIF)">
							<xsl:value-of select="($MOD_LANE_H + $MOD_LABEL_H + $MOD_BIF_GAP_V + (@BIF_Y * ($BIF_H + $MOD_BIF_GAP_V)) + ceiling($BIF_H div 2))"/>
						</xsl:if>
				
						<xsl:if test="@IS_MEMBIF">
							<xsl:value-of select="($periMOD_H +  $MOD_LANE_H + ceiling($BIF_H div 2))"/>
						</xsl:if> </xsl:variable>  
					
					<use   x="{$mp_bc_x_ - ceiling($BIFC_W div 2)}"
		       			   y="{$mp_stack_mod_y_ + $mp_stack_mod_dy_ - ceiling($BIFC_H div 2)}"
		       				xlink:href="#{../@BUSSTD}_busconn_{@BIFRANK}"/>
					
					<xsl:if test="$oriented_ = 'WEST'">
						<line x1="{$mp_stack_x_ + $periMOD_W - $MOD_LANE_W}" 
			          		  y1="{$mp_stack_mod_y_  + $mp_stack_mod_dy_}" 
			          		  x2="{$mp_bc_x_}" 
			          		  y2="{$mp_stack_mod_y_  + $mp_stack_mod_dy_}" 
			  		  		  style="stroke:{$busColor_};stroke-width:1"/>
					</xsl:if>		
					
					<xsl:if test="$oriented_ = 'EAST'">
						<line x1="{$mp_bc_x_}" 
			          		  y1="{$mp_stack_mod_y_  + $mp_stack_mod_dy_}" 
			          		  x2="{$mp_stack_x_ + $MOD_LANE_W}" 
			          		  y2="{$mp_stack_mod_y_  + $mp_stack_mod_dy_}" 
			  		  		style="stroke:{$busColor_};stroke-width:1"/>
					</xsl:if>		
			  
					
				</xsl:when>
				
				
				<xsl:otherwise>
				</xsl:otherwise>		
			</xsl:choose>
		</xsl:for-each>
			
		
		<!-- Store the bus conn Ys in a variable to use to draw the P2P bus -->	
		<xsl:variable name="busConn_Ys_">
		<xsl:for-each select="BUSCONN">
			<xsl:choose>
				
				<!-- A processor connection -->		
				<xsl:when test="(@PBIF_Y and @BIFRANK)">
					
					<xsl:variable name="mp_proc_bif_dy_" select="((($BIF_H + $MOD_BIF_GAP_V) * @PBIF_Y) + ($MOD_LABEL_H + $MOD_BIF_GAP_V + $MOD_LANE_H))"/>	
					<xsl:variable name="mp_proc_bif_y_" select="$mp_proc_y_ + $mp_proc_bif_dy_"/>
					
					<BUSCONN Y="{$mp_proc_bif_y_}"/>
					
				</xsl:when>
				
				<!-- A non processor connection from some peripheral in the stack-->		
				<xsl:when test="(@BIF_Y and @CSTACK_MODS_Y and @CSTACK_INDEX and @BIFRANK)">
					
					<xsl:variable name="mp_stack_mod_h_">
						<xsl:call-template name="_calc_CStackShapesAbv_Height">
							<xsl:with-param name="cstkIndex"  select="@CSTACK_INDEX"/>
							<xsl:with-param name="cstkMods_Y" select="@CSTACK_MODS_Y"/>
						</xsl:call-template>	
					</xsl:variable>
					
					<xsl:variable name="mp_stack_mod_y_" select="$mp_stack_y_ + $mp_stack_mod_h_"/>
					
					<xsl:variable name="mp_stack_mod_dy_" >
						<xsl:if test="not(@IS_MEMBIF)">
							<xsl:value-of select="($MOD_LANE_H + $MOD_LABEL_H + $MOD_BIF_GAP_V + (@BIF_Y * ($BIF_H + $MOD_BIF_GAP_V)) + ceiling($BIF_H div 2))"/>
						</xsl:if>
				
						<xsl:if test="@IS_MEMBIF">
							<xsl:value-of select="($periMOD_H +  $MOD_LANE_H + ceiling($BIF_H div 2))"/>
						</xsl:if> </xsl:variable>  
					
					<BUSCONN Y="{$mp_stack_mod_y_ + $mp_stack_mod_dy_ - ceiling($BIFC_H div 2)}"/>
					
				</xsl:when>
				
				
				<xsl:otherwise>
				</xsl:otherwise>		
			</xsl:choose>
		</xsl:for-each>
			
		</xsl:variable>
		
		
<!--		
		<xsl:message>MAX Height is <xsl:value-of select="math:max(exsl:node-set($busConn_Ys_)/BUSCONN/@Y)"/></xsl:message>
		<xsl:message>MIN Height is <xsl:value-of select="math:min(exsl:node-set($busConn_Ys_)/BUSCONN/@Y)"/></xsl:message>
-->	
		
		<xsl:call-template name="Draw_P2PBus">
			<xsl:with-param name="busX"    select="$mp_bc_x_ - ceiling($BIFC_W div 2)"/>
			<xsl:with-param name="busTop"  select="math:min(exsl:node-set($busConn_Ys_)/BUSCONN/@Y)"/>
			<xsl:with-param name="busBot"  select="math:max(exsl:node-set($busConn_Ys_)/BUSCONN/@Y)"/>
			<xsl:with-param name="busStd"  select="@BUSSTD"/>
			<xsl:with-param name="busName" select="@BUSNAME"/>
		</xsl:call-template>
			
	</xsl:for-each>		
	
	
	<!--
		 ============================================================ 
	        Draw Multiproc connections to the shared busses 
		 ============================================================ 
	 -->	
	
	<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/PROCSHAPES/MODULE/BUSCONNS/BUSCONN[(@IS_MULTIPROC and not(@IS_SPLITCONN) and @BUSINDEX and @BIF_Y and @BUSLANE_X and @BUSSTD and @BIFRANK)]">
		
<!--		
		<xsl:message>Reached Shared bus Multi Processor connections loop</xsl:message>
-->		
			
		<xsl:variable name="oriented_"         select="../@ORIENTED"/>
		<xsl:variable name="busName_"          select="@BUSNAME"/>
		
		<xsl:variable name="busColor_">
			<xsl:call-template name="BusType2Color">
				<xsl:with-param name="busType" select="@BUSSTD"/>
			</xsl:call-template>	
		</xsl:variable>
		
		<xsl:variable name="mp_proc_inst_"    select="../../@INSTANCE"/>
		<xsl:variable name="mp_proc_bifs_h_"  select="../../@BIFS_H"/>
		<xsl:variable name="mp_proc_bifs_w_"  select="../../@BIFS_W"/>
		<xsl:variable name="mp_proc_pbktW_"   select="../../@PSTACK_BKT_W"/>
		<xsl:variable name="mp_proc_pbktH_"   select="../../@PSTACK_BKT_H"/>
		<xsl:variable name="mp_proc_pmodW_"   select="../../@PSTACK_MOD_W"/>
		<xsl:variable name="mp_proc_pmodH_"   select="../../@PSTACK_MOD_H"/>
		
		<xsl:variable name="mp_proc_gaps_right_"      select="(../../@GAPS_X      * $MOD_SHAPES_G)"/>
		<xsl:variable name="mp_proc_mods_right_"      select="(../../@MODS_X      * $periMOD_W)"/>
		<xsl:variable name="mp_proc_lanes_right_"     select="(../../@BUS_LANES_X * $BUS_LANE_W)"/>
		<xsl:variable name="mp_proc_bkt_lanes_right_" select="(../../@BKT_LANES_X * $MOD_BKTLANE_W)"/>
		<xsl:variable name="mp_proc_bkt_gaps_right_"  select="(../../@BKT_GAPS_X  * $MOD_BUCKET_G)"/>
		
		<xsl:variable name="mp_proc_h_"  select="(($MOD_LANE_H * 2) + (($BIF_H + $MOD_BIF_GAP_V) * $mp_proc_bifs_h_) + ($MOD_LABEL_H + $MOD_BIF_GAP_V))"/>
		<xsl:variable name="mp_proc_y_"  select="($SharedBus_Y - ($PROC2SBS_GAP + $mp_proc_h_))"/>
		<xsl:variable name="mp_proc_x_"  select="($Inner_X + $mp_proc_gaps_right_ +  $mp_proc_mods_right_ + $mp_proc_bkt_lanes_right_ + $mp_proc_bkt_gaps_right_ + $mp_proc_lanes_right_)"/>
		
		<xsl:variable name="mp_proc_numSbsBkts_"  select="count(/EDKSYSTEM/BLKDSHAPES/SBSBUCKETS/SBSBUCKET[   (@PROCESSOR = $mp_proc_inst_)])"/>	
		
		<xsl:variable name="mp_proc_bktModsW_">
			<xsl:if test="($mp_proc_numSbsBkts_ &gt; 0)">
				<xsl:value-of select="(($MOD_BKTLANE_W * 2) + ($periMOD_W * $mp_proc_pbktW_) + ($MOD_BUCKET_G * ($mp_proc_pbktW_ - 1)))"/>	
			</xsl:if>
			<xsl:if test="not($mp_proc_numSbsBkts_ &gt; 0)">0</xsl:if>
		</xsl:variable> 
		
		<xsl:variable name="mp_proc_pstkModsW_" select="($mp_proc_pmodW_ * $periMOD_W)"/>
		
		<xsl:variable name="mp_proc_stack_w_">
			<xsl:if test="$mp_proc_bktModsW_ &gt; $mp_proc_pstkModsW_">
				<xsl:value-of select="$mp_proc_bktModsW_"/>
			</xsl:if>
			<xsl:if test="not($mp_proc_bktModsW_ &gt; $mp_proc_pstkModsW_)">
				<xsl:value-of select="$mp_proc_pstkModsW_"/>
			</xsl:if>
		</xsl:variable>
		
		<xsl:variable name="mp_stack_numMemus_"        select="count(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[((@PSTACK_BLKD_X = @PSTACK_BLKD_X) and (@MODCLASS = 'MEMORY_UNIT'))])"/>	
		
		<xsl:variable name="mp_stack_h_">
			<xsl:call-template name="_calc_MultiProc_Stack_Height">
				<xsl:with-param name="mpstack_blkd_x" select="(@PSTACK_BLKD_X)"/>
			</xsl:call-template>
		</xsl:variable>
		
		<xsl:variable name="sbus_bc_y_" 			   select="($SharedBus_Y + (@BUSINDEX * $SBS_LANE_H))"/>
		<xsl:variable name="mp_stack_y_"			   select="($SharedBus_Y - ($PROC2SBS_GAP + $Max_Proc_H + $Max_Proc_PerisAbvSbs_H + $mp_stack_h_))"/>

		<xsl:variable name="mp_stack_gaps_right_"      select="(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@PSTACK_BLKD_X = @PSTACK_BLKD_X)]/@GAPS_X 	  * $MOD_SHAPES_G)"/>
		<xsl:variable name="mp_stack_mods_right_"      select="(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@PSTACK_BLKD_X = @PSTACK_BLKD_X)]/@MODS_X      * $periMOD_W)"/>
		<xsl:variable name="mp_stack_lanes_right_"     select="(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@PSTACK_BLKD_X = @PSTACK_BLKD_X)]/@BUS_LANES_X * $BUS_LANE_W)"/>
		<xsl:variable name="mp_stack_bkt_lanes_right_" select="(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@PSTACK_BLKD_X = @PSTACK_BLKD_X)]/@BKT_LANES_X * $MOD_BKTLANE_W)"/>
		<xsl:variable name="mp_stack_bkt_gaps_right_"  select="(/EDKSYSTEM/BLKDSHAPES/CMPLXSHAPES/CMPLXSHAPE[(@PSTACK_BLKD_X = @PSTACK_BLKD_X)]/@BKT_GAPS_X  * $MOD_BUCKET_G)"/>
		<xsl:variable name="mp_stack_x_"               select="($Inner_X + $mp_stack_gaps_right_ +  $mp_stack_mods_right_ + $mp_stack_bkt_lanes_right_ + $mp_stack_bkt_gaps_right_ + $mp_stack_lanes_right_)"/>
		
		<xsl:variable name="mp_stack_w_">
			<xsl:if test="($mp_stack_numMemus_ &gt; 0)">
				<xsl:value-of select="($periMOD_W * 2)"/>
			</xsl:if>
			<xsl:if test="not($mp_stack_numMemus_ &gt; 0)">
				<xsl:value-of select="$periMOD_W"/>
			</xsl:if>
		</xsl:variable>
		
		<xsl:variable name="mp_busLaneWestW_">
			<xsl:if test="(../../BUSCONNS[@ORIENTED = 'WEST'])">
				<xsl:value-of select="((../../BUSCONNS[@ORIENTED ='WEST']/@BUSLANE_W) * $BUS_LANE_W)"/>
			</xsl:if>
			<xsl:if test="not(../../BUSCONNS[@ORIENTED = 'WEST'])">0</xsl:if>
		</xsl:variable>
			
		<xsl:variable name="mp_busLaneEastW_">
			<xsl:if test="(../../BUSCONNS[@ORIENTED = 'EAST'])">
				<xsl:value-of select="((../../BUSCONNS[@ORIENTED ='EAST']/@BUSLANE_W) * $BUS_LANE_W)"/>
			</xsl:if>
			<xsl:if test="not(../../BUSCONNS[@ORIENTED = 'EAST'])">0</xsl:if>
		</xsl:variable>
<!--		
-->	
	
		<xsl:variable name="mp_stack_dx_" >
			
			<xsl:if test="$oriented_= 'WEST'">
				<xsl:if test="@IS_MEMBIF= 'TRUE'">
					<xsl:value-of select="(($mp_stack_w_ div 2) + ($periMOD_W - $MOD_LANE_W))"/>
				</xsl:if>	
				
				<xsl:if test="not(@IS_MEMBIF= 'TRUE')">
					<xsl:value-of select="(($mp_stack_w_ div 2) + (($periMOD_W div 2) - $MOD_LANE_W))"/>
				</xsl:if>	
			</xsl:if>
			
			<xsl:if test="$oriented_= 'EAST'">
				<xsl:if test="@IS_MEMBIF= 'TRUE'">
					<xsl:value-of select="(($mp_stack_w_ div 2) - ($periMOD_W - $MOD_LANE_W))"/>
				</xsl:if>	
				
				<xsl:if test="not(@IS_MEMBIF= 'TRUE')">
					<xsl:value-of select="(($mp_stack_w_ div 2) - (($periMOD_W div 2) - $MOD_LANE_W))"/>
				</xsl:if>	
			</xsl:if>	
			
		</xsl:variable>  
		
		<xsl:variable name="mp_stack_mod_h_">
			<xsl:call-template name="_calc_CStackShapesAbv_Height">
				<xsl:with-param name="cstkIndex"  select="@CSTACK_INDEX"/>
				<xsl:with-param name="cstkMods_Y" select="@CSTACK_MODS_Y"/>
			</xsl:call-template>	
		</xsl:variable>
		
		<xsl:variable name="mp_stack_mod_y_" select="$mp_stack_y_ + $mp_stack_mod_h_"/>
		
		<xsl:variable name="mp_stack_mod_dy_" >
			<xsl:if test="not(@IS_MEMBIF)">
				<xsl:value-of select="($MOD_LANE_H + $MOD_LABEL_H + $MOD_BIF_GAP_V + (@BIF_Y * ($BIF_H + $MOD_BIF_GAP_V)) + ceiling($BIF_H div 2))"/>
			</xsl:if>
				
			<xsl:if test="@IS_MEMBIF">
				<xsl:value-of select="($periMOD_H +  $MOD_LANE_H + ceiling($BIF_H div 2))"/>
			</xsl:if>
		</xsl:variable>  
		
		<xsl:variable name="mp_sbs_bc_x_" >
			<xsl:if test="$oriented_= 'EAST'">
				<xsl:value-of select="($mp_proc_x_ + $mp_busLaneWestW_ + $mp_proc_stack_w_ + ((@BUSLANE_X + 1) * $BUS_LANE_W))"/>
			</xsl:if>	
				
			<xsl:if test="$oriented_= 'WEST'">
				<xsl:value-of select="($mp_proc_x_ + $mp_busLaneWestW_ + - ((@BUSLANE_X + 1) * $BUS_LANE_W))"/>
			</xsl:if>	
		</xsl:variable>  
		
		<use   x="{$mp_sbs_bc_x_ - ceiling($BIFC_W div 2)}"    
		       y="{$sbus_bc_y_         - ceiling($BIFC_H div 2) + ($BUS_ARROW_G * 2)}"   
		       xlink:href="#{@BUSSTD}_busconn_{@BIFRANK}"/>
		
		<!-- Horizontal line out from module -->		
		<xsl:choose>
			<xsl:when test="$oriented_ = 'EAST'">
				<line x1="{$mp_sbs_bc_x_}" 
			          y1="{$mp_stack_mod_y_  + $mp_stack_mod_dy_}" 
			          x2="{$mp_stack_x_ + $MOD_LANE_W}" 
			          y2="{$mp_stack_mod_y_  + $mp_stack_mod_dy_}" 
			  		  style="stroke:{$busColor_};stroke-width:1"/>
			</xsl:when>
			<xsl:otherwise>
				<line x1="{$mp_sbs_bc_x_}" 
			          y1="{$mp_stack_mod_y_  + $mp_stack_mod_dy_}" 
			          x2="{$mp_stack_x_ + $MOD_LANE_W}" 
			          y2="{$mp_stack_mod_y_  + $mp_stack_mod_dy_}" 
			  		  style="stroke:{$busColor_};stroke-width:1"/>
			</xsl:otherwise>		
		</xsl:choose>
			  
		<!-- Vertical line down to shared bus -->		
		<line x1="{$mp_sbs_bc_x_}" 
			  y1="{$mp_stack_mod_y_  + $mp_stack_mod_dy_}" 
			  x2="{$mp_sbs_bc_x_}" 
			  y2="{$sbus_bc_y_ + ceiling($BIFC_H div 2)}" 
			  style="stroke:{$busColor_};stroke-width:1"/>
			  
<!--			  
		<xsl:message>==============================================</xsl:message>
		<xsl:message>Busname <xsl:value-of select="$busName_"/></xsl:message>
		<xsl:message>====<xsl:value-of select="$mp_stack_h_"/></xsl:message>
		<xsl:message>====<xsl:value-of select="$mp_proc_y_"/></xsl:message>
		<xsl:message>====<xsl:value-of select="$mp_stack_y_"/></xsl:message>
		<xsl:message>====<xsl:value-of select="$mp_stack_mod_begX_"/></xsl:message>
		<xsl:message>====<xsl:value-of select="$mp_stack_mod_endX_"/></xsl:message>
		<xsl:message>====<xsl:value-of select="$mp_stack_mod_y_"/></xsl:message>
		<xsl:message>====<xsl:value-of select="$mp_stack_mod_dy_"/></xsl:message>
		<xsl:message>=============================================</xsl:message>
-->
			      
	</xsl:for-each>		
	
</xsl:template>
	
	
<xsl:template name="Draw_BlkDiagram_Key">
	<xsl:param name="blkd_w"     select="820"/>
	<xsl:param name="blkd_h"     select="520"/>
	<xsl:param name="drawarea_w" select="800"/>
	<xsl:param name="drawarea_h" select="500"/>
	<use   x="{ceiling($blkd_w div 2) - ceiling($BLKD_KEY_W div 2)}"   y="0"  xlink:href="#BlkDiagram_Key"/> 
</xsl:template>

<xsl:template name="Define_BlkDiagram_Key">
	
	<xsl:variable name="key_col_">
		<xsl:call-template name="BusType2Color">
			<xsl:with-param name="busType" select="'KEY'"/>
		</xsl:call-template>	
	</xsl:variable>
	
	<xsl:variable name="key_lt_col_">
		<xsl:call-template name="BusType2LightColor">
			<xsl:with-param name="busType" select="'KEY'"/>
		</xsl:call-template>	
	</xsl:variable>
	
	<symbol id="KEY_IntrCntrl">
		<rect  
			x="0"
			y="0"
			rx="3"
			ry="3"
			width= "{ceiling($INTR_W div 2)}" 
			height="{$INTR_H}" style="fill:{$key_lt_col_}; stroke:none; stroke-width:1"/> 
			
		<line x1="0" 
			  y1="{ceiling($INTR_H div 4)}"
			  x2="{ceiling($INTR_W div 2)}" 
			  y2="{ceiling($INTR_H div 4)}" 
			  style="stroke:{$COL_BLACK};stroke-width:2"/>
			  
		<text class="intrsymbol" 
			  x="1.5"
			  y="{7 + ceiling($INTR_H div 2)}">x</text>
			
	</symbol>
		
	<symbol id="KEY_IntrdProc">
		<rect  
			x="0"
			y="0"
			rx="3"
			ry="3"
			width= "{ceiling($INTR_W div 2)}" 
			height="{$INTR_H}" style="fill:{$key_lt_col_}; stroke:none; stroke-width:1"/> 
			
		<line x1="0" 
			  y1="{ceiling($INTR_H div 4) - 2}"
			  x2="{ceiling($INTR_W div 2)}" 
			  y2="{ceiling($INTR_H div 4) - 2}" 
			  style="stroke:{$COL_BLACK};stroke-width:1"/>
			  
		<line x1="0" 
			  y1="{ceiling($INTR_H div 4) + 2}"
			  x2="{ceiling($INTR_W div 2)}" 
			  y2="{ceiling($INTR_H div 4) + 2}" 
			  style="stroke:{$COL_BLACK};stroke-width:1"/>
			  
		<text class="intrsymbol" 
			  x="1.5"
			  y="{7 + ceiling($INTR_H div 2)}">x</text>
	</symbol>
	
	<symbol id="KEY_IntrSrc">
		<rect  
			x="0"
			y="0"
			rx="3"
			ry="3"
			width= "{$INTR_W}" 
			height="{ceiling($INTR_H div 2)}" style="fill:{$key_lt_col_}; stroke:none; stroke-width:1"/> 
			
		<line x1="{ceiling($INTR_W div 2)}" 
			  y1="0"
			  x2="{ceiling($INTR_W div 2)}" 
			  y2="{ceiling($INTR_H div 2)}" 
			  style="stroke:{$COL_BLACK};stroke-width:1"/>
			  
		<text class="intrsymbol" 
			  x="2"
			  y="7">y</text>
			
		<text class="intrsymbol" 
			  x="{2 + ceiling($INTR_W div 2)}"
			  y="7">x</text>
	</symbol>
	
	
	<symbol id="BlkDiagram_Key">
		<rect 
              x="0"
			  y="0"
		      width= "{$BLKD_KEY_W}"
		      height="{$BLKD_KEY_H}"
			  style="fill:{$COL_BG}; stroke:none;"/>		
			  
		<rect 
              x="0"
			  y="0"
		      width= "{$BLKD_KEY_W}"
		      height="16"
			  style="fill:{$COL_BG}; stroke:none;"/>		
			  
		<text class="keytitle"
              x="{ceiling($BLKD_KEY_W div 2)} "
			  y="14">KEY</text>		  
			  
		<rect 
              x="0"
			  y="16"
		      width= "{$BLKD_KEY_W}"
		      height="16"
			  style="fill:{$COL_BG_LT}; stroke:none;"/>		
			  
		<text class="keyheader"
              x="{ceiling($BLKD_KEY_W div 2)} "
			  y="30">SYMBOLS</text>		  
			  
   		<use  x="32"  y="47"  xlink:href="#KEY_Bif" transform="scale(0.75)"/> 
		<text class="keylabel"
              x="12"
			  y="60">bus interface</text>		  
			  
   		<use   x="20"  y="68"  xlink:href="#KEY_SharedBus"/> 
		<text class="keylabel"
              x="12"
			  y="85">shared bus</text>		  
			  
		<text class="keylblul"
              x="110"
			  y="47">Bus connections</text>		  
			  
   		<use   x="110"  y="58"  xlink:href="#KEY_busconn_MASTER"/> 
		<text class="keylabel"
              x="140"
			  y="72">master or initiator</text>		  
			  
   		<use   x="110"  y="{58 + (($BIFC_H  + 4) * 1)}"  xlink:href="#KEY_busconn_SLAVE"/> 
		<text class="keylabel"
              x="140"
			  y="{72 + (($BIFC_H + 4) * 1)}">slave or target</text>		  
			  
   		<use   x="110"  y="{58 + (($BIFC_H  + 4) * 2)}"  xlink:href="#KEY_busconn_MASTER_SLAVE"/> 
		<text class="keylabel"
              x="140"
			  y="{72 + (($BIFC_H + 4) * 2)}">master slave</text>		  
			  
   		<use   x="110"  y="{58 + (($BIFC_H  + 4) * 3)}"  xlink:href="#KEY_busconn_MONITOR"/>
		<text class="keylabel"
              x="140"
			  y="{72 + (($BIFC_H + 4) * 3)}">monitor</text>		  
			  
		<text class="keylblul"
              x="258"
			  y="47">External Ports</text>		  
		
   		<use   x="258"  y="58"  xlink:href="#KEY_INPort"/> 
		<text class="keylabel"
              x="288"
			  y="72">input</text>		  
			  
   		<use   x="258"  y="{58 + ($IOP_H * 1) + 4}"  xlink:href="#KEY_OUTPort"/> 
		<text class="keylabel"
              x="288"
			  y="{72 + ($IOP_H * 1) + 4}">output</text>		  
			  
   		<use   x="258" y="{58 + ($IOP_H * 2) + 8}"  xlink:href="#KEY_INOUTPort"/> 
		<text class="keylabel"
              x="288"
			  y="{72 + ($IOP_H * 2) + 8}">inout</text>		  
		
		
		<text class="keylblul"
              x="380"
			  y="47">Interrupts</text>
		
   		<use   x="380"  y="58"  xlink:href="#KEY_IntrCntrl"/> 
		<text class="keylabel"
              x="396"
			  y="64">interrupt</text>		  
		<text class="keylabel"
              x="396"
			  y="74">controller</text>		  
			  
		
		<use   x="380"  y="88"  xlink:href="#KEY_IntrdProc"/> 
		<text class="keylabel"
              x="396"
			  y="94">interrupted</text>		  
		<text class="keylabel"
              x="396"
			  y="104">processor</text>		  
			  
		
		<use   x="380"  y="118"  xlink:href="#KEY_IntrSrc"/> 
		<text class="keylabel"
              x="400"
			  y="124">interrupt</text>		  
		<text class="keylabel"
              x="400"
			  y="134">source</text>		  
		
		<text class="keylabel"
              x="360"
			  y="146">x = controller ID</text>		  
		
		<text class="keylabel"
              x="360"
			  y="156">y = priority</text>		  
<!--		
		<text class="keylabel"
              x="400"
			  y="134">source</text>		  
	
-->
			  
		
		
		
		
		
		<rect 
              x="0"
			  y="160"
		      width= "{$BLKD_KEY_W}"
		      height="16"
			  style="fill:{$COL_BG_LT}; stroke:none;"/>		
			  
		<text class="keyheader"
              x="{ceiling($BLKD_KEY_W div 2)} "
			  y="172">COLORS</text>		  
		
			  
		<text class="keylblul"
              x="110"
			  y="190">Bus Standards</text>		  
			  
		<xsl:variable name="dcr_col_">
			<xsl:call-template name="BusType2Color">
				<xsl:with-param name="busType" select="'DCR'"/>
			</xsl:call-template>	
		</xsl:variable>
		
		<rect 
              x="{12 + ((12 + $BIFC_W + 36) * 0)}"
			  y="200"
		      width= "{$BIFC_H}"
		      height="{$BIFC_W}"
			  style="fill:{$dcr_col_}; stroke:none;"/>		
		<text class="keylabel"
              x="{12 + $BIFC_W + 4}"
			  y="{200 + (($BIF_H + 4) * 1)}">DCR</text>		  
			  
		<xsl:variable name="fcb_col_">
			<xsl:call-template name="BusType2Color">
				<xsl:with-param name="busType" select="'FCB'"/>
			</xsl:call-template>	
		</xsl:variable>
		
		<rect 
              x="{12 + ((12 + $BIFC_W + 36) * 0)}"
			  y="{200 + (($BIFC_H + 4) * 1)}"
		      width= "{$BIFC_H}"
		      height="{$BIFC_W}"
			  style="fill:{$fcb_col_}; stroke:none;"/>		
		<text class="keylabel"
              x="{12 + $BIFC_W + 4}"
			  y="{200 + (($BIF_H + 4) * 2)}">FCB</text>		  
		
		<xsl:variable name="fsl_col_">
			<xsl:call-template name="BusType2Color">
				<xsl:with-param name="busType" select="'FSL'"/>
			</xsl:call-template>	
		</xsl:variable>
			  
		<rect 
              x="{12 + ((12 + $BIFC_W + 36) * 1)}"
			  y="200"
		      width= "{$BIFC_H}"
		      height="{$BIFC_W}"
			  style="fill:{$fsl_col_}; stroke:none;"/>		
		<text class="keylabel"
              x="{12  + ($BIFC_W + 4) + ((12 + $BIFC_W + 36) * 1)}"
			  y="{200 + (($BIF_H + 4) * 1)}">FSL</text>		  
		
		<xsl:variable name="col_lmb_">
			<xsl:call-template name="BusType2Color">
				<xsl:with-param name="busType" select="'LMB'"/>
			</xsl:call-template>	
		</xsl:variable>
			  
		<rect 
              x="{12 + ((12 + $BIFC_W + 36) * 1)}"
			  y="{200 + (($BIFC_H + 4) * 1)}"
		      width= "{$BIFC_H}"
		      height="{$BIFC_W}"
			  style="fill:{$col_lmb_}; stroke:none;"/>		
		<text class="keylabel"
              x="{12  + ($BIFC_W + 4) + ((12 + $BIFC_W + 36) * 1)}"
			  y="{200 + (($BIF_H + 4) * 2)}">LMB</text>		  
			  
		
		<xsl:variable name="opb_col_">
			<xsl:call-template name="BusType2Color">
				<xsl:with-param name="busType" select="'OPB'"/>
			</xsl:call-template>	
		</xsl:variable>
			  
		<rect 
              x="{12 + ((12 + $BIFC_W + 36) * 2)}"
			  y="200"
		      width= "{$BIFC_H}"
		      height="{$BIFC_W}"
			  style="fill:{$opb_col_}; stroke:none;"/>		
		<text class="keylabel"
              x="{12  + ($BIFC_W + 4) + ((12 + $BIFC_W + 36) * 2)}"
			  y="{200 + (($BIF_H + 4) * 1)}">OPB</text>		  
		
		<xsl:variable name="plb_col_">
			<xsl:call-template name="BusType2Color">
				<xsl:with-param name="busType" select="'PLB'"/>
			</xsl:call-template>	
		</xsl:variable>
		
		<rect 
              x="{12 + ((12 + $BIFC_W + 36) * 2)}"
			  y="{200 + (($BIFC_H + 4) * 1)}"
		      width= "{$BIFC_H}"
		      height="{$BIFC_W}"
			  style="fill:{$plb_col_}; stroke:none;"/>		
		<text class="keylabel"
              x="{12  + ($BIFC_W + 4) + ((12 + $BIFC_W + 36) * 2)}"
			  y="{200 + (($BIF_H + 4) * 2)}">PLB</text>		  
		
			 
		<xsl:variable name="ocm_col_">
			<xsl:call-template name="BusType2Color">
				<xsl:with-param name="busType" select="'OCM'"/>
			</xsl:call-template>	
		</xsl:variable>
			  
		<rect 
              x="{12 + ((12 + $BIFC_W + 36) * 3)}"
			  y="200"
		      width= "{$BIFC_H}"
		      height="{$BIFC_W}"
			  style="fill:{$ocm_col_}; stroke:none;"/>		
		<text class="keylabel"
              x="{12  + ($BIFC_W + 4) + ((12 + $BIFC_W + 36) * 3)}"
			  y="{200 + (($BIF_H + 4) * 1)}">SOCM</text>
		
		
		<xsl:variable name="xil_col_">
			<xsl:call-template name="BusType2Color">
				<xsl:with-param name="busType" select="'XIL'"/>
			</xsl:call-template>	
		</xsl:variable>
			  
		<rect 
              x="{12 + ((12 + $BIFC_W + 36) * 3)}"
			  y="{200 + (($BIFC_H + 4) * 1)}"
		      width= "{$BIFC_H}"
		      height="{$BIFC_W}"
			  style="fill:{$xil_col_}; stroke:none;"/>		
		<text class="keylabel"
              x="{12  + ($BIFC_W + 4) + ((12 + $BIFC_W + 36) * 3)}"
			  y="{200 + (($BIF_H + 4) * 2)}">XIL (prefix) P2P</text>		  
			 
			  
		<xsl:variable name="trs_col_">
			<xsl:call-template name="BusType2Color">
				<xsl:with-param name="busType" select="'TRS'"/>
			</xsl:call-template>	
		</xsl:variable>
			  
		<rect 
              x="{12 + ((12 + $BIFC_W + 36) * 4)}"
			  y="200"
		      width= "{$BIFC_H}"
		      height="{$BIFC_W}"
			  style="fill:{$trs_col_}; stroke:none;"/>		
		<text class="keylabel"
              x="{12  + ($BIFC_W + 4) + ((12 + $BIFC_W + 36) * 4)}"
			  y="{200 + (($BIF_H + 4) * 1)}">GEN. P2P, USER, etc</text>		  
			  
</symbol>	
</xsl:template>

<xsl:template name="Define_BlkDiagram_Specs">

	<xsl:param name="blkd_arch"     select="'NA'"/>
	<xsl:param name="blkd_part"     select="'NA'"/>
	<xsl:param name="blkd_edkver"   select="'NA'"/>
	<xsl:param name="blkd_gentime"  select="'NA'"/>
			
	<symbol id="BlkDiagram_Specs">
		<rect 
              x="0"
			  y="0"
		      width= "{$BLKD_SPECS_W}"
		      height="{$BLKD_SPECS_H}"
			  style="fill:{$COL_BG}; stroke:none;"/>		
			  
		<rect 
              x="0"
			  y="0"
		      width= "{$BLKD_SPECS_W}"
		      height="16"
			  style="fill:{$COL_BG}; stroke:none;"/>		
			  
		<text class="keytitle"
              x="{ceiling($BLKD_SPECS_W div 2)} "
			  y="14">SPECS</text>
			  
		<rect 
              x="0"
			  y="20"
		      width= "{$BLKD_SPECS_W}"
		      height="16"
			  style="fill:{$COL_BG_LT}; stroke:none;"/>		
			  
		<text class="specsheader"
              x="4"
			  y="32">EDK VERSION</text>
			  
<!--		
		<text class="specsvalue"
              x="{($BLKD_SPECS_W + 1) - (string-length($blkd_edkver) * 6.5)}"
			  y="32"><xsl:value-of select="$blkd_edkver"/></text>
-->		
		<text class="specsvaluemid"
              x="{($BLKD_SPECS_W + 1) - ceiling($BLKD_SPECS_W div 5)}"
			  y="32"><xsl:value-of select="$blkd_edkver"/></text>
			  
		<rect 
              x="0"
			  y="40"
		      width= "{$BLKD_SPECS_W}"
		      height="16"
			  style="fill:{$COL_BG_LT}; stroke:none;"/>		
			  
		<text class="specsheader"
              x="4"
			  y="52">ARCH</text>
			  
<!--		
		<text class="specsvalue"
              x="{($BLKD_SPECS_W + 1) - (string-length($blkd_arch) * 6.5)}"
			  y="52"><xsl:value-of select="$blkd_arch"/></text>
-->		
		<text class="specsvaluemid"
              x="{($BLKD_SPECS_W + 1) - ceiling($BLKD_SPECS_W div 5)}"
			  y="52"><xsl:value-of select="$blkd_arch"/></text>
			  
		<rect 
              x="0"
			  y="60"
		      width= "{$BLKD_SPECS_W}"
		      height="16"
			  style="fill:{$COL_BG_LT}; stroke:none;"/>		
			  
		<text class="specsheader"
              x="4"
			  y="72">PART</text>
			  
<!--		
		<text class="specsvalue"
              x="{($BLKD_SPECS_W  + 1) - ((string-length($blkd_part) + 2) * 6.5)}"
			  y="72"><xsl:value-of select="$blkd_part"/></text>
-->		
		<text class="specsvaluemid"
              x="{($BLKD_SPECS_W + 1) - ceiling($BLKD_SPECS_W div 5)}"
			  y="72"><xsl:value-of select="$blkd_part"/></text>
			  
		<rect 
              x="0"
			  y="80"
		      width= "{$BLKD_SPECS_W}"
		      height="16"
			  style="fill:{$COL_BG_LT}; stroke:none;"/>		
			  
		<text class="specsheader"
              x="4"
			  y="92">GENERATED</text>
			  
		<text class="specsvalue"
              x="{($BLKD_SPECS_W  + 1) - (string-length($blkd_gentime) * 6.5)}"
			  y="92"><xsl:value-of select="$blkd_gentime"/></text>
			  
			  
	</symbol>	
</xsl:template>
	

<xsl:template name="Draw_BlkdShapes_old">
	<xsl:param name="blkd_w"     select="820"/>
	<xsl:param name="blkd_h"     select="520"/>
	<xsl:param name="drawarea_w" select="800"/>
	<xsl:param name="drawarea_h" select="500"/>
	
	<xsl:variable name="inner_X_" select="($BLKD_PRTCHAN_W  + $BLKD_IORCHAN_W + $BLKD_INNER_GAP)"/>
	<xsl:variable name="inner_Y_" select="($BLKD_PRTCHAN_H  + $BLKD_IORCHAN_H + $BLKD_INNER_GAP)"/>
	
<!--	
	<xsl:message>Number mods above procs <xsl:value-of  select="$lmt_modsAbvProcsH_"/></xsl:message>
	<xsl:message>Number memus above procs <xsl:value-of select="$lmt_memusAbvProcsH_"/></xsl:message>
-->	

	<xsl:variable name="max_Proc_h_">
		<xsl:call-template name="_calc_Max_Proc_Height"/>
	</xsl:variable>
	
	<xsl:variable name="max_Proc_PerisAbvSbs_h_">
		<xsl:call-template name="_calc_Max_Proc_PerisAbvSbs_Height"/>
	</xsl:variable>
	
	<xsl:variable name="max_Proc_PerisBlwSbs_h_">
		<xsl:call-template name="_calc_Max_Proc_PerisBlwSbs_Height"/>
	</xsl:variable>
	
	<xsl:variable name="max_MultiProc_Stack_h_">
		<xsl:call-template name="_calc_Max_MultiProc_Stack_Height"/>
	</xsl:variable>
	
	<xsl:variable name="max_SbsBuckets_h_">
		<xsl:call-template name="_calc_Max_SbsBuckets_Height"/>		
	</xsl:variable>
	
	
<!--	
	<xsl:variable name="lmt_slvs_h_"  select="($lmt_slvsabv_sbs_h_  * ( $periMOD_H      + $BIF_H))"/>
-->	
	
	<xsl:variable name="numSbs_"    select="count(BLKDSHAPES/SBSSHAPES/MODULE)"/>			
	<xsl:variable name="numProcs_"  select="count(BLKDSHAPES/PROCSHAPES/MODULE)"/>			
<!--	
	
	<xsl:message>inner y  <xsl:value-of select="$inner_Y_"/></xsl:message>
	<xsl:message>max_proc  <xsl:value-of select="$max_proc_h_"/></xsl:message>
	<xsl:message>max_multiprocstack <xsl:value-of select="$max_MultiProc_Stack_h_"/></xsl:message>
	<xsl:message>max_proc_perisabvsbs_h_ <xsl:value-of select="$max_Proc_PerisAbvSbs_h_"/></xsl:message>
-->	
	<xsl:variable name="sbs_h_"     select="($numSbs_  * $SBS_LANE_H)"/>
	<xsl:variable name="sbs_y_"     select="($inner_Y_ + $max_MultiProc_Stack_h_ + $max_Proc_h_ + $max_Proc_PerisAbvSbs_h_  + $PROC2SBS_GAP)"/>
	
<!-- Draw the Bridges -->	
	<xsl:call-template name="Draw_BlkDiagram_Bridges">
		<xsl:with-param name="Inner_X"      select="$inner_X_"/>
		<xsl:with-param name="SharedBus_Y"  select="$sbs_y_"/>
	</xsl:call-template>	
	
<!-- Draw the Processors -->	
	<xsl:call-template name="Draw_BlkDiagram_Processors">
		<xsl:with-param name="Inner_X"                 select="$inner_X_"/>
		<xsl:with-param name="SharedBus_Y"  		   select="$sbs_y_"/>
		<xsl:with-param name="Max_Proc_H"              select="$max_Proc_h_"/>
	    <xsl:with-param name="Max_Proc_PerisAbvSbs_H"  select="$max_Proc_PerisAbvSbs_h_"/>
	    <xsl:with-param name="Max_Proc_PerisBlwSbs_H"  select="$max_Proc_PerisBlwSbs_h_"/>
	</xsl:call-template>	
	
<!-- Draw the Complex stacks, (collections of more than one module that are not memory and not connected to a processor) -->	
	<xsl:call-template name="Draw_BlkDiagram_ComplexStacks">
		<xsl:with-param name="Inner_X"                 select="$inner_X_"/>
		<xsl:with-param name="SharedBus_Y"  		   select="$sbs_y_"/>
		<xsl:with-param name="Max_Proc_H"              select="$max_Proc_h_"/>
	    <xsl:with-param name="Max_Proc_PerisAbvSbs_H"  select="$max_Proc_PerisAbvSbs_h_"/>
	    <xsl:with-param name="Max_Proc_PerisBlwSbs_H"  select="$max_Proc_PerisBlwSbs_h_"/>
	</xsl:call-template>	
	
<!-- Draw the Complex Modules, (Modules that are not memory and not connected to a processor) -->	
	<xsl:call-template name="Draw_BlkDiagram_ComplexModules">
		<xsl:with-param name="Inner_X"                 select="$inner_X_"/>
		<xsl:with-param name="SharedBus_Y"  		   select="$sbs_y_"/>
		<xsl:with-param name="SharedBus_H"  		   select="$sbs_h_"/>
	</xsl:call-template>	


<!-- Draw the shared bus buckets -->	
	<xsl:call-template name="Draw_BlkDiagram_SharedBusBuckets">
		<xsl:with-param name="Inner_X"                 select="$inner_X_"/>
		<xsl:with-param name="SharedBus_Y"  		   select="$sbs_y_"/>
		<xsl:with-param name="SharedBus_H"  		   select="$sbs_h_"/>
	</xsl:call-template>	
	
<!-- Draw the IP bucket -->	
	<xsl:call-template name="Draw_BlkDiagram_IPBucket">
		<xsl:with-param name="Blkd_W"                  select="$blkd_w"/>
		<xsl:with-param name="Inner_X"                 select="$inner_X_"/>
		<xsl:with-param name="SharedBus_Y"  		   select="$sbs_y_"/>
		<xsl:with-param name="SharedBus_H"  		   select="$sbs_h_"/>
		<xsl:with-param name="Max_Proc_H"              select="$max_Proc_h_"/>
	    <xsl:with-param name="Max_Proc_PerisAbvSbs_H"  select="$max_Proc_PerisAbvSbs_h_"/>
	    <xsl:with-param name="Max_Proc_PerisBlwSbs_H"  select="$max_Proc_PerisBlwSbs_h_"/>
	    <xsl:with-param name="Max_SbsBuckets_H"        select="$max_SbsBuckets_h_"/>
	</xsl:call-template>	
	
<!-- Draw bucket for floating modules, modules not connected to a shared bus or a processor -->	
	<xsl:call-template name="Draw_BlkDiagram_FloatingModsBucket">
		<xsl:with-param name="Blkd_W"                  select="$blkd_w"/>
		<xsl:with-param name="Inner_X"                 select="$inner_X_"/>
		<xsl:with-param name="SharedBus_Y"  		   select="$sbs_y_"/>
		<xsl:with-param name="SharedBus_H"  		   select="$sbs_h_"/>
		<xsl:with-param name="Max_Proc_H"              select="$max_Proc_h_"/>
	    <xsl:with-param name="Max_Proc_PerisAbvSbs_H"  select="$max_Proc_PerisAbvSbs_h_"/>
	    <xsl:with-param name="Max_Proc_PerisBlwSbs_H"  select="$max_Proc_PerisBlwSbs_h_"/>
	    <xsl:with-param name="Max_SbsBuckets_H"        select="$max_SbsBuckets_h_"/>
	</xsl:call-template>	
	
<!-- Draw processor to processor connections -->	
	<xsl:call-template name="Draw_BlkDiagram_Proc2ProcConnections">
		<xsl:with-param name="Inner_X"                 select="$inner_X_"/>
		<xsl:with-param name="SharedBus_Y"  		   select="$sbs_y_"/>
		<xsl:with-param name="SharedBus_H"  		   select="$sbs_h_"/>
		<xsl:with-param name="Max_Proc_H"              select="$max_Proc_h_"/>
	    <xsl:with-param name="Max_Proc_PerisAbvSbs_H"  select="$max_Proc_PerisAbvSbs_h_"/>
	    <xsl:with-param name="Max_Proc_PerisBlwSbs_H"  select="$max_Proc_PerisBlwSbs_h_"/>
	    <xsl:with-param name="Max_SbsBuckets_H"        select="$max_SbsBuckets_h_"/>
	</xsl:call-template>	
	
<!-- Draw multi processor connections -->	
	<xsl:call-template name="Draw_BlkDiagram_MultiProcConnections">
		<xsl:with-param name="Inner_X"                 select="$inner_X_"/>
		<xsl:with-param name="SharedBus_Y"  		   select="$sbs_y_"/>
		<xsl:with-param name="SharedBus_H"  		   select="$sbs_h_"/>
		<xsl:with-param name="Max_Proc_H"              select="$max_Proc_h_"/>
	    <xsl:with-param name="Max_Proc_PerisAbvSbs_H"  select="$max_Proc_PerisAbvSbs_h_"/>
	    <xsl:with-param name="Max_Proc_PerisBlwSbs_H"  select="$max_Proc_PerisBlwSbs_h_"/>
	</xsl:call-template>	
	
	
	<!-- 
		 ===========================================================
	 					Draw the shared busses 
		 ===========================================================
	-->
	
	
	<use   x="{$inner_X_}"    y="{$sbs_y_}"  xlink:href="#group_sharedBusses"/> 
	
	<!-- ************************************************************ -->	
	<!-- Draw the Key -->	
	<!-- ************************************************************ -->	
	<use   x="{$blkd_w - $BLKD_KEY_W - $BLKD_PRTCHAN_W}"   y="{$blkd_h + $BLKD2KEY_GAP - 8}"  xlink:href="#BlkDiagram_Key"/> 
	
	<!-- ************************************************************ -->	
	<!-- Draw the Specs -->	
	<!-- ************************************************************ -->	
	<use   x="{$BLKD_PRTCHAN_W}"                           y="{$blkd_h + $BLKD2KEY_GAP - 8}"  xlink:href="#BlkDiagram_Specs"/> 
	
<!--	
	<use   x="{$blkd_w - $BLKD_KEY_W - $BLKD_PRTCHAN_W}"   y="{$blkd_h + $BLKD2KEY_GAP - 16}"  xlink:href="#symbol_extportstable"/> 
-->	
	<!-- ************************************************************ -->	
	<!-- ***************  DONE DRAWING BLOCK DIAGRAM   ************** -->
	<!-- ************************************************************ -->	
	
</xsl:template>
	

</xsl:stylesheet>

<!-- =========================================================================== -->
<!--                          FUNCTION TEMPLATE                                  -->
<!--																			 -->
<!-- =========================================================================== -->