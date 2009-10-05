<?xml version="1.0" standalone="no"?>
<xsl:stylesheet version="1.0"
           xmlns:svg="http://www.w3.org/2000/svg"
           xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
           xmlns:exsl="http://exslt.org/common"
           xmlns:xlink="http://www.w3.org/1999/xlink">
                
<xsl:output method="xml" version="1.0" encoding="UTF-8" indent="yes"
	       doctype-public="-//W3C//DTD SVG 1.0//EN"
		   doctype-system="http://www.w3.org/TR/SVG/DTD/svg10.dtd"/>
		

	
<xsl:template name="Define_Busses">
<!--	
	<xsl:param name="drawarea_w"  select="500"/>
	<xsl:param name="drawarea_h"  select="500"/>
-->	
	
	<xsl:for-each select="exsl:node-set($COL_BUSSTDS)/BUSCOLOR">
		
		<xsl:call-template name="Define_BusArrowsEastWest"> 
			<xsl:with-param name="iBusStd"    select="@BUSSTD"/>
		</xsl:call-template>
		
		<xsl:call-template name="Define_BusArrowsNorthSouth"> 
			<xsl:with-param name="iBusStd"    select="@BUSSTD"/>
		</xsl:call-template>
		
		<xsl:call-template name="Define_SplitBusses"> 
			<xsl:with-param name="iBusStd"    select="@BUSSTD"/>
		</xsl:call-template>
		
	</xsl:for-each>
	
	<xsl:call-template name="Define_SharedBus"> 
		<xsl:with-param name="iBusStd"    select="'PLB'"/>
	</xsl:call-template>
	
	<xsl:call-template name="Define_SharedBus"> 
		<xsl:with-param name="iBusStd"    select="'PLBV46'"/>
	</xsl:call-template>
	
	<xsl:call-template name="Define_SharedBus"> 
		<xsl:with-param name="iBusStd"    select="'OPB'"/>
	</xsl:call-template>
	
	<xsl:call-template name="Define_SharedBus_Group"/> 
	
</xsl:template>

<xsl:template name="Define_BusArrowsEastWest"> 
	<xsl:param name="iBusStd"    select="'PLB'"/>
	
	<xsl:variable name="busStdColor_">
		<xsl:call-template name="F_BusStd2RGB">
			<xsl:with-param name="iBusStd" select="$iBusStd"/>
		</xsl:call-template>	
	</xsl:variable>
	
	<xsl:variable name="busStdColor_lt_">
		<xsl:call-template name="F_BusStd2RGB_LT">
			<xsl:with-param name="iBusStd" select="$iBusStd"/>
		</xsl:call-template>	
	</xsl:variable>
	
	<g id="{$iBusStd}_BusArrowEast">
		<path class="bus"
			  d="M   0,0
				 L     {$BLKD_BUS_ARROW_W}, {ceiling($BLKD_BUS_ARROW_H div 2)}
				 L   0,{$BLKD_BUS_ARROW_H}, 
				 Z" style="stroke:none; fill:{$busStdColor_}"/>
	</g>
	
	<g id="{$iBusStd}_BusArrowWest">
		<use   x="0"   y="0"  xlink:href="#{$iBusStd}_BusArrowEast" transform="scale(-1,1) translate({$BLKD_BUS_ARROW_W * -1},0)"/>
	</g>
	
	<g id="{$iBusStd}_BusArrowHInitiator">
		<rect x="0" 
		  	  y="{$BLKD_BUS_ARROW_G}"  
		 	  width= "{$BLKD_BUS_ARROW_W}" 
		 	  height="{$BLKD_P2P_BUS_W}" 
		 	 style="stroke:none; fill:{$busStdColor_}"/>
	</g>
	
</xsl:template>

<!--	
	<xsl:param name="bus_col"     select="'OPB'"/>
-->	

<xsl:template name="Define_BusArrowsNorthSouth">
	<xsl:param name="iBusStd"    select="'PLB'"/>
	
	<xsl:variable name="busStdColor_">
		<xsl:call-template name="F_BusStd2RGB">
			<xsl:with-param name="iBusStd" select="$iBusStd"/>
		</xsl:call-template>	
	</xsl:variable>
	
	<xsl:variable name="busStdColor_lt_">
		<xsl:call-template name="F_BusStd2RGB_LT">
			<xsl:with-param name="iBusStd" select="$iBusStd"/>
		</xsl:call-template>	
	</xsl:variable>
	
	<g id="{$iBusStd}_BusArrowSouth">
		<path class="bus"
			  d="M   0,0
				 L   {$BLKD_BUS_ARROW_H},0
				 L   {ceiling($BLKD_BUS_ARROW_H div 2)}, {$BLKD_BUS_ARROW_W}
				 Z" style="stroke:none; fill:{$busStdColor_}"/>
	</g>
	
	<g id="{$iBusStd}_BusArrowNorth">
		<use   x="0"   y="0"  xlink:href="#{$iBusStd}_BusArrowSouth" transform="scale(1,-1) translate(0,{$BLKD_BUS_ARROW_H * -1})"/>
	</g>
	
	<g id="{$iBusStd}_BusArrowInitiator">
		<rect x="{$BLKD_BUS_ARROW_G}" 
		  	  y="0"  
		 	  width= "{$BLKD_BUS_ARROW_W - ($BLKD_BUS_ARROW_G * 2)}" 
		 	  height="{$BLKD_BUS_ARROW_H}" 
		 	 style="stroke:none; fill:{$busStdColor_}"/>
	</g>
	
</xsl:template>
	

<xsl:template name="Draw_P2PBus">
	
	<xsl:param name="iBusX"        select="0"/>
	<xsl:param name="iBusTop"  	   select="0"/>
	<xsl:param name="iBusBot"  	   select="0"/>
	<xsl:param name="iBusStd" 	   select="'_bstd_'"/>
	<xsl:param name="iBusName" 	   select="'_p2pbus_'"/>
	<xsl:param name="iBotBifType"  select="'_unk_'"/>
	<xsl:param name="iTopBifType"  select="'_unk_'"/>
	
	<xsl:variable name="busStdColor_">
		<xsl:choose>
			
			<xsl:when test="@BUSSTD">
				<xsl:call-template name="F_BusStd2RGB">
					<xsl:with-param name="iBusStd" select="@BUSSTD"/>
				</xsl:call-template>	
			</xsl:when>
			
			<xsl:when test="not($iBusStd = '_bstd_')">
				<xsl:call-template name="F_BusStd2RGB">
					<xsl:with-param name="iBusStd" select="$iBusStd"/>
				</xsl:call-template>	
			</xsl:when>
			
			<xsl:otherwise>
				<xsl:call-template name="F_BusStd2RGB">
					<xsl:with-param name="iBusStd" select="'TRS'"/>
				</xsl:call-template>	
			</xsl:otherwise>
			
		</xsl:choose>
	</xsl:variable>
	
	<xsl:variable name="p2pH_" select="($iBusBot - $iBusTop) - ($BLKD_BUS_ARROW_H * 2)"/>

	<xsl:variable name="botArrow_">
		<xsl:choose>
			<xsl:when test="((($iBotBifType = 'INITIATOR') or ($iBotBifType = 'MASTER')) and ($iBusStd = 'FSL'))">BusArrowInitiator</xsl:when>
			<xsl:otherwise>BusArrowSouth</xsl:otherwise> 
		</xsl:choose>		
	</xsl:variable>
	
	<xsl:variable name="topArrow_">
		<xsl:choose>
			<xsl:when test="((($iTopBifType = 'INITIATOR') or ($iTopBifType = 'MASTER')) and ($iBusStd = 'FSL'))">BusArrowInitiator</xsl:when>
			<xsl:otherwise>BusArrowNorth</xsl:otherwise> 
		</xsl:choose>		
	</xsl:variable>
	
	<xsl:if test="@BUSSTD">		
		<use  x="{($iBusX + ceiling($BLKD_BIFC_W div 2)) - ceiling($BLKD_BUS_ARROW_W div 2)}"  
		      y="{$iBusTop + ($BLKD_BIFC_H  - $BLKD_BUS_ARROW_H) + $BLKD_BUS_ARROW_H}"  
		      xlink:href="#{@BUSSTD}_{$topArrow_}"/>	
		  
		<use  x="{($iBusX + ceiling($BLKD_BIFC_W div 2)) - ceiling($BLKD_BUS_ARROW_W div 2)}"  
		      y="{$iBusBot - $BLKD_BUS_ARROW_H}"  
		      xlink:href="#{@BUSSTD}_{$botArrow_}"/>	
	</xsl:if>		  
	
	<xsl:if test="(not(@BUSSTD) and not($iBusStd = '_bstd_'))">		
		<use  x="{($iBusX + ceiling($BLKD_BIFC_W div 2)) - ceiling($BLKD_BUS_ARROW_W div 2)}"  
		      y="{$iBusTop + ($BLKD_BIFC_H  - $BLKD_BUS_ARROW_H) + $BLKD_BUS_ARROW_H}"  
		      xlink:href="#{$iBusStd}_{$topArrow_}"/>	
		  
		<use  x="{($iBusX + ceiling($BLKD_BIFC_W div 2)) - ceiling($BLKD_BUS_ARROW_W div 2)}"  
		      y="{$iBusBot - $BLKD_BUS_ARROW_H}"  
		      xlink:href="#{$iBusStd}_{$botArrow_}"/>	
	</xsl:if>		  
	
	
	<rect x="{($iBusX + ceiling($BLKD_BIFC_W div 2)) - ceiling($BLKD_BUS_ARROW_W div 2) + $BLKD_BUS_ARROW_G}"  
		  y="{$iBusTop + $BLKD_BIFC_H + $BLKD_BUS_ARROW_H}"  
		  height= "{$p2pH_  - ($BLKD_BUS_ARROW_H * 2)}" 
		  width="{$BLKD_BUS_ARROW_W - ($BLKD_BUS_ARROW_G * 2)}" 
		  style="stroke:none; fill:{$busStdColor_}"/>
		  
<!--
	<text class="p2pbuslabel" 
			  x="{$iBusX   + $BLKD_BUS_ARROW_W + ceiling($BLKD_BUS_ARROW_W div 2) + ceiling($BLKD_BUS_ARROW_W div 4) + 4}"
			  y="{$iBusTop + ($BLKD_BUS_ARROW_H * 3)}">
			<xsl:value-of select="$iBusName"/>
	</text>
-->	

		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="($iBusX   + $BLKD_BUS_ARROW_W + ceiling($BLKD_BUS_ARROW_W div 2) + ceiling($BLKD_BUS_ARROW_W div 4) + 4)"/>
			<xsl:with-param name="iY" 		select="($iBusTop + ($BLKD_BUS_ARROW_H * 3))"/>
			<xsl:with-param name="iText"	select="$iBusName"/>
			<xsl:with-param name="iClass"	select="'p2pbus_label'"/>
		</xsl:call-template>
			  
  	<xsl:if test="$G_ROOT/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $iBusName)]/@GROUP">
<!-- 
   	   <text class="ioplblgrp" 
		  x="{$iBusX   +  $BLKD_BUS_ARROW_W + ceiling($BLKD_BUS_ARROW_W div 2) + ceiling($BLKD_BUS_ARROW_W div 4) + 6}"
		  y="{$iBusTop + ($BLKD_BUS_ARROW_H * 10)}">
			   <xsl:value-of select="$G_ROOT/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $iBusName)]/@GROUP"/>
   		</text>
-->	  	
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="(iBusX   +  $BLKD_BUS_ARROW_W + ceiling($BLKD_BUS_ARROW_W div 2) + ceiling($BLKD_BUS_ARROW_W div 4) + 6)"/>
			<xsl:with-param name="iY" 		select="($iBusTop + ($BLKD_BUS_ARROW_H * 10))"/>
			<xsl:with-param name="iText"	select="$G_ROOT/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $iBusName)]/@GROUP"/>
			<xsl:with-param name="iClass"	select="'iogrp_label'"/>
		</xsl:call-template>
	   
  	</xsl:if> 	
		
</xsl:template>

	
<xsl:template name="Draw_Proc2ProcBus">
	
	<xsl:param name="iBc_Y"     	select="0"/>
	<xsl:param name="iBusStd"   	select="'_bstd_'"/>
	<xsl:param name="iBusName"  	select="'_p2pbus_'"/>
	<xsl:param name="iBcLeft_X" 	select="0"/>
	<xsl:param name="iBcRght_X" 	select="0"/>
	<xsl:param name="iLeftBifType"  select="'_unk_'"/>
	<xsl:param name="iRghtBifType"  select="'_unk_'"/>
	
	<xsl:variable name="busStdColor_">
		<xsl:call-template name="F_BusStd2RGB">
			<xsl:with-param name="iBusStd" select="$iBusStd"/>
		</xsl:call-template>	
	</xsl:variable>
	
	<xsl:variable name="pr2pr_W_" select="($iBcRght_X - $iBcLeft_X)"/>

	<xsl:variable name="leftArrow_">
		<xsl:choose>
			<xsl:when test="((($iLeftBifType = 'INITIATOR') or ($iLeftBifType = 'MASTER')) and ($iBusStd = 'FSL'))">BusArrowHInitiator</xsl:when>
			<xsl:otherwise>BusArrowWest</xsl:otherwise> 
		</xsl:choose>		
	</xsl:variable>
	
	<xsl:variable name="rghtArrow_">
		<xsl:choose>
			<xsl:when test="((($iRghtBifType = 'INITIATOR') or ($iRghtBifType = 'MASTER')) and ($iBusStd = 'FSL'))">BusArrowHInitiator</xsl:when>
			<xsl:otherwise>BusArrowEast</xsl:otherwise> 
		</xsl:choose>		
	</xsl:variable>
	
	
	<xsl:variable name="bus_Y_" select="($iBc_Y + ceiling($BLKD_BIFC_H div 2) - ceiling($BLKD_BUS_ARROW_H div 2))"/>
	
	<use  x="{$iBcLeft_X}"                     y="{$bus_Y_}"  xlink:href="#{$iBusStd}_{$leftArrow_}"/>	
	<use  x="{$iBcRght_X - $BLKD_BUS_ARROW_W}" y="{$bus_Y_}"  xlink:href="#{$iBusStd}_{$rghtArrow_}"/>	
	
	<rect x="{$iBcLeft_X + $BLKD_BUS_ARROW_W}" 
		  y="{$bus_Y_    + $BLKD_BUS_ARROW_G}"  
		  width= "{$pr2pr_W_    -      (2 * $BLKD_BUS_ARROW_W)}" 
		  height="{$BLKD_BUS_ARROW_H - (2 * $BLKD_BUS_ARROW_G)}" style="stroke:none; fill:{$busStdColor_}"/>
	
<!-- 
		<text class="horizp2pbuslabel" 
			  x="{$iBcLeft_X  + $BLKD_BUS_ARROW_W + ceiling($BLKD_BUS_ARROW_W div 2) + ceiling($BLKD_BUS_ARROW_W div 4) + 4}"
			  y="{($bus_Y_)}"><xsl:value-of select="$iBusName"/></text>
			  
		<text class="horizp2pbuslabel" 
			  x="{$iBcRght_X - (string-length($iBusName) * 8)}"
			  y="{($bus_Y_)}"><xsl:value-of select="$iBusName"/></text>
-->	
	   
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="($iBcLeft_X  + $BLKD_BUS_ARROW_W + ceiling($BLKD_BUS_ARROW_W div 2) + ceiling($BLKD_BUS_ARROW_W div 4) + 4)"/>
			<xsl:with-param name="iY" 		select="$bus_Y_"/>
			<xsl:with-param name="iText"	select="$iBusName"/>
			<xsl:with-param name="iClass"	select="'p2pbus_label'"/>
		</xsl:call-template>	
				
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="(iBcRght_X - (string-length($iBusName) * 8))"/>
			<xsl:with-param name="iY" 		select="$bus_Y_"/>
			<xsl:with-param name="iText"	select="$iBusName"/>
			<xsl:with-param name="iClass"	select="'p2pbus_label'"/>
		</xsl:call-template>					
	
</xsl:template>
	
	
<xsl:template name="Draw_SplitConnBus">
	
	<xsl:param name="iBc_X"     select="0"/>
	<xsl:param name="iBc_Y"     select="0"/>
	<xsl:param name="iBc_Type"  select="'_unk_'"/>
	<xsl:param name="iBc_Side"  select="'_unk_'"/>
	<xsl:param name="iBusStd"   select="'_bstd_'"/>
	<xsl:param name="iBusName"  select="'_p2pbus_'"/>
	
	<xsl:variable name="busStdColor_">
		<xsl:call-template name="F_BusStd2RGB">
			<xsl:with-param name="iBusStd" select="$iBusStd"/>
		</xsl:call-template>	
	</xsl:variable>
	
	<xsl:variable name="connArrow_">
		<xsl:choose>
			<xsl:when test="((($iBc_Type = 'INITIATOR') or ($iBc_Type = 'MASTER')) and ($iBusStd = 'FSL'))">BusArrowHInitiator</xsl:when>
			<xsl:otherwise>BusArrowEast</xsl:otherwise> 
		</xsl:choose>		
	</xsl:variable>
	
	<xsl:variable name="arrow_Y_" select="($iBc_Y + ceiling($BLKD_BIFC_H div 2) - ceiling($BLKD_BUS_ARROW_H div 2))"/>
	
	<xsl:variable name="bus_X_">
		<xsl:choose>
			<xsl:when test="$iBc_Side = '0'"><xsl:value-of select="($iBc_X - ($BLKD_BUS_ARROW_W * 2))"/></xsl:when>
			<xsl:when test="$iBc_Side = '1'"><xsl:value-of select="($iBc_X + $BLKD_BIFC_W + $BLKD_BUS_ARROW_W)"/></xsl:when>
		</xsl:choose>		
	</xsl:variable>	
	
<!--	
	<use  x="{$bus_X_}"  y="{$arrow_Y_}"  xlink:href="#{$busStd}_BusArrowHInitiator"/>	
-->	
	
	<xsl:variable name="arrow_X_">
		<xsl:choose>
			<xsl:when test="$iBc_Side = '0'"><xsl:value-of select="($iBc_X - $BLKD_BUS_ARROW_W)"/></xsl:when>
			<xsl:when test="$iBc_Side = '1'"><xsl:value-of select="($iBc_X + $BLKD_BIFC_W)"/></xsl:when>
		</xsl:choose>		
	</xsl:variable>	
	<xsl:choose>
		<xsl:when test="(($iBusStd = 'FSL') and (($iBc_Type = 'MASTER') or ($iBc_Type = 'INITIATOR')))">
			<use  x="{$arrow_X_}"  y="{$arrow_Y_}"  xlink:href="#{$iBusStd}_{$connArrow_}"/>	
			<use  x="{$bus_X_}"    y="{$arrow_Y_}"  xlink:href="#{$iBusStd}_BusArrowHInitiator"/>	
		</xsl:when>
		<xsl:when test="(($iBc_Side = '1') and not($iBusStd = 'FSL') and (($iBc_Type = 'MASTER') or ($iBc_Type = 'INITIATOR')))">
			<use  x="{$arrow_X_ - $BLKD_BIFC_W}"  y="{$arrow_Y_}"  xlink:href="#{$iBusStd}_SplitBus_WEST"/>
		</xsl:when>
		<xsl:when test="(($iBc_Side = '1') and (($iBc_Type = 'SLAVE') or ($iBc_Type = 'TARGET') or ($iBc_Type = 'USER')))">
			<use  x="{$arrow_X_}"  y="{$arrow_Y_}"  xlink:href="#{$iBusStd}_SplitBus_EAST"/>
		</xsl:when>
		<xsl:otherwise>
			<use  x="{$arrow_X_}" y="{$arrow_Y_}" xlink:href="#{$iBusStd}_{$connArrow_}"/>	
			<use  x="{$bus_X_}"   y="{$arrow_Y_}" xlink:href="#{$iBusStd}_BusArrowHInitiator"/>	
		</xsl:otherwise>
	</xsl:choose>
	
	<xsl:variable name="text_X_">
		<xsl:choose>
			<xsl:when test="$iBc_Side = '0'"><xsl:value-of select="($bus_X_ - $BLKD_BUS_ARROW_W - (string-length($iBusName) * 5))"/></xsl:when>
			<xsl:when test="$iBc_Side = '1'"><xsl:value-of select="($bus_X_ + $BLKD_BUS_ARROW_W)"/></xsl:when>
		</xsl:choose>		
	</xsl:variable>	
		
	
<!-- 
	<text class="horizp2pbuslabel" 
			  x="{$text_X_}"
			  y="{($arrow_Y_)}">
			<xsl:value-of select="$iBusName"/>
	</text>
-->	
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="$text_X_"/>
			<xsl:with-param name="iY" 		select="$arrow_Y_"/>
			<xsl:with-param name="iText"	select="$iBusName"/>
			<xsl:with-param name="iClass"	select="'p2pbus_label'"/>
		</xsl:call-template>
	
</xsl:template>
	
	
<xsl:template name="Define_SharedBus"> 
	
	<xsl:param name="iBusStd"    select="'PLB46'"/>
	
	<xsl:variable name="sharedbus_w_"  select="($G_Total_DrawArea_W - ($BLKD_INNER_GAP * 2))"/>
	
	<xsl:variable name="busStdColor_">
		<xsl:call-template name="F_BusStd2RGB">
			<xsl:with-param name="iBusStd" select="$iBusStd"/>
		</xsl:call-template>	
	</xsl:variable>
	
	<xsl:variable name="busStdColor_lt_">
		<xsl:call-template name="F_BusStd2RGB_LT">
			<xsl:with-param name="iBusStd" select="$iBusStd"/>
		</xsl:call-template>	
	</xsl:variable>
	
	 <g id="{$iBusStd}_SharedBus">
		<use  x="0"                                   y="0"  xlink:href="#{$iBusStd}_BusArrowWest"/>	
		<use  x="{$sharedbus_w_ - $BLKD_BUS_ARROW_W}" y="0"  xlink:href="#{$iBusStd}_BusArrowEast"/>	
		
		<rect x="{$BLKD_BUS_ARROW_W}" 
			  y="{$BLKD_BUS_ARROW_G}"  
			  width= "{$sharedbus_w_  - ($BLKD_BUS_ARROW_W * 2)}" 
			  height="{$BLKD_BUS_ARROW_H - (2 * $BLKD_BUS_ARROW_G)}" style="stroke:none; fill:{$busStdColor_}"/>
	</g>
</xsl:template>

	
<xsl:template name="Define_SplitBusses"> 
	
	<xsl:param name="iBusStd"    select="'FSL'"/>
	
	<xsl:variable name="busStdColor_">
		<xsl:call-template name="F_BusStd2RGB">
			<xsl:with-param name="iBusStd" select="$iBusStd"/>
		</xsl:call-template>	
	</xsl:variable>
	
	<xsl:variable name="bifc_r_" select="ceiling($BLKD_BIFC_W div 3)"/>
	
	 <g id="{$iBusStd}_SplitBus_EAST">
		<use  x="0"  y="0"    xlink:href="#{$iBusStd}_BusArrowWest"/>	
		
		<rect x="{$BLKD_BUS_ARROW_W}" 
			  y="{$BLKD_BUS_ARROW_G}"  
			  width= "{$BLKD_BIFC_W}" 
			  height="{$BLKD_BUS_ARROW_H - (2 * $BLKD_BUS_ARROW_G)}" style="stroke:none; fill:{$busStdColor_}"/>
		 
	</g>
	
	<xsl:variable name="splbus_w_" select="($BLKD_BUS_ARROW_W + $BLKD_BIFC_W + $BLKD_BIFC_Wi)"/>
	
	 <g id="{$iBusStd}_SplitBus_WEST">
		<use   x="0"   y="0"  xlink:href="#{$iBusStd}_SplitBus_EAST" transform="scale(-1,1) translate({$splbus_w_ * -1},0)"/>
	</g>
	
	 <g id="{$iBusStd}_SplitBus_OneWay">
		 
		<rect x="0" 
			  y="{$BLKD_BUS_ARROW_G}"  
			  width= "{($BLKD_BUS_ARROW_W * 2)}" 
			  height="{$BLKD_BUS_ARROW_H - (2 * $BLKD_BUS_ARROW_G)}" style="stroke:none; fill:{$busStdColor_}"/>
		 
		<rect x="{($BLKD_BUS_ARROW_W * 2)}"
			  y="0"  
			  width= "{$BLKD_BUS_ARROW_H}" 
			  height="{$BLKD_BUS_ARROW_H}" style="stroke:none; fill:{$busStdColor_}"/>
		 
	</g>
</xsl:template>


<xsl:template name="Define_SharedBus_Group"> 

<!-- The Bridges go into the shared bus shape -->
	<xsl:for-each select="$G_ROOT/EDKSYSTEM/BLKDIAGRAM/BRIDGESHAPES/MODULE">	
	
		<xsl:variable name="modInst_" select="@INSTANCE"/>
		<xsl:variable name="modType_" select="$G_ROOT/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $modInst_)]/@MODTYPE"/>
		
		<xsl:call-template name="Define_Peripheral"> 
			<xsl:with-param name="iModVori"  select="'normal'"/>
			<xsl:with-param name="iModInst"  select="$modInst_"/>
			<xsl:with-param name="iModType"  select="$modType_"/>
		</xsl:call-template>
	
	</xsl:for-each>
	
<g id="group_sharedBusses">
	
	<!-- Draw the shared bus shapes first -->	
	<xsl:for-each select="$G_ROOT/EDKSYSTEM/BLKDIAGRAM/SBSSHAPES/MODULE">	
		<xsl:variable name="instance_"  select="@INSTANCE"/>
		
		<xsl:variable name="busStd_"   select="$G_ROOT/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $instance_)]/@BUSSTD"/>	
		<xsl:variable name="busIndex_" select="$G_ROOT/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $instance_)]/@BUS_INDEX"/>	
		
		<xsl:variable name="busY_"  select="($busIndex_ * $BLKD_SBS_LANE_H)"/>	
		
		<use  x="0"  y="{$busY_}"  xlink:href="#{$busStd_}_SharedBus"/>	
		
<!-- 
		<text class="sharedbuslabel" 
			  x="8"
			  y="{$busY_ + $BLKD_BUS_ARROW_H + 10}">
			<xsl:value-of select="$instance_"/>
		</text>
-->		
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="'8'"/>
			<xsl:with-param name="iY" 		select="($busY_ + $BLKD_BUS_ARROW_H + 10)"/>
			<xsl:with-param name="iText"	select="$instance_"/>
			<xsl:with-param name="iClass"	select="'sharedbus_label'"/>
		</xsl:call-template>				
	</xsl:for-each>
	
</g>	

<g id="KEY_SharedBus">
	<use  x="0"  y="0"  xlink:href="#KEY_BusArrowWest"/>	
	<use  x="30" y="0"  xlink:href="#KEY_BusArrowEast"/>	
	 
	<xsl:variable name="key_col_">
		<xsl:call-template name="F_BusStd2RGB">
			<xsl:with-param name="iBusStd" select="'KEY'"/>
		</xsl:call-template>	
	</xsl:variable>
		
	<rect x="{$BLKD_BUS_ARROW_W}" 
		  y="{$BLKD_BUS_ARROW_G}"  
		  width= "{30 - $BLKD_BUS_ARROW_W}" 
		  height="{$BLKD_BUS_ARROW_H - (2 * $BLKD_BUS_ARROW_G)}" style="stroke:none; fill:{$key_col_}"/>
</g>
	
</xsl:template>
	
</xsl:stylesheet>
