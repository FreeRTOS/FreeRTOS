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
			<xsl:with-param name="iBusType"    select="@BUSSTD"/>
		</xsl:call-template>
		
		<xsl:call-template name="Define_BusArrowsNorthSouth"> 
			<xsl:with-param name="iBusType"    select="@BUSSTD"/>
		</xsl:call-template>
		
		<xsl:call-template name="Define_SplitBusses"> 
			<xsl:with-param name="iBusType"    select="@BUSSTD"/>
		</xsl:call-template>
		
	</xsl:for-each>
	
	<xsl:call-template name="Define_SharedBus"> 
		<xsl:with-param name="iBusType"    select="'PLB'"/>
	</xsl:call-template>
	
	<xsl:call-template name="Define_SharedBus"> 
		<xsl:with-param name="iBusType"    select="'PLBV46'"/>
	</xsl:call-template>
	
	<xsl:call-template name="Define_SharedBus"> 
		<xsl:with-param name="iBusType"    select="'OPB'"/>
	</xsl:call-template>
	
	<xsl:call-template name="Define_SharedBus_Group"/> 
	
</xsl:template>

<xsl:template name="Define_BusArrowsEastWest"> 
	<xsl:param name="iBusType"    select="'OPB'"/>
	
	<xsl:variable name="bus_col_">
		<xsl:call-template name="BusType2Color">
			<xsl:with-param name="iBusType" select="$iBusType"/>
		</xsl:call-template>	
	</xsl:variable>
	
	<xsl:variable name="bus_col_lt_">
		<xsl:call-template name="BusType2LightColor">
			<xsl:with-param name="iBusType" select="$iBusType"/>
		</xsl:call-template>	
	</xsl:variable>
	
	<symbol id="{$iBusType}_BusArrowEast">
		<path class="bus"
			  d="M   0,0
				 L     {$BLKD_BUS_ARROW_W}, {ceiling($BLKD_BUS_ARROW_H div 2)}
				 L   0,{$BLKD_BUS_ARROW_H}, 
				 Z" style="stroke:none; fill:{$bus_col_}"/>
	</symbol>
	
	<symbol id="{$iBusType}_BusArrowWest">
		<use   x="0"   y="0"  xlink:href="#{$iBusType}_BusArrowEast" transform="scale(-1,1) translate({$BLKD_BUS_ARROW_W * -1},0)"/>
	</symbol>
	
	<symbol id="{$iBusType}_BusArrowHInitiator">
		<rect x="0" 
		  	  y="{$BLKD_BUS_ARROW_G}"  
		 	  width= "{$BLKD_BUS_ARROW_W}" 
		 	  height="{$BLKD_P2P_BUS_W}" 
		 	 style="stroke:none; fill:{$bus_col_}"/>
	</symbol>
	
</xsl:template>

<!--	
	<xsl:param name="bus_col"     select="'OPB'"/>
-->	

<xsl:template name="Define_BusArrowsNorthSouth">
	<xsl:param name="iBusType"    select="'OPB'"/>
	
	<xsl:variable name="busColor_">
		<xsl:call-template name="BusType2Color">
			<xsl:with-param name="iBusType" select="$iBusType"/>
		</xsl:call-template>	
	</xsl:variable>
	
	<xsl:variable name="busColor_lt_">
		<xsl:call-template name="BusType2LightColor">
			<xsl:with-param name="iBusType" select="$iBusType"/>
		</xsl:call-template>	
	</xsl:variable>
	
	<symbol id="{$iBusType}_BusArrowSouth">
		<path class="bus"
			  d="M   0,0
				 L   {$BLKD_BUS_ARROW_H},0
				 L   {ceiling($BLKD_BUS_ARROW_H div 2)}, {$BLKD_BUS_ARROW_W}
				 Z" style="stroke:none; fill:{$busColor_}"/>
	</symbol>
	
	<symbol id="{$iBusType}_BusArrowNorth">
		<use   x="0"   y="0"  xlink:href="#{$iBusType}_BusArrowSouth" transform="scale(1,-1) translate(0,{$BLKD_BUS_ARROW_H * -1})"/>
	</symbol>
	
	<symbol id="{$iBusType}_BusArrowInitiator">
		<rect x="{$BLKD_BUS_ARROW_G}" 
		  	  y="0"  
		 	  width= "{$BLKD_BUS_ARROW_W - ($BLKD_BUS_ARROW_G * 2)}" 
		 	  height="{$BLKD_BUS_ARROW_H}" 
		 	 style="stroke:none; fill:{$busColor_}"/>
	</symbol>
	
</xsl:template>
	

<xsl:template name="Draw_P2PBus">
	
	<xsl:param name="iBusX"    select="0"/>
	<xsl:param name="iBusTop"  select="0"/>
	<xsl:param name="iBusBot"  select="0"/>
	<xsl:param name="iBotRnk"  select="'_unk_'"/>
	<xsl:param name="iTopRnk"  select="'_unk_'"/>
	<xsl:param name="iBusStd"  select="'_bstd_'"/>
	<xsl:param name="iBusName" select="'_p2pbus_'"/>
	
	<xsl:variable name="busColor_">
		<xsl:choose>
			
			<xsl:when test="@BUSSTD">
				<xsl:call-template name="BusType2Color">
					<xsl:with-param name="iBusType" select="@BUSSTD"/>
				</xsl:call-template>	
			</xsl:when>
			
			<xsl:when test="not($iBusStd = '_bstd_')">
				<xsl:call-template name="BusType2Color">
					<xsl:with-param name="iBusType" select="$iBusStd"/>
				</xsl:call-template>	
			</xsl:when>
			
			<xsl:otherwise>
				<xsl:call-template name="BusType2Color">
					<xsl:with-param name="iBusType" select="'TRS'"/>
				</xsl:call-template>	
			</xsl:otherwise>
			
		</xsl:choose>
	</xsl:variable>
	
	<xsl:variable name="p2pH_" select="($iBusBot - $iBusTop) - ($BLKD_BUS_ARROW_H * 2)"/>

	<xsl:variable name="botArrow_">
		<xsl:choose>
			<xsl:when test="((($iBotRnk = 'INITIATOR') or ($iBotRnk = 'MASTER')) and ($iBusStd = 'FSL'))">BusArrowInitiator</xsl:when>
			<xsl:otherwise>BusArrowSouth</xsl:otherwise> 
		</xsl:choose>		
	</xsl:variable>
	
	<xsl:variable name="topArrow_">
		<xsl:choose>
			<xsl:when test="((($iTopRnk = 'INITIATOR') or ($iTopRnk = 'MASTER')) and ($iBusStd = 'FSL'))">BusArrowInitiator</xsl:when>
			<xsl:otherwise>BusArrowNorth</xsl:otherwise> 
		</xsl:choose>		
	</xsl:variable>
	
	<xsl:if test="@BUSSTD">		
		<use  x="{($iBusX + ceiling($BLKD_BIFC_W div 2)) - ceiling($BLKD_BUS_ARROW_W div 2)}"  
		      y="{$iBusTop + ($BLKD_BIFC_H  - $BLKD_BUS_ARROW_H) + $BLKD_BUS_ARROW_H}"  
		      xlink:href="#{@BUSSTD}_{$topArrow_}"/>	
		  
		<use  x="{($busX + ceiling($BLKD_BIFC_W div 2)) - ceiling($BLKD_BUS_ARROW_W div 2)}"  
		      y="{$busBot - $BLKD_BUS_ARROW_H}"  
		      xlink:href="#{@BUSSTD}_{$botArrow_}"/>	
	</xsl:if>		  
	
	<xsl:if test="(not(@BUSSTD) and not($busStd = '_bstd_'))">		
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
		  style="stroke:none; fill:{$busColor_}"/>
		  
	<text class="p2pbuslabel" 
			  x="{$iBusX   + $BLKD_BUS_ARROW_W + ceiling($BLKD_BUS_ARROW_W div 2) + ceiling($BLKD_BUS_ARROW_W div 4) + 4}"
			  y="{$iBusTop + ($BLKD_BUS_ARROW_H * 3)}">
			<xsl:value-of select="$iBusName"/>
	</text>
	
  	<xsl:if test="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $iBusName)]/@GROUP">
	  	
   	   <text class="ioplblgrp" 
		  x="{$iBusX   +  $BLKD_BUS_ARROW_W + ceiling($BLKD_BUS_ARROW_W div 2) + ceiling($BLKD_BUS_ARROW_W div 4) + 6}"
		  y="{$iBusTop + ($BLKD_BUS_ARROW_H * 10)}">
			   <xsl:value-of select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE=$iBusName)]/@GROUP"/>
   		</text>
	   
  	</xsl:if> 	
		
</xsl:template>

	
<xsl:template name="Draw_Proc2ProcBus">
	
	<xsl:param name="iBc_Y"     select="0"/>
	<xsl:param name="iBcLeft_X" select="0"/>
	<xsl:param name="iBcRght_X" select="0"/>
	<xsl:param name="iLeftRnk"  select="'_unk_'"/>
	<xsl:param name="iRghtRnk"  select="'_unk_'"/>
	<xsl:param name="iBusStd"   select="'_bstd_'"/>
	<xsl:param name="iBusName"  select="'_p2pbus_'"/>
	
	<xsl:variable name="busColor_">
		<xsl:call-template name="BusType2Color">
			<xsl:with-param name="iBusType" select="$iBusStd"/>
		</xsl:call-template>	
	</xsl:variable>
	
	<xsl:variable name="pr2pr_W_" select="($iBcRght_X - $iBcLeft_X)"/>

	<xsl:variable name="leftArrow_">
		<xsl:choose>
			<xsl:when test="((($iLeftRnk = 'INITIATOR') or ($iLeftRnk = 'MASTER')) and ($iBusStd = 'FSL'))">BusArrowHInitiator</xsl:when>
			<xsl:otherwise>BusArrowWest</xsl:otherwise> 
		</xsl:choose>		
	</xsl:variable>
	
	<xsl:variable name="rghtArrow_">
		<xsl:choose>
			<xsl:when test="((($iRghtRnk = 'INITIATOR') or ($iRghtRnk = 'MASTER')) and ($iBusStd = 'FSL'))">BusArrowHInitiator</xsl:when>
			<xsl:otherwise>BusArrowEast</xsl:otherwise> 
		</xsl:choose>		
	</xsl:variable>
	
	
	<xsl:variable name="bus_Y_" select="($iBc_Y + ceiling($BLKD_BIFC_H div 2) - ceiling($BLKD_BUS_ARROW_H div 2))"/>
	
	<use  x="{$iBcLeft_X}"                     y="{$bus_Y_}"  xlink:href="#{$iBusStd}_{$leftArrow_}"/>	
	<use  x="{$iBcRght_X - $BLKD_BUS_ARROW_W}" y="{$bus_Y_}"  xlink:href="#{$iBusStd}_{$rghtArrow_}"/>	
	
	<rect x="{$iBcLeft_X + $BLKD_BUS_ARROW_W}" 
		  y="{$bus_Y_    + $BLKD_BUS_ARROW_G}"  
		  width= "{$pr2pr_W_    -      (2 * $BLKD_BUS_ARROW_W)}" 
		  height="{$BLKD_BUS_ARROW_H - (2 * $BLKD_BUS_ARROW_G)}" style="stroke:none; fill:{$busColor_}"/>
	
	<text class="horizp2pbuslabel" 
			  x="{$iBcLeft_X  + $BLKD_BUS_ARROW_W + ceiling($BLKD_BUS_ARROW_W div 2) + ceiling($BLKD_BUS_ARROW_W div 4) + 4}"
			  y="{($bus_Y_)}"><xsl:value-of select="$iBusName"/></text>
	
	<text class="horizp2pbuslabel" 
			  x="{$iBcRght_X - (string-length($iBusName) * 8)}"
			  y="{($bus_Y_)}"><xsl:value-of select="$iBusName"/></text>
	
</xsl:template>
	
	
<xsl:template name="Draw_SplitConnBus">
	
	<xsl:param name="iBc_X"     select="0"/>
	<xsl:param name="iBc_Y"     select="0"/>
	<xsl:param name="iBc_Rnk"   select="'_unk_'"/>
	<xsl:param name="iBc_Side"  select="'_unk_'"/>
	
	<xsl:param name="iBusStd"   select="'_bstd_'"/>
	<xsl:param name="iBusName"  select="'_p2pbus_'"/>
	
	<xsl:variable name="busColor_">
		<xsl:call-template name="BusType2Color">
			<xsl:with-param name="iBusType" select="$iBusStd"/>
		</xsl:call-template>	
	</xsl:variable>
	
	<xsl:variable name="connArrow_">
		<xsl:choose>
			<xsl:when test="((($iBc_Rnk = 'INITIATOR') or ($iBc_Rnk = 'MASTER')) and ($iBusStd = 'FSL'))">BusArrowHInitiator</xsl:when>
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
	
<!--	
	<xsl:message>The bus name is <xsl:value-of select="$busName"/></xsl:message>
	<xsl:message>The bif side is <xsl:value-of select="$bc_Side"/></xsl:message>
	<xsl:message>The bif rank is <xsl:value-of select="$bc_Rnk"/></xsl:message>
-->	
	<xsl:choose>
		<xsl:when test="(($iBusStd = 'FSL') and (($iBc_Rnk = 'MASTER') or ($iBc_Rnk = 'INITIATOR')))">
			<use  x="{$arrow_X_}"  y="{$arrow_Y_}"  xlink:href="#{$iBusStd}_{$connArrow_}"/>	
			<use  x="{$bus_X_}"    y="{$arrow_Y_}"  xlink:href="#{$iBusStd}_BusArrowHInitiator"/>	
		</xsl:when>
		<xsl:when test="(($iBc_Side = '1') and not($iBusStd = 'FSL') and (($iBc_Rnk = 'MASTER') or ($iBc_Rnk = 'INITIATOR')))">
			<use  x="{$arrow_X_ - $BLKD_BIFC_W}"  y="{$arrow_Y_}"  xlink:href="#{$iBusStd}_SplitBus_WEST"/>
		</xsl:when>
		<xsl:when test="(($iBc_Side = '1') and (($iBc_Rnk = 'SLAVE') or ($iBc_Rnk = 'TARGET') or ($iBc_Rnk = 'TRANSPARENT')))">
			<use  x="{$arrow_X_}"  y="{$arrow_Y_}"  xlink:href="#{$iBusStd}_SplitBus_EAST"/>
		</xsl:when>
		<xsl:otherwise>
			<use  x="{$arrow_X_}" y="{$arrow_Y_}" xlink:href="#{$iBusStd}_{$connArrow_}"/>	
			<use  x="{$bus_X_}"   y="{$arrow_Y_}"   xlink:href="#{$iBusStd}_BusArrowHInitiator"/>	
		</xsl:otherwise>
	</xsl:choose>
	
	<xsl:variable name="text_X_">
		<xsl:choose>
			<xsl:when test="$iBc_Side = '0'"><xsl:value-of select="($bus_X_ - $BLKD_BUS_ARROW_W - (string-length($iBusName) * 5))"/></xsl:when>
			<xsl:when test="$iBc_Side = '1'"><xsl:value-of select="($bus_X_ + $BLKD_BUS_ARROW_W)"/></xsl:when>
		</xsl:choose>		
	</xsl:variable>	
		
	
	<text class="horizp2pbuslabel" 
			  x="{$text_X_}"
			  y="{($arrow_Y_)}">
			<xsl:value-of select="$iBusName"/>
	</text>
	
</xsl:template>
	
	
<xsl:template name="Define_SharedBus"> 
	
	<xsl:param name="iBusType"    select="'OPB'"/>
	
	<xsl:variable name="sharedbus_w_"  select="($G_total_drawarea_W - ($BLKD_INNER_GAP * 2))"/>
	
	<xsl:variable name="bus_col_">
		<xsl:call-template name="BusType2Color">
			<xsl:with-param name="iBusType" select="$iBusType"/>
		</xsl:call-template>	
	</xsl:variable>
	
	<xsl:variable name="bus_col_lt_">
		<xsl:call-template name="BusType2LightColor">
			<xsl:with-param name="iBusType" select="$iBusType"/>
		</xsl:call-template>	
	</xsl:variable>
	
	 <symbol id="{$iBusType}_SharedBus">
		<use  x="0"                                   y="0"  xlink:href="#{$iBusType}_BusArrowWest"/>	
		<use  x="{$sharedbus_w_ - $BLKD_BUS_ARROW_W}" y="0"  xlink:href="#{$iBusType}_BusArrowEast"/>	
		
		<rect x="{$BLKD_BUS_ARROW_W}" 
			  y="{$BLKD_BUS_ARROW_G}"  
			  width= "{$sharedbus_w_  - ($BLKD_BUS_ARROW_W * 2)}" 
			  height="{$BLKD_BUS_ARROW_H - (2 * $BLKD_BUS_ARROW_G)}" style="stroke:none; fill:{$bus_col_}"/>
	</symbol>
</xsl:template>

	
<xsl:template name="Define_SplitBusses"> 
	
	<xsl:param name="iBusType"    sselect="'FSL'"/>
	
	<xsl:variable name="busColor_">
		<xsl:call-template name="BusType2Color">
			<xsl:with-param name="iBusType" select="$iBusType"/>
		</xsl:call-template>	
	</xsl:variable>
	
	<xsl:variable name="bifc_r_" select="ceiling($BLKD_BIFC_W div 3)"/>
	
	 <symbol id="{$iBusType}_SplitBus_EAST">
		<use  x="0"  y="0"    xlink:href="#{$iBusType}_BusArrowWest"/>	
		
		<rect x="{$BLKD_BUS_ARROW_W}" 
			  y="{$BLKD_BUS_ARROW_G}"  
			  width= "{$BLKD_BIFC_W}" 
			  height="{$BLKD_BUS_ARROW_H - (2 * $BLKD_BUS_ARROW_G)}" style="stroke:none; fill:{$busColor_}"/>
		 
	</symbol>
	
	<xsl:variable name="splbus_w_" select="($BLKD_BUS_ARROW_W + $BLKD_BIFC_W + $BLKD_BIFC_Wi)"/>
	
	 <symbol id="{$iBusType}_SplitBus_WEST">
		<use   x="0"   y="0"  xlink:href="#{$iBusType}_SplitBus_EAST" transform="scale(-1,1) translate({$splbus_w_ * -1},0)"/>
	</symbol>
	
	 <symbol id="{$iBusType}_SplitBus_OneWay">
		 
		<rect x="0" 
			  y="{$BLKD_BUS_ARROW_G}"  
			  width= "{($BLKD_BUS_ARROW_W * 2)}" 
			  height="{$BLKD_BUS_ARROW_H - (2 * $BLKD_BUS_ARROW_G)}" style="stroke:none; fill:{$busColor_}"/>
		 
		<rect x="{($BLKD_BUS_ARROW_W * 2)}"
			  y="0"  
			  width= "{$BLKD_BUS_ARROW_H}" 
			  height="{$BLKD_BUS_ARROW_H}" style="stroke:none; fill:{$busColor_}"/>
		 
	</symbol>
	
	
</xsl:template>


<xsl:template name="Define_SharedBus_Group"> 

<!-- The Bridges go into the shared bus shape -->
	<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/BRIDGESHAPES/MODULE">	
	
		<xsl:variable name="modInst_" select="@INSTANCE"/>
		<xsl:variable name="modType_" select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $modInst_)]/@MODTYPE"/>
		
		<xsl:call-template name="Define_Peripheral"> 
			<xsl:with-param name="iModVori"  select="'normal'"/>
			<xsl:with-param name="iModInst"  select="$modInst_"/>
			<xsl:with-param name="iModType"  select="$modType_"/>
		</xsl:call-template>
	
	</xsl:for-each>
	
 <symbol id="group_sharedBusses">
	
	<!-- Draw the shared bus shapes first -->	
	<xsl:for-each select="BLKDSHAPES/SBSSHAPES/MODULE">	
		<xsl:variable name="instance_"  select="@INSTANCE"/>
		
		<xsl:variable name="busStd_"   select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $instance_)]/@BUSSTD"/>	
		<xsl:variable name="busIndex_" select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $instance_)]/@BUSINDEX"/>	
		
		<xsl:variable name="busY_"  select="($busIndex_ * $BLKD_SBS_LANE_H)"/>	
		
		<use  x="0"  y="{$busY_}"  xlink:href="#{$busStd_}_SharedBus"/>	
		
		<text class="sharedbuslabel" 
			  x="8"
			  y="{$busY_ + $BLKD_BUS_ARROW_H + 10}">
			<xsl:value-of select="$instance_"/>
		</text>
		
	</xsl:for-each>
</symbol>	

 <symbol id="KEY_SharedBus">
	<use  x="0"  y="0"  xlink:href="#KEY_BusArrowWest"/>	
	<use  x="30" y="0"  xlink:href="#KEY_BusArrowEast"/>	
	 
	<xsl:variable name="key_col_">
		<xsl:call-template name="BusType2Color">
			<xsl:with-param name="iBusType" select="'KEY'"/>
		</xsl:call-template>	
	</xsl:variable>
		
	<rect x="{$BLKD_BUS_ARROW_W}" 
		  y="{$BLKD_BUS_ARROW_G}"  
		  width= "{30 - $BLKD_BUS_ARROW_W}" 
		  height="{$BLKD_BUS_ARROW_H - (2 * $BLKD_BUS_ARROW_G)}" style="stroke:none; fill:{$key_col_}"/>
</symbol>
	
</xsl:template>
	
</xsl:stylesheet>
