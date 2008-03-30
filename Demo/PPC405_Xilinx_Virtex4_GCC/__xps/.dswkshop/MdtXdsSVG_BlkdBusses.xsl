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
	<xsl:param name="drawarea_w"  select="500"/>
	<xsl:param name="drawarea_h"  select="500"/>
	
	<xsl:for-each select="exsl:node-set($COL_BUSSTDS)/BUSCOLOR">
		
		<xsl:call-template name="Define_BusArrowsEastWest"> 
			<xsl:with-param name="bus_type"    select="@BUSSTD"/>
		</xsl:call-template>
		
		<xsl:call-template name="Define_BusArrowsNorthSouth"> 
			<xsl:with-param name="bus_type"    select="@BUSSTD"/>
		</xsl:call-template>
		
		<xsl:call-template name="Define_SplitBusses"> 
			<xsl:with-param name="bus_type"    select="@BUSSTD"/>
		</xsl:call-template>
		
	</xsl:for-each>
	
	<xsl:call-template name="Define_SharedBus"> 
		<xsl:with-param name="bus_type"    select="'PLB'"/>
		<xsl:with-param name="drawarea_w"  select="$drawarea_w"/>
	</xsl:call-template>
	
	<xsl:call-template name="Define_SharedBus"> 
		<xsl:with-param name="bus_type"    select="'PLBV46'"/>
		<xsl:with-param name="drawarea_w"  select="$drawarea_w"/>
	</xsl:call-template>
	
	<xsl:call-template name="Define_SharedBus"> 
		<xsl:with-param name="bus_type"    select="'OPB'"/>
		<xsl:with-param name="drawarea_w"  select="$drawarea_w"/>
	</xsl:call-template>
	
	<xsl:call-template name="Define_SharedBus_Group"/> 
	
<!--	
	<xsl:call-template name="Define_SharedBus"> 
		<xsl:with-param name="bus_type"    select="'PLB'"/>
		<xsl:with-param name="drawarea_w"  select="$drawarea_w"/>
	</xsl:call-template>
-->	
	
</xsl:template>

<xsl:template name="Define_BusArrowsEastWest"> 
	<xsl:param name="bus_type"    select="'OPB'"/>
	
	<xsl:variable name="bus_col_">
		<xsl:call-template name="BusType2Color">
			<xsl:with-param name="busType" select="$bus_type"/>
		</xsl:call-template>	
	</xsl:variable>
	
	<xsl:variable name="bus_col_lt_">
		<xsl:call-template name="BusType2LightColor">
			<xsl:with-param name="busType" select="$bus_type"/>
		</xsl:call-template>	
	</xsl:variable>
	
	<symbol id="{$bus_type}_BusArrowEast">
		<path class="bus"
			  d="M   0,0
				 L     {$BUS_ARROW_W}, {ceiling($BUS_ARROW_H div 2)}
				 L   0,{$BUS_ARROW_H}, 
				 Z" style="stroke:none; fill:{$bus_col_}"/>
	</symbol>
	
	<symbol id="{$bus_type}_BusArrowWest">
		<use   x="0"   y="0"  xlink:href="#{$bus_type}_BusArrowEast" transform="scale(-1,1) translate({$BUS_ARROW_W * -1},0)"/>
	</symbol>
	
<!--	
	<symbol id="{$bus_type}_BusArrowHInitiator">
		<rect x="0" 
		  	  y="{$BUS_ARROW_G}"  
		 	  width= "{$BUS_ARROW_W}" 
		 	  height="{$BUS_ARROW_W - ($BUS_ARROW_G * 2)}" 
		 	 style="stroke:none; fill:{$bus_col_}"/>
	</symbol>
-->	
	<symbol id="{$bus_type}_BusArrowHInitiator">
		<rect x="0" 
		  	  y="{$BUS_ARROW_G}"  
		 	  width= "{$BUS_ARROW_W}" 
		 	  height="{$P2P_BUS_W}" 
		 	 style="stroke:none; fill:{$bus_col_}"/>
	</symbol>
	
</xsl:template>

<!--	
	<xsl:param name="bus_col"     select="'OPB'"/>
-->	

<xsl:template name="Define_BusArrowsNorthSouth">
	<xsl:param name="bus_type"    select="'OPB'"/>
	
	<xsl:variable name="bus_col_">
		<xsl:call-template name="BusType2Color">
			<xsl:with-param name="busType" select="$bus_type"/>
		</xsl:call-template>	
	</xsl:variable>
	
	<xsl:variable name="bus_col_lt_">
		<xsl:call-template name="BusType2LightColor">
			<xsl:with-param name="busType" select="$bus_type"/>
		</xsl:call-template>	
	</xsl:variable>
	
	<symbol id="{$bus_type}_BusArrowSouth">
		<path class="bus"
			  d="M   0,0
				 L   {$BUS_ARROW_W},0
				 L   {ceiling($BUS_ARROW_W div 2)}, {$BUS_ARROW_H}
				 Z" style="stroke:none; fill:{$bus_col_}"/>
	</symbol>
	
	<symbol id="{$bus_type}_BusArrowNorth">
		<use   x="0"   y="0"  xlink:href="#{$bus_type}_BusArrowSouth" transform="scale(1,-1) translate(0,{$BUS_ARROW_H * -1})"/>
	</symbol>
	
	<symbol id="{$bus_type}_BusArrowInitiator">
		<rect x="{$BUS_ARROW_G}" 
		  	  y="0"  
		 	  width= "{$BUS_ARROW_W - ($BUS_ARROW_G * 2)}" 
		 	  height="{$BUS_ARROW_H}" 
		 	 style="stroke:none; fill:{$bus_col_}"/>
	</symbol>
	
</xsl:template>
	

<xsl:template name="Draw_P2PBus">
	
	<xsl:param name="busX"    select="0"/>
	<xsl:param name="busTop"  select="0"/>
	<xsl:param name="busBot"  select="0"/>
	<xsl:param name="botRnk"  select="'_unk_'"/>
	<xsl:param name="topRnk"  select="'_unk_'"/>
	<xsl:param name="busStd"  select="'_bstd_'"/>
	<xsl:param name="busName" select="'_p2pbus_'"/>
	
	<xsl:variable name="busCol_">
		<xsl:choose>
			
			<xsl:when test="@BUSSTD">
				<xsl:call-template name="BusType2Color">
					<xsl:with-param name="busType" select="@BUSSTD"/>
				</xsl:call-template>	
			</xsl:when>
			
			<xsl:when test="not($busStd = '_bstd_')">
				<xsl:call-template name="BusType2Color">
					<xsl:with-param name="busType" select="$busStd"/>
				</xsl:call-template>	
			</xsl:when>
			
			<xsl:otherwise>
				<xsl:value-of select="$COL_OPBBUS"/>	
			</xsl:otherwise>
			
		</xsl:choose>
	</xsl:variable>
	
	<xsl:variable name="p2pH_" select="($busBot - $busTop) - ($BUS_ARROW_H * 2)"/>

	<xsl:variable name="botArrow_">
		<xsl:choose>
			<xsl:when test="((($botRnk = 'INITIATOR') or ($botRnk = 'MASTER')) and ($busStd = 'FSL'))">BusArrowInitiator</xsl:when>
			<xsl:otherwise>BusArrowSouth</xsl:otherwise> 
		</xsl:choose>		
	</xsl:variable>
	
	<xsl:variable name="topArrow_">
		<xsl:choose>
			<xsl:when test="((($topRnk = 'INITIATOR') or ($topRnk = 'MASTER')) and ($busStd = 'FSL'))">BusArrowInitiator</xsl:when>
			<xsl:otherwise>BusArrowNorth</xsl:otherwise> 
		</xsl:choose>		
	</xsl:variable>
	
	<xsl:if test="@BUSSTD">		
		<use  x="{($busX + ceiling($BIFC_W div 2)) - ceiling($BUS_ARROW_W div 2)}"  
		      y="{$busTop + ($BIFC_H  - $BUS_ARROW_H) + $BUS_ARROW_H}"  
		      xlink:href="#{@BUSSTD}_{$topArrow_}"/>	
		  
		<use  x="{($busX + ceiling($BIFC_W div 2)) - ceiling($BUS_ARROW_W div 2)}"  
		      y="{$busBot - $BUS_ARROW_H}"  
		      xlink:href="#{@BUSSTD}_{$botArrow_}"/>	
	</xsl:if>		  
	
	<xsl:if test="(not(@BUSSTD) and not($busStd = '_bstd_'))">		
		<use  x="{($busX + ceiling($BIFC_W div 2)) - ceiling($BUS_ARROW_W div 2)}"  
		      y="{$busTop + ($BIFC_H  - $BUS_ARROW_H) + $BUS_ARROW_H}"  
		      xlink:href="#{$busStd}_{$topArrow_}"/>	
		  
		<use  x="{($busX + ceiling($BIFC_W div 2)) - ceiling($BUS_ARROW_W div 2)}"  
		      y="{$busBot - $BUS_ARROW_H}"  
		      xlink:href="#{$busStd}_{$botArrow_}"/>	
	</xsl:if>		  
	
	
	<rect x="{($busX + ceiling($BIFC_W div 2)) - ceiling($BUS_ARROW_W div 2) + $BUS_ARROW_G}"  
		  y="{$busTop + $BIFC_H + $BUS_ARROW_H}"  
		  height= "{$p2pH_  - ($BUS_ARROW_H * 2)}" 
		  width="{$BUS_ARROW_W - ($BUS_ARROW_G * 2)}" 
		  style="stroke:none; fill:{$busCol_}"/>
		  
	<text class="p2pbuslabel" 
			  x="{$busX   + $BUS_ARROW_W + ceiling($BUS_ARROW_W div 2) + ceiling($BUS_ARROW_W div 4) + 4}"
			  y="{$busTop + ($BUS_ARROW_H * 3)}">
			<xsl:value-of select="$busName"/>
	</text>
	
  	<xsl:if test="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $busName)]/@GROUP">
	  	
   	   <text class="ioplblgrp" 
		  x="{$busX   + $BUS_ARROW_W + ceiling($BUS_ARROW_W div 2) + ceiling($BUS_ARROW_W div 4) + 6}"
		  y="{$busTop + ($BUS_ARROW_H * 10)}">
			   <xsl:value-of select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE=$busName)]/@GROUP"/>
   		</text>
	   
  	</xsl:if> 	
		
</xsl:template>

	
<xsl:template name="Draw_Proc2ProcBus">
	
	<xsl:param name="bc_Y"     select="0"/>
	<xsl:param name="bcLeft_X" select="0"/>
	<xsl:param name="bcRght_X" select="0"/>
	
	<xsl:param name="leftRnk"  select="'_unk_'"/>
	<xsl:param name="rghtRnk"  select="'_unk_'"/>
	
	<xsl:param name="busStd"   select="'_bstd_'"/>
	<xsl:param name="busName"  select="'_p2pbus_'"/>
	
	<xsl:variable name="busCol_">
		<xsl:call-template name="BusType2Color">
			<xsl:with-param name="busType" select="$busStd"/>
		</xsl:call-template>	
	</xsl:variable>
	
	<xsl:variable name="pr2pr_W_" select="($bcRght_X - $bcLeft_X)"/>

	<xsl:variable name="leftArrow_">
		<xsl:choose>
			<xsl:when test="((($leftRnk = 'INITIATOR') or ($leftRnk = 'MASTER')) and ($busStd = 'FSL'))">BusArrowHInitiator</xsl:when>
			<xsl:otherwise>BusArrowWest</xsl:otherwise> 
		</xsl:choose>		
	</xsl:variable>
	
	<xsl:variable name="rghtArrow_">
		<xsl:choose>
			<xsl:when test="((($rghtRnk = 'INITIATOR') or ($rghtRnk = 'MASTER')) and ($busStd = 'FSL'))">BusArrowHInitiator</xsl:when>
			<xsl:otherwise>BusArrowEast</xsl:otherwise> 
		</xsl:choose>		
	</xsl:variable>
	
	
	<xsl:variable name="bus_Y_" select="($bc_Y + ceiling($BIFC_H div 2) - ceiling($BUS_ARROW_H div 2))"/>
	
	<use  x="{$bcLeft_X}"                y="{$bus_Y_}"  xlink:href="#{$busStd}_{$leftArrow_}"/>	
	<use  x="{$bcRght_X - $BUS_ARROW_W}" y="{$bus_Y_}"  xlink:href="#{$busStd}_{$rghtArrow_}"/>	
	
	<rect x="{$bcLeft_X + $BUS_ARROW_W}" 
		  y="{$bus_Y_   + $BUS_ARROW_G}"  
		  width= "{$pr2pr_W_    - (2 * $BUS_ARROW_W)}" 
		  height="{$BUS_ARROW_H - (2 * $BUS_ARROW_G)}" style="stroke:none; fill:{$busCol_}"/>
	
	<text class="horizp2pbuslabel" 
			  x="{$bcLeft_X  + $BUS_ARROW_W + ceiling($BUS_ARROW_W div 2) + ceiling($BUS_ARROW_W div 4) + 4}"
			  y="{($bus_Y_)}">
			<xsl:value-of select="$busName"/>
	</text>
	
	<text class="horizp2pbuslabel" 
			  x="{$bcRght_X - (string-length($busName) * 8)}"
			  y="{($bus_Y_)}">
			<xsl:value-of select="$busName"/>
	</text>
	
</xsl:template>
	
	
<xsl:template name="Draw_SplitConnBus">
	
	<xsl:param name="bc_X"     select="0"/>
	<xsl:param name="bc_Y"     select="0"/>
	<xsl:param name="bc_Rnk"   select="'_unk_'"/>
	<xsl:param name="bc_Side"  select="'_unk_'"/>
	
	<xsl:param name="busStd"   select="'_bstd_'"/>
	<xsl:param name="busName"  select="'_p2pbus_'"/>
	
	<xsl:variable name="busCol_">
		<xsl:call-template name="BusType2Color">
			<xsl:with-param name="busType" select="$busStd"/>
		</xsl:call-template>	
	</xsl:variable>
	
	<xsl:variable name="connArrow_">
		<xsl:choose>
			<xsl:when test="((($bc_Rnk = 'INITIATOR') or ($bc_Rnk = 'MASTER')) and ($busStd = 'FSL'))">BusArrowHInitiator</xsl:when>
			<xsl:otherwise>BusArrowEast</xsl:otherwise> 
		</xsl:choose>		
	</xsl:variable>
	
	<xsl:variable name="arrow_Y_" select="($bc_Y + ceiling($BIFC_H div 2) - ceiling($BUS_ARROW_H div 2))"/>
	
	<xsl:variable name="bus_X_">
		<xsl:choose>
			<xsl:when test="$bc_Side = '0'"><xsl:value-of select="($bc_X - ($BUS_ARROW_W * 2))"/></xsl:when>
			<xsl:when test="$bc_Side = '1'"><xsl:value-of select="($bc_X + $BIFC_W + $BUS_ARROW_W)"/></xsl:when>
		</xsl:choose>		
	</xsl:variable>	
	
<!--	
	<use  x="{$bus_X_}"  y="{$arrow_Y_}"  xlink:href="#{$busStd}_BusArrowHInitiator"/>	
-->	
	
	<xsl:variable name="arrow_X_">
		<xsl:choose>
			<xsl:when test="$bc_Side = '0'"><xsl:value-of select="($bc_X - $BUS_ARROW_W)"/></xsl:when>
			<xsl:when test="$bc_Side = '1'"><xsl:value-of select="($bc_X + $BIFC_W)"/></xsl:when>
		</xsl:choose>		
	</xsl:variable>	
	
<!--	
	<xsl:message>The bus name is <xsl:value-of select="$busName"/></xsl:message>
	<xsl:message>The bif side is <xsl:value-of select="$bc_Side"/></xsl:message>
	<xsl:message>The bif rank is <xsl:value-of select="$bc_Rnk"/></xsl:message>
-->	
	<xsl:choose>
		<xsl:when test="(($busStd = 'FSL') and (($bc_Rnk = 'MASTER') or ($bc_Rnk = 'INITIATOR')))">
			<use  x="{$arrow_X_}"  y="{$arrow_Y_}"  xlink:href="#{$busStd}_{$connArrow_}"/>	
			<use  x="{$bus_X_}"  y="{$arrow_Y_}"  xlink:href="#{$busStd}_BusArrowHInitiator"/>	
		</xsl:when>
		<xsl:when test="(($bc_Side = '1') and not(@busStd = 'FSL') and (($bc_Rnk = 'MASTER') or ($bc_Rnk = 'INITIATOR')))">
			<use  x="{$arrow_X_ - $BIFC_W}"  y="{$arrow_Y_}"  xlink:href="#{$busStd}_SplitBus_WEST"/>
		</xsl:when>
		<xsl:when test="(($bc_Side = '1') and (($bc_Rnk = 'SLAVE') or ($bc_Rnk = 'TARGET') or ($bc_Rnk = 'TRANSPARENT')))">
			<use  x="{$arrow_X_}"  y="{$arrow_Y_}"  xlink:href="#{$busStd}_SplitBus_EAST"/>
		</xsl:when>
		<xsl:otherwise>
			<use  x="{$arrow_X_}"  y="{$arrow_Y_}"  xlink:href="#{$busStd}_{$connArrow_}"/>	
			<use  x="{$bus_X_}"  y="{$arrow_Y_}"  xlink:href="#{$busStd}_BusArrowHInitiator"/>	
		</xsl:otherwise>
	</xsl:choose>
	
	<xsl:variable name="text_X_">
		<xsl:choose>
			<xsl:when test="$bc_Side = '0'"><xsl:value-of select="($bus_X_ - $BUS_ARROW_W - (string-length($busName) * 5))"/></xsl:when>
			<xsl:when test="$bc_Side = '1'"><xsl:value-of select="($bus_X_ + $BUS_ARROW_W)"/></xsl:when>
		</xsl:choose>		
	</xsl:variable>	
		
	
	<text class="horizp2pbuslabel" 
			  x="{$text_X_}"
			  y="{($arrow_Y_)}">
			<xsl:value-of select="$busName"/>
	</text>
	
</xsl:template>
	
	
<xsl:template name="Define_SharedBus"> 
	
	<xsl:param name="bus_type"    select="'OPB'"/>
	<xsl:param name="drawarea_w"  select="500"/>
	
	<xsl:variable name="sharedbus_w_"  select="($drawarea_w - ($BLKD_INNER_GAP * 2))"/>
	
	<xsl:variable name="bus_col_">
		<xsl:call-template name="BusType2Color">
			<xsl:with-param name="busType" select="$bus_type"/>
		</xsl:call-template>	
	</xsl:variable>
	
	<xsl:variable name="bus_col_lt_">
		<xsl:call-template name="BusType2LightColor">
			<xsl:with-param name="busType" select="$bus_type"/>
		</xsl:call-template>	
	</xsl:variable>
	
	 <symbol id="{$bus_type}_SharedBus">
		<use  x="0"                            y="0"    xlink:href="#{$bus_type}_BusArrowWest"/>	
		<use  x="{$sharedbus_w_ - $BUS_ARROW_W}" y="0"  xlink:href="#{$bus_type}_BusArrowEast"/>	
		
		<rect x="{$BUS_ARROW_W}" 
			  y="{$BUS_ARROW_G}"  
			  width= "{$sharedbus_w_  - ($BUS_ARROW_W * 2)}" 
			  height="{$BUS_ARROW_H - (2 * $BUS_ARROW_G)}" style="stroke:none; fill:{$bus_col_}"/>
	</symbol>
</xsl:template>

	
<xsl:template name="Define_SplitBusses"> 
	
	<xsl:param name="bus_type"    sselect="'FSL'"/>
	
	<xsl:variable name="bus_col_">
		<xsl:call-template name="BusType2Color">
			<xsl:with-param name="busType" select="$bus_type"/>
		</xsl:call-template>	
	</xsl:variable>
	
	<xsl:variable name="bifc_r_" select="ceiling($BIFC_W div 3)"/>
	
	 <symbol id="{$bus_type}_SplitBus_EAST">
		<use  x="0"  y="0"    xlink:href="#{$bus_type}_BusArrowWest"/>	
		
		<rect x="{$BUS_ARROW_W}" 
			  y="{$BUS_ARROW_G}"  
			  width= "{$BIFC_W}" 
			  height="{$BUS_ARROW_H - (2 * $BUS_ARROW_G)}" style="stroke:none; fill:{$bus_col_}"/>
		 
<!--		 
		<rect x="{$BUS_ARROW_W + $BIFC_W}"
			  y="0"  
			  width= "{$BIFC_W}" 
			  height="{$BUS_ARROW_H}" style="stroke:none; fill:{$bus_col_}"/>
	-->	 
<!--		
		<circle 
			  cx="{$BUS_ARROW_W + $BIFC_W}"  
			  cy="{ceiling($BIFC_Wi div 2)}" 
			  r="{ceiling($BIFC_Wi div 2)}" 
			  style="fill:{$bus_col_}; stroke:none;"/> 	  
-->		 
	</symbol>
	
	<xsl:variable name="splbus_w_" select="($BUS_ARROW_W + $BIFC_W + $BIFC_Wi)"/>
	
	 <symbol id="{$bus_type}_SplitBus_WEST">
		<use   x="0"   y="0"  xlink:href="#{$bus_type}_SplitBus_EAST" transform="scale(-1,1) translate({$splbus_w_ * -1},0)"/>
		 
	</symbol>
	
	 <symbol id="{$bus_type}_SplitBus_OneWay">
		 
<!--		 
		<use  x="0"  y="0"    xlink:href="#{$bus_type}_BusArrowWest"/>	
-->	
		<rect x="0" 
			  y="{$BUS_ARROW_G}"  
			  width= "{($BUS_ARROW_W * 2)}" 
			  height="{$BUS_ARROW_H - (2 * $BUS_ARROW_G)}" style="stroke:none; fill:{$bus_col_}"/>
		 
		<rect x="{($BUS_ARROW_W * 2)}"
			  y="0"  
			  width= "{$BUS_ARROW_H}" 
			  height="{$BUS_ARROW_H}" style="stroke:none; fill:{$bus_col_}"/>
		 
<!--		 
		
		<rect x="{$BUS_ARROW_W}" 
			  y="{$BUS_ARROW_G}"  
			  width= "{$BUS_ARROW_W}" 
			  height="{$BUS_ARROW_H}" style="stroke:none; fill:{$bus_col_}"/>
		<circle 
			  cx="{$BUS_ARROW_W + $BIFC_W}"  
			  cy="{ceiling($BIFC_Wi div 2)}" 
			  r="{ceiling($BIFC_Wi div 2)}" 
			  style="fill:{$bus_col_}; stroke:none;"/> 	  
-->	
	</symbol>
	
	
</xsl:template>


<xsl:template name="Define_SharedBus_Group"> 

<!-- The Bridges go into the shared bus shape -->
	<xsl:for-each select="/EDKSYSTEM/BLKDSHAPES/BRIDGESHAPES/MODULE">	
	
		<xsl:variable name="modInst_" select="@INSTANCE"/>
		<xsl:variable name="modType_" select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE=$modInst_)]/@MODTYPE"/>
		
		<xsl:call-template name="Define_Peripheral"> 
			<xsl:with-param name="modVori"  select="'normal'"/>
			<xsl:with-param name="modInst"  select="$modInst_"/>
			<xsl:with-param name="modType"  select="$modType_"/>
		</xsl:call-template>
	
	</xsl:for-each>
	
 <symbol id="group_sharedBusses">
	
	<!-- Draw the shared bus shapes first -->	
	<xsl:for-each select="BLKDSHAPES/SBSSHAPES/MODULE">	
		<xsl:variable name="instance_"  select="@INSTANCE"/>
		
		<xsl:variable name="busStd_"   select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE=$instance_)]/@BUSSTD"/>	
		<xsl:variable name="busIndex_"  select="/EDKSYSTEM/MODULES/MODULE[(@INSTANCE=$instance_)]/@BUSINDEX"/>	
		
		<xsl:variable name="busY_"  select="($busIndex_ * $SBS_LANE_H)"/>	
		
		<use  x="0"  y="{$busY_}"  xlink:href="#{$busStd_}_SharedBus"/>	
		
		<text class="sharedbuslabel" 
			  x="8"
			  y="{$busY_ + $BUS_ARROW_H + 10}">
			<xsl:value-of select="$instance_"/>
		</text>
		
	</xsl:for-each>
</symbol>	

 <symbol id="KEY_SharedBus">
	<use  x="0"  y="0"  xlink:href="#KEY_BusArrowWest"/>	
	<use  x="30" y="0"  xlink:href="#KEY_BusArrowEast"/>	
	 
	<xsl:variable name="key_col_">
		<xsl:call-template name="BusType2Color">
			<xsl:with-param name="busType" select="'KEY'"/>
		</xsl:call-template>	
	</xsl:variable>
		
	<rect x="{$BUS_ARROW_W}" 
		  y="{$BUS_ARROW_G}"  
		  width= "{30 - $BUS_ARROW_W}" 
		  height="{$BUS_ARROW_H - (2 * $BUS_ARROW_G)}" style="stroke:none; fill:{$key_col_}"/>
</symbol>
	
</xsl:template>
	
</xsl:stylesheet>
