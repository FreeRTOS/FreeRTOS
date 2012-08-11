<?xml version="1.0" standalone="no"?>
<xsl:stylesheet version="1.0"
           xmlns:svg="http://www.w3.org/2000/svg"
           xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
           xmlns:exsl="http://exslt.org/common"
           xmlns:xlink="http://www.w3.org/1999/xlink">
                
<xsl:output method="xml" version="1.0" encoding="UTF-8" indent="yes"
	       doctype-public="-//W3C//DTD SVG 1.0//EN"
		   doctype-system="http://www.w3.org/TR/SVG/DTD/svg10.dtd"/>
			
<!-- ======================= DEF BLOCK =================================== -->

<xsl:template name="Define_ConnectedBifTypes">

	<xsl:for-each select="exsl:node-set($COL_BUSSTDS)/BUSCOLOR">
		<xsl:variable name="busStd_" select="@BUSSTD"/>
	
		<xsl:for-each select="exsl:node-set($G_BIFTYPES)/BIFTYPE">
			<xsl:variable name="bifType_" select="@TYPE"/>
			
			<xsl:variable name="connectedBifs_cnt_"  select="count($G_ROOT/EDKSYSTEM/MODULES/MODULE/BUSINTERFACE[((@IS_INMHS = 'TRUE') and (@TYPE = $bifType_) and (@BUSSTD = $busStd_))])"/>
			
			<xsl:if test="($connectedBifs_cnt_ &gt; 0)">
<!-- 
				<xsl:message>DEBUG : Connected BifType : <xsl:value-of select="$busStd_"/> : <xsl:value-of select="@TYPE"/> : <xsl:value-of select="$connectedBifs_cnt_"/> </xsl:message> 
-->				
				<xsl:call-template name="Define_BifTypeConnector"> 
					<xsl:with-param name="iBusStd"  select="$busStd_"/>
					<xsl:with-param name="iBifType" select="$bifType_"/>
				</xsl:call-template>
				
				<xsl:call-template name="Define_BifLabel"> 
					<xsl:with-param name="iBusStd"  select="$busStd_"/>
				</xsl:call-template>
				
			</xsl:if>
			
		</xsl:for-each>
		
	</xsl:for-each>
	
	<xsl:for-each select="exsl:node-set($G_BIFTYPES)/BIFTYPE">
		<xsl:variable name="bifType_" select="@TYPE"/>
	
		<xsl:call-template name="Define_BifTypeConnector"> 
			<xsl:with-param name="iBusStd"  select="'KEY'"/>
			<xsl:with-param name="iBifType" select="$bifType_"/>
		</xsl:call-template>
			
		<xsl:call-template name="Define_BifLabel"> 
			<xsl:with-param name="iBusStd"  select="'KEY'"/>
		</xsl:call-template>
	</xsl:for-each>	
	
</xsl:template>

<xsl:template name="Define_BifLabel"> 
	
	<xsl:param name="iBusStd"    select="'OPB'"/>
	
	<xsl:variable name="busStdColor_">
		<xsl:call-template name="F_BusStd2RGB">
			<xsl:with-param name="iBusStd" select="$iBusStd"/>
		</xsl:call-template>	
	</xsl:variable>
			
    <g id="{$iBusStd}_BifLabel">
		<rect x="0"  
			  y="0" 
			  rx="3"
			  ry="3"
			  width= "{$BIF_W}" 
			  height="{$BIF_H}" 
			  style="fill:{$busStdColor_}; stroke:black; stroke-width:1"/> 
	</g>
	
</xsl:template>


<xsl:template name="Define_BifTypeConnector"> 
	
	<xsl:param name="iBusStd"     select="'OPB'"/>
	<xsl:param name="iBifType"    select="'USER'"/>
	
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
	
	<xsl:variable name="bifc_wi_" select="ceiling($BIFC_W div 3)"/>
	<xsl:variable name="bifc_hi_" select="ceiling($BIFC_H div 3)"/>
	
	<xsl:choose>
	
		<xsl:when test="$iBifType = 'SLAVE'">
    		<g id="{$iBusStd}_busconn_{$iBifType}">
				<circle 
			  		cx="{ceiling($BIFC_W div 2)}"  
			  		cy="{ceiling($BIFC_H div 2)}" 
			 		r="{ceiling($BIFC_W  div 2)}" 
			  		style="fill:{$busStdColor_lt_}; stroke:{$busStdColor_}; stroke-width:1"/> 
				<circle 
			  		cx="{ceiling($BIFC_W div 2) + 0.5}"  
			  		cy="{ceiling($BIFC_H div 2)}" 
			  		r="{ceiling($BIFC_Wi div 2)}" 
			  		style="fill:{$busStdColor_}; stroke:none;"/> 
			</g>
		</xsl:when>
	
		<xsl:when test="$iBifType = 'MASTER'">
    		<g id="{$iBusStd}_busconn_{$iBifType}">
				<rect x="0"  
			  		  y="0" 
			  		  width= "{$BIFC_W}" 
			  		  height="{$BIFC_H}" 
			  		  style="fill:{$busStdColor_lt_}; stroke:{$busStdColor_}; stroke-width:1"/> 
				<rect x="{$BIFC_dx + 0.5}"  
			  		  y="{$BIFC_dy}" 
			  		  width= "{$BIFC_Wi}" 
			  		  height="{$BIFC_Hi}" 
			  		  style="fill:{$busStdColor_}; stroke:none;"/> 
			</g>
		</xsl:when>
		
		<xsl:when test="$iBifType = 'INITIATOR'">
    		<g id="{$iBusStd}_busconn_{$iBifType}">
				<rect x="0"  
			  		  y="0" 
			          width= "{$BIFC_W}" 
			          height="{$BIFC_H}" 
			          style="fill:{$busStdColor_lt_}; stroke:{$busStdColor_}; stroke-width:1"/> 
				<rect x="{$BIFC_dx + 0.5}"  
			  		  y="{$BIFC_dy}" 
			          width= "{$BIFC_Wi}" 
			          height="{$BIFC_Hi}" 
			  	      style="fill:{$busStdColor_}; stroke:none;"/> 
			</g>
		</xsl:when>
		
		<xsl:when test="$iBifType = 'TARGET'">
    		<g id="{$iBusStd}_busconn_{$iBifType}">
				<circle 
			  		cx="{ceiling($BIFC_W div 2)}"  
			  		cy="{ceiling($BIFC_H div 2)}" 
			  		r="{ceiling($BIFC_W  div 2)}" 
			  		style="fill:{$busStdColor_lt_}; stroke:{$busStdColor_}; stroke-width:1"/> 
				<circle 
			  		cx="{ceiling($BIFC_W div 2) + 0.5}"  
			  		cy="{ceiling($BIFC_H div 2)}" 
			  		r="{ceiling($BIFC_Wi div 2)}" 
			  		style="fill:{$busStdColor_}; stroke:none;"/> 
			</g>
		</xsl:when>
		
		<xsl:when test="$iBifType = 'MASTER_SLAVE'">
    		<g id="{$iBusStd}_busconn_{$iBifType}">
				<circle 
			  		cx="{ceiling($BIFC_W div 2)}"  
			  		cy="{ceiling($BIFC_H div 2)}" 
			  		r="{ceiling($BIFC_W  div 2)}" 
			  		style="fill:{$busStdColor_lt_}; stroke:{$busStdColor_}; stroke-width:1"/> 
				<circle 
			  		cx="{ceiling($BIFC_W div 2) + 0.5}"  
			  		cy="{ceiling($BIFC_H div 2)}" 
			  		r="{ceiling($BIFC_Wi div 2)}" 
			  		style="fill:{$busStdColor_}; stroke:none;"/> 
				<rect 
					x="0"  
			  		y="{ceiling($BIFC_H div 2)}" 
			  		width= "{$BIFC_W}" 
			  		height="{ceiling($BIFC_H div 2)}" 
			  		style="fill:{$busStdColor_lt_}; stroke:{$busStdColor_}; stroke-width:1"/> 
				<rect 
					x="{$BIFC_dx + 0.5}"  
			  		y="{ceiling($BIFC_H div 2)}" 
			  		width= "{$BIFC_Wi}" 
			  		height="{ceiling($BIFC_Hi div 2)}" 
			  		style="fill:{$busStdColor_}; stroke:none;"/> 
			</g>
		</xsl:when>
		
		<xsl:when test="$iBifType = 'MONITOR'">
  			<g id="{$iBusStd}_busconn_{$iBifType}">
				<rect 
					x="0"  
			 		y="0.5" 
			  		width= "{$BIFC_W}" 
			  		height="{ceiling($BIFC_Hi div 2)}" 
			  		style="fill:{$busStdColor_}; stroke:none;"/> 
				<rect 
					x="0"  
			  		y="{ceiling($BIFC_H div 2) + 4}" 
			  		width= "{$BIFC_W}" 
			  		height="{ceiling($BIFC_Hi div 2)}" 
			  		style="fill:{$busStdColor_}; stroke:none;"/> 
			</g>
		</xsl:when>
		
		<xsl:when test="$iBifType  = 'USER'">
    		<g id="{$iBusStd}_busconn_USER">
				<circle 
			  		cx="{ceiling($BIFC_W div 2)}"  
			  		cy="{ceiling($BIFC_H div 2)}" 
			  		r="{ceiling($BIFC_W  div 2)}" 
			  		style="fill:{$busStdColor_lt_}; stroke:{$busStdColor_}; stroke-width:1"/> 
				<circle 
			  		cx="{ceiling($BIFC_W div 2) + 0.5}"  
			  		cy="{ceiling($BIFC_H div 2)}" 
			  		r="{ceiling($BIFC_Wi div 2)}" 
			  		style="fill:{$busStdColor_}; stroke:none;"/> 
			</g>
		</xsl:when>
		
		<xsl:otherwise>
    		<g id="{$iBusStd}_busconn_{$iBifType}">
				<circle 
			  		cx="{ceiling($BIFC_W div 2)}"  
			  		cy="{ceiling($BIFC_H div 2)}" 
			  		r="{ceiling($BIFC_W  div 2)}" 
			  		style="fill:{$COL_WHITE}; stroke:{$busStdColor_}; stroke-width:1"/> 
				<circle 
			  		cx="{ceiling($BIFC_W div 2) + 0.5}"  
			  		cy="{ceiling($BIFC_H div 2)}" 
			  		r="{ceiling($BIFC_Wi div 2)}" 
			  		style="fill:{$COL_WHITE}; stroke:none;"/> 
			</g>
		</xsl:otherwise>
	</xsl:choose>
	
</xsl:template>


</xsl:stylesheet>
