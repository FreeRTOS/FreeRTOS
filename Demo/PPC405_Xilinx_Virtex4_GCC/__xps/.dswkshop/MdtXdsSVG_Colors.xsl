<?xml version="1.0" standalone="no"?>
<xsl:stylesheet version="1.0"
           xmlns:svg="http://www.w3.org/2000/svg"
           xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
           xmlns:exsl="http://exslt.org/common"
           xmlns:xlink="http://www.w3.org/1999/xlink">
           
<xsl:variable name="COL_RED"        select="'#AA0000'"/>
<xsl:variable name="COL_GRAY"       select="'#E1E1E1'"/>
<xsl:variable name="COL_BLACK"      select="'#000000'"/>
<xsl:variable name="COL_WHITE"      select="'#FFFFFF'"/>
<xsl:variable name="COL_YELLOW"     select="'#FFFFDD'"/>
<xsl:variable name="COL_YELLOW_LT"  select="'#FFFFEE'"/>				
				
<xsl:variable name="COL_BG"          select="'#CCCCCC'"/>				
<xsl:variable name="COL_BG_LT"       select="'#EEEEEE'"/>				
<xsl:variable name="COL_UNK_BG"      select="'#DDDDDD'"/>				
<xsl:variable name="COL_PROC_BG"     select="'#FFCCCC'"/>				
<xsl:variable name="COL_PROC_BG_MB"  select="'#222222'"/>				
<xsl:variable name="COL_PROC_BG_PP"  select="'#90001C'"/>				
<xsl:variable name="COL_PROC_BG_USR" select="'#666699'"/>				

<xsl:variable name="COL_MOD_BG"      select="'#F0F0F0'"/>				
<xsl:variable name="COL_MOD_SPRT"    select="'#888888'"/>
<xsl:variable name="COL_MOD_MPRT"    select="'#888888'"/>

<xsl:variable name="COL_INTR_0"      select="'#FF9900'"/>
<xsl:variable name="COL_INTR_1"      select="'#00CCCC'"/>
<xsl:variable name="COL_INTR_2"      select="'#33FF33'"/>
<xsl:variable name="COL_INTR_3"      select="'#FF00CC'"/>
<xsl:variable name="COL_INTR_4"      select="'#99FF33'"/>
<xsl:variable name="COL_INTR_5"      select="'#0066CC'"/>
<xsl:variable name="COL_INTR_6"      select="'#9933FF'"/>
<xsl:variable name="COL_INTR_7"      select="'#3300FF'"/>
<xsl:variable name="COL_INTR_8"      select="'#00FF33'"/>
<xsl:variable name="COL_INTR_9"      select="'#FF3333'"/>


<xsl:variable name="COL_IORING"     select="'#000088'"/>				
<xsl:variable name="COL_IORING_LT"  select="'#CCCCFF'"/>				
<xsl:variable name="COL_SYSPRT"     select="'#0000BB'"/>		        
	
	
<xsl:variable name="COL_BUSSTDS">
	
	<BUSCOLOR BUSSTD="XIL"        RGB="#990066" RGB_LT="#CC3399"/>
	<BUSCOLOR BUSSTD="OCM" 		  RGB="#0000DD" RGB_LT="#9999DD"/>
	<BUSCOLOR BUSSTD="OPB"        RGB="#339900" RGB_LT="#CCDDCC"/>
	<BUSCOLOR BUSSTD="LMB"        RGB="#7777FF" RGB_LT="#DDDDFF"/>
	<BUSCOLOR BUSSTD="FSL"        RGB="#CC00CC" RGB_LT="#FFBBFF"/>
	<BUSCOLOR BUSSTD="DCR"        RGB="#6699FF" RGB_LT="#BBDDFF"/>
	<BUSCOLOR BUSSTD="FCB"        RGB="#8C00FF" RGB_LT="#CCCCFF"/>
	<BUSCOLOR BUSSTD="PLB"        RGB="#FF5500" RGB_LT="#FFBB00"/>
	<BUSCOLOR BUSSTD="PLBV46"     RGB="#BB9955" RGB_LT="#FFFFDD"/>
	<BUSCOLOR BUSSTD="PLBV46_P2P" RGB="#BB9955" RGB_LT="#FFFFDD"/>
	
<!--	
	<BUSCOLOR BUSSTD="PLBV46"     RGB="#9966FF" RGB_LT="#CCCCFF"/>
	<BUSCOLOR BUSSTD="PLBV46_P2P" RGB="#9966FF" RGB_LT="#CCCCFF"/>
	<BUSCOLOR BUSSTD="PLB"        RGB="#FFAA33" RGB_LT="#FFEE33"/>
	<BUSCOLOR BUSSTD="PLBV46"     RGB="#FF5500" RGB_LT="#FFBB00"/>
	<BUSCOLOR BUSSTD="PLBV46_P2P" RGB="#FF5500" RGB_LT="#FFBB00"/>
-->	
	
	<BUSCOLOR BUSSTD="TRS"         RGB="#009999" RGB_LT="#00CCCC"/>
	<BUSCOLOR BUSSTD="TRANS"       RGB="#009999" RGB_LT="#00CCCC"/>
	<BUSCOLOR BUSSTD="TRANSPARENT" RGB="#009999" RGB_LT="#00CCCC"/>

	<BUSCOLOR BUSSTD="TARGET"      RGB="#009999" RGB_LT="#00CCCC"/>
	<BUSCOLOR BUSSTD="INITIATOR"   RGB="#009999" RGB_LT="#00CCCC"/>
	
	<BUSCOLOR BUSSTD="KEY" 		   RGB="#444444" RGB_LT="#888888"/>
	
</xsl:variable>
	
<xsl:template name="BusType2Color">
	<xsl:param name="busType"  select="'OPB'"/>
	
	<xsl:choose>
		<xsl:when test="exsl:node-set($COL_BUSSTDS)/BUSCOLOR[(@BUSSTD = $busType)]/@RGB">
			<xsl:value-of select="exsl:node-set($COL_BUSSTDS)/BUSCOLOR[(@BUSSTD = $busType)]/@RGB"/>
		</xsl:when>
		<xsl:otherwise>
			<xsl:value-of select="exsl:node-set($COL_BUSSTDS)/BUSCOLOR[(@BUSSTD = 'TRS')]/@RGB"/>
		</xsl:otherwise>
	</xsl:choose>		
</xsl:template>	
	
	
<xsl:template name="BusType2LightColor">
	<xsl:param name="busType"  select="'OPB'"/>
	
<!--	
	<xsl:message>The color of bus  <xsl:value-of select="$busType"/> is <xsl:value-of select="exsl:node-set($COL_BUSSTDS)/BUSCOLOR[(@BUSSTD = $busType)]/@RGB"/>
-->	
		
	<xsl:choose>
		<xsl:when test="exsl:node-set($COL_BUSSTDS)/BUSCOLOR[(@BUSSTD = $busType)]/@RGB_LT">
			<xsl:value-of select="exsl:node-set($COL_BUSSTDS)/BUSCOLOR[(@BUSSTD = $busType)]/@RGB_LT"/>
		</xsl:when>
		<xsl:otherwise>
			<xsl:value-of select="exsl:node-set($COL_BUSSTDS)/BUSCOLOR[(@BUSSTD = 'TRS')]/@RGB_LT"/>
		</xsl:otherwise>
	</xsl:choose>		
</xsl:template>	
		

<xsl:template name="intcIdx2Color">
	<xsl:param name="intcIdx"  select="'0'"/>

	<xsl:variable name="idx_" select="$intcIdx mod 9"/>
	
	<xsl:choose>
		<xsl:when test="$idx_ = '0'"><xsl:value-of select="$COL_INTR_0"/></xsl:when>
		<xsl:when test="$idx_ = '1'"><xsl:value-of select="$COL_INTR_1"/></xsl:when>
		<xsl:when test="$idx_ = '2'"><xsl:value-of select="$COL_INTR_2"/></xsl:when>
		<xsl:when test="$idx_ = '3'"><xsl:value-of select="$COL_INTR_3"/></xsl:when>
		<xsl:when test="$idx_ = '4'"><xsl:value-of select="$COL_INTR_4"/></xsl:when>
		<xsl:when test="$idx_ = '5'"><xsl:value-of select="$COL_INTR_5"/></xsl:when>
		<xsl:when test="$idx_ = '6'"><xsl:value-of select="$COL_INTR_6"/></xsl:when>
		<xsl:when test="$idx_ = '7'"><xsl:value-of select="$COL_INTR_7"/></xsl:when>
		<xsl:when test="$idx_ = '8'"><xsl:value-of select="$COL_INTR_8"/></xsl:when>
		<xsl:when test="$idx_ = '9'"><xsl:value-of select="$COL_INTR_9"/></xsl:when>
		<xsl:otherwise>
			<xsl:value-of select="$COL_INTR_0"/>	
		</xsl:otherwise>
	</xsl:choose>
</xsl:template>


</xsl:stylesheet>
