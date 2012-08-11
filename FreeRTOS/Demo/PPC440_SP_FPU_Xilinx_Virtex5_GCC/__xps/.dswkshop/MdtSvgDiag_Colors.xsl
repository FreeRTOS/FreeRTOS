<?xml version="1.0" standalone="no"?>
<xsl:stylesheet version="1.0"
           xmlns:svg="http://www.w3.org/2000/svg"
           xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
           xmlns:exsl="http://exslt.org/common"
           xmlns:xlink="http://www.w3.org/1999/xlink">
           
<xsl:variable name="COL_RED"        select="'#AA0000'"/>
<xsl:variable name="COL_GRAY"       select="'#E1E1E1'"/>
<xsl:variable name="COL_XLNX"       select="'#AA0017'"/>
<xsl:variable name="COL_BLACK"      select="'#000000'"/>
<xsl:variable name="COL_WHITE"      select="'#FFFFFF'"/>
<xsl:variable name="COL_YELLOW"     select="'#FFFFDD'"/>
<xsl:variable name="COL_YELLOW_LT"  select="'#FFFFEE'"/>
				
<xsl:variable name="COL_BG"          select="'#CCCCCC'"/>
<xsl:variable name="COL_BG_LT"       select="'#EEEEEE'"/>
<xsl:variable name="COL_BG_UNK"      select="'#DDDDDD'"/>
	
<xsl:variable name="COL_PROC_BG"     select="'#FFCCCC'"/>
<xsl:variable name="COL_PROC_BG_MB"  select="'#222222'"/>
<xsl:variable name="COL_PROC_BG_PP"  select="'#90001C'"/>
<xsl:variable name="COL_PROC_BG_USR" select="'#666699'"/>
	
<xsl:variable name="COL_MPMC_BG"     select="'#8B0800'"/>
	
<xsl:variable name="COL_MOD_BG"      select="'#F0F0F0'"/>
<xsl:variable name="COL_MOD_SPRT"    select="'#888888'"/>
<xsl:variable name="COL_MOD_MPRT"    select="'#888888'"/>


<xsl:variable name="COL_IORING"     select="'#000088'"/>
<xsl:variable name="COL_IORING_LT"  select="'#CCCCFF'"/>
<xsl:variable name="COL_SYSPRT"     select="'#0000BB'"/>

<!-- 
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
-->

<xsl:variable name="COL_INTCS">
	<INTCCOLOR INDEX="0"	RGB="#FF9900"/> 
	<INTCCOLOR INDEX="1"	RGB="#00CCCC"/> 
	<INTCCOLOR INDEX="2"	RGB="#33FF33"/> 
	<INTCCOLOR INDEX="3"	RGB="#FF00CC"/> 
	<INTCCOLOR INDEX="4"	RGB="#99FF33"/> 
	<INTCCOLOR INDEX="5"	RGB="#0066CC"/> 
	<INTCCOLOR INDEX="6"	RGB="#9933FF"/> 
	<INTCCOLOR INDEX="7"	RGB="#3300FF"/> 
	<INTCCOLOR INDEX="8"	RGB="#00FF33"/> 
	<INTCCOLOR INDEX="9"	RGB="#FF3333"/> 
</xsl:variable>
	
<xsl:variable name="COL_BUSSTDS">

	<BUSCOLOR BUSSTD="XIL"        RGB="#990066" RGB_LT="#CC3399"/>
	<BUSCOLOR BUSSTD="OCM" 		  RGB="#0000DD" RGB_LT="#9999DD"/>
	<BUSCOLOR BUSSTD="OPB"        RGB="#339900" RGB_LT="#CCDDCC"/>
	<BUSCOLOR BUSSTD="LMB"        RGB="#7777FF" RGB_LT="#DDDDFF"/>
	<BUSCOLOR BUSSTD="FSL"        RGB="#CC00CC" RGB_LT="#FFBBFF"/>
	<BUSCOLOR BUSSTD="DCR"        RGB="#6699FF" RGB_LT="#BBDDFF"/>
	<BUSCOLOR BUSSTD="FCB"        RGB="#8C00FF" RGB_LT="#CCCCFF"/>
	<BUSCOLOR BUSSTD="PLB"        RGB="#FF5500" RGB_LT="#FFBB00"/>
	<BUSCOLOR BUSSTD="PLBV34"     RGB="#FF5500" RGB_LT="#FFBB00"/>
	<BUSCOLOR BUSSTD="PLBV34_P2P" RGB="#FF5500" RGB_LT="#FFBB00"/>
	<BUSCOLOR BUSSTD="PLBV46"     RGB="#BB9955" RGB_LT="#FFFFDD"/>
	<BUSCOLOR BUSSTD="PLBV46_P2P" RGB="#BB9955" RGB_LT="#FFFFDD"/>
	
<!--	
	<BUSCOLOR BUSSTD="PLBV46"     RGB="#9966FF" RGB_LT="#CCCCFF"/>
	<BUSCOLOR BUSSTD="PLBV46_P2P" RGB="#9966FF" RGB_LT="#CCCCFF"/>
	<BUSCOLOR BUSSTD="PLB"        RGB="#FFAA33" RGB_LT="#FFEE33"/>
	<BUSCOLOR BUSSTD="PLBV46"     RGB="#FF5500" RGB_LT="#FFBB00"/>
	<BUSCOLOR BUSSTD="PLBV46_P2P" RGB="#FF5500" RGB_LT="#FFBB00"/>
-->	
	
	<BUSCOLOR BUSSTD="TARGET"      RGB="#009999" RGB_LT="#00CCCC"/>
	<BUSCOLOR BUSSTD="INITIATOR"   RGB="#009999" RGB_LT="#00CCCC"/>
	
	<BUSCOLOR BUSSTD="USER"        RGB="#009999" RGB_LT="#00CCCC"/>
	<BUSCOLOR BUSSTD="KEY" 		   RGB="#444444" RGB_LT="#888888"/>
	
</xsl:variable>
	
<xsl:template name="F_BusStd2RGB">
	<xsl:param name="iBusStd"  select="'USER'"/>
	
	<xsl:choose>
		<xsl:when test="exsl:node-set($COL_BUSSTDS)/BUSCOLOR[(@BUSSTD = $iBusStd)]/@RGB">
			<xsl:value-of select="exsl:node-set($COL_BUSSTDS)/BUSCOLOR[(@BUSSTD = $iBusStd)]/@RGB"/>
		</xsl:when>
		<xsl:otherwise>
			<xsl:value-of select="exsl:node-set($COL_BUSSTDS)/BUSCOLOR[(@BUSSTD = 'USER')]/@RGB"/>
		</xsl:otherwise>
	</xsl:choose>		
</xsl:template>	
	
<xsl:template name="F_BusStd2RGB_LT">
	<xsl:param name="iBusStd"  select="'USER'"/>
	
	<xsl:choose>
		<xsl:when test="exsl:node-set($COL_BUSSTDS)/BUSCOLOR[(@BUSSTD = $iBusStd)]/@RGB_LT">
			<xsl:value-of select="exsl:node-set($COL_BUSSTDS)/BUSCOLOR[(@BUSSTD = $iBusStd)]/@RGB_LT"/>
		</xsl:when>
		<xsl:otherwise>
			<xsl:value-of select="exsl:node-set($COL_BUSSTDS)/BUSCOLOR[(@BUSSTD = 'USER')]/@RGB_LT"/>
		</xsl:otherwise>
	</xsl:choose>		
</xsl:template>	
		
<xsl:template name="F_IntcIdx2RGB">
	<xsl:param name="iIntcIdx"  select="'0'"/>

	<xsl:variable name="index_" select="$iIntcIdx mod 9"/>

	<xsl:choose>
		<xsl:when test="exsl:node-set($COL_INTCS)/INTCCOLOR[(@INDEX = $index_)]/@RGB">
			<xsl:value-of select="exsl:node-set($COL_INTCS)/INTCCOLOR[(@INDEX = $index_)]/@RGB"/>
		</xsl:when>
		<xsl:otherwise>
			<xsl:value-of select="exsl:node-set($COL_INTCS)/INTCCOLOR[(@INDEX = '0')]/@RGB"/>
		</xsl:otherwise>
	</xsl:choose>		
</xsl:template>

</xsl:stylesheet>
