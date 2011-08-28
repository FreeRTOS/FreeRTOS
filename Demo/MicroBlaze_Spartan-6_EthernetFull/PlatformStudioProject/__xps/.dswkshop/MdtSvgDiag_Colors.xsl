<?xml version="1.0" standalone="no"?>
<xsl:stylesheet version="1.0"
	   xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
       xmlns:exsl="http://exslt.org/common"
       xmlns:dyn="http://exslt.org/dynamic"
       xmlns:math="http://exslt.org/math"
       xmlns:xlink="http://www.w3.org/1999/xlink"
       extension-element-prefixes="math dyn exsl xlink">
           
<!--  Generic colors, shared between modules like webpages diagrams and pdfs -->           

<xsl:variable name="COL_XLNX"       select="'#AA0017'"/>

<xsl:variable name="COL_BLACK"      select="'#000000'"/>
<xsl:variable name="COL_WHITE"      select="'#FFFFFF'"/>

<xsl:variable name="COL_GRAY"       select="'#CECECE'"/>
<xsl:variable name="COL_GRAY_LT"    select="'#E1E1E1'"/>
<xsl:variable name="COL_GRAY_DK"    select="'#B1B1B1'"/>

<xsl:variable name="COL_YELLOW"     select="'#FFFFDD'"/>
<xsl:variable name="COL_YELLOW_LT"  select="'#FFFFEE'"/>

<xsl:variable name="COL_RED"        select="'#AA0000'"/>

<xsl:variable name="COL_GREEN"      select="'#33CC33'"/>

<xsl:variable name="COL_BLUE_LT"    select="'#AAAAFF'"/>

<!--  Colors specific to  the Diagrams -->
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
	<BUSCOLOR BUSSTD="AXI"        RGB="#0084AB" RGB_LT="#D0E6EF" RGB_DK="#85C3D9" RGB_TXT="#FFFFFF"/>
	<BUSCOLOR BUSSTD="XIL"        RGB="#990066" RGB_LT="#CC3399" RGB_DK="#85C3D9" RGB_TXT="#FFFFFF"/>
	<BUSCOLOR BUSSTD="OCM" 		  RGB="#0000DD" RGB_LT="#9999DD" RGB_DK="#85C3D9" RGB_TXT="#FFFFFF"/>
	<BUSCOLOR BUSSTD="OPB"        RGB="#339900" RGB_LT="#CCDDCC" RGB_DK="#85C3D9" RGB_TXT="#FFFFFF"/>
	
	<BUSCOLOR BUSSTD="LMB"        RGB="#7777FF" RGB_LT="#DDDDFF" RGB_DK="#85C3D9" RGB_TXT="#FFFFFF"/>
	<BUSCOLOR BUSSTD="FSL"        RGB="#CC00CC" RGB_LT="#FFBBFF" RGB_DK="#85C3D9" RGB_TXT="#FFFFFF"/>
	<BUSCOLOR BUSSTD="DCR"        RGB="#6699FF" RGB_LT="#BBDDFF" RGB_DK="#85C3D9" RGB_TXT="#FFFFFF"/>
	<BUSCOLOR BUSSTD="FCB"        RGB="#8C00FF" RGB_LT="#CCCCFF" RGB_DK="#85C3D9" RGB_TXT="#FFFFFF"/>
	
	<BUSCOLOR BUSSTD="PLB"        RGB="#FF5500" RGB_LT="#FFBB00" RGB_DK="#85C3D9" RGB_TXT="#FFFFFF"/>
	<BUSCOLOR BUSSTD="PLBV34"     RGB="#FF5500" RGB_LT="#FFBB00" RGB_DK="#85C3D9" RGB_TXT="#FFFFFF"/>
	<BUSCOLOR BUSSTD="PLBV46"     RGB="#BB9955" RGB_LT="#FFFFDD" RGB_DK="#85C3D9" RGB_TXT="#FFFFFF"/>
	<BUSCOLOR BUSSTD="PLBV46_P2P" RGB="#BB9955" RGB_LT="#FFFFDD" RGB_DK="#85C3D9" RGB_TXT="#FFFFFF"/>
	
	<BUSCOLOR BUSSTD="USER"       RGB="#009999" RGB_LT="#00CCCC" RGB_DK="#85C3D9" RGB_TXT="#FFFFFF"/>
	<BUSCOLOR BUSSTD="KEY"        RGB="#444444" RGB_LT="#888888" RGB_DK="#85C3D9" RGB_TXT="#FFFFFF"/>
	<BUSCOLOR BUSSTD="GRAYSCALE"  RGB="#444444" RGB_LT="#888888" RGB_DK="#85C3D9" RGB_TXT="#FFFFFF"/>
</xsl:variable>
<xsl:variable name = "COL_BUSSTDS_NUMOF" select="count(exsl:node-set($COL_BUSSTDS)/BUSCOLOR)"/>

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

<xsl:template name="F_BusStd2RGB_DK">
    <xsl:param name="iBusStd"  select="'USER'"/>
    <xsl:choose>
        <xsl:when test="exsl:node-set($COL_BUSSTDS)/BUSCOLOR[(@BUSSTD = $iBusStd)]/@RGB_DK">
            <xsl:value-of select="exsl:node-set($COL_BUSSTDS)/BUSCOLOR[(@BUSSTD = $iBusStd)]/@RGB_DK"/>
        </xsl:when>
        <xsl:otherwise>
            <xsl:value-of select="exsl:node-set($COL_BUSSTDS)/BUSCOLOR[(@BUSSTD = 'USER')]/@RGB_DK"/>
        </xsl:otherwise>
    </xsl:choose>       
</xsl:template> 		

<xsl:template name="F_BusStd2RGB_TXT">
    <xsl:param name="iBusStd"  select="'USER'"/>
    <xsl:choose>
        <xsl:when test="exsl:node-set($COL_BUSSTDS)/BUSCOLOR[(@BUSSTD = $iBusStd)]/@RGB_TXT">
            <xsl:value-of select="exsl:node-set($COL_BUSSTDS)/BUSCOLOR[(@BUSSTD = $iBusStd)]/@RGB_TXT"/>
        </xsl:when>
        <xsl:otherwise>
            <xsl:value-of select="exsl:node-set($COL_BUSSTDS)/BUSCOLOR[(@BUSSTD = 'USER')]/@RGB_TXT"/>
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
