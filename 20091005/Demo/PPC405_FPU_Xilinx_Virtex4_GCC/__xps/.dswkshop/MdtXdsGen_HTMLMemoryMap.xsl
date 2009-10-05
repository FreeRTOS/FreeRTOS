<?xml version="1.0" standalone="no"?>

<!DOCTYPE stylesheet [
	<!ENTITY HEXUPPER "ABCDEFxx0123456789">
	<!ENTITY HEXLOWER "abcdefxX0123456789">
	<!ENTITY HEXU2L " '&HEXLOWER;' , '&HEXUPPER;' ">
]>	
<!--
-->

<xsl:stylesheet version="1.0"
           xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
           xmlns:exsl="http://exslt.org/common"
           xmlns:xlink="http://www.w3.org/1999/xlink">
         
<xsl:output method="html"/>
			
<!-- ======================= MAIN MEMORY MAP SECTION =============================== -->
<xsl:template name="Layout_MemoryMap">
<xsl:param name="table_width" select="600"/>

<xsl:variable name="procName" select="@INSTANCE"/>
<!--
<BR></BR>
<BR></BR>
-->
	<xsl:if test="MEMORYMAP/MEMRANGE[(@INSTANCE)]">
		
	<TABLE BGCOLOR="{$DS_COL_BLACK}" WIDTH="{$table_width}" COLS="5" cellspacing="1" cellpadding="2" border="0">
		<TR></TR>	
		<TD COLSPAN="5" width="100%" align="middle" bgcolor="{$DS_COL_XPRP}">
			<A name="_{@INSTANCE}_MemoryMap"/>
			<SPAN style="color:{$DS_COL_WHITE}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">MEMORY MAP</SPAN>
		</TD>
		<TR></TR>
		<TD COLSPAN="5" width="100%" align="middle" bgcolor="{$DS_COL_WHITE}"><SPAN style="color:{$DS_COL_INFO}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">D=DATA ADDRESSABLE &#160;&#160; I=INSTRUCTION ADDRESSABLE</SPAN></TD>
		<TR></TR>
		<TD COLSPAN="1" width="5%"  align="middle" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 12px Verdana,Arial,Helvetica,sans-serif">D</SPAN></TD>
		<TD COLSPAN="1" width="5%"  align="middle" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 12px Verdana,Arial,Helvetica,sans-serif">I</SPAN></TD>
		<TD COLSPAN="1" width="20%" align="middle" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">BASE</SPAN></TD>
		<TD COLSPAN="1" width="20%" align="middle" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">HIGH</SPAN></TD>
		<TD COLSPAN="1" width="50%" align="middle" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">MODULE</SPAN></TD>
		<TR></TR>
		
		<xsl:for-each select="MEMORYMAP/MEMRANGE[(@INSTANCE)]">
			<xsl:sort data-type="number" select="@BASEVALUE" order="ascending"/>
			<TR></TR>
				<xsl:variable name="isdata">
					<xsl:if test="@IS_DATA='TRUE'">&#9632;</xsl:if>	
					<xsl:if test="not(@IS_DATA='TRUE')">&#160;</xsl:if>	
				</xsl:variable>
			
			<xsl:variable name="isinst">
				<xsl:if test="@IS_INSTRUCTION='TRUE'">
					&#9632;
				</xsl:if>	
				<xsl:if test="not(@IS_INSTRUCTION='TRUE')">
					&#160;
				</xsl:if>	
			</xsl:variable>
			
			<xsl:variable name="bupper" select ="@BASE"/>
			<xsl:variable name="hupper" select ="@HIGH"/>
			<xsl:variable name="iname"  select ="@INSTANCE"/>
			<TD COLSPAN="1" width="5%"  align="middle" bgcolor="{$DS_COL_WHITE}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 14px Verdana,Arial,sans-serif"><xsl:value-of select="$isdata"/></SPAN></TD>
			<TD COLSPAN="1" width="5%"  align="middle" bgcolor="{$DS_COL_WHITE}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 14px Verdana,Arial,sans-serif"><xsl:value-of select="$isinst"/></SPAN></TD>
			<TD COLSPAN="1" width="20%" align="middle" bgcolor="{$DS_COL_WHITE}"><SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="translate($bupper,&HEXU2L;)"/></SPAN></TD>
			<TD COLSPAN="1" width="20%" align="middle" bgcolor="{$DS_COL_WHITE}"><SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="translate($hupper,&HEXU2L;)"/></SPAN></TD>
			<TD COLSPAN="1" width="50%" align="right"  bgcolor="{$DS_COL_WHITE}">
				<A HREF="#_{$iname}" style="text-decoration:none">
				<SPAN style="color:{$DS_COL_BLACK}; vertical-align:sub; font: normal 8px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@BASENAME"/>:<xsl:value-of select="@HIGHNAME"/></SPAN><SPAN style="color:{$DS_COL_XPRP}; font: bold 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@INSTANCE"/></SPAN>
				</A>
			</TD>
		</xsl:for-each>
	</TABLE>			
	</xsl:if>
</xsl:template>

<xsl:template name="FindCorrectLocation">
	<xsl:param name="ranges"/>
	<xsl:param name="location"/>
	<xsl:param name="instname"/>
	
</xsl:template>

</xsl:stylesheet>
