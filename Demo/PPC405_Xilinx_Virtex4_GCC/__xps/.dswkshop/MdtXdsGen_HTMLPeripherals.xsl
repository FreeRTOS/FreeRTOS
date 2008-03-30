<?xml version="1.0" standalone="no"?>
<xsl:stylesheet version="1.0"
           xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
           xmlns:exsl="http://exslt.org/common"
           xmlns:xlink="http://www.w3.org/1999/xlink">
         
<xsl:output method="html"/>
			
<xsl:param name="PERI_COL_OPB"    select="'#339900'"/>
<xsl:param name="PERI_COL_WHIT"   select="'#FFFFFF'"/>
<xsl:param name="PERI_COL_INFO"   select="'#2233FF'"/>
<xsl:param name="PERI_COL_BLCK"   select="'#000000'"/>
<xsl:param name="PERI_COL_GREY"   select="'#CCCCCC'"/>
<xsl:param name="PERI_COL_XPRP"   select="'#810017'"/>
<xsl:param name="PERI_COL_DOCLNK" select="'#FF9900'"/>
	        
<!-- ======================= MAIN PERIPHERAL SECTION =============================== -->
<xsl:template name="Layout_Peripherals">
<BR></BR>
<BR></BR>
<BR></BR>
<BR></BR>
<A name="_{@INSTANCE}"/>
<SPAN style="color:{$DS_COL_BLCK}; font: bold italic 12px Verdana,Arial,Helvetica,sans-serif">
	<xsl:value-of select="@INSTANCE"/>
	<BR></BR>
	________________________________________________
</SPAN>
<BR></BR>
<BR></BR>
<TABLE BGCOLOR="{$PERI_COL_WHIT}" WIDTH="800" COLS="2" cellspacing="0" cellpadding="0" border="0">
	<!-- Layout the Module information table-->
	<TD COLSPAN="1" width="50%" align="LEFT" valign="TOP">
			<TABLE BGCOLOR="{$PERI_COL_WHIT}" WIDTH="400" COLS="2" cellspacing="0" cellpadding="0" border="0">
			<TD COLSPAN="1" width="50%" align="MIDDLE" valign="TOP">
				<IMG SRC="imgs/{@INSTANCE}.jpg" alt="{@INSTANCE} IP Image" border="0" vspace="10" hspace="0"/>
			</TD>
			<TR></TR>
			<TD COLSPAN="1" width="50%" align="LEFT" valign="TOP">
				<xsl:call-template name="Peri_PinoutTable"/>
			</TD>
		 </TABLE>
	</TD>
				
	<TD COLSPAN="1" width="50%" align="RIGHT" valign="BOTTOM">
		<xsl:call-template name="Peri_InfoTable"/>
	</TD>
</TABLE>	
</xsl:template>

<!-- ======================= PERIHERAL TABLE PARTS   =============================== -->
<!-- Layout the Module's Information table -->
<xsl:template name="Peri_InfoTable">
	<TABLE BGCOLOR="{$PERI_COL_BLCK}" WIDTH="410" COLS="5" cellspacing="1" cellpadding="2" border="0">
		<TH COLSPAN="5" width="100%" align="middle" bgcolor="{$PERI_COL_XPRP}"><SPAN style="color:{$PERI_COL_WHIT}; font: bold 12px Verdana,Arial,Helvetica,sans-serif">General</SPAN></TH>
		<TR></TR>
		<TH COLSPAN="3" width="60%" align="middle" bgcolor="{$PERI_COL_GREY}"><SPAN style="color:{$PERI_COL_XPRP}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">Type</SPAN></TH>
		<TH COLSPAN="2" width="40%" align="middle" bgcolor="{$PERI_COL_WHIT}"><SPAN style="color:{$PERI_COL_XPRP}; font: bold 10px Verdana,Arial,Helvetica,sans-serif"><A HREF="docs/{@MODTYPE}.pdf" style="text-decoration:none; color:{$PERI_COL_XPRP}"><xsl:value-of select="@MODTYPE"/></A></SPAN></TH>
		<TR></TR>	
		<TH COLSPAN="3" width="60%" align="middle" bgcolor="{$PERI_COL_GREY}"><SPAN style="color:{$PERI_COL_XPRP}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">Version</SPAN></TH>
		<TH COLSPAN="2" width="40%" align="middle" bgcolor="{$PERI_COL_WHIT}"><SPAN style="color:{$PERI_COL_BLCK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@HWVERSION"/></SPAN></TH>
		<TR></TR>	
		<TH COLSPAN="5" width="100%" align="middle" bgcolor="{$PERI_COL_XPRP}"><SPAN style="color:{$PERI_COL_WHIT}; font: bold 12px Verdana,Arial,Helvetica,sans-serif">Parameters</SPAN></TH>
		
		<TR></TR>
		<TH COLSPAN="5" width="100%" align="left" bgcolor="{$PERI_COL_WHIT}">
			<SPAN style="color:{$PERI_COL_INFO}; font: bold 9px Verdana,Arial,Helvetica,sans-serif">
				The paramaters listed here are only those set in the MHS file. Refer to the IP
					<A HREF="docs/{@MODTYPE}.pdf" style="text-decoration:none; color:{$PERI_COL_XPRP}"> documentation </A>for complete information about module parameters.
			</SPAN>
		</TH>
		<TR></TR>
		<TH COLSPAN="3" width="60%" align="middle" bgcolor="{$PERI_COL_GREY}"><SPAN style="color:{$PERI_COL_XPRP}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">Name</SPAN></TH>
		<TH COLSPAN="2" width="40%" align="middle" bgcolor="{$PERI_COL_GREY}"><SPAN style="color:{$PERI_COL_XPRP}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">Value</SPAN></TH>
		<xsl:for-each select="PARAMETER">
			<TR></TR>	
			<TH COLSPAN="3" width="60%" align="left" bgcolor="{$PERI_COL_WHIT}"><SPAN style="color:{$PERI_COL_BLCK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@NAME"/></SPAN></TH>
			<TH COLSPAN="2" width="40%" align="left" bgcolor="{$PERI_COL_WHIT}"><SPAN style="color:{$PERI_COL_BLCK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@VALUE"/></SPAN></TH>
		</xsl:for-each>
		<TR></TR>
		<TH COLSPAN="5" width="100%" align="middle" bgcolor="{$PERI_COL_XPRP}"><SPAN style="color:{$PERI_COL_WHIT}; font: bold 12px Verdana,Arial,Helvetica,sans-serif">Device Utilization</SPAN></TH>
		<TR></TR>
		<xsl:choose>
			<xsl:when test="not(RESOURCES)">
				<TH COLSPAN="5" width="100%" align="middle" bgcolor="{$PERI_COL_WHIT}">
				<SPAN style="color:{$PERI_COL_INFO}; font: bold 9px Verdana,Arial,Helvetica,sans-serif">
					Device utilization information is not available for this IP.
				</SPAN>
				</TH>
			</xsl:when>	
			<xsl:otherwise>
				<TH COLSPAN="2" width="55%" align="middle" bgcolor="{$PERI_COL_GREY}"><SPAN style="color:{$PERI_COL_XPRP}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">Resource Type</SPAN></TH>
				<TH COLSPAN="1" width="15%" align="middle" bgcolor="{$PERI_COL_GREY}"><SPAN style="color:{$PERI_COL_XPRP}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">Used</SPAN></TH>
				<TH COLSPAN="1" width="15%" align="middle" bgcolor="{$PERI_COL_GREY}"><SPAN style="color:{$PERI_COL_XPRP}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">Available</SPAN></TH>
				<TH COLSPAN="1" width="15%" align="middle" bgcolor="{$PERI_COL_GREY}"><SPAN style="color:{$PERI_COL_XPRP}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">Percent</SPAN></TH>
				
				<xsl:for-each select="RESOURCES/RESOURCE">
					<TR></TR>	
					<TH COLSPAN="2" width="55%" align="left"   bgcolor="{$PERI_COL_WHIT}"><SPAN style="color:{$PERI_COL_BLCK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@TYPE"/></SPAN></TH>
					<TH COLSPAN="1" width="15%" align="middle" bgcolor="{$PERI_COL_WHIT}"><SPAN style="color:{$PERI_COL_BLCK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@USED"/></SPAN></TH>
					<TH COLSPAN="1" width="15%" align="middle" bgcolor="{$PERI_COL_WHIT}"><SPAN style="color:{$PERI_COL_BLCK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@TOTAL"/></SPAN></TH>
					<TH COLSPAN="1" width="15%" align="middle" bgcolor="{$PERI_COL_WHIT}"><SPAN style="color:{$PERI_COL_BLCK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@PERCENT"/></SPAN></TH>
				</xsl:for-each>
			</xsl:otherwise>
		</xsl:choose>
		
	    <TR></TR>	
		<TH COLSPAN="5" width="100%" align="middle" bgcolor="{$PERI_COL_XPRP}"><SPAN style="color:{$PERI_COL_WHIT}; font: bold 12px Verdana,Arial,Helvetica,sans-serif"></SPAN></TH>
</TABLE>

</xsl:template>

<!-- Layout the Module's pinout table -->
<xsl:template name="Peri_PinoutTable">

	<TABLE BGCOLOR="{$PERI_COL_BLCK}" WIDTH="310" COLS="6" cellspacing="1" cellpadding="2" border="0">
		<TH COLSPAN="6" width="100%" align="middle" bgcolor="{$PERI_COL_XPRP}"><SPAN style="color:{$PERI_COL_WHIT}; font: bold 9px Verdana,Arial,Helvetica,sans-serif">PINOUT</SPAN></TH>
	 	<TR></TR>	
		<TH COLSPAN="6" width="100%" align="left" bgcolor="{$PERI_COL_WHIT}">
			<SPAN style="color:{$PERI_COL_INFO}; font: bold 9px Verdana,Arial,Helvetica,sans-serif">
				The ports listed here are only those connected in the MHS file. Refer to the IP
					<A HREF="docs/{@MODTYPE}.pdf" style="text-decoration:none; color:{$PERI_COL_XPRP}"> documentation </A>for complete information about module ports.
			</SPAN>
		</TH>
		<TR></TR>
		<TH COLSPAN="1" width="5%"  align="left" bgcolor="{$PERI_COL_GREY}"><SPAN style="color:{$PERI_COL_XPRP}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">#</SPAN></TH>
		<TH COLSPAN="2" width="25%" align="left" bgcolor="{$PERI_COL_GREY}"><SPAN style="color:{$PERI_COL_XPRP}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">NAME</SPAN></TH>
		<TH COLSPAN="1" width="10%" align="left" bgcolor="{$PERI_COL_GREY}"><SPAN style="color:{$PERI_COL_XPRP}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">DIR</SPAN></TH>
		<TH COLSPAN="2" width="60%" align="left" bgcolor="{$PERI_COL_GREY}"><SPAN style="color:{$PERI_COL_XPRP}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">SIGNAL</SPAN></TH>
		<xsl:for-each select="PORT[(not(@SIGNAME = '__DEF__') and not(@SIGNAME = '__NOC__'))]">
			<xsl:sort data-type="number" select="@INDEX" order="ascending"/>
			<TR></TR>	
			<TH COLSPAN="1" width="5%"  align="left" bgcolor="{$PERI_COL_WHIT}"><SPAN style="color:{$PERI_COL_BLCK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@INDEX"/></SPAN></TH>
			<TH COLSPAN="2" width="25%" align="left" bgcolor="{$PERI_COL_WHIT}"><SPAN style="color:{$PERI_COL_BLCK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@NAME"/></SPAN></TH>
			<TH COLSPAN="1" width="10%" align="left" bgcolor="{$PERI_COL_WHIT}"><SPAN style="color:{$PERI_COL_BLCK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@DIR"/></SPAN></TH>
			<TH COLSPAN="2" width="60%" align="left" bgcolor="{$PERI_COL_WHIT}"><SPAN style="color:{$PERI_COL_BLCK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@SIGNAME"/></SPAN></TH>
		</xsl:for-each>
	</TABLE>	
	
</xsl:template>
</xsl:stylesheet>
