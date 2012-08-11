<?xml version="1.0" standalone="no"?>
<xsl:stylesheet version="1.0"
           xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
           xmlns:exsl="http://exslt.org/common"
           xmlns:xlink="http://www.w3.org/1999/xlink">
         
<xsl:template name="Write_TOCTree">
<HTML>
<HEAD>
<TITLE>Table of Contents</TITLE>
	
	<BASE target="{$DS_FRAME_MAIN}"></BASE>
	
	<!--specify a css for the TOC -->
	<link   rel="stylesheet"      href="ds_Report.css" type="text/css"></link>
	
	<!--specify the javascript for the TOC-->
	<script src="ds_Report.js" type="text/javascript"></script>
</HEAD>	

	<!--Layout Table of contents   -->
	<BODY class="main_body">
		<xsl:call-template name="Layout_TOCTree"/>
	</BODY>		
	
</HTML>
</xsl:template>

	
<!-- ======================= LAYOUT TABLE OF CONTENTS ====================================== -->
<xsl:template name="Layout_TOCTree">
	
<xsl:variable name="toc_col_">
	<xsl:if test="$DS_TYPE='NOFRAMES'">
		<xsl:value-of select="$DS_COL_LGRY"/>	
	</xsl:if>
	
	<xsl:if test="$DS_TYPE='FRAMES'">
		<xsl:value-of select="$DS_COL_WHITE"/>	
	</xsl:if>
</xsl:variable>

<xsl:variable name="toc_width_">
	<xsl:if test="$DS_TYPE='NOFRAMES'">
		<xsl:value-of select="$DS_WIDTH"/>	
	</xsl:if>
	
	<xsl:if test="$DS_TYPE='FRAMES'">
		<xsl:value-of select="$DS_TOC_WIDTH"/>	
	</xsl:if>
</xsl:variable>

<xsl:variable name="toc_target_">
	<xsl:if test="$DS_TYPE='NOFRAMES'">
		<xsl:value-of select="$DS_FRAME_SELF"/>	
	</xsl:if>
	
	<xsl:if test="$DS_TYPE='FRAMES'">
		<xsl:value-of select="$DS_FRAME_MAIN"/>	
	</xsl:if>
</xsl:variable>

<xsl:variable name="trg_html_">
	<xsl:if test="$DS_TYPE='NOFRAMES'">
		<xsl:value-of select="''"/>	
	</xsl:if>
	
	<xsl:if test="$DS_TYPE='FRAMES'">
		<xsl:value-of select="$DS_HTML_MAIN"/>	
	</xsl:if>
</xsl:variable>
	
	
<A name="_TOC"/>
<TABLE BGCOLOR="{$toc_col_}" WIDTH="{$toc_width_}" COLS="2" cellspacing="0" cellpadding="3" border="0">

	<xsl:if test="$DS_TYPE='NOFRAMES'">
		<TH COLSPAN="2" width="100%" align="middle"><SPAN style="color:{$DS_COL_XPRP}; font: bold 20px Arial,Helvetica,sans-serif">TABLE OF CONTENTS</SPAN></TH>
	</xsl:if>
	
	<TR></TR>
	<TD COLSPAN="1" width="40%" align="left">
		<BR></BR>
		<A HREF="{$trg_html_}#_Overview" style="text-decoration:none"><SPAN style="color:{$DS_COL_BLACK}; font: bold 16px Verdana Arial,Helvetica,sans-serif">Overview</SPAN></A>
		
		<BR></BR>
		<A HREF="{$trg_html_}#_BlockDiagram" style="text-decoration:none"><SPAN style="color:{$DS_COL_BLACK}; font: bold 16px Verdana Arial,Helvetica,sans-serif">Block Diagram</SPAN></A>
		
		<BR></BR>
		<A HREF="{$trg_html_}#_ExternalPorts" style="text-decoration:none"><SPAN style="color:{$DS_COL_BLACK}; font: bold 16px Verdana Arial,Helvetica,sans-serif">External Ports</SPAN></A>
		
		<BR></BR>
		<xsl:variable name="proc_CNT" select="count(MODULES/MODULE[(@MODCLASS = 'PROCESSOR')])"/>
		
		<xsl:if test="MODULES/MODULE[(@MODCLASS='PROCESSOR')]">
		<DIV class="trigger" onClick="showBranch('Processors'); swapBranchImg('BranchImg_Processors');">
			<xsl:if test="$proc_CNT &gt; 1">
				<SPAN style="color:{$DS_COL_BLACK}; font: bold 16px Verdana Arial,Helvetica,sans-serif">Processors&#160;</SPAN>
			</xsl:if>	
			<xsl:if test="not($proc_CNT &gt; 1)">
				<SPAN style="color:{$DS_COL_BLACK}; font: bold 16px Verdana Arial,Helvetica,sans-serif">Processor&#160;</SPAN>
			</xsl:if>	
			<IMG src="imgs/IMG_openBranch.gif" border="0" id="BranchImg_Processors"></IMG>	
		</DIV>
		
		<SPAN class="branch" id="Processors">		
			<xsl:for-each select="MODULES/MODULE[(@MODCLASS='PROCESSOR')]">
				<xsl:sort select="@INSTANCE"/>
				<A HREF="{$trg_html_}#_{@INSTANCE}" style="text-decoration:none"><SPAN style="color:{$DS_COL_XPRP}; font: italic 14px Verdana Arial,Helvetica,sans-serif">&#160;&#160;&#160;<xsl:value-of select="@INSTANCE"/></SPAN></A><BR></BR>
				<xsl:if test="MEMORYMAP/MEMRANGE[(@INSTANCE)]">
					<A HREF="{$trg_html_}#_{@INSTANCE}_MemoryMap" style="text-decoration:none"><SPAN style="color:{$DS_COL_BLACK}; font: italic 14px Verdana Arial,Helvetica,sans-serif">&#160;&#160;&#160;&#160;&#160;&#160;&#160;&#160;&#160;&#160;memory map</SPAN></A><xsl:if test="LICENSEINFO"><IMG SRC="imgs/IMG_LicensedCore.bmp" border="0" vspace="0" hspace="0"/></xsl:if><BR></BR>
				</xsl:if>
			</xsl:for-each>
		</SPAN>	
		</xsl:if>
		
		<xsl:if test="MODULES/MODULE[(@MODCLASS='DEBUG')]">
		<DIV class="trigger" onClick="showBranch('Debuggers'); swapBranchImg('BranchImg_Debugger');">
			<SPAN style="color:{$DS_COL_BLACK}; font: bold 16px Verdana Arial,Helvetica,sans-serif">Debuggers&#160;</SPAN>
			<IMG src="imgs/IMG_openBranch.gif" border="0" id="BranchImg_Debugger"></IMG>	
		</DIV>		
		
		<SPAN class="branch" id="Debuggers">		
			<xsl:for-each select="MODULES/MODULE[(@MODCLASS='DEBUG')]">
				<xsl:sort select="@INSTANCE"/>
				<A HREF="{$trg_html_}#_{@INSTANCE}" style="text-decoration:none"><SPAN style="color:{$DS_COL_XPRP}; font: italic 14px Verdana Arial,Helvetica,sans-serif">&#160;&#160;&#160;<xsl:value-of select="@INSTANCE"/></SPAN></A><xsl:if test="LICENSEINFO"><IMG SRC="imgs/IMG_LicensedCore.bmp" border="0" vspace="0" hspace="0"/></xsl:if><BR></BR>
			</xsl:for-each>
		</SPAN>	
		</xsl:if>
		
		
		<xsl:if test="MODULES/MODULE[(@MODCLASS='INTERRUPT_CNTLR')]">
		<DIV class="trigger" onClick="showBranch('Interrupts'); swapBranchImg('BranchImg_Interrupts');">
			<SPAN style="color:{$DS_COL_BLACK}; font: bold 16px Verdana Arial,Helvetica,sans-serif">Interrupt Controllers&#160;</SPAN>
			<IMG src="imgs/IMG_openBranch.gif" border="0" id="BranchImg_Interrupts"></IMG>	
		</DIV>
		
		<SPAN class="branch" id="Interrupts">		
			<xsl:for-each select="MODULES/MODULE[(@MODCLASS='INTERRUPT_CNTLR')]">
				<xsl:sort select="@INSTANCE"/>
				<A HREF="{$trg_html_}#_{@INSTANCE}" style="text-decoration:none"><SPAN style="color:{$DS_COL_XPRP}; font: italic 14px Verdana Arial,Helvetica,sans-serif">&#160;&#160;&#160;<xsl:value-of select="@INSTANCE"/></SPAN></A><xsl:if test="LICENSEINFO"><IMG SRC="imgs/IMG_LicensedCore.bmp" border="0" vspace="0" hspace="0"/></xsl:if><BR></BR>
			</xsl:for-each>
		</SPAN>	
		</xsl:if>
		
		<xsl:if test="MODULES/MODULE[@MODCLASS='BUS' or @MODCLASS='BUS_ARBITER']">
		<DIV class="trigger" onClick="showBranch('Busses'); swapBranchImg('BranchImg_Busses');">
			<SPAN style="color:{$DS_COL_BLACK}; font: bold 16px Verdana Arial,Helvetica,sans-serif">Busses&#160;</SPAN>
			<IMG src="imgs/IMG_openBranch.gif" border="0" id="BranchImg_Busses"></IMG>	
		</DIV>		
			
		<SPAN class="branch" id="Busses">		
			<xsl:for-each select="MODULES/MODULE[@MODCLASS='BUS' or @MODCLASS='BUS_ARBITER']">
				<xsl:sort select="@INSTANCE"/>
				<A HREF="{$trg_html_}#_{@INSTANCE}" style="text-decoration:none"><SPAN style="color:{$DS_COL_XPRP}; font: italic 14px Verdana Arial,Helvetica,sans-serif">&#160;&#160;&#160;<xsl:value-of select="@INSTANCE"/></SPAN></A><xsl:if test="LICENSEINFO"><IMG SRC="imgs/IMG_LicensedCore.bmp" border="0" vspace="0" hspace="0"/></xsl:if><BR></BR>
			</xsl:for-each>
		</SPAN>	
		</xsl:if>
		
		<xsl:if test="MODULES/MODULE[@MODCLASS='BUS_BRIDGE']">
		<DIV class="trigger" onClick="showBranch('Bridges'); swapBranchImg('BranchImg_Bridges');">
			<SPAN style="color:{$DS_COL_BLACK}; font: bold 16px Verdana Arial,Helvetica,sans-serif">Bridges&#160;</SPAN>
			<IMG src="imgs/IMG_openBranch.gif" border="0" id="BranchImg_Bridges"></IMG>	
		</DIV>	
		<SPAN class="branch" id="Bridges">
			<xsl:for-each select="MODULES/MODULE[@MODCLASS='BUS_BRIDGE']">
				<xsl:sort select="@INSTANCE"/>
				<A HREF="{$trg_html_}#_{@INSTANCE}" style="text-decoration:none"><SPAN style="color:{$DS_COL_XPRP}; font: italic 14px Verdana Arial,Helvetica,sans-serif">&#160;&#160;&#160;<xsl:value-of select="@INSTANCE"/></SPAN></A><xsl:if test="LICENSEINFO"><IMG SRC="imgs/IMG_LicensedCore.bmp" border="0" vspace="0" hspace="0"/></xsl:if><BR></BR>
			</xsl:for-each>
		</SPAN>	
		</xsl:if>
		
		<xsl:if test="MODULES/MODULE[@MODCLASS='MEMORY']">
		<DIV class="trigger" onClick="showBranch('Memory'); swapBranchImg('BranchImg_Memory');">
			<SPAN style="color:{$DS_COL_BLACK}; font: bold 16px Verdana Arial,Helvetica,sans-serif">Memory&#160;</SPAN>
			<IMG src="imgs/IMG_openBranch.gif" border="0" id="BranchImg_Memory"></IMG>	
		</DIV>		
		<SPAN class="branch" id="Memory">
			<xsl:for-each select="MODULES/MODULE[@MODCLASS='MEMORY']">
				<xsl:sort select="@INSTANCE"/>
				<A HREF="{$trg_html_}#_{@INSTANCE}" style="text-decoration:none"><SPAN style="color:{$DS_COL_XPRP}; font: italic 14px Verdana Arial,Helvetica,sans-serif">&#160;&#160;&#160;<xsl:value-of select="@INSTANCE"/></SPAN></A><xsl:if test="LICENSEINFO"><IMG SRC="imgs/IMG_LicensedCore.bmp" border="0" vspace="0" hspace="0"/></xsl:if><BR></BR>
			</xsl:for-each>
		</SPAN>	
		</xsl:if>		
		
		<xsl:if test="MODULES/MODULE[@MODCLASS='MEMORY_CNTLR']">
		<DIV class="trigger" onClick="showBranch('MemoryCntlr'); swapBranchImg('BranchImg_MemoryCntlr');">
			<SPAN style="color:{$DS_COL_BLACK}; font: bold 16px Verdana Arial,Helvetica,sans-serif">Memory Controllers&#160;</SPAN>
			<IMG src="imgs/IMG_openBranch.gif" border="0" id="BranchImg_MemoryCntlr"></IMG>	
		</DIV>		
		<SPAN class="branch" id="MemoryCntlr">
			<xsl:for-each select="MODULES/MODULE[@MODCLASS='MEMORY_CNTLR']">
			<xsl:sort select="@INSTANCE"/>
				<A HREF="{$trg_html_}#_{@INSTANCE}" style="text-decoration:none"><SPAN style="color:{$DS_COL_XPRP}; font: italic 14px Verdana Arial,Helvetica,sans-serif">&#160;&#160;&#160;<xsl:value-of select="@INSTANCE"/></SPAN></A><xsl:if test="LICENSEINFO"><IMG SRC="imgs/IMG_LicensedCore.bmp" border="0" vspace="0" hspace="0"/></xsl:if><BR></BR>
			</xsl:for-each>
		</SPAN>	
		</xsl:if>		
		
		<xsl:if test="MODULES/MODULE[@MODCLASS='PERIPHERAL']">
		<DIV class="trigger" onClick="showBranch('Peripheral'); swapBranchImg('BranchImg_Peripheral');">
			<SPAN style="color:{$DS_COL_BLACK}; font: bold 16px Verdana Arial,Helvetica,sans-serif">Peripherals&#160;</SPAN>
			<IMG src="imgs/IMG_openBranch.gif" border="0" id="BranchImg_Peripheral"></IMG>	
		</DIV>	
		<SPAN class="branch" id="Peripheral">
			<xsl:for-each select="MODULES/MODULE[@MODCLASS='PERIPHERAL']">
				<xsl:sort select="@INSTANCE"/>
				<A HREF="{$trg_html_}#_{@INSTANCE}" style="text-decoration:none"><SPAN style="color:{$DS_COL_XPRP}; font: italic 14px Courier Verdana Arial,Helvetica,sans-serif">&#160;&#160;&#160;<xsl:value-of select="@INSTANCE"/></SPAN></A><xsl:if test="LICENSEINFO"><IMG SRC="imgs/IMG_LicensedCore.bmp" border="0" vspace="0" hspace="0"/></xsl:if><BR></BR>
			</xsl:for-each>
		</SPAN>	
		</xsl:if>		
		
		<xsl:if test="MODULES/MODULE[@MODCLASS='IP']">
		<DIV class="trigger" onClick="showBranch('IP'); swapBranchImg('BranchImg_IP');">
			<SPAN style="color:{$DS_COL_BLACK}; font: bold 16px Verdana Arial,Helvetica,sans-serif">IP&#160;</SPAN>
			<IMG src="imgs/IMG_openBranch.gif" border="0" id="BranchImg_IP"></IMG>	
		</DIV>
		<SPAN class="branch" id="IP">
			<xsl:for-each select="MODULES/MODULE[@MODCLASS='IP']">
				<xsl:sort select="@INSTANCE"/>
				<A HREF="{$trg_html_}#_{@INSTANCE}" style="text-decoration:none"><SPAN style="color:{$DS_COL_XPRP}; font: italic 14px Courier Verdana Arial,Helvetica,sans-serif">&#160;&#160;&#160;<xsl:value-of select="@INSTANCE"/></SPAN></A><xsl:if test="LICENSEINFO"><IMG SRC="imgs/IMG_LicensedCore.bmp" border="0" vspace="0" hspace="0"/></xsl:if><BR></BR>
			</xsl:for-each>
		</SPAN>	
		</xsl:if>			
		
		<A HREF="{$trg_html_}#_TimingInfo" style="text-decoration:none"><SPAN style="color:{$DS_COL_BLACK}; font: bold 16px Verdana Arial,Helvetica,sans-serif">Timing Information</SPAN></A><BR></BR>
<!--		
-->	

	</TD>
	
</TABLE>
</xsl:template>

</xsl:stylesheet>
<!-- ======================= END LAYOUT TABLE OF CONTENT TREE =================================== -->
