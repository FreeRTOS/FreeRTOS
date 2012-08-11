<?xml version="1.0" standalone="no"?>
<xsl:stylesheet version="1.0"
           xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
           xmlns:exsl="http://exslt.org/common"
           xmlns:xlink="http://www.w3.org/1999/xlink">
         
<xsl:output method="html"/>

<xsl:include href="MdtXdsGen_HTMLIPSection.xsl"/>
<xsl:include href="MdtXdsGen_HTMLMemoryMap.xsl"/>
<xsl:include href="MdtXdsGen_HTMLTOCTree.xsl"/>

<xsl:param name="DS_TYPE"      select="'NOFRAMES'"/>			
<xsl:param name="DS_PART"      select="'TOC_TREE'"/>			

<xsl:param name="DS_WIDTH"     select="850"/>			
<xsl:param name="DS_TOC_WIDTH" select="200"/>			

<xsl:param name="DS_FRAME_TOC"  select="'DS_TOC'"/>			
<xsl:param name="DS_FRAME_SELF" select="'_self'"/>			
<xsl:param name="DS_FRAME_MAIN" select="'DS_FMAIN'"/>			

<xsl:param name="DS_HTML_BLKD"    select="'ds_Blkd.html'"/>			

<xsl:param name="DS_HTML_MAIN"    select="'ds_Main.html'"/>
<xsl:param name="DS_HTML_TOC"     select="'ds_TOC.html'"/>
<xsl:param name="DS_HTML_TOCTREE" select="'ds_TOCTree.html'"/>

<xsl:param name="DS_BLKD_NAME"   select="'system_blkd.jpg'"/>
<xsl:param name="DS_BLKD_TYPE"   select="'svg'"/>
<xsl:param name="DS_BLKD_WIDTH"  select="800"/>
<xsl:param name="DS_BLKD_HEIGHT" select="600"/>

<xsl:param name="DS_COL_OPB"     select="'#339900'"/>

<xsl:param name="DS_COL_INFO"    select="'#2233FF'"/>
<xsl:param name="DS_COL_ASH"     select="'#DEDEDE'"/>
<xsl:param name="DS_COL_ASH1"    select="'#F0F0F8'"/>
<xsl:param name="DS_COL_GREY"    select="'#BBBBBB'"/>
<xsl:param name="DS_COL_LGRY"    select="'#F1F1F1'"/>
<xsl:param name="DS_COL_XPRP"    select="'#810017'"/>
<xsl:param name="DS_COL_RED"     select="'#FF1010'"/>
<xsl:param name="DS_COL_GREEN"   select="'#33CC33'"/>
<xsl:param name="DS_COL_BLACK"   select="'#000000'"/>
<xsl:param name="DS_COL_WHITE"   select="'#FFFFFF'"/>

<!--
<xsl:param name="DS_COL_ATTR_RD"   select="'#FF5555'"/>
<xsl:param name="DS_COL_ATTR_GREN" select="'#55FF55'"/>
<xsl:param name="DS_COL_ATTR_BLE"  select="'#5555FF'"/>
-->

<xsl:param name="DS_COL_ATTR_BUF"   select="'#FF5555'"/>
<xsl:param name="DS_COL_ATTR_CLK"   select="'#55FF55'"/>
<xsl:param name="DS_COL_ATTR_INT"   select="'#5555FF'"/>
<xsl:param name="DS_COL_ATTR_RST"   select="'#FFCC00'"/>


<xsl:param name="DS_COL_MODUSR" select="'#FFFFAA'"/>
<xsl:param name="DS_COL_MODSYS" select="'#AAAAFF'"/>
<xsl:param name="DS_COL_MODSYSNW" select="'#000099'"/>

<!-- ======================= MAIN DATASHEET SECTION  =============================== -->
<xsl:template match="EDKSYSTEM">
	<xsl:if test="$DS_TYPE='NOFRAMES'">
		<xsl:call-template name="Write_Main"/>	
	</xsl:if>
	<xsl:if test="$DS_TYPE='FRAMES'">
		<xsl:call-template name="Write_Frames"/>	
	</xsl:if>
</xsl:template>	

<xsl:template name="Write_Frames">
<!--	
	<xsl:if test="$DS_PART='TOC'">
		<xsl:call-template name="Write_TOC"/>	
	</xsl:if>
-->	
	
	<xsl:if test="$DS_PART='TOC'">
		<xsl:call-template name="Write_TOCTree"/>	
	</xsl:if>
	
	<xsl:if test="$DS_PART='INDEX'">
		<xsl:call-template name="Write_Index"/>	
	</xsl:if>
	
	<xsl:if test="$DS_PART='MAIN'">
		<xsl:call-template name="Write_Main"/>	
	</xsl:if>
	
	<xsl:if test="$DS_PART='BLKD'">
		<xsl:call-template name="Write_BLKD"/>	
	</xsl:if>
	
</xsl:template>	

<xsl:template name="Write_TOC">
<HTML>
<HEAD>
	<TITLE>Table of Contents</TITLE>
	<BASE target="{$DS_FRAME_MAIN}"/>
</HEAD>

	<!--Layout Table of contents   -->
	<BODY class="main_body">
		<xsl:call-template name="Layout_TOC"/>
	</BODY>		
	
</HTML>
</xsl:template>

<xsl:template name="Write_Index">
<HTML>
<HEAD><TITLE>EDK Project Report</TITLE></HEAD>
	<FRAMESET COLS="20%,80%" BORDER="0" FRAMESPACING="0">
		<FRAME SRC="{$DS_HTML_TOC}"
		   MARGINWIDTH="0" 
		   MARINHEIGHT="0" 
		   FRAMEBORDER="NO"
		   BORDER="NO"
		   NAME="{$DS_FRAME_TOC}"
		   SCROLLING="YES"/>
		<FRAME SRC="{$DS_HTML_MAIN}"
		   MARGINWIDTH="0" 
		   MARINHEIGHT="0"
		   FRAMEBORDER="NO"
		   BORDER="NO"
		   NAME="{$DS_FRAME_MAIN}" 
		   SCROLLING="YES"/>
	</FRAMESET>
</HTML>
</xsl:template>	

<xsl:template name="Write_BLKD">
<HTML>
	
<HEAD><TITLE>Block Diagram</TITLE></HEAD>
	
<!--
	<xsl:message> Embedded image name <xsl:value-of select="$DS_BLKD_NAME"/></xsl:message>
	<xsl:message> Embedded image name <xsl:value-of select="$DS_BLKD_NAME"/></xsl:message>
	<xsl:message> Embedded image type <xsl:value-of select="$DS_BLKD_TYPE"/></xsl:message>
	<xsl:message> Embedded image width <xsl:value-of select="$DS_BLKD_WIDTH"/></xsl:message>
	<xsl:message> Embedded image height <xsl:value-of select="$DS_BLKD_HEIGHT"/></xsl:message>
-->	
	
	<BODY class="main_body">
		
	<xsl:if test="$DS_BLKD_TYPE = 'svg'">
		<EMBED src="{$DS_BLKD_NAME}" width="{$DS_BLKD_WIDTH}" height="{$DS_BLKD_HEIGHT}" type="image/svg+xml"/>
	</xsl:if>
	
	<xsl:if test="not($DS_BLKD_TYPE = 'svg')">
		<IMG SRC="{$DS_BLKD_NAME}" alt="BlockDiagram" width="{$DS_BLKD_WIDTH}" height="{$DS_BLKD_HEIGHT}" border="0" vspace="0" hspace="0"/>
	</xsl:if>
		<BR></BR>
		<BR></BR>
		<xsl:call-template name="Layout_ExternalPorts"/>
		<BR></BR>
	</BODY>		
</HTML>
</xsl:template>

	
<xsl:template name="Write_Main">
<html>
	<!--Layout head -->
	<head>
		<title>EDK PROJECT REPORT</title>
		
		<!--specify a css for the file -->
	    <meta http-equiv="PRAGMA" content="NO-CACHE"/>
	    <meta http-equiv="content-Type" content="text/html; charset=iso-8859-1"/>
	    
	</head>	
	
	<body bgcolor="#FFFFFF">
	
		<!--Layout Table of contents   -->
		<xsl:if test="not($DS_TYPE='FRAMES')">
			<xsl:call-template name="Layout_TOC"/>
		</xsl:if>	
		
		<TABLE BGCOLOR="{$DS_COL_WHITE}" WIDTH="{$DS_WIDTH}" COLS="1" cellspacing="0" cellpadding="3" border="0">
		
<!--  ==========================Overview Section ============== -->
			<TR></TR>
			<TR></TR>
			<TR></TR>
			<xsl:if test="$DS_TYPE='FRAMES'">
				<TD COLSPAN="1" ALIGN="LEFT">
					<A HREF="ds_MainNF.html" target="_top" style="text-decoration:none"><SPAN style="color:{$DS_COL_GREEN}; font: normal 14px Verdana Arial,Helvetica,sans-serif">Printable Version</SPAN></A>
				</TD>
				<TR></TR>
			</xsl:if>
			<TD COLSPAN="1" WIDTH="100%">
				<A name="_Overview"/>
				<xsl:call-template name="Layout_NavigateHeader">
					<xsl:with-param name="header_name" select="'Overview'"/>
				</xsl:call-template>	
				<BR></BR>
				<BR></BR>
				<xsl:call-template name="Layout_Overview"/>
			</TD>
			
<!--  ==========================Block Diagram section ============== -->
<!--
	<xsl:message> Embedded image name <xsl:value-of select="$DS_BLKD_NAME"/></xsl:message>
-->	
			<TR></TR>
			<TD COLSPAN="1">
				<A name="_BlockDiagram"/>
				<xsl:call-template name="Layout_NavigateHeader">
					<xsl:with-param name="header_name" select="'Block Diagram'"/>
				</xsl:call-template>
				<BR></BR>
				<BR></BR>
				<IMG SRC="imgs/{$DS_BLKD_NAME}" alt="BlockDiagram" border="0" vspace="0" hspace="0"/>
			</TD>
			
<!--			
-->			

<!--  ========================== External Ports ======================= -->

			<TR></TR>
			<TD COLSPAN="1" WIDTH="100%">
				<A name="_ExternalPorts"/>
				<xsl:call-template name="Layout_NavigateHeader">
					<xsl:with-param name="header_name" select="'External Ports'"/>
				</xsl:call-template>
				<BR></BR>
				<BR></BR>
				<xsl:call-template name="Layout_ExternalPorts"/>
			</TD>
			
<!--  ========================== Memory Map Section ======================= -->
<!---
			<xsl:if test="MODULES/MODULE[@MODCLASS='PROCESSOR']/MEMORYMAP">
				<TR></TR>
				<TD COLSPAN="1">
					<A name="_MemoryMap"/>
					<xsl:call-template name="Layout_NavigateHeader">
						<xsl:with-param name="header_name" select="'MEMORY MAP'"/>
					</xsl:call-template>
					<xsl:for-each select="MODULES/MODULE[@MODCLASS='PROCESSOR']">
						<xsl:sort select="@INSTANCE"/>
						<xsl:call-template name="Layout_MemoryMap"/>
					</xsl:for-each>
				</TD>
			</xsl:if>
-->		
			
<!--  ========================== Processor Information Section ================== -->
			<TR></TR>
			<TD COLSPAN="1" WIDTH="100%">
				<A name="_Processor"/>
				<xsl:call-template name="Layout_NavigateHeader">
						<xsl:with-param name="header_name" select="'Processors'"/>
				</xsl:call-template>
				<BR></BR>
				<TABLE align="left" width="{$DS_WIDTH}" cellspacing="0" cellpadding="0" border="0">
					<xsl:for-each select="MODULES/MODULE[((@MODCLASS='PROCESSOR') and (contains(@MODTYPE,'microblaze')))]">
					<xsl:sort select="@INSTANCE"/>
						<TR/>
						<TD COLSPAN="1" align="left">
							<xsl:call-template name="Layout_IPSection"/>
						</TD>
					</xsl:for-each>
					
					<xsl:for-each select="MODULES/MODULE[((@MODCLASS='PROCESSOR') and (contains(@MODTYPE,'ppc')))]">
					<xsl:sort select="@INSTANCE"/>
						<TR/>
						<TD COLSPAN="1" align="left">
							<xsl:call-template name="Layout_IPSection"/>
						</TD>
					</xsl:for-each>
				</TABLE>
			</TD>
					
<!--						
			<TR></TR>
			<xsl:if test="MODULES/MODULE[@MODCLASS='PROCESSOR_DEBUG']">
				<A name="_Debug"/>
						<xsl:call-template name="Layout_NavigateHeader">
							<xsl:with-param name="header_name" select="'Debuggers'"/>
						</xsl:call-template>
						<BR></BR>
						
						<xsl:for-each select="MODULES/MODULE[@MODCLASS='PROCESSOR_DEBUG']">
						<xsl:sort select="@INSTANCE"/>
							<TR/>
							<TD COLSPAN="1" align="left">
								<xsl:call-template name="Layout_IPSection"/>
							</TD>
						</xsl:for-each>
					</xsl:if>
-->					
					
<!--						
					<xsl:if test="MODULES/MODULE[@MODCLASS='INTERRUPT_CONTROLLER']">
					<A name="_Intc"/>
					<xsl:call-template name="Layout_NavigateHeader">
						<xsl:with-param name="header_name" select="'Interrupt Controllers'"/>
					</xsl:call-template>
					<BR></BR>
						<TABLE align="left" width="{$DS_WIDTH}" cellspacing="0" cellpadding="0" border="0">
							<xsl:for-each select="MODULES/MODULE[@MODCLASS='INTERRUPT_CONTROLLER']">
							<xsl:sort select="@INSTANCE"/>
								<TR/>
								<TD COLSPAN="1" align="left">
								<xsl:call-template name="Layout_IPSection"/>
								</TD>
							</xsl:for-each>
						</TABLE>
						
					</xsl:if>
				</TABLE>
			</TD>
			
						<xsl:for-each select="MODULES/MODULE[@MODCLASS='INTERRUPT_CONTROLLER']">
						<xsl:sort select="@INSTANCE"/>
							<TR/>
							<TD COLSPAN="1" align="left">
								<xsl:call-template name="Layout_IPSection"/>
							</TD>
						</xsl:for-each>
-->				

<!--  ========================== Debugger Section ================== -->
			<xsl:if test="MODULES/MODULE[(@MODCLASS='DEBUG')]">
			<TR></TR>		
			<TD COLSPAN="1">
				<A name="_Debug"/>
				<xsl:call-template name="Layout_NavigateHeader">
					<xsl:with-param name="header_name" select="'Debuggers'"/>
				</xsl:call-template>	
				<TABLE align="left" width="{$DS_WIDTH}" cellspacing="0" cellpadding="0" border="0">
					<xsl:for-each select="MODULES/MODULE[(@MODCLASS='DEBUG')]">
					<xsl:sort select="@INSTANCE"/>
						<TR/>
						<TD COLSPAN="1" align="left">
							<xsl:call-template name="Layout_IPSection"/>
						</TD>
					</xsl:for-each>
				</TABLE>
			</TD>
		</xsl:if>	

<!--  ========================== Interrupt Controllers Section ================== -->
		<xsl:if test="MODULES/MODULE[(@MODCLASS='INTERRUPT_CNTLR')]">
			<TR></TR>		
			<TD COLSPAN="1">
				<A name="_Intc"/>
				<xsl:call-template name="Layout_NavigateHeader">
					<xsl:with-param name="header_name" select="'Interrupt Controllers'"/>
				</xsl:call-template>	
				<TABLE align="left" width="{$DS_WIDTH}" cellspacing="0" cellpadding="0" border="0">
					<xsl:for-each select="MODULES/MODULE[(@MODCLASS='INTERRUPT_CNTLR')]">
					<xsl:sort select="@INSTANCE"/>
						<TR/>
						<TD COLSPAN="1" align="left">
							<xsl:call-template name="Layout_IPSection"/>
						</TD>
					</xsl:for-each>
				</TABLE>
			</TD>
		</xsl:if>	
				

<!--  ========================== Bus Information Section ================== -->
			<TR></TR>		
			<TD COLSPAN="1">
				<A name="_BusModules"/>
				<xsl:call-template name="Layout_NavigateHeader">
					<xsl:with-param name="header_name" select="'Busses'"/>
				</xsl:call-template>	
				<TABLE align="left" width="{$DS_WIDTH}" cellspacing="0" cellpadding="0" border="0">
					<xsl:for-each select="MODULES/MODULE[((@MODCLASS='BUS') or (@MODCLASS='BUS_ARBITER'))]">
					<xsl:sort select="@INSTANCE"/>
						<TR/>
						<TD COLSPAN="1" align="left">
							<xsl:call-template name="Layout_IPSection"/>
						</TD>
					</xsl:for-each>
				</TABLE>
			</TD>
				
<!--  ========================== Bridge Information Section ================== -->
			<xsl:if test="MODULES/MODULE[(@MODCLASS='BUS_BRIDGE')]">
			<TR></TR>		
			<TD COLSPAN="1">
				<BR></BR>
				<A name="_BridgeModules"/>
				<xsl:call-template name="Layout_NavigateHeader">
					<xsl:with-param name="header_name" select="'Bus Bridges'"/>
				</xsl:call-template>	
				<TABLE align="left" width="{$DS_WIDTH}" cellspacing="0" cellpadding="0" border="0">
					<xsl:for-each select="MODULES/MODULE[(@MODCLASS='BUS_BRIDGE')]">
					<xsl:sort select="@INSTANCE"/>
						<TR/>
						<TD COLSPAN="1" align="left">
							<xsl:call-template name="Layout_IPSection"/>
						</TD>
					</xsl:for-each>
				</TABLE>
			
			</TD>
			</xsl:if>					
			
<!--  ========================== Memory Information Section ============== -->
			<xsl:if test="MODULES/MODULE[(@MODCLASS='MEMORY')]">
			<TR></TR>		
			<TD COLSPAN="1">
				<A name="_MemoryModules"/>
				<xsl:call-template name="Layout_NavigateHeader">
					<xsl:with-param name="header_name" select="'Memory'"/>
				</xsl:call-template>	
				
				<TABLE align="left" width="{$DS_WIDTH}" cellspacing="0" cellpadding="0" border="0">
					<xsl:for-each select="MODULES/MODULE[(@MODCLASS='MEMORY')]">
					<xsl:sort select="@INSTANCE"/>
						<TR/>
						<TD COLSPAN="1" align="left">
							<xsl:call-template name="Layout_IPSection"/>
						</TD>
					</xsl:for-each>
				</TABLE>
			</TD>
			</xsl:if>
<!--  ========================== Memory Controller Information Section ============== -->
			<xsl:if test="MODULES/MODULE[(@MODCLASS='MEMORY_CNTLR')]">
			<TR></TR>		
			<TD COLSPAN="1">
				<A name="_MemCntlrModules"/>
				<xsl:call-template name="Layout_NavigateHeader">
					<xsl:with-param name="header_name" select="'Memory Controllers'"/>
				</xsl:call-template>	
				
				<TABLE align="left" width="{$DS_WIDTH}" cellspacing="0" cellpadding="0" border="0">
					<xsl:for-each select="MODULES/MODULE[(@MODCLASS='MEMORY_CNTLR')]">
					<xsl:sort select="@INSTANCE"/>
						<TR/>
						<TD COLSPAN="1" align="left">
							<xsl:call-template name="Layout_IPSection"/>
						</TD>
					</xsl:for-each>
				</TABLE>
			</TD>
		</xsl:if>	
			
<!--  ========================== Peripheral Information Section ============== -->
		<xsl:if test="MODULES/MODULE[(@MODCLASS='PERIPHERAL')]">
			<TR></TR>		
			<TD COLSPAN="1" align="left">
				<A name="_Peripherals"/>
				<xsl:call-template name="Layout_NavigateHeader">
					<xsl:with-param name="header_name" select="'Peripherals'"/>
				</xsl:call-template>	
				<TABLE align="left" COLS="1" width="{$DS_WIDTH}" cellspacing="0" cellpadding="0" border="0">
					<xsl:for-each select="MODULES/MODULE[(@MODCLASS='PERIPHERAL')]">
					<xsl:sort select="@INSTANCE"/>
						<TD ROWSPAN="2"/><TR/>
						<TD ROWSPAN="2"/><TR/>
						<TD COLSPAN="1" align="left">
							<xsl:call-template name="Layout_IPSection"/>
						</TD>
					</xsl:for-each>
				</TABLE>
			</TD>	
		</xsl:if>	
			
<!--  ========================== IP Information Section ====================== -->
		<xsl:if test="MODULES/MODULE[(@MODCLASS='IP')]">
			<TR></TR>		
			<TD COLSPAN="1" align="left">
				<A name="_IPModules"/>
				<xsl:call-template name="Layout_NavigateHeader">
					<xsl:with-param name="header_name" select="'IP'"/>
				</xsl:call-template>	
				<BR></BR>
				<TABLE align="left" COLS="1" width="{$DS_WIDTH}" cellspacing="0" cellpadding="0" border="0">
					<xsl:for-each select="MODULES/MODULE[(@MODCLASS='IP')]">
					<xsl:sort select="@INSTANCE"/>
						<TD ROWSPAN="2"/><TR/>
						<TD ROWSPAN="2"/><TR/>
						<TD COLSPAN="1" align="left">
							<xsl:call-template name="Layout_IPSection"/>
						</TD>
					</xsl:for-each>
				</TABLE>
			</TD>	
		</xsl:if>
			
		<!--Timing Information section -->
			<TR></TR>		
			<TD COLSPAN="1">
				<A name="_TimingInfo"/>
				<xsl:call-template name="Layout_NavigateHeader">
					<xsl:with-param name="header_name" select="'Timing Information'"/>
				</xsl:call-template>	
				<BR></BR>
				<BR></BR>
				<xsl:call-template name="Layout_TimingInfo"/>
			</TD>
			<TR></TR>
			<TD COLSPAN="1" align="left">
				<BR></BR>
				<BR></BR>
				<TABLE BGCOLOR="{$DS_COL_WHITE}" WIDTH="{$DS_WIDTH}" COLS="3" cellspacing="0" cellpadding="0" border="0">
					<TD COLSPAN="3" width="100%" align="middle" BGCOLOR="{$DS_COL_XPRP}"><SPAN style="color:{$DS_COL_XPRP}; font: bold 5px Verdana,Arial,Helvetica,sans-serif">line</SPAN></TD>
					<TR></TR>
					<TD COLSPAN="1" width="25%" align="left">
						<SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@TIMESTAMP"/></SPAN>
					</TD>
					<TD COLSPAN="2" width="75%" align="middle">
						<A HREF="http://www.xilinx.com" style="text-decoration:none"><SPAN style="color:{$DS_COL_INFO}; font: bold 12px Verdana,Arial,Helvetica,sans-serif">www.xilinx.com</SPAN></A>
						<BR></BR>
						<SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif">1-800-255-7778</SPAN>
					</TD>
				</TABLE>
			</TD>
			
			
		</TABLE>		
</body>
</html>

</xsl:template>

<!-- ======================= LAYOUT TABLE OF CONTENTS ====================================== -->
<xsl:template name="Layout_TOC">
	
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
		
<!--		
		<BR></BR>
		<xsl:if test="MODULES/MODULE[@MODCLASS='PROCESSOR']/MEMORYMAP">
			<A HREF="{$trg_html_}#_MemoryMap" style="text-decoration:none"><SPAN style="color:{$DS_COL_BLACK}; font: bold 16px Verdana Arial,Helvetica,sans-serif">Memory Map</SPAN></A>
		</xsl:if>
-->		
		
		<BR></BR>
		<xsl:variable name="proc_CNT" select="count(MODULES/MODULE[@MODCLASS = 'PROCESSOR'])"/>
		<xsl:if test="$proc_CNT &gt; 1">
			<A HREF="{$trg_html_}#_Processor" style="text-decoration:none"><SPAN style="color:{$DS_COL_BLACK}; font: bold 16px Verdana Arial,Helvetica,sans-serif">Processors</SPAN></A>
		</xsl:if>	
		<xsl:if test="not($proc_CNT &gt; 1)">
			<A HREF="{$trg_html_}#_Processor" style="text-decoration:none"><SPAN style="color:{$DS_COL_BLACK}; font: bold 16px Verdana Arial,Helvetica,sans-serif">Processor</SPAN></A>
		</xsl:if>	
		
		<xsl:for-each select="MODULES/MODULE[(@MODCLASS='PROCESSOR')]">
			<xsl:sort select="@INSTANCE"/>
			<BR></BR>
			<A HREF="{$trg_html_}#_{@INSTANCE}" style="text-decoration:none"><SPAN style="color:{$DS_COL_XPRP}; font: italic 14px Verdana Arial,Helvetica,sans-serif">&#160;&#160;&#160;<xsl:value-of select="@INSTANCE"/></SPAN><xsl:if test="LICENSEINFO"><IMG SRC="imgs/IMG_LicensedCore.bmp" border="0" vspace="0" hspace="0"/></xsl:if></A>
			<xsl:if test="MEMORYMAP/MEMRANGE[(@INSTANCE)]">
				<BR></BR>
				<A HREF="{$trg_html_}#_{@INSTANCE}_MemoryMap" style="text-decoration:none"><SPAN style="color:{$DS_COL_XPRP}; font: italic 14px Verdana Arial,Helvetica,sans-serif">&#160;&#160;&#160;&#160;&#160;&#160;&#160;&#160;&#160;&#160;memory map</SPAN></A>
			</xsl:if>
		</xsl:for-each>
		
		<xsl:if test="MODULES/MODULE[@MODCLASS='PROCESSOR_DEBUG']">
			<BR></BR>
			<A HREF="{$trg_html_}#_Debug" style="text-decoration:none"><SPAN style="color:{$DS_COL_BLACK}; font: bold 14px Verdana Arial,Helvetica,sans-serif">Debuggers</SPAN></A>
			<xsl:for-each select="MODULES/MODULE[@MODCLASS='PROCESSOR_DEBUG']">
				<xsl:sort select="@INSTANCE"/>
				<BR></BR>
				<A HREF="{$trg_html_}#_{@INSTANCE}" style="text-decoration:none"><SPAN style="color:{$DS_COL_XPRP}; font: italic 14px Verdana Arial,Helvetica,sans-serif">&#160;&#160;&#160;<xsl:value-of select="@INSTANCE"/></SPAN><xsl:if test="LICENSEINFO"><IMG SRC="imgs/IMG_LicensedCore.bmp" border="0" vspace="0" hspace="0"/></xsl:if></A>
			</xsl:for-each>
		</xsl:if>
		
		<xsl:if test="MODULES/MODULE[@MODCLASS='INTERRUPT_CONTROLLER']">
			<BR></BR>
			<A HREF="{$trg_html_}#_Intc" style="text-decoration:none"><SPAN style="color:{$DS_COL_BLACK}; font: bold 14px Verdana Arial,Helvetica,sans-serif">Interrupt Controllers</SPAN></A>
			<xsl:for-each select="MODULES/MODULE[@MODCLASS='INTERRUPT_CONTROLLER']">
				<xsl:sort select="@INSTANCE"/>
				<BR></BR>
				<A HREF="{$trg_html_}#_{@INSTANCE}" style="text-decoration:none"><SPAN style="color:{$DS_COL_XPRP}; font: italic 14px Verdana Arial,Helvetica,sans-serif">&#160;&#160;&#160;<xsl:value-of select="@INSTANCE"/></SPAN><xsl:if test="LICENSEINFO"><IMG SRC="imgs/IMG_LicensedCore.bmp" border="0" vspace="0" hspace="0"/></xsl:if></A>
			</xsl:for-each>
		</xsl:if>
		
		<xsl:if test="MODULES/MODULE[@MODCLASS='BUS' or @MODCLASS='BUS_ARBITER']">
			<BR></BR>
			<A HREF="{$trg_html_}#_BusModules" style="text-decoration:none"><SPAN style="color:{$DS_COL_BLACK}; font: bold 16px Verdana Arial,Helvetica,sans-serif">Busses</SPAN></A>
			<xsl:for-each select="MODULES/MODULE[@MODCLASS='BUS' or @MODCLASS='BUS_ARBITER']">
				<xsl:sort select="@INSTANCE"/>
	 			<BR></BR>
				<A HREF="{$trg_html_}#_{@INSTANCE}" style="text-decoration:none"><SPAN style="color:{$DS_COL_XPRP}; font: italic 14px Verdana Arial,Helvetica,sans-serif">&#160;&#160;&#160;<xsl:value-of select="@INSTANCE"/></SPAN><xsl:if test="LICENSEINFO"><IMG SRC="imgs/IMG_LicensedCore.bmp" border="0" vspace="0" hspace="0"/></xsl:if></A>
			</xsl:for-each>
		</xsl:if>
		
		<xsl:if test="MODULES/MODULE[@MODCLASS='BUS_BRIDGE']">
			<BR></BR>
			<A HREF="{$trg_html_}#_BridgeModules" style="text-decoration:none"><SPAN style="color:{$DS_COL_BLACK}; font: bold 16px Verdana Arial,Helvetica,sans-serif">Bridges</SPAN></A>
			<xsl:for-each select="MODULES/MODULE[@MODCLASS='BUS_BRIDGE']">
				<xsl:sort select="@INSTANCE"/>
				<BR></BR>
				<A HREF="{$trg_html_}#_{@INSTANCE}" style="text-decoration:none"><SPAN style="color:{$DS_COL_XPRP}; font: italic 14px Verdana Arial,Helvetica,sans-serif">&#160;&#160;&#160;<xsl:value-of select="@INSTANCE"/></SPAN><xsl:if test="LICENSEINFO"><IMG SRC="imgs/IMG_LicensedCore.bmp" border="0" vspace="0" hspace="0"/></xsl:if></A>
			</xsl:for-each>
		</xsl:if>
		
		<xsl:if test="MODULES/MODULE[@MODCLASS='MEMORY']">
			<BR></BR>
			<A HREF="{$trg_html_}#_MemoryModules" style="text-decoration:none"><SPAN style="color:{$DS_COL_BLACK}; font: bold 16px Verdana Arial,Helvetica,sans-serif">Memory</SPAN></A>
			<xsl:for-each select="MODULES/MODULE[@MODCLASS='MEMORY']">
				<xsl:sort select="@INSTANCE"/>
				<BR></BR>
				<A HREF="{$trg_html_}#_{@INSTANCE}" style="text-decoration:none"><SPAN style="color:{$DS_COL_XPRP}; font: italic 14px Verdana Arial,Helvetica,sans-serif">&#160;&#160;&#160;<xsl:value-of select="@INSTANCE"/></SPAN><xsl:if test="LICENSEINFO"><IMG SRC="imgs/IMG_LicensedCore.bmp" border="0" vspace="0" hspace="0"/></xsl:if></A>
			</xsl:for-each>
		</xsl:if>		
		
		<xsl:if test="MODULES/MODULE[@MODCLASS='MEMORY_CONTROLLER']">
				<BR></BR>	
				<A HREF="{$trg_html_}#_MemCntlrModules" style="text-decoration:none"><SPAN style="color:{$DS_COL_BLACK}; font: bold 16px Verdana Arial,Helvetica,sans-serif">Memory Controllers</SPAN></A>
				<xsl:for-each select="MODULES/MODULE[@MODCLASS='MEMORY_CONTROLLER']">
					<xsl:sort select="@INSTANCE"/>
					<BR></BR>
					<A HREF="{$trg_html_}#_{@INSTANCE}" style="text-decoration:none"><SPAN style="color:{$DS_COL_XPRP}; font: italic 14px Verdana Arial,Helvetica,sans-serif">&#160;&#160;&#160;<xsl:value-of select="@INSTANCE"/></SPAN><xsl:if test="LICENSEINFO"><IMG SRC="imgs/IMG_LicensedCore.bmp" border="0" vspace="0" hspace="0"/></xsl:if></A>
				</xsl:for-each>
		</xsl:if>		
		
		<xsl:if test="MODULES/MODULE[@MODCLASS='PERIPHERAL']">
			<BR></BR>
			<A HREF="{$trg_html_}#_Peripherals" style="text-decoration:none"><SPAN style="color:{$DS_COL_BLACK}; font: bold 16px Verdana Arial,Helvetica,sans-serif">Peripherals</SPAN></A>
			<xsl:for-each select="MODULES/MODULE[@MODCLASS='PERIPHERAL']">
				<xsl:sort select="@INSTANCE"/>
				<BR></BR>
				<A HREF="{$trg_html_}#_{@INSTANCE}" style="text-decoration:none"><SPAN style="color:{$DS_COL_XPRP}; font: italic 14px Courier Verdana Arial,Helvetica,sans-serif">&#160;&#160;&#160;<xsl:value-of select="@INSTANCE"/></SPAN><xsl:if test="LICENSEINFO"><IMG SRC="imgs/IMG_LicensedCore.bmp" border="0" vspace="0" hspace="0"/></xsl:if></A>
			</xsl:for-each>
		</xsl:if>		
		
		<xsl:if test="MODULES/MODULE[@MODCLASS='IP']">
			<BR></BR>
			<A HREF="{$trg_html_}#_IPModules" style="text-decoration:none"><SPAN style="color:{$DS_COL_BLACK}; font: bold 16px Verdana Arial,Helvetica,sans-serif">IP</SPAN></A>
			<xsl:for-each select="MODULES/MODULE[@MODCLASS='IP']">
				<xsl:sort select="@INSTANCE"/>
				<BR></BR>
				<A HREF="{$trg_html_}#_{@INSTANCE}" style="text-decoration:none"><SPAN style="color:{$DS_COL_XPRP}; font: italic 14px Courier Verdana Arial,Helvetica,sans-serif">&#160;&#160;&#160;<xsl:value-of select="@INSTANCE"/></SPAN><xsl:if test="LICENSEINFO"><IMG SRC="imgs/IMG_LicensedCore.bmp" border="0" vspace="0" hspace="0"/></xsl:if></A>
			</xsl:for-each>
		</xsl:if>			
		
		<BR></BR>
		<A HREF="{$trg_html_}#_TimingInfo" style="text-decoration:none"><SPAN style="color:{$DS_COL_BLACK}; font: bold 16px Verdana Arial,Helvetica,sans-serif">Timing Information</SPAN></A>
	</TD>
	
</TABLE>
</xsl:template>
<!-- ======================= END LAYOUT TABLE OF CONTENT =================================== -->

<!-- ==============================  LAYOUT SNAPSHOT  ====================================== -->
<xsl:template name="Layout_Overview">
	
<xsl:variable name="cnt_ip_"      select="count(MODULES/MODULE)"/>
<xsl:variable name="cnt_proc_"    select="count(MODULES/MODULE[@MODCLASS = 'PROCESSOR'])"/>
<xsl:variable name="cnt_busses_"  select="count(MODULES/MODULE[@MODCLASS = 'BUS'])"/>
<TABLE width="{$DS_WIDTH}" valign="top" align="left" border="0" cellpadding="0" cellspacing="1" COLS="2" BGCOLOR="{$DS_COL_BLACK}"> 

	<TD COLSPAN="2" ALIGN="middle" BGCOLOR="{$DS_COL_XPRP}">
		<SPAN style="color:{$DS_COL_WHITE}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">Overview</SPAN>
	</TD>
	<TR/>
	
	<xsl:if test="@TIMESTAMP">
		<TD COLSPAN="1" BGCOLOR="{$DS_COL_WHITE}" align="left">
			<SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif">Generated on</SPAN>
		</TD>
		<TD COLSPAN="1" BGCOLOR="{$DS_COL_WHITE}" align="middle">
			<SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@TIMESTAMP"/></SPAN>
		</TD>
		<TR></TR>
	</xsl:if>	
	
	<xsl:if test="@PROJECTSRC">
		<TD COLSPAN="1" BGCOLOR="{$DS_COL_WHITE}" align="left">
			<SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif">Source</SPAN>
		</TD>
		<TD COLSPAN="1" BGCOLOR="{$DS_COL_WHITE}" align="middle">
			<SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif">
<!--				
				<A HREF="{@PROJECTSRC}" style="text-decoration:none; color:{$DS_COL_XPRP}"><xsl:value-of select="@PROJECTSRC"/></A>
-->				
				<xsl:value-of select="@PROJECTSRC"/>
			</SPAN>
		</TD>
		<TR></TR>
	</xsl:if>	

	<TD COLSPAN="1" BGCOLOR="{$DS_COL_WHITE}" align="left">
		<SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif">EDK Version</SPAN>
	</TD>
	
	<TD COLSPAN="1" BGCOLOR="{$DS_COL_WHITE}" align="middle">
		<xsl:if test="@EDKVERSION">
			<SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@EDKVERSION"/></SPAN>
		</xsl:if>
		<xsl:if test="not(@EDKVERSION)">
			<SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif">NA</SPAN>
		</xsl:if>
	</TD>
	<TR/>

	<TD COLSPAN="1" BGCOLOR="{$DS_COL_WHITE}" align="left">
		<SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif">FPGA Family</SPAN>
	</TD>
	<TD COLSPAN="1" BGCOLOR="{$DS_COL_WHITE}" align="middle">
		<xsl:if test="@ARCH">
			<SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@ARCH"/></SPAN>
		</xsl:if>
		<xsl:if test="not(@ARCH)">
			<SPAN style="color:{$DS_COL_BLACK}; font: normal 10px Verdana,Arial,Helvetica,sans-serif">NA</SPAN>
		</xsl:if>
	</TD>
	<TR/>

	<TD COLSPAN="1" BGCOLOR="{$DS_COL_WHITE}" align="left">
		<SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif">Device</SPAN>
	</TD>
	<TD COLSPAN="1" BGCOLOR="{$DS_COL_WHITE}" align="middle">
		<xsl:if test="@PART">
			<SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@PART"/></SPAN>
		</xsl:if>
		<xsl:if test="not(@PART)">
			<SPAN style="color:{$DS_COL_BLACK}; font: bold 12px Verdana,Arial,Helvetica,sans-serif">-</SPAN>
		</xsl:if>
	</TD>
	<TR/>
	
	<TD COLSPAN="1" BGCOLOR="{$DS_COL_WHITE}" align="left">
		<SPAN style="color:{$DS_COL_BLACK}; font: Normal 12px Verdana,Arial,Helvetica,sans-serif"># IP Instantiated </SPAN>
	</TD>
	<TD COLSPAN="1" BGCOLOR="{$DS_COL_WHITE}" align="middle">
		<SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="$cnt_ip_"/></SPAN>
	</TD>
	<TR/>
	
	<TD COLSPAN="1" BGCOLOR="{$DS_COL_WHITE}" align="left">
		<SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif"># Processors </SPAN>
	</TD>
	<TD COLSPAN="1" BGCOLOR="{$DS_COL_WHITE}" align="middle">
		<SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="$cnt_proc_"/></SPAN>
	</TD>
	<TR/>
	
	<TD COLSPAN="1" BGCOLOR="{$DS_COL_WHITE}" align="left">
		<SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif"># Busses </SPAN>
	</TD>
	<TD COLSPAN="1" BGCOLOR="{$DS_COL_WHITE}" align="middle">
		<SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="$cnt_busses_"/></SPAN>
	</TD>
	<TR/>
	
	
</TABLE>

</xsl:template>

<!-- ==============================  END LAYOUT SNAPSHOT  =================================== -->

<!-- ==============================  LAYOUT INTRODUCTION  =================================== -->
<xsl:template name="Layout_Introduction">
</xsl:template>
<!-- ==============================  END INTRODUCTION    ==================================== -->

<!-- ==============================  External Ports      ==================================== -->
<xsl:template name="Layout_ExternalPorts">
	
	<xsl:variable name="gpin_CNT_"  select="count(EXTERNALPORTS/PORT)"/>
	<xsl:variable name="ipin_CNT_"  select="count(EXTERNALPORTS/PORT[@DIR='I'])"/>
	<xsl:variable name="opin_CNT_"  select="count(EXTERNALPORTS/PORT[@DIR='O'])"/>
	<xsl:variable name="iopin_CNT_" select="count(EXTERNALPORTS/PORT[@DIR='IO'])"/>
	
	<xsl:variable name="table_width_">
		<xsl:if test="$gpin_CNT_ &gt;  16"><xsl:value-of select="$DS_WIDTH"/></xsl:if>
		<xsl:if test="$gpin_CNT_ &lt;= 16"><xsl:value-of select="$DS_WIDTH"/></xsl:if>
		
	</xsl:variable>
	
	<xsl:variable name="left_extra_">
		<xsl:if test="($gpin_CNT_ mod 2)     = 1">1</xsl:if>
		<xsl:if test="not(($gpin_CNT_ mod 2) = 1)">0</xsl:if>
	</xsl:variable>
	
	<xsl:variable name="num_left_" select="floor($gpin_CNT_ div 2) + $left_extra_"/>
	<xsl:variable name="num_rhgt_" select="floor($gpin_CNT_ div 2)"/>
	
	<TABLE BGCOLOR="{$DS_COL_BLACK}" WIDTH="{$table_width_}" COLS="8" cellspacing="1" cellpadding="1" border="0">
		
		<TD COLSPAN="8" ALIGN="middle" BGCOLOR="{$DS_COL_XPRP}"><SPAN style="color:{$DS_COL_WHITE}; font: bold 9px Verdana,Arial,Helvetica,sans-serif">EXTERNAL PORTS</SPAN></TD>
	 	<TR></TR>	
		<TD COLSPAN="8" ALIGN="middle" bgcolor="{$DS_COL_WHITE}">
			<SPAN style="color:{$DS_COL_INFO}; font: bold 9px Verdana,Arial,Helvetica,sans-serif">
				These are the external ports defined in the MHS file.
			</SPAN>
		</TD>
		
		<TR></TR>
		<TD COLSPAN="8" ALIGN="left" bgcolor="{$DS_COL_WHITE}">
			<SPAN style="color:{$DS_COL_INFO}; font: bold 9px Verdana,Arial,Helvetica,sans-serif">Attributes Key</SPAN>
			<BR></BR>
			<SPAN style="color:{$DS_COL_BLACK}; font: italic 9px Verdana,Arial,Helvetica,sans-serif">The attributes are obtained from the SIGIS and IOB_STATE parameters set on the PORT in the MHS file </SPAN>
			<BR></BR>
			<SPAN style="color:{$DS_COL_ATTR_CLK}; font: bold 12px Verdana,Arial,Helvetica,sans-serif">CLK</SPAN>
			<SPAN style="color:{$DS_COL_INFO}; font: bold 9px Verdana,Arial,Helvetica,sans-serif">&#160;&#160;indicates Clock ports, (SIGIS = CLK)&#160;</SPAN>
			<BR></BR>
			<SPAN style="color:{$DS_COL_ATTR_INT}; font: bold 12px Verdana,Arial,Helvetica,sans-serif">INTR</SPAN>
			<SPAN style="color:{$DS_COL_INFO}; font: bold 9px Verdana,Arial,Helvetica,sans-serif">&#160;&#160;indicates Interrupt ports,(SIGIS = INTR)&#160;</SPAN>
			<BR></BR>
			<SPAN style="color:{$DS_COL_ATTR_RST}; font: bold 12px Verdana,Arial,Helvetica,sans-serif">RESET</SPAN>
			<SPAN style="color:{$DS_COL_INFO}; font: bold 9px Verdana,Arial,Helvetica,sans-serif">&#160;&#160;indicates Reset ports, (SIGIS = RST)&#160;</SPAN>
			<BR></BR>
			<SPAN style="color:{$DS_COL_ATTR_BUF}; font: bold 12px Verdana,Arial,Helvetica,sans-serif">BUF or REG</SPAN>
			<SPAN style="color:{$DS_COL_INFO}; font: bold 9px Verdana,Arial,Helvetica,sans-serif">&#160;&#160;Indicates ports that instantiate or infer IOB primitives, (IOB_STATE = BUF or REG)&#160;</SPAN>
		</TD>
		
		<xsl:if test="$gpin_CNT_ &lt;= 16">
			
		<TR></TR>
		
		<TD COLSPAN="7" ALIGN="left" bgcolor="{$DS_COL_WHITE}">
			
		<TABLE BGCOLOR="{$DS_COL_BLACK}" WIDTH="100%" COLS="9" cellspacing="1" cellpadding="0" border="0">
			
		<TD COLSPAN="1" width="5%"  align="left" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_XPRP}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">#</SPAN></TD>
		<TD COLSPAN="2" width="30%" align="left" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_XPRP}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">NAME</SPAN></TD>
		<TD COLSPAN="1" width="5%"  align="left"  bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_XPRP}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">DIR</SPAN></TD>
		<TD COLSPAN="1" width="5%"  align="left"  bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_XPRP}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">[LSB:MSB]</SPAN></TD>
		<TD COLSPAN="2" width="30%" align="left" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_XPRP}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">SIG</SPAN></TD>
		<TD COLSPAN="2" width="25%" align="left" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_XPRP}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">ATTRIBUTES</SPAN></TD>
		
		<xsl:for-each select="EXTERNALPORTS/PORT">
			<xsl:sort data-type="number" select="@INDEX" order = "ascending"/>
			
<!--			
			<xsl:message>The end of the string is <xsl:value-of select="substring(@GROUP,(string-length(@GROUP) -string-length(@GROUP)) + 1)"/></xsl:message>			
			<xsl:message>The letter is <xsl:value-of select="$groupLetter_"/></xsl:message>			
			<xsl:message>The color is <xsl:value-of select="$glb_bg_col_"/></xsl:message>			
			<xsl:variable name="glb_bg_col_">
				<xsl:choose>
					<xsl:when test="(@GROUP mod 2) = 1">
						<xsl:value-of select="$DS_COL_ASH"/>
					</xsl:when>		
					<xsl:otherwise>
						<xsl:value-of select="$DS_COL_WHITE"/>
					</xsl:otherwise>		
				</xsl:choose>	
			</xsl:variable>	
-->			

			<xsl:variable name="glb_bg_col_">
				<xsl:call-template name="Group2Color">
					<xsl:with-param name="group" select="@GROUP"/>
				</xsl:call-template>
			</xsl:variable>	
			
			<TR></TR>	
			<TD COLSPAN="1" width="5%"  align="left"   bgcolor="{$glb_bg_col_}">
				<SPAN style="color:{$DS_COL_BLACK}; font: bold 14px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@INDEX"/></SPAN><SPAN style="color:{$DS_COL_BLACK}; vertical-align: super; font: bold 10px Arial,Helvetica,sans-serif"><xsl:value-of select="@GROUP"/></SPAN>
			</TD>
			<TD COLSPAN="2" width="30%" align="left"   bgcolor="{$glb_bg_col_}"><SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@NAME"/></SPAN></TD>
			<TD COLSPAN="1" width="5%"  align="middle" bgcolor="{$glb_bg_col_}"><SPAN style="color:{$DS_COL_BLACK}; font: bold   10px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@DIR"/></SPAN></TD>
			<xsl:if test="@MSB and @LSB">
				<TD COLSPAN="1" width="5%" align="middle" bgcolor="{$glb_bg_col_}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@LSB"/>:<xsl:value-of select="@MSB"/></SPAN></TD>
			</xsl:if>			
			<xsl:if test="not(@MSB and @LSB)">
				<TD COLSPAN="1" width="5%" align="middle" bgcolor="{$glb_bg_col_}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">1</SPAN></TD>
			</xsl:if>			
			<TD COLSPAN="2" width="30%" align="left" bgcolor="{$glb_bg_col_}"><SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@SIGNAME"/></SPAN></TD>
			<TD COLSPAN="2" width="25%" align="left" bgcolor="{$glb_bg_col_}">
				<xsl:if test="@SIGIS='CLK'"><SPAN style="color:{$DS_COL_ATTR_CLK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">&#160;CLK&#160;</SPAN></xsl:if>
				<xsl:if test="@SIGIS='RST'"><SPAN style="color:{$DS_COL_ATTR_RST}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">&#160;RESET&#160;</SPAN></xsl:if>
				<xsl:if test="@SIGIS='INTERRUPT'"><SPAN style="color:{$DS_COL_ATTR_INT}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">&#160;INTR&#160;</SPAN></xsl:if>
				<xsl:if test="@IOB_STATE='BUF'"><SPAN style="color:{$DS_COL_ATTR_BUF}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">&#160;BUF&#160;</SPAN></xsl:if>
				<xsl:if test="@IOB_STATE='REG'"><SPAN style="color:{$DS_COL_ATTR_BUF}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">&#160;REG&#160;</SPAN></xsl:if>
			</TD>
		</xsl:for-each>
		
		</TABLE>
		</TD>
		</xsl:if>	
		
		<xsl:if test="$gpin_CNT_ &gt; 16">
			
			<TR></TR>	
			
			<TD COLSPAN="3" WIDTH="49%">
				<TABLE BGCOLOR="{$DS_COL_BLACK}" WIDTH="100%" COLS="9" cellspacing="1" cellpadding="0" border="0">
					<TD COLSPAN="1" width="5"   align="left" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_XPRP}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">#</SPAN></TD>
					<TD COLSPAN="2" width="30%" align="left" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_XPRP}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">NAME</SPAN></TD>
					<TD COLSPAN="1" width="5%"  align="left" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_XPRP}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">DIR</SPAN></TD>
					<TD COLSPAN="1" width="5%"  align="left" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_XPRP}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">[LSB:MSB]</SPAN></TD>
					<TD COLSPAN="2" width="30%" align="left" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_XPRP}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">SIG</SPAN></TD>
					<TD COLSPAN="2" width="25%" align="left" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_XPRP}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">ATTRIBUTES</SPAN></TD>
			
					<xsl:for-each select="EXTERNALPORTS/PORT">
					<xsl:sort data-type="number" select="@INDEX" order = "ascending"/>
					
					<xsl:if test="position() &lt;= $num_left_">
					
						<xsl:variable name="glb_bg_col_">
							<xsl:call-template name="Group2Color">	
								<xsl:with-param name="group" select="@GROUP"/>
							</xsl:call-template>		
						</xsl:variable>	
<!--
						<xsl:message>NAME: <xsl:value-of select="@NAME"/></xsl:message>						
						<xsl:message>SIGIS: <xsl:value-of select="@SIGIS"/></xsl:message>						
-->	
					    
						<TR></TR>	
						<TD COLSPAN="1" width="5%"  align="left"   bgcolor="{$glb_bg_col_}">
							<SPAN style="color:{$DS_COL_BLACK}; font: bold 14px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@INDEX"/></SPAN><SPAN style="color:{$DS_COL_BLACK}; vertical-align: super; font: bold 10px Arial,Helvetica,sans-serif"><xsl:value-of select="@GROUP"/></SPAN>
						</TD>
						<TD COLSPAN="2" width="30%" align="left"   bgcolor="{$glb_bg_col_}"><SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@NAME"/></SPAN></TD>
						<TD COLSPAN="1" width="5%"  align="middle" bgcolor="{$glb_bg_col_}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@DIR"/></SPAN></TD>
						<xsl:if test="@MSB and @LSB">
							<TD COLSPAN="1" width="5%" align="middle" bgcolor="{$glb_bg_col_}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@LSB"/>:<xsl:value-of select="@MSB"/></SPAN></TD>
						</xsl:if>			
						<xsl:if test="not(@MSB and @LSB)">
							<TD COLSPAN="1" width="5%" align="middle" bgcolor="{$glb_bg_col_}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">1</SPAN></TD>
						</xsl:if>			
						<TD COLSPAN="2" width="30%" align="left" bgcolor="{$glb_bg_col_}"><SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@SIGNAME"/></SPAN></TD>
						<TD COLSPAN="2" width="25%" align="left" bgcolor="{$glb_bg_col_}">
							<xsl:if test="@SIGIS='CLK'"><SPAN style="color:{$DS_COL_GREEN}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">&#160;CLK&#160;</SPAN></xsl:if>
							<xsl:if test="@SIGIS='RST'"><SPAN style="color:{$DS_COL_ATTR_RST}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">&#160;RESET&#160;</SPAN></xsl:if>
							<xsl:if test="@SIGIS='INTERRUPT'"><SPAN style="color:{$DS_COL_ATTR_INT}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">&#160;INTR&#160;</SPAN></xsl:if>
							<xsl:if test="@IOB_STATE='BUF'"><SPAN style="color:{$DS_COL_ATTR_BUF}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">&#160;BUF&#160;</SPAN></xsl:if>
							<xsl:if test="@IOB_STATE='REG'"><SPAN style="color:{$DS_COL_ATTR_BUF}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">&#160;REG&#160;</SPAN></xsl:if>
						</TD>
					</xsl:if>	
					</xsl:for-each>

					
				</TABLE>	
			</TD>	
			
			<TD COLSPAN="1" WIDTH="2%" BGCOLOR="{$DS_COL_GREY}">
				<SPAN style="color:{$DS_COL_XPRP}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">&#160;</SPAN>
			</TD> 
			
			<TD COLSPAN="3" WIDTH="49%">
				
				<TABLE BGCOLOR="{$DS_COL_BLACK}" WIDTH="100%" COLS="9" cellspacing="1" cellpadding="0" border="0">
					<TD COLSPAN="1" width="5%"  align="left" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_XPRP}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">#</SPAN></TD>
					<TD COLSPAN="2" width="30%" align="left" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_XPRP}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">NAME</SPAN></TD>
					<TD COLSPAN="1" width="5%"  align="left" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_XPRP}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">DIR</SPAN></TD>
					<TD COLSPAN="1" width="5%"  align="left" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_XPRP}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">[LSB:MSB]</SPAN></TD>
					<TD COLSPAN="2" width="30%" align="left" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_XPRP}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">SIG</SPAN></TD>
					<TD COLSPAN="2" width="25%" align="left" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_XPRP}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">ATTRIBUTES</SPAN></TD>
					
					<xsl:for-each select="EXTERNALPORTS/PORT">
					<xsl:sort data-type="number" select="@INDEX" order = "ascending"/>
					
					<xsl:if test="position() &gt; $num_left_">
<!--					
						<xsl:variable name="glb_bg_col_">
							<xsl:choose>
								<xsl:when test="(@GROUP mod 2) = 1">
									<xsl:value-of select="$DS_COL_ASH"/>
								</xsl:when>		
								<xsl:otherwise>
									<xsl:value-of select="$DS_COL_WHITE"/>
								</xsl:otherwise>		
							</xsl:choose>	
						</xsl:variable>	
-->						
						
						<xsl:variable name="glb_bg_col_">
							<xsl:call-template name="Group2Color">	
								<xsl:with-param name="group" select="@GROUP"/>
							</xsl:call-template>		
						</xsl:variable>	
			
						<TR></TR>	
						<TD COLSPAN="1" width="5%"  align="left"   bgcolor="{$glb_bg_col_}">
							<SPAN style="color:{$DS_COL_BLACK}; font: bold 14px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@INDEX"/></SPAN><SPAN style="color:{$DS_COL_BLACK}; vertical-align: super; font: bold 10px Arial,Helvetica,sans-serif"><xsl:value-of select="@GROUP"/></SPAN>
						</TD>
						<TD COLSPAN="2" width="30%" align="left"   bgcolor="{$glb_bg_col_}"><SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@NAME"/></SPAN></TD>
						<TD COLSPAN="1" width="5%"  align="middle" bgcolor="{$glb_bg_col_}"><SPAN style="color:{$DS_COL_BLACK}; font: bold   10px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@DIR"/></SPAN></TD>
						
						<xsl:if test="@MSB and @LSB">
							<TD COLSPAN="1" width="5%" align="middle" bgcolor="{$glb_bg_col_}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@LSB"/>:<xsl:value-of select="@MSB"/></SPAN></TD>
						</xsl:if>			
						<xsl:if test="not(@MSB and @LSB)">
							<TD COLSPAN="1" width="5%" align="middle" bgcolor="{$glb_bg_col_}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">1</SPAN></TD>
						</xsl:if>			
						<TD COLSPAN="2" width="30%" align="left" bgcolor="{$glb_bg_col_}"><SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@SIGNAME"/></SPAN></TD>
						<TD COLSPAN="2" width="25%" align="left" bgcolor="{$glb_bg_col_}">
							<xsl:if test="@SIGIS='CLK'"><SPAN style="color:{$DS_COL_GREEN}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">&#160;CLK&#160;</SPAN></xsl:if>
							<xsl:if test="@SIGIS='RST'"><SPAN style="color:{$DS_COL_ATTR_RST}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">&#160;RESET&#160;</SPAN></xsl:if>
							<xsl:if test="@SIGIS='INTERRUPT'"><SPAN style="color:{$DS_COL_ATTR_INT}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">&#160;INTR&#160;</SPAN></xsl:if>
							<xsl:if test="@IOB_STATE='BUF'"><SPAN style="color:{$DS_COL_ATTR_BUF}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">&#160;BUF&#160;</SPAN></xsl:if>
							<xsl:if test="@IOB_STATE='REG'"><SPAN style="color:{$DS_COL_ATTR_BUF}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">&#160;REG&#160;</SPAN></xsl:if>
						</TD>
					</xsl:if>	
					</xsl:for-each>
					
					<xsl:if test="$left_extra_ &gt; 0">
						<TR></TR>	
						<TD COLSPAN="9" WIDTH="100%" align="left" bgcolor="{$DS_COL_WHITE}"><SPAN style="color:{$DS_COL_WHITE}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">&#160;</SPAN></TD>
					</xsl:if>
					
				</TABLE>	
				
			</TD>	
	
		</xsl:if> 
		
	</TABLE>		

</xsl:template>

<xsl:template name="Group2Color">

	<xsl:param name="group"  select="'A'"/>
		
	<xsl:variable name="letter">
		<xsl:value-of select="substring($group,(string-length($group) -string-length($group)) + 1)"/>
	</xsl:variable>
	
	<xsl:choose>
		<xsl:when test="$group = 'GLB'"><xsl:value-of select="$DS_COL_WHITE"/></xsl:when>
		
		<xsl:when test="$letter = 'A'"><xsl:value-of select="$DS_COL_ASH"/></xsl:when>
		<xsl:when test="$letter = 'C'"><xsl:value-of select="$DS_COL_ASH"/></xsl:when>
		<xsl:when test="$letter = 'E'"><xsl:value-of select="$DS_COL_ASH"/></xsl:when>
		<xsl:when test="$letter = 'G'"><xsl:value-of select="$DS_COL_ASH"/></xsl:when>
		<xsl:when test="$letter = 'I'"><xsl:value-of select="$DS_COL_ASH"/></xsl:when>
		<xsl:when test="$letter = 'K'"><xsl:value-of select="$DS_COL_ASH"/></xsl:when>
		<xsl:when test="$letter = 'M'"><xsl:value-of select="$DS_COL_ASH"/></xsl:when>
		<xsl:when test="$letter = 'O'"><xsl:value-of select="$DS_COL_ASH"/></xsl:when>
		<xsl:when test="$letter = 'Q'"><xsl:value-of select="$DS_COL_ASH"/></xsl:when>
		<xsl:when test="$letter = 'S'"><xsl:value-of select="$DS_COL_ASH"/></xsl:when>
		<xsl:when test="$letter = 'U'"><xsl:value-of select="$DS_COL_ASH"/></xsl:when>
		<xsl:when test="$letter = 'W'"><xsl:value-of select="$DS_COL_ASH"/></xsl:when>
		<xsl:when test="$letter = 'Y'"><xsl:value-of select="$DS_COL_ASH"/></xsl:when>
		
		<xsl:when test="$letter = 'B'"><xsl:value-of select="$DS_COL_WHITE"/></xsl:when>
		<xsl:when test="$letter = 'D'"><xsl:value-of select="$DS_COL_WHITE"/></xsl:when>
		<xsl:when test="$letter = 'F'"><xsl:value-of select="$DS_COL_WHITE"/></xsl:when>
		<xsl:when test="$letter = 'H'"><xsl:value-of select="$DS_COL_WHITE"/></xsl:when>
		<xsl:when test="$letter = 'J'"><xsl:value-of select="$DS_COL_WHITE"/></xsl:when>
		<xsl:when test="$letter = 'L'"><xsl:value-of select="$DS_COL_WHITE"/></xsl:when>
		<xsl:when test="$letter = 'N'"><xsl:value-of select="$DS_COL_WHITE"/></xsl:when>
		<xsl:when test="$letter = 'P'"><xsl:value-of select="$DS_COL_WHITE"/></xsl:when>
		<xsl:when test="$letter = 'R'"><xsl:value-of select="$DS_COL_WHITE"/></xsl:when>
		<xsl:when test="$letter = 'T'"><xsl:value-of select="$DS_COL_WHITE"/></xsl:when>
		<xsl:when test="$letter = 'V'"><xsl:value-of select="$DS_COL_WHITE"/></xsl:when>
		<xsl:when test="$letter = 'X'"><xsl:value-of select="$DS_COL_WHITE"/></xsl:when>
		<xsl:when test="$letter = 'Z'"><xsl:value-of select="$DS_COL_WHITE"/></xsl:when>
		
		<xsl:otherwise>
			<xsl:value-of select="$DS_COL_WHITE"/>	
		</xsl:otherwise>
	</xsl:choose>
</xsl:template>





<xsl:template name="Layout_TimingInfo">
	
	<xsl:variable name="mtiming_CNT_" select="count(MODULES/MODULE/TIMING)"/>
	 
	<TABLE BGCOLOR="{$DS_COL_BLACK}" WIDTH="{ceiling($DS_WIDTH div 2)}" COLS="5" cellspacing="1" cellpadding="1" border="1">
		<TD COLSPAN="5" width="100%" align="middle" bgcolor="{$DS_COL_XPRP}"><SPAN style="color:{$DS_COL_WHITE}; font: bold 9px Verdana,Arial,Helvetica,sans-serif">Post Synthesis Clock Limits</SPAN></TD>
	 	<TR></TR>	
		<xsl:if test="$mtiming_CNT_ &lt; 1">
			<TD COLSPAN="5" width="100%" align="middle" bgcolor="{$DS_COL_WHITE}">
				<SPAN style="color:{$DS_COL_INFO}; font: bold 9px Verdana,Arial,Helvetica,sans-serif">
					No clocks could be identified in the design. Run platgen to generate synthesis information.
				</SPAN>
			</TD>
		</xsl:if>
		<xsl:if test="$mtiming_CNT_ &gt; 0">
			<TD COLSPAN="5" width="100%" align="left" bgcolor="{$DS_COL_WHITE}">
				<SPAN style="color:{$DS_COL_INFO}; font: bold 9px Verdana,Arial,Helvetica,sans-serif">
					These are the post synthesis clock frequencies. The critical frequencies are marked with
				</SPAN>
				<SPAN style="color:{$DS_COL_GREEN}; font: bold 9px Verdana,Arial,Helvetica,sans-serif">
					green.
				</SPAN>
				<BR></BR>
				<SPAN style="color:{$DS_COL_RED}; font: bold 9px Verdana,Arial,Helvetica,sans-serif">
					The values reported here are post synthesis estimates calculated for each individual module. These values will change after place and route is performed on the entire system.
				</SPAN>
			</TD>
			<TR></TR>
			<TD COLSPAN="2" width="40%" align="left" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_XPRP}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">MODULE</SPAN></TD>
			<TD COLSPAN="2" width="40%" align="left" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_XPRP}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">CLK Port</SPAN></TD>
			<TD COLSPAN="1" width="20%" align="left" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_XPRP}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">MAX FREQ</SPAN></TD>
			
			<xsl:for-each select="MODULES/MODULE/TIMING">
			<xsl:sort data-type="number" select="@MAXFREQ" order="ascending"/>
				<xsl:variable name="maxFreq_"  select="@MAXFREQ"/>
				<xsl:variable name="freqUnit_" select="@FREQUNITS"/>
				<xsl:variable name="freqCol_">
					<xsl:if test="position() = 1">	
						<xsl:value-of select="$DS_COL_GREEN"/>
					</xsl:if>
					<xsl:if test="not(position() = 1)">	
						<xsl:value-of select="$DS_COL_BLACK"/>
					</xsl:if>
				</xsl:variable>
				
				<xsl:for-each select="TIMECLK">
					<TR></TR>
					
					<TD COLSPAN="2" width="40%" align="left" bgcolor="{$DS_COL_WHITE}">
							<A HREF="#_{../../@INSTANCE}" style="text-decoration:none">
								<SPAN style="color:{$DS_COL_XPRP}; font: italic 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="../../@INSTANCE"/></SPAN>
							</A>
					</TD>
					
					<TD COLSPAN="2" width="40%" align="left" bgcolor="{$DS_COL_WHITE}">
						<SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif">
							<xsl:value-of select="@SIGNAME"/>
						</SPAN>
					</TD>
					
					<TD COLSPAN="1" width="20%" align="left" bgcolor="{$DS_COL_WHITE}">
						<SPAN style="color:{$freqCol_}; font: normal 12px Verdana,Arial,Helvetica,sans-serif">
							<xsl:value-of select="$maxFreq_"/><xsl:value-of select="$freqUnit_"/>
						</SPAN>
					</TD>
					
			    </xsl:for-each>
			</xsl:for-each>
		</xsl:if>
		
	</TABLE>	
</xsl:template>

<!-- ==============================  END GLOBAL PINOUT      ==================================== -->

<xsl:template name="Layout_NavigateHeader">
	<xsl:param name="header_name" select="HEADER"/>
	<BR></BR>
	<BR></BR>
	<BR></BR>
	<TABLE BGCOLOR="{$DS_COL_XPRP}" WIDTH="{$DS_WIDTH}" COLS="3" cellspacing="0" cellpadding="0" border="0">
		<TH COLSPAN="1" width="90%" align="left">  <SPAN style="color:{$DS_COL_WHITE}; font: bold 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="$header_name"/></SPAN></TH>
		<xsl:if test="$DS_TYPE='NOFRAMES'">
			<TH COLSPAN="1" width="10%"  align="middle"><A HREF="#_TOC" style="text-decoration:none"><SPAN style="color:{$DS_COL_LGRY}; font: bold 14px Verdana Arial,Helvetica,sans-serif">TOC</SPAN></A></TH>
		</xsl:if>	
		<xsl:if test="$DS_TYPE='FRAMES'">
			<TH COLSPAN="1" width="10%"  align="middle"><A HREF="#_Overview" style="text-decoration:none"><SPAN style="color:{$DS_COL_LGRY}; font: bold 14px Verdana Arial,Helvetica,sans-serif">TOP</SPAN></A></TH>
		</xsl:if>	
	</TABLE>
</xsl:template>


</xsl:stylesheet>
