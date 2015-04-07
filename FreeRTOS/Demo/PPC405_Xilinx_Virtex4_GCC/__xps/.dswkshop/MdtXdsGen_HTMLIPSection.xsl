<?xml version="1.0" standalone="no"?>
<xsl:stylesheet version="1.0"
           xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
           xmlns:exsl="http://exslt.org/common"
           xmlns:xlink="http://www.w3.org/1999/xlink">
         
<xsl:output method="html"/>

<!--
<xsl:param name="DS_COL_OPB"    select="'#339900'"/>
<xsl:param name="DS_COL_WHITE"   select="'#FFFFFF'"/>
<xsl:param name="DS_COL_INFO"   select="'#2233FF'"/>
<xsl:param name="DS_COL_BLACK"   select="'#000000'"/>
<xsl:param name="DS_COL_GREY"   select="'#CCCCCC'"/>
<xsl:param name="DS_COL_XPRP"   select="'#810017'"/>
<xsl:param name="DS_COL_DOCLNK" select="'#FF9900'"/>
-->
	        
<!-- ======================= MAIN PERIPHERAL SECTION =============================== -->
<xsl:template name="Layout_IPSection">

<TABLE BGCOLOR="{$DS_COL_WHITE}" WIDTH="{$DS_WIDTH}" COLS="4" cellspacing="0" cellpadding="0" border="0">
	
	<TD COLSPAN="4" width="5%" align="LEFT" valign="BOTTOM">
		<A name="_{@INSTANCE}"/>
		<xsl:if test="LICENSEINFO"><IMG SRC="imgs/IMG_LicensedCore.bmp" border="0" vspace="0" hspace="0"/></xsl:if>		
		<SPAN style="color:{$DS_COL_XPRP}; font: bold italic 14px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@INSTANCE"/></SPAN>
		<xsl:if test="DESCRIPTION[(@TYPE = 'SHORT')]">
			<SPAN style="color:{$DS_COL_XPRP}; font: normal italic 12px Verdana,Arial,Helvetica,sans-serif">
				&#160;&#160;<xsl:value-of select="DESCRIPTION[(@TYPE = 'SHORT')]"/>
			</SPAN>
		</xsl:if>
		<BR></BR>
		<xsl:if test="DESCRIPTION[(@TYPE = 'LONG')]">
			<SPAN style="color:{$DS_COL_BLACK}; font: normal italic 12px Verdana,Arial,Helvetica,sans-serif">
				<xsl:value-of select="DESCRIPTION[(@TYPE = 'LONG')]" disable-output-escaping="yes"/>
			</SPAN>
		</xsl:if>
		<BR></BR>
		<BR></BR>
		<BR></BR>
	</TD>	
	
	<TR></TR>
	
	<!-- Layout the Module information table-->
	<TD COLSPAN="2" width="40%" align="LEFT" valign="TOP">
		<IMG SRC="imgs/{@INSTANCE}.jpg" alt="{@INSTANCE} IP Image" border="0" vspace="0" hspace="0"/>
	</TD>
	<TD COLSPAN="2" width="60%" align="MIDDLE" valign="TOP">
		<xsl:call-template name="Peri_PortListTable"/>
		<BR></BR>
		<BR></BR>
	</TD>
	
	<TR></TR>
				
	<TD COLSPAN="4" width="100%" align="LEFT" valign="BOTTOM">
		<xsl:call-template name="Peri_InfoTable"/>
	</TD>
	
<!--	
	<TD COLSPAN="1" width="5%" align="LEFT"     valign="BOTTOM">
		<SPAN style="color:{$DS_COL_XPRP}; font: bold normal 16px Verdana,Arial,Helvetica,sans-serif">&#8970;</SPAN>
	</TD>
	<TD COLSPAN="2" width="90%" align="MIDDLE"  valign="BOTTOM">
		<SPAN style="color:{$DS_COL_BLACK}; font: bold 12px Verdana,Arial,Helvetica,sans-serif">&#160;</SPAN>
	</TD>
	<TD COLSPAN="1" width="5%" align="RIGHT"    valign="BOTTOM">
		<SPAN style="color:{$DS_COL_XPRP}; font: bold normal 16px Verdana,Arial,Helvetica,sans-serif">&#8971;</SPAN>
	</TD>
-->	
</TABLE>	

<BR></BR>
<BR></BR>

</xsl:template>

<!-- ======================= PERIHERAL TABLE PARTS   =============================== -->
<!-- Layout the Module's Information table -->
<xsl:template name="Peri_InfoTable">
	
	<xsl:variable name="mhsParamCNT_" select="count(PARAMETER)"/>
	
	<xsl:variable name="table_is_split_">
		<xsl:if test="$mhsParamCNT_     &gt;  10">1</xsl:if>
		<xsl:if test="not($mhsParamCNT_ &gt;  10)">0</xsl:if>
	</xsl:variable>
	
	<xsl:variable name="table_width_">
		<xsl:if test="$mhsParamCNT_  &gt;  10"><xsl:value-of select="$DS_WIDTH"/></xsl:if>
		<xsl:if test="$mhsParamCNT_  &lt;= 10"><xsl:value-of select="ceiling($DS_WIDTH div 2)"/></xsl:if>
	</xsl:variable>
	
	
	<xsl:variable name="left_extra_">
		<xsl:if test="($mhsParamCNT_ mod 2)     = 1">1</xsl:if>
		<xsl:if test="not(($mhsParamCNT_ mod 2) = 1)">0</xsl:if>
	</xsl:variable>
	
	<xsl:variable name="num_left_" select="floor($mhsParamCNT_ div 2) + $left_extra_"/>
	<xsl:variable name="num_rhgt_" select="floor($mhsParamCNT_ div 2)"/>
	
	<xsl:variable name="mdr_main_col_">
		<xsl:if test="$mhsParamCNT_  &gt;  10">4</xsl:if>
		<xsl:if test="$mhsParamCNT_  &lt;= 10">2</xsl:if>
	</xsl:variable>
	
	<xsl:variable name="mdr_othr_col_">
		<xsl:if test="$mhsParamCNT_  &gt;  10">2</xsl:if>
		<xsl:if test="$mhsParamCNT_  &lt;= 10">1</xsl:if>
	</xsl:variable>
	
	<TABLE BGCOLOR="{$DS_COL_BLACK}" WIDTH="{$table_width_}" COLS="5" cellspacing="1" cellpadding="1" border="1">
		<TD COLSPAN="5" WIDTH="100%" align="middle" bgcolor="{$DS_COL_XPRP}"><SPAN style="color:{$DS_COL_WHITE}; font: bold 12px Verdana,Arial,Helvetica,sans-serif">General</SPAN></TD>
		<TR></TR>
		<TD COLSPAN="2" WIDTH="40%" align="middle"  bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">IP Core</SPAN></TD>
		<TD COLSPAN="3" WIDTH="60%" align="middle"  bgcolor="{$DS_COL_WHITE}">
			<xsl:if test="@DOC_IP">
				<SPAN style="color:{$DS_COL_XPRP}; font: bold italic 10px Verdana,Arial,Helvetica,sans-serif">
					<A HREF="{@DOC_IP}" style="text-decoration:none; color:{$DS_COL_XPRP}"><xsl:value-of select="@MODTYPE"/></A>
				</SPAN>
			</xsl:if>
			<xsl:if test="not(@DOC_IP)">
				<SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">
					<xsl:value-of select="@MODTYPE"/>
				</SPAN>
			</xsl:if>
		</TD>
		
		<TR></TR>	
		
		<TD COLSPAN="2" WIDTH="40%" align="middle" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">Version</SPAN></TD>
		<TD COLSPAN="3" WIDTH="60%" align="middle" bgcolor="{$DS_COL_WHITE}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@HWVERSION"/></SPAN></TD>
		
		<xsl:if test="@DOC_DRIVER">
			<TR></TR>	
			<TD COLSPAN="2" WIDTH="40%" align="middle" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">Driver</SPAN></TD>
			<TD COLSPAN="3" WIDTH="60%" align="middle" bgcolor="{$DS_COL_WHITE}">
				<SPAN style="color:{$DS_COL_XPRP}; font: bold italic 10px Verdana,Arial,Helvetica,sans-serif">
					<A HREF="{@DOC_DRIVER}" style="text-decoration:none; color:{$DS_COL_XPRP}">API</A>
				</SPAN>
			</TD>	
		</xsl:if>	
		
		<TR></TR>	
		
		<xsl:if test="LICENSEINFO">
			<TD COLSPAN="5" WIDTH="100%" align="middle" bgcolor="{$DS_COL_XPRP}"><SPAN style="color:{$DS_COL_WHITE}; font: bold 12px Verdana,Arial,Helvetica,sans-serif">License</SPAN></TD>
			
			<TR></TR>
			<TD COLSPAN="2" WIDTH="40%" align="middle" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">TYPE</SPAN></TD>
			<TD COLSPAN="3" WIDTH="60%" align="middle" bgcolor="{$DS_COL_WHITE}">
				<SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="LICENSEINFO/@TYPE"/></SPAN>
			</TD>	
<!--			
			<TR></TR>
			<TD COLSPAN="2" WIDTH="40%" align="middle" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">CURRENT STATUS</SPAN></TD>
			<TD COLSPAN="3" WIDTH="60%" align="middle" bgcolor="{$DS_COL_WHITE}">
				<SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="LICENSEINFO/@STATE"/></SPAN>
			</TD>	
-->			
			<xsl:if test="LICENSEINFO/@EXPIRESON">
				<TR></TR>
				<TD COLSPAN="2" WIDTH="40%" align="middle"  bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">EXPIRES ON</SPAN></TD>
				<TD COLSPAN="3" WIDTH="60%" align="middle" bgcolor="{$DS_COL_WHITE}">
					<SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="LICENSEINFO/@EXPIRESON"/></SPAN>
				</TD>	
			</xsl:if>
		</xsl:if>	
		
		<xsl:if test="$mhsParamCNT_ &gt; 0">
		<TR></TR>	
		<TD COLSPAN="5" WIDTH="100%" align="middle" bgcolor="{$DS_COL_XPRP}"><SPAN style="color:{$DS_COL_WHITE}; font: bold 12px Verdana,Arial,Helvetica,sans-serif">Parameters</SPAN></TD>
			<TR></TR>
			<TD COLSPAN="5" width="100%" align="left" bgcolor="{$DS_COL_WHITE}">
				<SPAN style="color:{$DS_COL_INFO}; font: bold 9px Verdana,Arial,Helvetica,sans-serif">
					These are parameters set for this module.
					<xsl:if test="@DOC_IP">
						 Refer to the IP <A HREF="{@DOC_IP}" style="text-decoration:none; color:{$DS_COL_XPRP}"><SPAN style="color:{$DS_COL_XPRP}; font: bold italic 9px Verdana,Arial,Helvetica,sans-serif"> documentation </SPAN></A>for complete information about module parameters.
					</xsl:if>
				</SPAN>
				<BR></BR>
				<SPAN style="color:{$DS_COL_INFO}; font: bold 9px Verdana,Arial,Helvetica,sans-serif">
						Parameters marked with 
				</SPAN>
				<SPAN style="color:#FFBB00; font: bold 9px Verdana,Arial,Helvetica,sans-serif">yellow</SPAN>
				<SPAN style="color:{$DS_COL_INFO}; font: bold 9px Verdana,Arial,Helvetica,sans-serif">
					indicate parameters set by the user.
				</SPAN>
				<BR></BR>
				<SPAN style="color:{$DS_COL_INFO}; font: bold 9px Verdana,Arial,Helvetica,sans-serif">
						Parameters marked with 
				</SPAN>
				<SPAN style="color:{$DS_COL_MODSYSNW}; font: bold 9px Verdana,Arial,Helvetica,sans-serif">blue</SPAN>
				<SPAN style="color:{$DS_COL_INFO}; font: bold 9px Verdana,Arial,Helvetica,sans-serif">
					indicate parameters set by the system.
				</SPAN>
			</TD>
			
		<xsl:if test="$mhsParamCNT_ &lt;= 10">
			<TR></TR>	
			<TD COLSPAN="2" WIDTH="40%" align="middle" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">Name</SPAN></TD>
			<TD COLSPAN="3" WIDTH="60%" align="middle" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">Value</SPAN></TD>
		
			<xsl:for-each select="PARAMETER">
				<xsl:sort select="@INDEX" data-type="number"/>
					<xsl:variable name="name_bg_col_">
						<xsl:choose>
							
							<xsl:when test="@CHANGEDBY='USER'">
								<xsl:value-of select="$DS_COL_MODUSR"/>
							</xsl:when>		
								
							<xsl:when test="@CHANGEDBY='SYSTEM'">
								<xsl:value-of select="$DS_COL_MODSYS"/>
							</xsl:when>		
							
							<xsl:when test="((position() - 1) mod 2) = 0">
								<xsl:value-of select="$DS_COL_ASH1"/>
							</xsl:when>		
							
							<xsl:otherwise>
								<xsl:value-of select="$DS_COL_WHITE"/>
							</xsl:otherwise>		
						</xsl:choose>	
					</xsl:variable>
						
					<xsl:variable name="value_bg_col_">
						<xsl:choose>
							
							<xsl:when test="@CHANGEDBY='USER'">
								<xsl:value-of select="$DS_COL_MODUSR"/>
							</xsl:when>		
								
							<xsl:when test="@CHANGEDBY='SYSTEM'">
								<xsl:value-of select="$DS_COL_MODSYS"/>
							</xsl:when>	
							
							<xsl:when test="((position() - 1) mod 2) = 0">
								<xsl:value-of select="$DS_COL_ASH1"/>
							</xsl:when>		
							
							<xsl:otherwise>
								<xsl:value-of select="$DS_COL_WHITE"/>
							</xsl:otherwise>		
								
						</xsl:choose>	
					</xsl:variable>
						
				<TR></TR>	
				<TD COLSPAN="2" WIDTH="40%" align="left"   bgcolor="{$name_bg_col_}">
					<SPAN style="color:{$DS_COL_BLACK};  font: normal 12px Verdana,Arial,Helvetica,sans-serif">
							<xsl:value-of select="@NAME"/>
					</SPAN>
					<xsl:if test="DESCRIPTION">
						<BR/>
						<SPAN style="color:{$DS_COL_BLACK};  font: bold italic 9px Verdana,Arial,Helvetica,sans-serif">
							<xsl:value-of select="DESCRIPTION"/>
						</SPAN>
					</xsl:if>	
				</TD>
				<TD COLSPAN="3" WIDTH="60%" align="middle" bgcolor="{$value_bg_col_}"><SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@VALUE"/></SPAN></TD>
			</xsl:for-each>
	</xsl:if>			
	
	<xsl:if test="$mhsParamCNT_ &gt; 10">
	<TR></TR>	
	<TD COLSPAN="5" WIDTH="100%">
	<TABLE BGCOLOR="{$DS_COL_GREY}" WIDTH="100%" COLS="5" cellspacing="0" cellpadding="0" border="0">
		
		<TD COLSPAN="2" WIDTH="49%">
			<TABLE BGCOLOR="{$DS_COL_BLACK}" WIDTH="100%" COLS="2" cellspacing="1" cellpadding="0" border="0">
				<TD COLSPAN="1" WIDTH="50%" align="middle" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">Name</SPAN></TD>
				<TD COLSPAN="1" WIDTH="50%" align="middle" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">Value</SPAN></TD>
				
				<xsl:for-each select="PARAMETER">
					<xsl:sort select="@INDEX" data-type="number"/>
					<xsl:if test="position() &lt;= $num_left_">	
						
						<xsl:variable name="name_bg_col_">
							<xsl:choose>
								<xsl:when test="@CHANGEDBY='USER'">
									<xsl:value-of select="$DS_COL_MODUSR"/>
								</xsl:when>		
								
								<xsl:when test="@CHANGEDBY='SYSTEM'">
									<xsl:value-of select="$DS_COL_MODSYS"/>
								</xsl:when>		
							
								<xsl:when test="((position() - 1) mod 2) = 0">
									<xsl:value-of select="$DS_COL_ASH1"/>
								</xsl:when>		
							
								<xsl:otherwise>
									<xsl:value-of select="$DS_COL_WHITE"/>
								</xsl:otherwise>		
							</xsl:choose>	
						</xsl:variable>
						
						<xsl:variable name="value_bg_col_">
							<xsl:choose>
								<xsl:when test="@CHANGEDBY='USER'">
									<xsl:value-of select="$DS_COL_MODUSR"/>
								</xsl:when>		
								
								<xsl:when test="@CHANGEDBY='SYSTEM'">
									<xsl:value-of select="$DS_COL_MODSYS"/>
								</xsl:when>		
							
								<xsl:when test="((position() - 1) mod 2) = 0">
									<xsl:value-of select="$DS_COL_ASH1"/>
								</xsl:when>		
							
								<xsl:otherwise>
									<xsl:value-of select="$DS_COL_WHITE"/>
								</xsl:otherwise>		
							</xsl:choose>	
						</xsl:variable>
						
					<TR></TR>	
					<TD COLSPAN="1" WIDTH="50%" align="left"   bgcolor="{$name_bg_col_}">
						<SPAN style="color:{$DS_COL_BLACK};  font: normal 12px Verdana,Arial,Helvetica,sans-serif">
							<xsl:value-of select="@NAME"/>
						</SPAN>
						<xsl:if test="DESCRIPTION">
							<BR/>
							<SPAN style="color:{$DS_COL_BLACK};  font: bold italic 9px Verdana,Arial,Helvetica,sans-serif">
								<xsl:value-of select="DESCRIPTION"/>
							</SPAN>
						</xsl:if>	
					</TD>
					<TD COLSPAN="1" WIDTH="50%" align="middle" bgcolor="{$value_bg_col_}"><SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@VALUE"/></SPAN></TD>
				</xsl:if>
			</xsl:for-each>
			</TABLE>
		</TD> 
	
		<TD COLSPAN="1" WIDTH="2%">
			<TABLE BGCOLOR="{$DS_COL_GREY}"  WIDTH="100%" COLS="1" cellspacing="0" cellpadding="0" border="0">
				<TD COLSPAN="1" align="middle" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_XPRP}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">&#160;</SPAN></TD>
			</TABLE>
		</TD> 
	
		<TD COLSPAN="2" WIDTH="49%">
			<TABLE BGCOLOR="{$DS_COL_BLACK}" WIDTH="100%" COLS="2" cellspacing="1" cellpadding="0" border="0">
				<TD COLSPAN="1" WIDTH="50%" align="middle" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">Name</SPAN></TD>
				<TD COLSPAN="1" WIDTH="50%" align="middle" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">Value</SPAN></TD>
				<xsl:for-each select="PARAMETER">
					<xsl:sort select="@INDEX" data-type="number"/>
					<xsl:if test="position() &gt; $num_left_">	
						
						<xsl:variable name="name_bg_col_">
							<xsl:choose>
								<xsl:when test="@CHANGEDBY='USER'">
									<xsl:value-of select="$DS_COL_MODUSR"/>
								</xsl:when>		
								
								<xsl:when test="@CHANGEDBY='SYSTEM'">
									<xsl:value-of select="$DS_COL_MODSYS"/>
								</xsl:when>		
							
								<xsl:when test="((position() - $num_left_ - 1) mod 2) = 0">
									<xsl:value-of select="$DS_COL_ASH1"/>
								</xsl:when>		
							
								<xsl:otherwise>
									<xsl:value-of select="$DS_COL_WHITE"/>
								</xsl:otherwise>		
							</xsl:choose>	
						</xsl:variable>
						
						<xsl:variable name="value_bg_col_">
							<xsl:choose>
							
								<xsl:when test="@CHANGEDBY='USER'">
									<xsl:value-of select="$DS_COL_MODUSR"/>
								</xsl:when>		
								
								<xsl:when test="@CHANGEDBY='SYSTEM'">
									<xsl:value-of select="$DS_COL_MODSYS"/>
								</xsl:when>		
							
								<xsl:when test="((position() - $num_left_ - 1) mod 2) = 0">
									<xsl:value-of select="$DS_COL_ASH1"/>
								</xsl:when>		
							
								<xsl:otherwise>
									<xsl:value-of select="$DS_COL_WHITE"/>
								</xsl:otherwise>		
							</xsl:choose>	
						</xsl:variable>
					<TR></TR>	
					<TD COLSPAN="1" WIDTH="50%" align="left"   bgcolor="{$name_bg_col_}">
						<SPAN style="color:{$DS_COL_BLACK};  font: normal 12px Verdana,Arial,Helvetica,sans-serif">
							<xsl:value-of select="@NAME"/>
						</SPAN>
						<xsl:if test="DESCRIPTION">
							<BR/>
							<SPAN style="color:{$DS_COL_BLACK};  font: bold italic 9px Verdana,Arial,Helvetica,sans-serif">
								<xsl:value-of select="DESCRIPTION"/>
							</SPAN>
						</xsl:if>	
					</TD>
					<TD COLSPAN="1" WIDTH="50%" align="middle" bgcolor="{$value_bg_col_}"><SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@VALUE"/></SPAN></TD>
					
				</xsl:if>
			</xsl:for-each>
			
			<xsl:if test="$left_extra_ &gt; 0">
				<TR></TR>	
				<TD COLSPAN="2" WIDTH="100%" align="left" bgcolor="{$DS_COL_WHITE}"><SPAN style="color:{$DS_COL_WHITE}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">&#160;</SPAN></TD>
			</xsl:if>
			
			</TABLE>
		</TD> 
		
	</TABLE>
	</TD>	
	</xsl:if>			
	</xsl:if>
	</TABLE>
<!--	
		<BR></BR>	
-->		
		<xsl:if test="(@MODCLASS = 'PROCESSOR') and MEMORYMAP">
<!--			
			<xsl:message>Found a memory map</xsl:message>
-->			
			<xsl:call-template name="Layout_MemoryMap">
				<xsl:with-param name="table_width" select="$table_width_"/>
			</xsl:call-template>	
		</xsl:if>
<!--		
		<BR></BR>
-->	
		<TABLE BGCOLOR="{$DS_COL_BLACK}" WIDTH="{$table_width_}" COLS="5" cellspacing="1" cellpadding="1" border="0">
		<TD width="100%" COLSPAN="5" align="middle" bgcolor="{$DS_COL_XPRP}"><SPAN style="color:{$DS_COL_WHITE}; font: bold 12px Verdana,Arial,Helvetica,sans-serif">Post Synthesis Device Utilization</SPAN></TD>
		<xsl:choose>
			<xsl:when test="not(RESOURCES)">
				<TR></TR>
				<TD width="100%" COLSPAN="5" align="middle" bgcolor="{$DS_COL_WHITE}">
				<SPAN style="color:{$DS_COL_INFO}; font: bold 9px Verdana,Arial,Helvetica,sans-serif">
					Device utilization information is not available for this IP. Run platgen to generate synthesis information.
				</SPAN>
				</TD>
			</xsl:when>	
			<xsl:otherwise>
				<TR></TR>
				<TD COLSPAN="2" width="55%" align="middle" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">Resource Type</SPAN></TD>
				<TD COLSPAN="1" width="15%" align="middle" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">Used</SPAN></TD>
				<TD COLSPAN="1" width="15%" align="middle" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">Available</SPAN></TD>
				<TD COLSPAN="1" width="15%" align="middle" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">Percent</SPAN></TD>
				
				<xsl:for-each select="RESOURCES/RESOURCE">
					<TR></TR>	
					<TD COLSPAN="2" width="55%" align="left"   bgcolor="{$DS_COL_WHITE}"><SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@TYPE"/></SPAN></TD>
					<TD COLSPAN="1" width="15%" align="middle" bgcolor="{$DS_COL_WHITE}"><SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@USED"/></SPAN></TD>
					<TD COLSPAN="1" width="15%" align="middle" bgcolor="{$DS_COL_WHITE}"><SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@TOTAL"/></SPAN></TD>
					<TD COLSPAN="1" width="15%" align="middle" bgcolor="{$DS_COL_WHITE}"><SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@PERCENT"/></SPAN></TD>
				</xsl:for-each>
			</xsl:otherwise>
		</xsl:choose>
<!--		
	    <BR></BR>	
		<TD COLSPAN="5" width="100%" align="middle" bgcolor="{$DS_COL_XPRP}"><SPAN style="color:{$DS_COL_WHITE}; font: bold 12px Verdana,Arial,Helvetica,sans-serif"></SPAN></TD>
-->		
	</TABLE>

</xsl:template>

<!-- Layout the Module's Port list table -->
<xsl:template name="Peri_PortListTable">

	
	<TABLE BGCOLOR="{$DS_COL_BLACK}" WIDTH="{ceiling($DS_WIDTH div 2)}" COLS="7" cellspacing="1" cellpadding="1" border="0">
		<TH COLSPAN="7" width="100%" align="middle" bgcolor="{$DS_COL_XPRP}"><SPAN style="color:{$DS_COL_WHITE}; font: bold 9px Verdana,Arial,Helvetica,sans-serif">PORT LIST</SPAN></TH>
	 	<TR></TR>	
		<TH COLSPAN="7" width="100%" align="left" bgcolor="{$DS_COL_WHITE}">
			<SPAN style="color:{$DS_COL_INFO}; font: bold 9px Verdana,Arial,Helvetica,sans-serif">
				The ports listed here are only those connected in the MHS file. 
				<xsl:if test="@DOC_IP">
					Refer to the IP <A HREF="{@DOC_IP}" style="text-decoration:none; color:{$DS_COL_XPRP}"> <SPAN style="color:{$DS_COL_XPRP}; font: bold italic 9px Verdana,Arial,Helvetica,sans-serif"> documentation </SPAN> </A>for complete information about module ports.
				</xsl:if>
			</SPAN>
		</TH>
		<TR></TR>
		<TH COLSPAN="1" width="5%"  align="left"   bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">#</SPAN></TH>
		<TH COLSPAN="2" width="25%" align="left"   bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">NAME</SPAN></TH>
		<TH COLSPAN="1" width="10%" align="middle" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">DIR</SPAN></TH>
		<TH COLSPAN="1" width="10%" align="middle" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">[LSB:MSB]</SPAN></TH>
		<TH COLSPAN="2" width="50%" align="left"   bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">SIGNAL</SPAN></TH>
		<xsl:for-each select="PORT[(not(@SIGNAME = '__NOC__') and not(@SIGNAME = '__DEF__') and (@INMHS))]">
			<xsl:sort data-type="number" select="@INDEX" order="ascending"/>
			<TR></TR>	
			<TD COLSPAN="1" width="5%"  align="left" bgcolor="{$DS_COL_WHITE}"><SPAN style="color:{$DS_COL_BLACK};   font: normal 10px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@INDEX"/></SPAN></TD>
			<TD COLSPAN="2" width="25%" align="left" bgcolor="{$DS_COL_WHITE}"><SPAN style="color:{$DS_COL_BLACK};   font: normal 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@NAME"/></SPAN></TD>
			<TD COLSPAN="1" width="10%" align="middle" bgcolor="{$DS_COL_WHITE}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@DIR"/></SPAN></TD>
			
			<xsl:if test="@MSB and @LSB">
				<TD COLSPAN="1" width="10%" align="middle" bgcolor="{$DS_COL_WHITE}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@LSB"/>:<xsl:value-of select="@MSB"/></SPAN></TD>
			</xsl:if>			
			<xsl:if test="not(@MSB and @LSB)">
				<TD COLSPAN="1" width="10%" align="middle" bgcolor="{$DS_COL_WHITE}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">1</SPAN></TD>
			</xsl:if>			
			
			<TD COLSPAN="2" width="50%" align="left" bgcolor="{$DS_COL_WHITE}"><SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@SIGNAME"/></SPAN></TD>
		</xsl:for-each>
		
		<xsl:if test="BUSINTERFACE">
			<xsl:variable name="instance_"><xsl:value-of select="@INSTANCE"/></xsl:variable>
			<TR></TR>
			<TH COLSPAN="7" width="100%" align="middle" bgcolor="{$DS_COL_XPRP}">
				<SPAN style="color:{$DS_COL_WHITE}; font: bold 9px Verdana,Arial,Helvetica,sans-serif">Bus Interfaces</SPAN>
			</TH>	
			<TR></TR>
			
			<TH COLSPAN="1" width="15%" align="middle" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">MASTERSHIP</SPAN></TH>
			<TH COLSPAN="1" width="10%" align="middle" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">NAME</SPAN></TH>
			<TH COLSPAN="1" width="25%" align="middle" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">STD</SPAN></TH>
			<TH COLSPAN="3" width="25%" align="middle" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">BUS</SPAN></TH>
			<TH COLSPAN="1" width="25%" align="middle" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">P2P</SPAN></TH>
			<xsl:for-each select="BUSINTERFACE[(not(@BUSNAME = '__NOC__') and not(@BUSNAME = '__DEF__'))]">
			<xsl:sort select="@BIFRANK"/>
					
				<xsl:variable name="busname_"><xsl:value-of select="@BUSNAME"/></xsl:variable>
					
				<xsl:variable name="p2pname_">
					<xsl:choose>
						<xsl:when test="(@BUSSTD and not((@BUSSTD='PLB') or (@BUSSTD='OPB')) or (@BIFRANK='TRANSPARENT'))">
							<xsl:value-of select="../../MODULE[not(@INSTANCE = $instance_) and BUSINTERFACE[(@BUSNAME = $busname_)]]/@INSTANCE"/>
						</xsl:when>
						<xsl:when test="not(@BUSSTD) or (@BUSSTD='OPB') or (@BUSSTD='PLB') or (@BIFRANK='TRANSPARENT')">NA</xsl:when>
				   </xsl:choose>
				</xsl:variable>					
				
				<xsl:variable name="bus_std_">
					<xsl:if test="@BUSSTD">
						<xsl:value-of select="@BUSSTD"/>
					</xsl:if>
					<xsl:if test="not(@BUSSTD)">NA</xsl:if>
				</xsl:variable>					
				
				
				<TR></TR>
				<TH COLSPAN="1" width="15%" align="middle" bgcolor="{$DS_COL_WHITE}"><SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@BIFRANK"/></SPAN></TH>
				<TH COLSPAN="1" width="10%" align="middle" bgcolor="{$DS_COL_WHITE}"><SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@NAME"/></SPAN></TH>
				<TH COLSPAN="1" width="25%" align="middle" bgcolor="{$DS_COL_WHITE}"><SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="$bus_std_"/></SPAN></TH>
				<xsl:if test="$bus_std_ = 'NA'">
					<TH COLSPAN="3" width="25%" align="middle" bgcolor="{$DS_COL_WHITE}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@BUSNAME"/></SPAN></TH>
				</xsl:if>	
				<xsl:if test="not($bus_std_ = 'NA')">
					<TH COLSPAN="3" width="25%" align="middle" bgcolor="{$DS_COL_WHITE}"><A HREF="#_{@BUSNAME}" style="text-decoration:none"><SPAN style="color:{$DS_COL_XPRP}; font: italic 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@BUSNAME"/></SPAN></A></TH>
				</xsl:if>	
				<xsl:if test="$p2pname_ = 'NA'">
					<TH COLSPAN="1" width="25%" align="middle" bgcolor="{$DS_COL_WHITE}"><SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="$p2pname_"/></SPAN></TH>
				</xsl:if>
				<xsl:if test="not($p2pname_ = 'NA')">
				    <TH COLSPAN="1" width="25%" align="middle" bgcolor="{$DS_COL_WHITE}"><A HREF="#_{$p2pname_}" style="text-decoration:none"><SPAN style="color:{$DS_COL_XPRP}; font: italic 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="$p2pname_"/></SPAN></A></TH>
				</xsl:if>
			</xsl:for-each>
		</xsl:if>
		
		<xsl:if test="@MODCLASS='BUS'">
			<xsl:variable name="instance_"><xsl:value-of select="@INSTANCE"/></xsl:variable>
			<TR></TR>
			<TH COLSPAN="7" width="100%" align="middle" bgcolor="{$DS_COL_XPRP}"><SPAN style="color:{$DS_COL_WHITE}; font: bold 9px Verdana,Arial,Helvetica,sans-serif">Bus Connections</SPAN></TH>	
			<TR></TR>
			<TH COLSPAN="1" width="25%" align="middle" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">TYPE</SPAN></TH>
			<TH COLSPAN="5" width="50%" align="middle" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">NAME</SPAN></TH>
			<TH COLSPAN="1" width="25%" align="middle" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">BIF</SPAN></TH>
			<xsl:for-each select="../MODULE/BUSINTERFACE[(@BUSNAME = $instance_)]">
				<xsl:sort select="@BIFRANK"/>
				<xsl:variable name="buscName_"><xsl:value-of select="../@INSTANCE"/></xsl:variable>
				<TR></TR>
				<TD COLSPAN="1" width="25%" align="middle" bgcolor="{$DS_COL_WHITE}"><SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@BIFRANK"/></SPAN></TD>
				<TD COLSPAN="5" width="50%" align="middle" bgcolor="{$DS_COL_WHITE}"><A HREF="#_{$buscName_}" style="text-decoration:none"><SPAN style="color:{$DS_COL_XPRP}; font: italic 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="$buscName_"/></SPAN></A></TD>
				<TD COLSPAN="1" width="25%" align="left"   bgcolor="{$DS_COL_WHITE}"><SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@NAME"/></SPAN></TD>
			</xsl:for-each>
		</xsl:if>
		
		<xsl:if test="INTERRUPTSRCS">
			<TR></TR>
			<TH COLSPAN="7" width="100%" align="middle" bgcolor="{$DS_COL_XPRP}">
				<SPAN style="color:{$DS_COL_WHITE}; font: bold 9px Verdana,Arial,Helvetica,sans-serif">Interrupt Priorities</SPAN>
				<TR></TR>
				<TH COLSPAN="1" width="10%" align="middle" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">Priority</SPAN></TH>
				<TH COLSPAN="3" width="55%" align="middle" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">SIG</SPAN></TH>
				<TH COLSPAN="3" width="35%" align="middle" bgcolor="{$DS_COL_GREY}"><SPAN style="color:{$DS_COL_BLACK}; font: bold 10px Verdana,Arial,Helvetica,sans-serif">MODULE</SPAN></TH>
				<TR></TR>
				<xsl:for-each select="INTERRUPTSRCS/INTRSRC">
				<xsl:sort data-type="number" select="@PRIORITY" order="ascending"/>
				
					<xsl:variable name="intrsrc_"><xsl:value-of select="@SIGNAME"/></xsl:variable>
					<xsl:variable name="intrpri_"><xsl:value-of select="@PRIORITY"/></xsl:variable>
					
					<xsl:for-each select="../../../MODULE[PORT[((@DIR='O') and (@SIGNAME = $intrsrc_))]]">
						<TR></TR>
						<TH COLSPAN="1" width="10%" align="middle" bgcolor="{$DS_COL_WHITE}"><SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="$intrpri_"/></SPAN></TH>
						<TH COLSPAN="3" width="55%" align="middle" bgcolor="{$DS_COL_WHITE}"><SPAN style="color:{$DS_COL_BLACK}; font: normal 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="$intrsrc_"/></SPAN></TH>
						<TH COLSPAN="3" width="35%" align="middle" bgcolor="{$DS_COL_WHITE}"><A HREF="#_{@INSTANCE}" style="text-decoration:none"><SPAN style="color:{$DS_COL_XPRP}; font: normal 12px Verdana,Arial,Helvetica,sans-serif"><xsl:value-of select="@INSTANCE"/></SPAN></A></TH>
					</xsl:for-each>
				</xsl:for-each>
			</TH>
		</xsl:if>
		
	</TABLE>	
	
</xsl:template>
</xsl:stylesheet>
