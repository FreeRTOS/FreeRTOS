<?xml version="1.0" standalone="no"?>

<xsl:stylesheet version="1.0"
           xmlns:svg="http://www.w3.org/2000/svg"
           xmlns:exsl="http://exslt.org/common"
           xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
           xmlns:math="http://exslt.org/math"
 	       xmlns:xlink="http://www.w3.org/1999/xlink"
           extension-element-prefixes="math">
           
		   
<!-- 
	===============================================
				INCLUDES
	===============================================
 -->	
<xsl:include href="MdtSvgBLKD_Dimensions.xsl"/>

<xsl:include href="MdtSvgDiag_Colors.xsl"/>
<xsl:include href="MdtSvgDiag_Globals.xsl"/>
<xsl:include href="MdtSvgDiag_StyleDefs.xsl"/>

<xsl:include href="MdtTinySvgDiag_BifShapes.xsl"/>

<xsl:include href="MdtTinySvgBLKD_IOPorts.xsl"/>
<xsl:include href="MdtTinySvgBLKD_Busses.xsl"/>
<xsl:include href="MdtTinySvgBLKD_Globals.xsl"/>
<xsl:include href="MdtTinySvgBLKD_Functions.xsl"/>
<xsl:include href="MdtTinySvgBLKD_Peripherals.xsl"/>
<xsl:include href="MdtTinySvgBLKD_Processors.xsl"/>
<xsl:include href="MdtTinySvgBLKD_BusLaneSpaces.xsl"/>
	
<xsl:output method="xml" version="1.0" encoding="UTF-8" indent="yes"
	       doctype-public="-//W3C//DTD SVG 1.0//EN"
		   doctype-system="svg10.dtd"/>
	
<!-- 
	===============================================
				PARAMETERS
	===============================================
 -->	
 
<xsl:param    name="ADD_VIEWBOX"        select="'FALSE'"/>		   
<xsl:param    name="IN_TESTMODE"        select="'FALSE'"/>

<!-- 
<xsl:param    name="CSS_SVG_DIAGRAMS"   select="'MdtSvgDiag_StyleDefs.css'"/>
<xsl:param    name="CSS_SVG_DIAGRAMS"   select="'__INTERNAL__'"/>
 -->
		
<!-- 
	====================================================== 
				MAIN BLOCKDIAGRAM TEMPLATE	
	====================================================== 
-->
<xsl:template match="EDKSYSTEM[not(BLKDIAGRAM)]">
	<xsl:message>ERROT: Project is missing BLKDIAGRAM Element. Cannot generate.</xsl:message>
</xsl:template>

<xsl:template match="EDKSYSTEM[BLKDIAGRAM]">
	
<!--
<xsl:message>STCK_W is <xsl:value-of select="$G_Total_Stacks_W"/></xsl:message>
<xsl:message>BRDG_W is <xsl:value-of select="$G_Total_Bridges_W"/></xsl:message>
<xsl:message>MPMC is <xsl:value-of select="$G_Total_StandAloneMpmc_H"/></xsl:message>
<xsl:message>MPMC is <xsl:value-of select="$G_Total_StandAloneMpmc_H"/></xsl:message>
<xsl:message>MABV is <xsl:value-of select="$G_Max_Stack_AbvSbs_H"/></xsl:message>
<xsl:message>MBLW is <xsl:value-of select="$G_Max_Stack_BlwSbs_H"/></xsl:message>
<xsl:message>IPBK is <xsl:value-of select="$G_Total_IpBucket_H"/></xsl:message>
<xsl:message>Blkd Total is <xsl:value-of select="$blkd_H_"/></xsl:message>
<xsl:message>max abv is <xsl:value-of select="$max_Stack_AbvSbs_H_"/></xsl:message>
<xsl:message>max blw is <xsl:value-of select="$max_Stack_BlwSbs_H_"/></xsl:message>
<xsl:message>Ip Bkt is <xsl:value-of select="$totalIpBkt_H_"/></xsl:message>
<xsl:message>Sbs is <xsl:value-of select="$totalSbs_H_"/></xsl:message>
<xsl:message>Unk Bkt is <xsl:value-of select="$totalUnkBkt_H_"/></xsl:message>
<xsl:message>Blkd DrawArea height as <xsl:value-of select="$total_DrawArea_H_"/></xsl:message>
-->

<!--specify a css for the file -->
<!-- 
<xsl:processing-instruction name="xml-stylesheet">href="<xsl:value-of select="$CSS_SVG_DIAGRAMS"/>" type="text/css"</xsl:processing-instruction>
<xsl:variable name="BLKD_ZOOM_Y">
	<xsl:choose>
		<xsl:when test="($ADD_VIEWBOX = 'TRUE')">
			<xsl:value-of select="($G_Total_Diag_H * 2)"/>
		</xsl:when>
		<xsl:otherwise>0</xsl:otherwise>		
	</xsl:choose>
</xsl:variable>
 -->
	
<xsl:text>&#10;</xsl:text>
<!--
<svg width="{$G_Total_Diag_W}" height="{$G_Total_Diag_H}" viewBox="0 0 0 {$BLKD_ZOOM_Y}">	
-->
<svg width="{$G_Total_Diag_W}" height="{$G_Total_Diag_H}">
<!-- 
	 =============================================== 
	       Layout All the various definitions       
	 =============================================== 
-->
	<defs>
		
		<!-- IO Port Defs -->
		<xsl:call-template name="Define_IOPorts"/>		
		
		<!-- BIF Defs -->
		<xsl:call-template name="Define_ConnectedBifTypes"/>		
		
		<!-- Bus Defs -->
		<xsl:call-template name="Define_Busses"/>		
		
		<!-- Shared Bus Buckets Defs -->
		<xsl:call-template name="Define_SBSBuckets"/>		
		
		<!-- IP Bucket Defs -->
		<xsl:call-template name="Define_IPBucket"/>		
		
		<!-- Stack Defs -->
		<xsl:call-template name="Define_AllStacks"/>		
		
		<!-- Space Defs -->
		<xsl:call-template name="Define_BusLaneSpaces"/>		
		
		<!-- Main MPMC Defs -->
		<xsl:if test="$G_ROOT/EDKSYSTEM/BLKDIAGRAM/CMPLXSHAPES/MPMCSHAPE">
			<xsl:call-template name="Define_StandAlone_MPMC"/>	
		</xsl:if>
		
		<!-- Diagram Key Definition -->
		<xsl:call-template name="Define_BlkDiagram_Key"/>		
		
		<!-- Diagram Specs Definition -->
		<xsl:call-template name="Define_BlkDiagram_Specs">		
			<xsl:with-param name="iArch"       select="SYSTEMINFO/@ARCH"/>
			<xsl:with-param name="iPart"       select="SYSTEMINFO/@PART"/>
			<xsl:with-param name="iTimeStamp"  select="@TIMESTAMP"/>
			<xsl:with-param name="iEdkVersion" select="@EDKVERSION"/>
		</xsl:call-template>		
		
	</defs>
	
<!-- =============================================== -->
<!--             Draw Outlines                       -->
<!-- =============================================== -->
	
	 <!-- The surrounding black liner -->
     <rect x="0"  
		   y="0" 
		   width ="{$G_Total_Diag_W}"
		   height="{$G_Total_Diag_H}" style="fill:{$COL_WHITE}; stroke:{$COL_BLACK};stroke-width:4"/>
		   
	 <!-- The outer IO channel -->
     <rect x="{$BLKD_PRTCHAN_W}"  
		   y="{$BLKD_PRTCHAN_H}" 
		   width= "{$G_Total_Blkd_W - ($BLKD_PRTCHAN_W * 2)}" 
		   height="{$G_Total_Blkd_H - ($BLKD_PRTCHAN_H * 2)}" style="fill:{$COL_IORING}"/>
		   
	 <!-- The Diagram's drawing area -->
     <rect x="{$BLKD_PRTCHAN_W + $BLKD_IORCHAN_W}"  
		   y="{$BLKD_PRTCHAN_H + $BLKD_IORCHAN_H}" 
		   width= "{$G_Total_DrawArea_W}"
		   height="{$G_Total_DrawArea_H}" rx="8" ry="8" style="fill:{$COL_BG}"/>
		   
<!-- =============================================== -->
<!--        Draw All the various components          -->
<!-- =============================================== -->
	
	<!--   Layout the IO Ports    -->	
<!-- 
	<xsl:if test="(not($IN_TESTMODE) or ($IN_TESTMODE = 'FALSE'))">
		<xsl:call-template name="Draw_IOPorts"/>	
	</xsl:if>
 -->	
	
	<!--   Layout the Shapes      -->	
	<xsl:call-template name="Draw_BlkDiagram_Shapes"/>		
	
</svg>
	
<!-- ======================= END MAIN SVG BLOCK =============================== -->
</xsl:template>
	
<xsl:template name="Draw_BlkDiagram_Shapes">

	<!-- 
		 ===========================================================
	 					Draw the Stand Alone MPMC, (if any)
	 ===========================================================
	-->
	<xsl:if test="$G_ROOT/EDKSYSTEM/BLKDIAGRAM/CMPLXSHAPES/MPMCSHAPE">
	
		<xsl:variable name="mpmc_inst_" select="$G_ROOT/EDKSYSTEM/BLKDIAGRAM/CMPLXSHAPES/MPMCSHAPE/@INSTANCE"/>
		<use   x="{$BLKD_INNER_X}"  y="{$BLKD_INNER_Y}"  xlink:href="#mpmcmodule_{$mpmc_inst_}"/> 
	
	<!-- 
		 ===========================================================
	 					Draw the connections to the Stand Alone MPMC
		 ===========================================================
	-->
		<xsl:call-template name="Draw_BlkDiagram_StandAloneMpmcConnections"/>	
	</xsl:if>	
	
	<!-- 
		 ===========================================================
	 					Draw the Stacks
		 ===========================================================
	-->
	<xsl:call-template name="Draw_BlkDiagram_Stacks"/>	
	
	
	
	<!-- 
		 ===========================================================
	 					Draw the Bus Lane Spaces 
		 ===========================================================
	-->
	<xsl:call-template name="Draw_BlkDiagram_BusLaneSpaces"/>	
	
	
	<!-- 
		 ===========================================================
	 					Draw the shared busses 
		 ===========================================================
	-->
	<use   x="{$BLKD_INNER_X}"      y="{$G_SharedBus_Y}"  xlink:href="#group_sharedBusses"/> 
	
	<!-- 
		 ===========================================================
	 					Draw the Bridges
		 ===========================================================
	-->
	<xsl:call-template name="Draw_BlkDiagram_Bridges"/>	
	
	
	<!-- 
		 ===========================================================
	 					Draw the Ip Bucket
		 ===========================================================
	-->
	<xsl:call-template name="Draw_BlkDiagram_IPBucket"/>
	
	
	<!-- 
		 ===========================================================
	 					Draw the Key
		 ===========================================================
	-->
	<xsl:if test="(not($IN_TESTMODE) or ($IN_TESTMODE = 'FALSE'))">
		<use   x="{$G_Total_Blkd_W - $BLKD_KEY_W - $BLKD_PRTCHAN_W}" y="{$G_Total_Blkd_H + $BLKD_DRAWAREA2KEY_GAP - 8}"  xlink:href="#BlkDiagram_Key"/> 
	</xsl:if>
	
	<!-- 
		 ===========================================================
	 					Draw the Specs
		 ===========================================================
	-->
	<xsl:if test="(not($IN_TESTMODE) or ($IN_TESTMODE = 'FALSE'))">
		<use   x="{$BLKD_PRTCHAN_W}"  y="{$G_Total_Blkd_H + $BLKD_DRAWAREA2KEY_GAP - 8}"  xlink:href="#BlkDiagram_Specs"/> 
	</xsl:if>
	
	<!-- 
		************************************************************ 
		***************  DONE DRAWING BLOCK DIAGRAM   ************** 
		************************************************************ 
	-->	
	
</xsl:template>	
	
	
<!-- ======================================================================= -->
<!--                         FUNCTION TEMPLATE                               -->
<!--																		 -->
<!--  Draw stacks on the Block Diagram										 -->
<!-- ======================================================================= -->
<xsl:template name="Draw_BlkDiagram_Stacks">
	
	<xsl:for-each select="$G_ROOT/EDKSYSTEM/BLKDIAGRAM/BCLANESPACES/BCLANESPACE[(@EAST &lt; $G_ROOT/EDKSYSTEM/BLKDIAGRAM/@STACK_HORIZ_WIDTH)]">
			
		<xsl:variable name="stack_line_x_">
			<xsl:call-template name="F_Calc_Stack_X">
				<xsl:with-param name="iStackIdx"  select="@EAST"/>
			</xsl:call-template>
		</xsl:variable>
		
		<xsl:variable name="stack_abv_sbs_">
			<xsl:call-template name="F_Calc_Stack_AbvSbs_Height">
				<xsl:with-param name="iStackIdx"  select="@EAST"/>
			</xsl:call-template>
		</xsl:variable>
		
		<xsl:variable name="bridges_w_"    select="(($G_NumOfBridges * ($BLKD_MOD_W + ($BLKD_BUS_LANE_W * 2))) + $BLKD_BRIDGE_GAP)"/>
		
		<xsl:variable name="stack_y_" select="($G_SharedBus_Y - $stack_abv_sbs_ - $BLKD_PROC2SBS_GAP)"/>
		<xsl:variable name="stack_x_" select="($BLKD_INNER_X + $stack_line_x_ + $bridges_w_)"/>
		
		<xsl:variable name="stack_name_">
			<xsl:call-template name="F_generate_Stack_Name"> 
				<xsl:with-param name="iHorizIdx" select="@EAST"/>
			</xsl:call-template>		
		</xsl:variable>	
		
		<use   x="{$stack_x_}"    y="{$stack_y_}"  xlink:href="#{$stack_name_}"/> 
	
	</xsl:for-each>	
			
</xsl:template>
	
<xsl:template name="Draw_BlkDiagram_StandAloneMpmcConnections">
	
	<xsl:variable name="mpmcInst_" select="$G_ROOT/EDKSYSTEM/BLKDIAGRAM/CMPLXSHAPES/MPMCSHAPE/@INSTANCE"/>
	<xsl:variable name="lastStack_" select="($G_ROOT/EDKSYSTEM/BLKDIAGRAM/@STACK_HORIZ_WIDTH) - 1"/>
	
	
	<xsl:for-each select="$G_ROOT/EDKSYSTEM/BLKDIAGRAM/BCLANESPACES/BCLANESPACE">
		<xsl:variable name="currentLane_" select="position()"/>
<!--		
		<xsl:message>Current lane <xsl:value-of select="$currentLane_"/></xsl:message>
-->	
		<xsl:variable name="stackToEast_">
			<xsl:choose>
				<xsl:when test="not(@WEST = $lastStack_)"><xsl:value-of select="@EAST"/></xsl:when>
				<xsl:when test="   (@WEST = $lastStack_)"><xsl:value-of select="'NONE'"/></xsl:when>
			</xsl:choose>
		</xsl:variable>
		
		<xsl:variable name="stackToWest_">
			<xsl:choose>
				<xsl:when test="not(@WEST = $lastStack_)"><xsl:value-of select="'NONE'"/></xsl:when>
				<xsl:when test="   (@WEST = $lastStack_)"><xsl:value-of select="@WEST"/></xsl:when>
			</xsl:choose>
		</xsl:variable>
		
		<xsl:variable name="spaceAbvSbs_H_">
			<xsl:call-template name="F_Calc_Space_AbvSbs_Height">
				<xsl:with-param name="iStackToEast"  select="$stackToEast_"/>
				<xsl:with-param name="iStackToWest"  select="$stackToWest_"/>
			</xsl:call-template>
		</xsl:variable>	
		
		<xsl:variable name="space_y_"   select="($G_SharedBus_Y - $spaceAbvSbs_H_ - $BLKD_PROC2SBS_GAP)"/>
	
<!--		
		<xsl:message>Stack To East <xsl:value-of select="$stackToEast_"/></xsl:message>
		<xsl:message>Stack To West <xsl:value-of select="$stackToWest_"/></xsl:message>
		<xsl:variable name="space_X_">
			<xsl:call-template name="F_Calc_Space_X"> 
				<xsl:with-param name="iStackToEast" select="$stackToEast_"/>
				<xsl:with-param name="iStackToWest" select="$stackToWest_"/>
			</xsl:call-template>		
		</xsl:variable>
		<xsl:variable name="space_y_"   select="($G_SharedBus_Y - $spaceAbvSbs_H_ - $BLKD_PROC2SBS_GAP)"/>
		<xsl:variable name="space_x_"   select="($BLKD_INNER_X + $G_Total_Bridges_W + $space_line_x_)"/>
-->		
		
	
		<xsl:for-each select="BUSCONNLANE[@IS_MPMCCONN]">
			
<!--			
			<xsl:variable name="bifSide_" select="$G_ROOT/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = BUSCONN/@INSTANCE)]/BUSINTERFACE[(@BUSNAME = @BUSNAME)]/@BIF_X"/>
-->	
			<xsl:variable name="bifInst_"     select="BUSCONN/@INSTANCE"/>
			<xsl:variable name="busName_"     select="@BUSNAME"/>
			<xsl:variable name="bifSide_"     select="$G_ROOT/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $bifInst_)]/BUSINTERFACE[(@BUSNAME = $busName_)]/@BIF_X"/>
			
			<xsl:variable name="mpmcBifName_">
				<xsl:choose>
					<xsl:when test="   (@IS_SBSCONN)"><xsl:value-of select="BUSCONN/@BUSINTERFACE"/></xsl:when>
					<xsl:when test="not(@IS_SBSCONN)"><xsl:value-of select="$G_ROOT/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $mpmcInst_)]/BUSINTERFACE[(@BUSNAME = $busName_)]/@NAME"/></xsl:when>
					<xsl:otherwise><xsl:value-of select="$G_ROOT/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $mpmcInst_)]/BUSINTERFACE[(@BUSNAME = $busName_)]/@NAME"/></xsl:otherwise>
				</xsl:choose>
			</xsl:variable>
			
<!--			
			<xsl:message>MPMC Bif Name <xsl:value-of select="$mpmcBifName_"/></xsl:message>
			<xsl:message>Bif Side <xsl:value-of select="$bifSide_"/></xsl:message>
			<xsl:message>Bus Name <xsl:value-of select="@BUSNAME"/></xsl:message>
			<xsl:message>Instance <xsl:value-of select="$bifInst_"/></xsl:message>
			<xsl:message>Space line x <xsl:value-of select="$space_line_X_"/></xsl:message>
-->	
			
			<xsl:variable name="space_line_X_">
				<xsl:call-template name="F_Calc_Space_X">
					<xsl:with-param name="iStackToEast"  select="$stackToEast_"/>
					<xsl:with-param name="iStackToWest"  select="$stackToWest_"/>
				</xsl:call-template>
			</xsl:variable>
			
			<xsl:variable name="space_X_"   select="($BLKD_INNER_X + $G_Total_Bridges_W + $space_line_X_)"/>
			
			<xsl:variable name = "stackToWest_W_">
				<xsl:choose>
					<xsl:when test="(($stackToEast_ = '0')   and     ($stackToWest_ = 'NONE'))">0</xsl:when>
					<xsl:when test="(($stackToEast_ = 'NONE') and not($stackToWest_ = 'NONE'))">
						<xsl:call-template name="F_Calc_Stack_Width">
							<xsl:with-param name="iStackIdx"  select="$stackToWest_"/>
						</xsl:call-template>
					</xsl:when>
					<xsl:when test="(not($stackToEast_ = '0') and not($stackToEast_ = 'NONE') and ($stackToWest_ = 'NONE'))">
						<xsl:call-template name="F_Calc_Stack_Width">
							<xsl:with-param name="iStackIdx"  select="($stackToEast_ - 1)"/>
						</xsl:call-template>
					</xsl:when>
					<xsl:otherwise>0</xsl:otherwise>
				</xsl:choose>
			</xsl:variable>
	
			<xsl:variable name = "stackToEast_W_">
				<xsl:call-template name="F_Calc_Stack_Width">
					<xsl:with-param name="iStackIdx"  select="$stackToEast_"/>
				</xsl:call-template>
			</xsl:variable>
	
			<xsl:variable name ="extSpaceWest_W_" select="ceiling($stackToWest_W_ div 2)"/>
			<xsl:variable name ="extSpaceEast_W_" select="ceiling($stackToEast_W_ div 2)"/>
			<xsl:variable name="laneInSpace_X_">
				<xsl:choose>
				   <xsl:when test="(@ORIENTED = 'EAST')">
					   <xsl:value-of select="($extSpaceWest_W_ + (@BUSLANE_X * $BLKD_BUS_LANE_W) - $BLKD_BUS_LANE_W - $BLKD_BUS_ARROW_W - $BLKD_P2P_BUS_W)"/>
				   </xsl:when>
				   <xsl:otherwise><xsl:value-of select="($extSpaceWest_W_ + (@BUSLANE_X * $BLKD_BUS_LANE_W))"/></xsl:otherwise>
				</xsl:choose>
			</xsl:variable> 
						
			
			<xsl:variable name="lane_X_"        select="($space_X_ + $laneInSpace_X_)"/>
			
			<xsl:variable name="mpmcBifType_" select="$G_ROOT/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $mpmcInst_)]/BUSINTERFACE[(@NAME = $mpmcBifName_)]/@TYPE"/>
			
		<!--	
			<xsl:variable name="bc_X_" select="($lane_X_ +  ceiling($BLKD_BIFC_W div 2) - ceiling($BLKD_BUS_ARROW_W div 2))"/>
			<xsl:variable name="bc_X_" select="($lane_X_ +  ceiling($BLKD_BIFC_W div 2) - ceiling($BLKD_BUS_ARROW_W div 2))"/>
			<xsl:variable name="bc_X_" select="($lane_X_ + ceiling($BLKD_BIFC_W div 2))"/>
		-->	
			
			<xsl:variable name="bc_Y_" select="($BLKD_INNER_Y + $BLKD_MPMC_MOD_H)"/>
			<xsl:variable name="bc_X_" >
				<xsl:choose>
					<xsl:when test="($bifSide_ = '0')"><xsl:value-of select="($lane_X_ + ceiling($BLKD_BIFC_W div 2))"/></xsl:when>
					<xsl:when test="($bifSide_ = '1')"><xsl:value-of select="($lane_X_ + $BLKD_BIFC_dx)"/></xsl:when>
					<xsl:otherwise>                    <xsl:value-of select="($lane_X_ + ceiling($BLKD_BIFC_W div 2))"/></xsl:otherwise>
				</xsl:choose>
			</xsl:variable>
			
			<xsl:variable name="busColor_">
				<xsl:call-template name="F_BusStd2RGB">
					<xsl:with-param name="iBusStd" select="@BUSSTD"/>
				</xsl:call-template>	
			</xsl:variable>
		
			<!-- Place the MPMC bif label -->
			<xsl:variable name="bcl_X_" select="($bc_X_ + ceiling($BLKD_BIFC_W div 2) - ceiling($BLKD_BIF_W div 2))"/>
			<xsl:variable name="bcl_Y_" select="($bc_Y_ - $BLKD_BIF_H - $BLKD_MOD_BIF_GAP_H)"/>
			<use  x="{$bcl_X_}"   y="{$bcl_Y_}"  xlink:href="#{@BUSSTD}_BifLabel"/>
			
			<xsl:call-template name="F_WriteText">
				<xsl:with-param name="iX" 		select="($bcl_X_ + ceiling($BLKD_BIF_W div 2))"/>
				<xsl:with-param name="iY" 		select="($bcl_Y_ + ceiling($BLKD_BIF_H div 2) + 3)"/>
				<xsl:with-param name="iText"	select="$mpmcBifName_"/>
				<xsl:with-param name="iClass"	select="'mpmc_biflabel'"/>
			</xsl:call-template>	
				  

			<!-- Place the MPMC bif -->
			<use   x="{$bc_X_}"   y="{$bc_Y_}"  xlink:href="#{@BUSSTD}_busconn_{$mpmcBifType_}"/>
			
			<xsl:variable name="bcArrow_X_" select="($bc_X_ +  ceiling($BLKD_BIFC_W div 2) - ceiling($BLKD_BUS_ARROW_H div 2))"/>
			<xsl:variable name="bcArrow_Y_" select="($bc_Y_ + $BLKD_BIFC_H - 3)"/>
			
			<!-- Place the MPMC Arrow -->
			<use   x="{$bcArrow_X_}"   y="{$bcArrow_Y_}"  xlink:href="#{@BUSSTD}_BusArrowNorth"/>
			
			<!-- 
				Place a block to cover the gap btw MPMC and top of Bus Lane Space, or to the correct SBS 
				For non SBS connections a vertical block will already have been drawn to the top of the
				space.
			-->
			
			<xsl:variable name="sbsDy_">
				<xsl:choose>
					<xsl:when test="@IS_SBSCONN"><xsl:value-of select="2 + ($G_ROOT/EDKSYSTEM/MODULES/MODULE[(@INSTANCE = $busName_)]/@BUS_INDEX * $BLKD_SBS_LANE_H)"/></xsl:when>
					<xsl:when test="not(@IS_SBSCONN)">0</xsl:when>
					<xsl:otherwise>0></xsl:otherwise>
				</xsl:choose>
			</xsl:variable>
			
			<xsl:variable name="mpmcBusHeight_">
				<xsl:choose>
					<xsl:when    test="(@IS_SBSCONN)"><xsl:value-of select="($G_SharedBus_Y - ($bcArrow_Y_ + $BLKD_BUS_ARROW_W + 4) + $sbsDy_)"/></xsl:when>
					<xsl:when test="not(@IS_SBSCONN)">
						<xsl:choose>
							<xsl:when test="($space_y_ &gt;= ($bcArrow_Y_ + $BLKD_BUS_ARROW_W + 4 + $sbsDy_))">
								<xsl:value-of select="($space_y_ - ($bcArrow_Y_ + $BLKD_BUS_ARROW_W + 4 + $sbsDy_))"/>
							</xsl:when>
							<xsl:when test="($space_y_ &lt; ($bcArrow_Y_ + $BLKD_BUS_ARROW_W + 4 + $sbsDy_))">
								<xsl:value-of select="(($bcArrow_Y_ + $BLKD_BUS_ARROW_W + 4 + $sbsDy_) - $space_y_)"/>
							</xsl:when>
						</xsl:choose>
					</xsl:when>
					<xsl:otherwise><xsl:value-of select="$BLKD_BIFC_H"/></xsl:otherwise>
				</xsl:choose>
			</xsl:variable>
			
			<rect x="{$bcArrow_X_ + $BLKD_BUS_ARROW_G}" 
		  	  	  y="{$bcArrow_Y_ + $BLKD_BUS_ARROW_W + 4}"  
		 	  	  width= "{$BLKD_P2P_BUS_W}" 
		  	  	  height="{$mpmcBusHeight_}"  
		 	      style="stroke:none; fill:{$busColor_}"/>	
			
			<!-- place the bus label here -->

			<xsl:call-template name="F_WriteText">
				<xsl:with-param name="iX" 		select="($bcArrow_X_ + $BLKD_BUS_ARROW_W + 6)"/>
				<xsl:with-param name="iY" 		select="($bcArrow_Y_ + ceiling($mpmcBusHeight_ div 2) + 6)"/>
				<xsl:with-param name="iText"	select="$busName_"/>
				<xsl:with-param name="iClass"	select="'p2pbus_label'"/>
			</xsl:call-template>	
			
		</xsl:for-each>    			
	</xsl:for-each>	
	
</xsl:template>
	
	
<!-- ======================================================================= -->
<!--                         FUNCTION TEMPLATE                               -->
<!--																		 -->
<!--  Draw bus lane spaces on the Block Diagram								 -->
<!-- ======================================================================= -->
<xsl:template name="Draw_BlkDiagram_BusLaneSpaces">
	
	<xsl:variable name="lastStack_" select="($G_ROOT/EDKSYSTEM/BLKDIAGRAM/@STACK_HORIZ_WIDTH) - 1"/>
	
	<xsl:for-each select="$G_ROOT/EDKSYSTEM/BLKDIAGRAM/BCLANESPACES/BCLANESPACE[@EAST]">
		<xsl:sort select="@EAST" data-type="number"/>
			
		<xsl:call-template name="Draw_BlkDiagram_BusLaneSpace">
			<xsl:with-param name="iStackToEast"  select="@EAST"/>
		</xsl:call-template>
	</xsl:for-each>	
	
	<xsl:for-each select="$G_ROOT/EDKSYSTEM/BLKDIAGRAM/BCLANESPACES/BCLANESPACE[(@WEST = $lastStack_)]">
		<xsl:call-template name="Draw_BlkDiagram_BusLaneSpace">
			<xsl:with-param name="iStackToWest"  select="$lastStack_"/>
		</xsl:call-template>
	</xsl:for-each>	
			
</xsl:template>
	
<xsl:template name="Draw_BlkDiagram_BusLaneSpace">
	
	<xsl:param name="iStackToEast" select="'NONE'"/>
	<xsl:param name="iStackToWest" select="'NONE'"/>
	
	<xsl:variable name="spaceAbvSbs_H_">
		<xsl:call-template name="F_Calc_Space_AbvSbs_Height">
			<xsl:with-param name="iStackToEast"  select="$iStackToEast"/>
			<xsl:with-param name="iStackToWest"  select="$iStackToWest"/>
		</xsl:call-template>
	</xsl:variable>	
	
	<xsl:variable name="spaceBlwSbs_H_">
		<xsl:call-template name="F_Calc_Space_BlwSbs_Height">
			<xsl:with-param name="iStackToEast"  select="$iStackToEast"/>
			<xsl:with-param name="iStackToWest"  select="$iStackToWest"/>
		</xsl:call-template>
	</xsl:variable>	
	
	<xsl:variable name="space_line_x_">
		<xsl:call-template name="F_Calc_Space_X">
			<xsl:with-param name="iStackToEast"  select="$iStackToEast"/>
			<xsl:with-param name="iStackToWest"  select="$iStackToWest"/>
		</xsl:call-template>
	</xsl:variable>
	
	<xsl:variable name="space_y_"   select="($G_SharedBus_Y - $spaceAbvSbs_H_ - $BLKD_PROC2SBS_GAP)"/>
	<xsl:variable name="space_x_"   select="($BLKD_INNER_X + $G_Total_Bridges_W + $space_line_x_)"/>
	
	<xsl:variable name="stackToEast_">
		<xsl:choose>
			<xsl:when test="not($iStackToEast = 'NONE')"><xsl:value-of select="$iStackToEast"/></xsl:when>
			<xsl:otherwise>NONE</xsl:otherwise>
		</xsl:choose>
	</xsl:variable>	
	
	<xsl:variable name="stackToWest_">
		<xsl:choose>
			<xsl:when test=" not($iStackToWest = 'NONE')"><xsl:value-of select="$iStackToWest"/></xsl:when>
			<xsl:when test="(not($iStackToEast = 'NONE') and not($iStackToEast = '0'))"><xsl:value-of select="($iStackToEast - 1)"/></xsl:when>
			<xsl:otherwise>NONE</xsl:otherwise>
		</xsl:choose>
	</xsl:variable>	
	
		
	<xsl:variable name="space_Name_">
		<xsl:call-template name="F_generate_Space_Name"> 
			<xsl:with-param name="iStackToEast" select="$stackToEast_"/>
			<xsl:with-param name="iStackToWest" select="$stackToWest_"/>
		</xsl:call-template>		
	</xsl:variable>	
	
<!--	
	<xsl:message>StackToEast is <xsl:value-of select="$iStackToEast"/></xsl:message>
	<xsl:message>StackToWest is <xsl:value-of select="$iStackToWest"/></xsl:message>
	<xsl:message>SpaceName is <xsl:value-of select="$space_Name_"/></xsl:message>
-->	
		
	<use   x="{$space_x_}"    y="{$space_y_}"  xlink:href="#{$space_Name_}"/> 
	
</xsl:template>
	
	
<!-- =========================================================================== -->
<!--                          FUNCTION TEMPLATE                                  -->
<!--																			 -->
<!--  Draw Bridges on the Block Diagram											 -->
<!-- =========================================================================== -->
<xsl:template name="Draw_BlkDiagram_Bridges">
	
	<!-- First save all the bridge indexs in a variable	 -->
	<xsl:variable name="bridgeShapes_">
		<xsl:for-each select="$G_ROOT/EDKSYSTEM/BLKDIAGRAM/BRIDGESHAPES/MODULE/BUSCONNS[(@ORIENTED = 'WEST')]/BUSCONN">	
			<BRIDGE BUS_INDEX="{@BUS_INDEX}" INSTANCE="{../../@INSTANCE}" POSITION="{(position() -1)}"/>
			<BRIDGECONN BUS_INDEX="{@BUS_INDEX}" INSTANCE="{../../@INSTANCE}" ORIENTED="{../@ORIENTED}" POSITION="{(position()  - 1)}" BUSSTD="{@BUSSTD}" TYPE="{@TYPE}"/>
			<!-- So both bus conns have same position.... -->
			<xsl:if test="../../BUSCONNS[(@ORIENTED = 'EAST')]">
				<BRIDGECONN BUS_INDEX="{../../BUSCONNS[(@ORIENTED ='EAST')]/BUSCONN/@BUS_INDEX}" INSTANCE="{../../@INSTANCE}" ORIENTED="EAST" POSITION="{(position()  - 1)}"   BUSSTD="{../../BUSCONNS[(@ORIENTED = 'EAST')]/BUSCONN/@BUSSTD}" TYPE="{../../BUSCONNS[(@ORIENTED = 'EAST')]/BUSCONN/@TYPE}"/>
			</xsl:if>
		</xsl:for-each>
	</xsl:variable>
<!--				
			<xsl:message>Found an east connection on <xsl:value-of select="../../@INSTANCE"/></xsl:message>
-->				
	<!-- Now layout the bridge shapes between the shared busses	 -->
	<xsl:for-each select="exsl:node-set($bridgeShapes_)/BRIDGE">
		<xsl:sort select="@POSITION" data-type="number"/>
		
		<xsl:variable name="brdgPosition_"  select="@POSITION"/>
		<xsl:variable name="brdgInstance_"  select="@INSTANCE"/>
		
		<xsl:variable name="min_bus_idx_" select="math:min(exsl:node-set($bridgeShapes_)/BRIDGECONN[(@POSITION = $brdgPosition_)]/@BUS_INDEX)"/>
<!--		
		<xsl:variable name="max_bus_idx_" select="math:max(exsl:node-set($bridgeShapes_)/BRIDGECONN[(@POSITION = $brdgPosition_)]/@BUS_INDEX)"/>
		
     	<xsl:message>Maximum index <xsl:value-of select="$max_bus_idx_"/></xsl:message>
     	<xsl:message>Minimum index <xsl:value-of select="$min_bus_idx_"/></xsl:message>
-->
		
		
		<xsl:variable name="brdg_X_"  select="($BLKD_INNER_X + $BLKD_BRIDGE_GAP + $BLKD_BUS_LANE_W + (@POSITION * ($BLKD_MOD_W + ($BLKD_BUS_LANE_W * 2))))"/>	
		<xsl:variable name="brdg_Y_"  select="($G_SharedBus_Y  + ($min_bus_idx_ * $BLKD_SBS_LANE_H) + ceiling($BLKD_SBS_LANE_H div 2) - ceiling($BLKD_MOD_H div 2))"/>
		
		<use  x="{$brdg_X_}"  y="{$brdg_Y_}"  xlink:href="#symbol_{$brdgInstance_}"/>	
	</xsl:for-each>	
	
		
	
<!--	
	<xsl:message>Found <xsl:value-of select="count(exsl:node-set($bridgeShapes_)/BRIDGECONN)"/> busconns </xsl:message>
		<xsl:message>Drawing connection for bridge <xsl:value-of select="$brdgInstance_"/> at <xsl:value-of select="@POSITION"/> </xsl:message>
-->	
	
	<xsl:for-each select="exsl:node-set($bridgeShapes_)/BRIDGECONN">
		<xsl:sort select="@POSITION" data-type="number"/>
		
		<xsl:variable name="brdgInstance_"  select="@INSTANCE"/>
		<xsl:variable name="brdgPosition_"  select="@POSITION"/>
		
		<xsl:variable name="busColor_">
			<xsl:call-template name="F_BusStd2RGB">
				<xsl:with-param name="iBusStd" select="@BUSSTD"/>
			</xsl:call-template>	
		</xsl:variable>
		
		<xsl:variable name="min_bus_idx_" select="math:min(exsl:node-set($bridgeShapes_)/BRIDGECONN[(@POSITION = $brdgPosition_)]/@BUS_INDEX)"/>
		<xsl:variable name="brdg_Y1_"     select="($G_SharedBus_Y  + ($min_bus_idx_ * $BLKD_SBS_LANE_H) + ceiling($BLKD_SBS_LANE_H div 2) - ceiling($BLKD_MOD_H div 2))"/>
		<xsl:variable name="brdg_X_"      select="($BLKD_INNER_X   + $BLKD_BRIDGE_GAP + $BLKD_BUS_LANE_W + (@POSITION * ($BLKD_MOD_W + ($BLKD_BUS_LANE_W * 2))))"/>	
		
		<xsl:variable name="bc_Y_"        select="$brdg_Y1_ + $BLKD_MOD_LANE_H + $BLKD_MOD_LABEL_H + $BLKD_MOD_BIF_GAP_V + ceiling($BLKD_BIF_H div 2) - ceiling($BLKD_BIFC_H div 2)"/>	
		<xsl:variable name="bc_X_">
			<xsl:choose>
				<xsl:when test="@ORIENTED='WEST'">
					<xsl:value-of select="($brdg_X_ - $BLKD_BIFC_W)"/>
				</xsl:when>
				<xsl:when test="@ORIENTED='EAST'">
					<xsl:value-of select="($brdg_X_ + $BLKD_MOD_W)"/>
				</xsl:when>
			</xsl:choose>
		</xsl:variable>	
		
		<!-- Layout the bus conn -->
		<use   x="{$bc_X_}"   y="{$bc_Y_}"  xlink:href="#{@BUSSTD}_busconn_{@TYPE}"/>
		
		<!-- Figure out the positions of the lines -->
		
<!--		
		<xsl:variable name="vert_line_x_"  select="$bc_X_    + ceiling($BLKD_BIFC_W div 2)"/>
		<xsl:message>vert line x <xsl:value-of select="$vert_line_x_"/></xsl:message>
		<xsl:message>bus index <xsl:value-of select="@BUS_INDEX"/></xsl:message>
-->		
		
		<xsl:variable name="vert_line_x_">
			<xsl:choose>
				<xsl:when test="@ORIENTED='WEST'">
					<xsl:value-of select="($bc_X_ - ($BLKD_BUS_LANE_W - $BLKD_BIFC_W))"/>
				</xsl:when>
				<xsl:when test="@ORIENTED='EAST'">
					<xsl:value-of select="($bc_X_ + ($BLKD_BUS_LANE_W - $BLKD_P2P_BUS_W))"/>
				</xsl:when>
			</xsl:choose>
		</xsl:variable>	
		
		<!-- At least one of the points is going to be the bus -->
<!--		
		<xsl:variable name="vert_line_y1_" select="($G_SharedBus_Y  + $BLKD_PROC2SBS_GAP + (@BUS_INDEX * $BLKD_SBS_LANE_H))"/>
-->		
		<xsl:variable name="vert_line_y1_" select="($G_SharedBus_Y  + (@BUS_INDEX * $BLKD_SBS_LANE_H))"/>
		<xsl:variable name="vert_line_y2_" select="$bc_Y_ + ceiling($BLKD_BIFC_H div 2)"/>
		
		<xsl:variable name="v_bus_ul_y_">
			<xsl:choose>
				<xsl:when test="$vert_line_y1_ &gt; $vert_line_y2_">
					<xsl:value-of select="$vert_line_y2_"/>
				</xsl:when>
				<xsl:when test="$vert_line_y2_ &gt; $vert_line_y1_">
					<xsl:value-of select="$vert_line_y1_"/>
				</xsl:when>
			</xsl:choose>
		</xsl:variable>	
<!--		
		<xsl:variable name="v_bus_ul_x_" select="$vert_line_x_"/>
-->	
		<xsl:variable name="v_bus_ul_x_">
			<xsl:choose>
				<xsl:when test="@ORIENTED='WEST'">
					<xsl:value-of select="($vert_line_x_ + $BLKD_MOD_BIF_GAP_H)"/>
				</xsl:when>
				<xsl:when test="@ORIENTED='EAST'">
					<xsl:value-of select="($vert_line_x_ - $BLKD_MOD_BIF_GAP_H)"/>
				</xsl:when>
			</xsl:choose>
		</xsl:variable>	
		
		
		<xsl:variable name="v_bus_width_" select="$BLKD_P2P_BUS_W"/>
		<xsl:variable name="v_bus_height_">
			<xsl:choose>
				<xsl:when test="$vert_line_y1_ &gt; $vert_line_y2_">
					<xsl:value-of select="($vert_line_y1_ - $vert_line_y2_)"/>
				</xsl:when>
				<xsl:when test="$vert_line_y2_ &gt; $vert_line_y1_">
					<xsl:value-of select="($vert_line_y2_ - $vert_line_y1_)"/>
				</xsl:when>
			</xsl:choose>
		</xsl:variable>	
		
		<xsl:variable name="h_bus_ul_x_">
			<xsl:choose>
				<xsl:when test="@ORIENTED='WEST'">
					<xsl:value-of select="($bc_X_ - ($BLKD_BUS_LANE_W - $BLKD_BIFC_W) + $BLKD_MOD_BIF_GAP_H)"/>
				</xsl:when>
				<xsl:when test="@ORIENTED='EAST'">
					<xsl:value-of select="($bc_X_ + $BLKD_BIFC_W - ceiling(($BLKD_BIFC_W - $BLKD_BIFC_Wi) div 2))"/>
				</xsl:when>
			</xsl:choose>
		</xsl:variable>	
		
		<xsl:variable name="h_bus_ul_y_" select="$bc_Y_ + ceiling($BLKD_BIFC_H div 2) - ceiling($BLKD_P2P_BUS_W div 2)"/>
		<xsl:variable name="h_bus_height_" select="$BLKD_P2P_BUS_W"/>
		
		<xsl:variable name="h_bus_width_">
			<xsl:choose>
				<xsl:when test="@ORIENTED='WEST'">
					<xsl:value-of select="(($bc_X_ + ceiling(($BLKD_BIFC_W - $BLKD_BIFC_Wi) div 2)) - $h_bus_ul_x_ + 1)"/>
				</xsl:when>
				<xsl:when test="@ORIENTED='EAST'">
					<xsl:value-of select="(($v_bus_ul_x_ + $BLKD_P2P_BUS_W) - $h_bus_ul_x_)"/>
				</xsl:when>
			</xsl:choose>
		</xsl:variable>	
		
		
<!--		
		<xsl:message>vert line y1 <xsl:value-of select="$vert_line_y1_"/></xsl:message>
-->		
		
		<rect x="{$v_bus_ul_x_}" 
		  	  y="{$v_bus_ul_y_ + 2}"  
		 	  width= "{$v_bus_width_}" 
		 	  height="{$v_bus_height_}" 
		 	  style="stroke:none; fill:{$busColor_}"/>
		
		<rect x="{$h_bus_ul_x_}" 
		  	  y="{$h_bus_ul_y_}"  
		 	  width= "{$h_bus_width_}" 
		 	  height="{$h_bus_height_}" 
		 	  style="stroke:none; fill:{$busColor_}"/>
		
	</xsl:for-each>	
	
</xsl:template>
	
	
	
	
<!-- =========================================================================== -->
<!--                          FUNCTION TEMPLATE                                  -->
<!--																			 -->
<!-- Draw the IP Bucket          												 -->
<!-- =========================================================================== -->
<xsl:template name="Draw_BlkDiagram_IPBucket">
	
	<!-- Draw IP Bucket -->	
	<xsl:for-each select="$G_ROOT/EDKSYSTEM/BLKDIAGRAM/IPBUCKET">
	
		<xsl:variable name="bucket_w_"  select="(($BLKD_MOD_BKTLANE_W * 2) + (($BLKD_MOD_W * @MODS_W) + ($BLKD_MOD_BUCKET_G * (@MODS_W - 1))))"/>
		<xsl:variable name="bucket_h_"  select="(($BLKD_MOD_BKTLANE_H * 2) + (($BLKD_MOD_H * @MODS_H) + ($BLKD_MOD_BUCKET_G * (@MODS_H - 1))))"/>
		
		<xsl:variable name="bucket_x_"  select="(ceiling($G_Total_Blkd_W div 2) - ceiling($bucket_w_ div 2))"/>
		<xsl:variable name="bucket_y_"  select="($G_SharedBus_Y + $G_Total_SharedBus_H + $G_Max_Stack_BlwSbs_H + $BLKD_SBS2IP_GAP)"/>
		
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="$bucket_x_"/>
			<xsl:with-param name="iY" 		select="($bucket_y_ - 4)"/>
			<xsl:with-param name="iText"	select="'IP'"/>
			<xsl:with-param name="iClass"	select="'bkt_label'"/>
		</xsl:call-template>
		
		<use   x="{$bucket_x_}"   y="{$bucket_y_}"  xlink:href="#ipbucket"/>
		
	</xsl:for-each>
	
</xsl:template>
	
	
<xsl:template name="Draw_BlkDiagram_Key">
	<use   x="{ceiling($G_Total_Blkd_W div 2) - ceiling($BLKD_KEY_W div 2)}"   y="0"  xlink:href="#BlkDiagram_Key"/> 
</xsl:template>

<xsl:template name="Define_BlkDiagram_Key">
	
	<xsl:variable name="key_col_">
		<xsl:call-template name="F_BusStd2RGB">
			<xsl:with-param name="iBusStd" select="'KEY'"/>
		</xsl:call-template>	
	</xsl:variable>
	
	<xsl:variable name="key_lt_col_">
		<xsl:call-template name="F_BusStd2RGB_LT">
			<xsl:with-param name="iBusStd" select="'KEY'"/>
		</xsl:call-template>	
	</xsl:variable>
	
	<g id="KEY_IntrCntrl">
		<rect  
			x="0"
			y="0"
			rx="3"
			ry="3"
			width= "{ceiling($BLKD_INTR_W div 2)}" 
			height="{$BLKD_INTR_H}" style="fill:{$key_lt_col_}; stroke:none; stroke-width:1"/> 
			
		<line x1="0" 
			  y1="{ceiling($BLKD_INTR_H div 4)}"
			  x2="{ceiling($BLKD_INTR_W div 2)}" 
			  y2="{ceiling($BLKD_INTR_H div 4)}" 
			  style="stroke:{$COL_BLACK};stroke-width:2"/>

		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="1.5"/>
			<xsl:with-param name="iY" 		select="(7 + ceiling($BLKD_INTR_H div 2))"/>
			<xsl:with-param name="iText"	select="'x'"/>
			<xsl:with-param name="iClass"	select="'intr_symbol'"/>
		</xsl:call-template>
			
	</g>
		
	<g id="KEY_IntrdProc">
		<rect  
			x="0"
			y="0"
			rx="3"
			ry="3"
			width= "{ceiling($BLKD_INTR_W div 2)}" 
			height="{$BLKD_INTR_H}" style="fill:{$key_lt_col_}; stroke:none; stroke-width:1"/> 
			
		<line x1="0" 
			  y1="{ceiling($BLKD_INTR_H div 4) - 2}"
			  x2="{ceiling($BLKD_INTR_W div 2)}" 
			  y2="{ceiling($BLKD_INTR_H div 4) - 2}" 
			  style="stroke:{$COL_BLACK};stroke-width:1"/>
			  
		<line x1="0" 
			  y1="{ceiling($BLKD_INTR_H div 4) + 2}"
			  x2="{ceiling($BLKD_INTR_W div 2)}" 
			  y2="{ceiling($BLKD_INTR_H div 4) + 2}" 
			  style="stroke:{$COL_BLACK};stroke-width:1"/>
			  
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="1.5"/>
			<xsl:with-param name="iY" 		select="(7 + ceiling($BLKD_INTR_H div 2))"/>
			<xsl:with-param name="iText"	select="'x'"/>
			<xsl:with-param name="iClass"	select="'intr_symbol'"/>
		</xsl:call-template>
	</g>
	
	<g id="KEY_IntrSrc">
		<rect  
			x="0"
			y="0"
			rx="3"
			ry="3"
			width= "{$BLKD_INTR_W}" 
			height="{ceiling($BLKD_INTR_H div 2)}" style="fill:{$key_lt_col_}; stroke:none; stroke-width:1"/> 
			
		<line x1="{ceiling($BLKD_INTR_W div 2)}" 
			  y1="0"
			  x2="{ceiling($BLKD_INTR_W div 2)}" 
			  y2="{ceiling($BLKD_INTR_H div 2)}" 
			  style="stroke:{$COL_BLACK};stroke-width:1"/>
			  
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="'2'"/>
			<xsl:with-param name="iY" 		select="'7'"/>
			<xsl:with-param name="iText"	select="'y'"/>
			<xsl:with-param name="iClass"	select="'intr_symbol'"/>
		</xsl:call-template>
			  
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="(2 + ceiling($BLKD_INTR_W div 2))"/>
			<xsl:with-param name="iY" 		select="'7'"/>
			<xsl:with-param name="iText"	select="'x'"/>
			<xsl:with-param name="iClass"	select="'intr_symbol'"/>
		</xsl:call-template>
	</g>
	
	
	<g id="BlkDiagram_Key">
		<rect 
              x="0"
			  y="0"
		      width= "{$BLKD_KEY_W}"
		      height="{$BLKD_KEY_H}"
			  style="fill:{$COL_BG}; stroke:none;"/>		
			  
		<rect x="0"
			  y="0"
		      width= "{$BLKD_KEY_W}"
		      height="16"
			  style="fill:{$COL_BG}; stroke:none;"/>		
			  
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="ceiling($BLKD_KEY_W div 2)"/>
			<xsl:with-param name="iY" 		select="'14'"/>
			<xsl:with-param name="iText"	select="'KEY'"/>
			<xsl:with-param name="iClass"	select="'key_title'"/>
		</xsl:call-template>
			  
		<rect x="0"
			  y="16"
		      width= "{$BLKD_KEY_W}"
		      height="16"
			  style="fill:{$COL_BG_LT}; stroke:none;"/>		

		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="ceiling($BLKD_KEY_W div 2)"/>
			<xsl:with-param name="iY" 		select="'30'"/>
			<xsl:with-param name="iText"	select="'SYMBOLS'"/>
			<xsl:with-param name="iClass"	select="'key_header'"/>
		</xsl:call-template>
			  
   		<use  x="32"  y="47"  xlink:href="#KEY_BifLabel" transform="scale(0.75)"/> 
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="'12'"/>
			<xsl:with-param name="iY" 		select="'60'"/>
			<xsl:with-param name="iText"	select="'bus interface'"/>
			<xsl:with-param name="iClass"	select="'key_label'"/>
		</xsl:call-template>
			  
   		<use   x="20"  y="68"  xlink:href="#KEY_SharedBus"/> 
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="'12'"/>
			<xsl:with-param name="iY" 		select="'89'"/>
			<xsl:with-param name="iText"	select="'shared bus'"/>
			<xsl:with-param name="iClass"	select="'key_label'"/>
		</xsl:call-template>
			  
   		
<!-- 
	==================================					
			BUS CONNECTIONS
	==================================					
-->		

		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="'110'"/>
			<xsl:with-param name="iY" 		select="'47'"/>
			<xsl:with-param name="iText"	select="'Bus connections'"/>
			<xsl:with-param name="iClass"	select="'key_label_ul'"/>
		</xsl:call-template>
			  
   		<use   x="110"  y="58"  xlink:href="#KEY_busconn_MASTER"/> 
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="'140'"/>
			<xsl:with-param name="iY" 		select="'72'"/>
			<xsl:with-param name="iText"	select="'master or initiator'"/>
			<xsl:with-param name="iClass"	select="'key_label'"/>
		</xsl:call-template>
			  
   		<use   x="110"  y="{58 + (($BLKD_BIFC_H  + 4) * 1)}"  xlink:href="#KEY_busconn_SLAVE"/> 
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="'140'"/>
			<xsl:with-param name="iY" 		select="(72 + (($BLKD_BIFC_H + 4) * 1))"/>
			<xsl:with-param name="iText"	select="'slave or target'"/>
			<xsl:with-param name="iClass"	select="'key_label'"/>
		</xsl:call-template>
			  
   		<use   x="110"  y="{58 + (($BLKD_BIFC_H  + 4) * 2)}"  xlink:href="#KEY_busconn_MASTER_SLAVE"/> 
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="'140'"/>
			<xsl:with-param name="iY" 		select="(72 + (($BLKD_BIFC_H + 4) * 2))"/>
			<xsl:with-param name="iText"	select="'master slave'"/>
			<xsl:with-param name="iClass"	select="'key_label'"/>
		</xsl:call-template>
			  
			  
   		<use   x="110"  y="{58 + (($BLKD_BIFC_H  + 4) * 3)}"  xlink:href="#KEY_busconn_MONITOR"/>
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="'140'"/>
			<xsl:with-param name="iY" 		select="(72 + (($BLKD_BIFC_H + 4) * 3))"/>
			<xsl:with-param name="iText"	select="'monitor'"/>
			<xsl:with-param name="iClass"	select="'key_label'"/>
		</xsl:call-template>
			  
<!-- 
	==================================					
			EXTERNAL PORTS
	==================================					
-->		
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="'258'"/>
			<xsl:with-param name="iY" 		select="'47'"/>
			<xsl:with-param name="iText"	select="'External Ports'"/>
			<xsl:with-param name="iClass"	select="'key_label_ul'"/>
		</xsl:call-template>			  
			  
   		<use   x="258"  y="58"  xlink:href="#KEY_INPort"/> 
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="'288'"/>
			<xsl:with-param name="iY" 		select="'72'"/>
			<xsl:with-param name="iText"	select="'input'"/>
			<xsl:with-param name="iClass"	select="'key_label'"/>
		</xsl:call-template>
			  
   		<use   x="258"  y="{58 + ($BLKD_IOP_H * 1) + 4}"  xlink:href="#KEY_OUTPort"/> 
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="'288'"/>
			<xsl:with-param name="iY" 		select="(72 + ($BLKD_IOP_H * 1) + 4)"/>
			<xsl:with-param name="iText"	select="'output'"/>
			<xsl:with-param name="iClass"	select="'key_label'"/>
		</xsl:call-template>
			
   		<use   x="258"  y="{58 + ($BLKD_IOP_H * 2) + 8}"  xlink:href="#KEY_INOUTPort"/> 
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="'288'"/>
			<xsl:with-param name="iY" 		select="(72 + ($BLKD_IOP_H * 2) + 8)"/>
			<xsl:with-param name="iText"	select="'inout'"/>
			<xsl:with-param name="iClass"	select="'key_label'"/>
		</xsl:call-template>
		
		
<!-- 
	==================================					
			INTERRUPTS 
	==================================					
-->		
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="'380'"/>
			<xsl:with-param name="iY" 		select="'47'"/>
			<xsl:with-param name="iText"	select="'Interrupts'"/>
			<xsl:with-param name="iClass"	select="'key_label_ul'"/>
		</xsl:call-template>			  
			  
   		<use   x="380"  y="58"  xlink:href="#KEY_IntrCntrl"/> 
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="'396'"/>
			<xsl:with-param name="iY" 		select="'64'"/>
			<xsl:with-param name="iText"	select="'Interrupt'"/>
			<xsl:with-param name="iClass"	select="'key_label_small'"/>
		</xsl:call-template>			  
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="'396'"/>
			<xsl:with-param name="iY" 		select="'74'"/>
			<xsl:with-param name="iText"	select="'Controller'"/>
			<xsl:with-param name="iClass"	select="'key_label_small'"/>
		</xsl:call-template>			  
			  
		
		<use   x="380"  y="88"  xlink:href="#KEY_IntrdProc"/> 
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="'396'"/>
			<xsl:with-param name="iY" 		select="'94'"/>
			<xsl:with-param name="iText"	select="'Interrupt'"/>
			<xsl:with-param name="iClass"	select="'key_label'"/>
		</xsl:call-template>			  
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="'396'"/>
			<xsl:with-param name="iY" 		select="'104'"/>
			<xsl:with-param name="iText"	select="'Target'"/>
			<xsl:with-param name="iClass"	select="'key_label_small'"/>
		</xsl:call-template>			  
		
		
		<use   x="380"  y="118"  xlink:href="#KEY_IntrSrc"/> 
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="'400'"/>
			<xsl:with-param name="iY" 		select="'124'"/>
			<xsl:with-param name="iText"	select="'Interrupt'"/>
			<xsl:with-param name="iClass"	select="'key_label_small'"/>
		</xsl:call-template>			  
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="'400'"/>
			<xsl:with-param name="iY" 		select="'134'"/>
			<xsl:with-param name="iText"	select="'Source'"/>
			<xsl:with-param name="iClass"	select="'key_label_small'"/>
		</xsl:call-template>			  
			  
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="'360'"/>
			<xsl:with-param name="iY" 		select="'146'"/>
			<xsl:with-param name="iText"	select="'X = Controller ID'"/>
			<xsl:with-param name="iClass"	select="'key_label_small'"/>
		</xsl:call-template>			  
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="'360'"/>
			<xsl:with-param name="iY" 		select="'156'"/>
			<xsl:with-param name="iText"	select="'Y = Interrupt Priority'"/>
			<xsl:with-param name="iClass"	select="'key_label_small'"/>
		</xsl:call-template>			  
		
<!-- 
	==================================					
			COLORS 
	==================================					
-->		
		<rect x="0"
			  y="160"
		      width= "{$BLKD_KEY_W}"
		      height="16"
			  style="fill:{$COL_BG_LT}; stroke:none;"/>		
			  
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="ceiling($BLKD_KEY_W div 2)"/>
			<xsl:with-param name="iY" 		select="'172'"/>
			<xsl:with-param name="iText"	select="'COLORS'"/>
			<xsl:with-param name="iClass"	select="'key_header'"/>
		</xsl:call-template>
		
<!-- 
		<text class="keylblul"
              x="110"
			  y="190">Bus Standards</text>		  
-->			  
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="'110'"/>
			<xsl:with-param name="iY" 		select="'190'"/>
			<xsl:with-param name="iText"	select="'Bus Standard'"/>
			<xsl:with-param name="iClass"	select="'key_label'"/>
		</xsl:call-template>
		
		<xsl:variable name="dcr_col_">
			<xsl:call-template name="F_BusStd2RGB">
				<xsl:with-param name="iBusStd" select="'DCR'"/>
			</xsl:call-template>	
		</xsl:variable>
		
		<rect x="{12 + ((12 + $BLKD_BIFC_W + 36) * 0)}"
			  y="200"
		      width= "{$BLKD_BIFC_H}"
		      height="{$BLKD_BIFC_W}"
			  style="fill:{$dcr_col_}; stroke:none;"/>		
			  
<!-- 
		<text class="keylabel"
              x="{12  + $BLKD_BIFC_W + 4}"
			  y="{200 + (($BLKD_BIF_H + 4) * 1)}">DCR</text>
-->			  
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="(12  + $BLKD_BIFC_W + 4)"/>
			<xsl:with-param name="iY" 		select="(200 + (($BLKD_BIF_H + 4) * 1))"/>
			<xsl:with-param name="iText"	select="'DCR'"/>
			<xsl:with-param name="iClass"	select="'key_label'"/>
		</xsl:call-template>
			  
		<xsl:variable name="fcb_col_">
			<xsl:call-template name="F_BusStd2RGB">
				<xsl:with-param name="iBusStd" select="'FCB'"/>
			</xsl:call-template>	
		</xsl:variable>
		
		<rect x="{12  + ((12 + $BLKD_BIFC_W + 36) * 0)}"
			  y="{200 + (($BLKD_BIFC_H + 4) * 1)}"
		      width= "{$BLKD_BIFC_H}"
		      height="{$BLKD_BIFC_W}"
			  style="fill:{$fcb_col_}; stroke:none;"/>		
			  
<!-- 
		<text class="keylabel"
              x="{12  + $BLKD_BIFC_W + 4}"
			  y="{200 + (($BLKD_BIF_H + 4) * 2)}">FCB</text>		  
-->			  
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="(12  + $BLKD_BIFC_W + 4)"/>
			<xsl:with-param name="iY" 		select="(200 + (($BLKD_BIF_H + 4) * 2))"/>
			<xsl:with-param name="iText"	select="'FCB'"/>
			<xsl:with-param name="iClass"	select="'key_label'"/>
		</xsl:call-template>
		
		<xsl:variable name="fsl_col_">
			<xsl:call-template name="F_BusStd2RGB">
				<xsl:with-param name="iBusStd" select="'FSL'"/>
			</xsl:call-template>	
		</xsl:variable>
			  
		<rect x="{12 + ((12 + $BLKD_BIFC_W + 36) * 1)}"
			  y="200"
		      width= "{$BLKD_BIFC_H}"
		      height="{$BLKD_BIFC_W}"
			  style="fill:{$fsl_col_}; stroke:none;"/>		
<!-- 
		<text class="keylabel"
              x="{12  +  ($BLKD_BIFC_W + 4) + ((12 + $BLKD_BIFC_W + 36) * 1)}"
			  y="{200 + (($BLKD_BIF_H + 4) * 1)}">FSL</text>		  
-->

		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="(12  +  ($BLKD_BIFC_W + 4) + ((12 + $BLKD_BIFC_W + 36) * 1))"/>
			<xsl:with-param name="iY" 		select="(200 + (($BLKD_BIF_H + 4) * 1))"/>
			<xsl:with-param name="iText"	select="'FSL'"/>
			<xsl:with-param name="iClass"	select="'key_label'"/>
		</xsl:call-template>
		
		<xsl:variable name="col_lmb_">
			<xsl:call-template name="F_BusStd2RGB">
				<xsl:with-param name="iBusStd" select="'LMB'"/>
			</xsl:call-template>	
		</xsl:variable>
			  
		<rect x="{12 + ((12 + $BLKD_BIFC_W + 36) * 1)}"
			  y="{200 + (($BLKD_BIFC_H + 4) * 1)}"
		      width= "{$BLKD_BIFC_H}"
		      height="{$BLKD_BIFC_W}"
			  style="fill:{$col_lmb_}; stroke:none;"/>		
<!--
		<text class="keylabel"
              x="{12  + ($BLKD_BIFC_W + 4) + ((12 + $BLKD_BIFC_W + 36) * 1)}"
			  y="{200 + (($BLKD_BIF_H + 4) * 2)}">LMB</text>		  
-->			  

		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="(12  + ($BLKD_BIFC_W + 4) + ((12 + $BLKD_BIFC_W + 36) * 1))"/>
			<xsl:with-param name="iY" 		select="(200 + (($BLKD_BIF_H + 4) * 2))"/>
			<xsl:with-param name="iText"	select="'LMB'"/>
			<xsl:with-param name="iClass"	select="'key_label'"/>
		</xsl:call-template>
		
		<xsl:variable name="opb_col_">
			<xsl:call-template name="F_BusStd2RGB">
				<xsl:with-param name="iBusStd" select="'OPB'"/>
			</xsl:call-template>	
		</xsl:variable>
			  
		<rect 
              x="{12 + ((12 + $BLKD_BIFC_W + 36) * 2)}"
			  y="200"
		      width= "{$BLKD_BIFC_H}"
		      height="{$BLKD_BIFC_W}"
			  style="fill:{$opb_col_}; stroke:none;"/>		
<!-- 
		<text class="keylabel"
              x="{12  +  ($BLKD_BIFC_W + 4) + ((12 + $BLKD_BIFC_W + 36) * 2)}"
			  y="{200 + (($BLKD_BIF_H + 4) * 1)}">OPB</text>
-->			  
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="(12  +  ($BLKD_BIFC_W + 4) + ((12 + $BLKD_BIFC_W + 36) * 2))"/>
			<xsl:with-param name="iY" 		select="(200 + (($BLKD_BIF_H + 4) * 1))"/>
			<xsl:with-param name="iText"	select="'OPB'"/>
			<xsl:with-param name="iClass"	select="'key_label'"/>
		</xsl:call-template>
		
		<xsl:variable name="plb_col_">
			<xsl:call-template name="F_BusStd2RGB">
				<xsl:with-param name="iBusStd" select="'PLB'"/>
			</xsl:call-template>	
		</xsl:variable>
		<rect 
              x="{12 + ((12 + $BLKD_BIFC_W + 36) * 2)}"
			  y="{200 + (($BLKD_BIFC_H + 4) * 1)}"
		      width= "{$BLKD_BIFC_H}"
		      height="{$BLKD_BIFC_W}"
			  style="fill:{$plb_col_}; stroke:none;"/>		
<!--
		<text class="keylabel"
              x="{12  +  ($BLKD_BIFC_W + 4) + ((12 + $BLKD_BIFC_W + 36) * 2)}"
			  y="{200 + (($BLKD_BIF_H + 4) * 2)}">PLB</text>		  
-->			  
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="(12  +  ($BLKD_BIFC_W + 4) + ((12 + $BLKD_BIFC_W + 36) * 2))"/>
			<xsl:with-param name="iY" 		select="(200 + (($BLKD_BIF_H + 4) * 2))"/>
			<xsl:with-param name="iText"	select="'PLB'"/>
			<xsl:with-param name="iClass"	select="'key_header'"/>
		</xsl:call-template>
		
			 
		<xsl:variable name="ocm_col_">
			<xsl:call-template name="F_BusStd2RGB">
				<xsl:with-param name="iBusStd" select="'OCM'"/>
			</xsl:call-template>	
		</xsl:variable>
			  
		<rect 
              x="{12 + ((12 + $BLKD_BIFC_W + 36) * 3)}"
			  y="200"
		      width= "{$BLKD_BIFC_H}"
		      height="{$BLKD_BIFC_W}"
			  style="fill:{$ocm_col_}; stroke:none;"/>		
<!--
		<text class="keylabel"
              x="{12  + ($BLKD_BIFC_W + 4) + ((12 + $BLKD_BIFC_W + 36) * 3)}"
			  y="{200 + (($BLKD_BIF_H + 4) * 1)}">SOCM</text>
 -->			  
		
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="(12  + ($BLKD_BIFC_W + 4) + ((12 + $BLKD_BIFC_W + 36) * 3))"/>
			<xsl:with-param name="iY" 		select="(200 + (($BLKD_BIF_H + 4) * 1))"/>
			<xsl:with-param name="iText"	select="'SOCM'"/>
			<xsl:with-param name="iClass"	select="'key_label'"/>
		</xsl:call-template>
		
		
		<xsl:variable name="xil_p2p_col_">
			<xsl:call-template name="F_BusStd2RGB">
				<xsl:with-param name="iBusStd" select="'XIL'"/>
			</xsl:call-template>	
		</xsl:variable>
			  
		<rect 
              x="{12 + ((12 + $BLKD_BIFC_W + 36) * 3)}"
			  y="{200 + (($BLKD_BIFC_H + 4) * 1)}"
		      width= "{$BLKD_BIFC_H}"
		      height="{$BLKD_BIFC_W}"
			  style="fill:{$xil_p2p_col_}; stroke:none;"/>		
<!--
		<text class="keylabel"
              x="{12  + ($BLKD_BIFC_W + 4) + ((12 + $BLKD_BIFC_W + 36) * 3)}"
			  y="{200 + (($BLKD_BIF_H + 4) * 2)}">Xilinx P2P</text>
-->			  
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="(12  + ($BLKD_BIFC_W + 4) + ((12 + $BLKD_BIFC_W + 36) * 3))"/>
			<xsl:with-param name="iY" 		select="(200 + (($BLKD_BIF_H + 4) * 2))"/>
			<xsl:with-param name="iText"	select="'Xilinx P2P'"/>
			<xsl:with-param name="iClass"	select="'key_label'"/>
		</xsl:call-template>
		
			  
		<xsl:variable name="user_p2p_col_">
			<xsl:call-template name="F_BusStd2RGB">
				<xsl:with-param name="iBusStd" select="'USER'"/>
			</xsl:call-template>	
		</xsl:variable>
			  
		<rect x="{12 + ((12 + $BLKD_BIFC_W + 36) * 4)}"
			  y="200"
		      width= "{$BLKD_BIFC_H}"
		      height="{$BLKD_BIFC_W}"
			  style="fill:{$user_p2p_col_}; stroke:none;"/>		
<!-- 
		<text class="keylabel"
              x="{12  + ($BLKD_BIFC_W + 4) + ((12 + $BLKD_BIFC_W + 36) * 4)}"
			  y="{200 + (($BLKD_BIF_H + 4) * 1)}">USER P2P</text>		  
-->			  

		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iX" 		select="(12  + ($BLKD_BIFC_W + 4) + ((12 + $BLKD_BIFC_W + 36) * 4))"/>
			<xsl:with-param name="iY" 		select="(200 + (($BLKD_BIF_H + 4) * 1))"/>
			<xsl:with-param name="iText"	select="'USER P2P'"/>
			<xsl:with-param name="iClass"	select="'key_label'"/>
		</xsl:call-template>
		
 
</g>	
</xsl:template>

<xsl:template name="Define_BlkDiagram_Specs">

	<xsl:param name="iArch"       select="'NA'"/>
	<xsl:param name="iPart"       select="'NA'"/>
	<xsl:param name="iTimeStamp"  select="'NA'"/>
	<xsl:param name="iEdkVersion" select="'NA'"/>
			
	<g id="BlkDiagram_Specs">
		<rect 
              x="0"
			  y="0"
		      width= "{$BLKD_SPECS_W}"
		      height="{$BLKD_SPECS_H}"
			  style="fill:{$COL_BG}; stroke:none;"/>		
			  
		<rect 
              x="0"
			  y="0"
		      width= "{$BLKD_SPECS_W}"
		      height="16"
			  style="fill:{$COL_BG}; stroke:none;"/>		
<!-- 
	==================================					
					SPEC HEADER
	==================================					
-->		
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iClass"	select="'key_title'"/>
			<xsl:with-param name="iX" 		select="ceiling($BLKD_SPECS_W div 2)"/>
			<xsl:with-param name="iY" 		select="'14'"/>
			<xsl:with-param name="iText"	select="'SPECS'"/>
		</xsl:call-template>			  
<!-- 
		<text class="keytitle"
              x="{ceiling($BLKD_SPECS_W div 2)} "
			  y="14">SPECS</text>
-->			  
	
<!-- 
	==================================					
			EDK VERSION
	==================================					
-->		
		<rect x="0"
			  y="20"
		      width= "{$BLKD_SPECS_W}"
		      height="16"
			  style="fill:{$COL_BG_LT}; stroke:none;"/>		
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iClass"	select="'blkd_spec_name'"/>
			<xsl:with-param name="iX" 		select="'4'"/>
			<xsl:with-param name="iY" 		select="'32'"/>
			<xsl:with-param name="iText"	select="'EDK VERSION'"/>
		</xsl:call-template>
			  
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iClass"	select="'blkd_spec_value_mid'"/>
			<xsl:with-param name="iX" 		select="($BLKD_SPECS_W + 1) - ceiling($BLKD_SPECS_W div 5)"/>
			<xsl:with-param name="iY" 		select="'32'"/>
			<xsl:with-param name="iText"	select="$iEdkVersion"/>
		</xsl:call-template>			  
		
<!-- 
	==================================					
					ARCH
	==================================					
-->		
		<rect x="0"
			  y="40"
		      width= "{$BLKD_SPECS_W}"
		      height="16"
			  style="fill:{$COL_BG_LT}; stroke:none;"/>		
			  
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iClass"	select="'blkd_spec_name'"/>
			<xsl:with-param name="iX" 		select="'4'"/>
			<xsl:with-param name="iY" 		select="'52'"/>
			<xsl:with-param name="iText"	select="'ARCH'"/>
		</xsl:call-template>			  
		
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iClass"	select="'blkd_spec_value_mid'"/>
			<xsl:with-param name="iX" 		select="($BLKD_SPECS_W + 1) - ceiling($BLKD_SPECS_W div 5)"/>
			<xsl:with-param name="iY" 		select="'52'"/>
			<xsl:with-param name="iText"	select="$iArch"/>
		</xsl:call-template>			  
		
<!--		
		<text class="specsvalue"
              x="{($BLKD_SPECS_W + 1) - (string-length($blkd_arch) * 6.5)}"
			  y="52"><xsl:value-of select="$blkd_arch"/></text>
		<text class="specsvaluemid"
              x="{($BLKD_SPECS_W + 1) - ceiling($BLKD_SPECS_W div 5)}"
			  y="52"><xsl:value-of select="$iArch"/></text>
-->		

<!-- 
	==================================					
					PART
	==================================					
-->		
		<rect x="0"
			  y="60"
		      width= "{$BLKD_SPECS_W}"
		      height="16"
			  style="fill:{$COL_BG_LT}; stroke:none;"/>		
			  
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iClass"	select="'blkd_spec_name'"/>
			<xsl:with-param name="iX" 		select="'4'"/>
			<xsl:with-param name="iY" 		select="'72'"/>
			<xsl:with-param name="iText"	select="'PART'"/>
		</xsl:call-template>			  
			  
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iClass"	select="'blkd_spec_value_mid'"/>
			<xsl:with-param name="iX" 		select="($BLKD_SPECS_W + 1) - ceiling($BLKD_SPECS_W div 5)"/>
			<xsl:with-param name="iY" 		select="'72'"/>
			<xsl:with-param name="iText"	select="$iPart"/>
		</xsl:call-template>			  
		
<!-- 
	==================================					
					TIMESTAMP
	==================================					
-->		
			  
		<rect x="0"
			  y="80"
		      width= "{$BLKD_SPECS_W}"
		      height="16"
			  style="fill:{$COL_BG_LT}; stroke:none;"/>		

		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iClass"	select="'blkd_spec_name'"/>
			<xsl:with-param name="iX" 		select="'4'"/>
			<xsl:with-param name="iY" 		select="'92'"/>
			<xsl:with-param name="iText"	select="'GENERATED'"/>
		</xsl:call-template>			  
		
		<xsl:call-template name="F_WriteText">
			<xsl:with-param name="iClass"	select="'blkd_spec_value_mid'"/>
			<xsl:with-param name="iX" 		select="($BLKD_SPECS_W  + 1) - (string-length($iTimeStamp) * 3.5)"/>
			<xsl:with-param name="iY" 		select="'92'"/>
			<xsl:with-param name="iText"	select="$iTimeStamp"/>
		</xsl:call-template>			  
	</g>	
</xsl:template>
	
	
</xsl:stylesheet>

<!-- =========================================================================== -->
<!--                          FUNCTION TEMPLATE                                  -->
<!--																			 -->
<!-- =========================================================================== -->